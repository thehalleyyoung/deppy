"""§7: Operad-Based Denotational Semantics.

Compiles Python functions to a canonical denotation — a high-level
term in a universal algebra of operations. Two programs with the
same denotation are provably equivalent.

The key insight: instead of tracking every intermediate variable
through Z3, extract the SPECIFICATION of what the function computes:
what operations it applies to its inputs and in what order.

This is the OTerm language from the monograph:
  OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict
"""
from __future__ import annotations
import ast
import hashlib
import textwrap
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union


def _hash(s: str) -> str:
    return hashlib.md5(s.encode()).hexdigest()[:8]


def _canonicalize_free_vars(canon_str: str, bound_prefixes: tuple = ('$0', '$1', '$2', '$3')) -> str:
    """Replace free variable names in a canonical string with positional names.

    Fold body hashes must be invariant to the naming of closed-over
    (free) variables.  Bound variables (accumulator $0, element $1, ...)
    are already canonical.  Any remaining $-prefixed names (like $mod,
    $p1, etc.) are free variables captured from the enclosing scope.
    We replace them with $f0, $f1, ... in order of first appearance so
    that the hash is stable regardless of parameter renaming.
    """
    import re
    # Find all $-prefixed variable tokens that aren't bound vars
    tokens = re.findall(r'\$[a-zA-Z_][a-zA-Z0-9_]*', canon_str)
    free_map: dict[str, str] = {}
    counter = 0
    for tok in tokens:
        if tok in ('$0', '$1', '$2', '$3', '$4', '$5'):
            continue  # bound var, skip
        if tok not in free_map:
            free_map[tok] = f'$f{counter}'
            counter += 1
    result = canon_str
    # Replace longest tokens first to avoid partial replacement
    for orig, repl in sorted(free_map.items(), key=lambda x: -len(x[0])):
        result = result.replace(orig, repl)
    return result


# ═══════════════════════════════════════════════════════════
# OTerm: Universal Term Language
# ═══════════════════════════════════════════════════════════

@dataclass(frozen=True)
class OVar:
    name: str
    def canon(self) -> str:
        return f'${self.name}'

@dataclass(frozen=True)
class OLit:
    value: Any
    def canon(self) -> str:
        return repr(self.value)

@dataclass(frozen=True)
class OOp:
    """Application of a named operation."""
    name: str
    args: Tuple['OTerm', ...]

    # Commutative operations — argument order doesn't matter
    _COMMUTATIVE = frozenset({
        'add', 'mult', 'eq', 'noteq',
        'bitand', 'bitor', 'bitxor', 'min', 'max',
        'gcd', 'lcm',
    })

    def canon(self) -> str:
        arg_strs = [a.canon() for a in self.args]
        if self.name in OOp._COMMUTATIVE and len(arg_strs) == 2:
            arg_strs.sort()
        return f'{self.name}({",".join(arg_strs)})'

@dataclass(frozen=True)
class OFold:
    """Fold/reduce over a collection."""
    op_name: str  # the accumulation operation (or 8-char hash)
    init: 'OTerm'
    collection: 'OTerm'
    body_fn: 'Optional[OTerm]' = None  # optional OLam(acc, x) → new_acc
    def canon(self) -> str:
        return f'fold[{self.op_name}]({self.init.canon()},{self.collection.canon()})'

@dataclass(frozen=True)
class OCase:
    """Case/branch expression."""
    test: 'OTerm'
    true_branch: 'OTerm'
    false_branch: 'OTerm'
    def canon(self) -> str:
        return f'case({self.test.canon()},{self.true_branch.canon()},{self.false_branch.canon()})'

@dataclass(frozen=True)
class OFix:
    """Fixed point (recursion)."""
    name: str
    body: 'OTerm'
    def canon(self) -> str:
        return f'fix[{self.name}]({self.body.canon()})'

@dataclass(frozen=True)
class OSeq:
    """Sequence/list construction."""
    elements: Tuple['OTerm', ...]
    def canon(self) -> str:
        elem_strs = ','.join(e.canon() for e in self.elements)
        return f'[{elem_strs}]'

@dataclass(frozen=True)
class ODict:
    """Dictionary construction."""
    pairs: Tuple[Tuple['OTerm', 'OTerm'], ...]
    def canon(self) -> str:
        pair_strs = ','.join(f'{k.canon()}:{v.canon()}' for k, v in self.pairs)
        return f'{{{pair_strs}}}'

@dataclass(frozen=True)
class OUnknown:
    """Unknown/opaque term."""
    desc: str
    def canon(self) -> str:
        return f'?{self.desc}'

@dataclass(frozen=True)
class OQuotient:
    """Quotient type — wraps a term where ordering is irrelevant.

    This is the key construction for nondeterminism:
    set iteration, dict iteration, concurrent operations
    all produce results where order doesn't matter.
    The quotient normalizes by sorting canonical forms of elements.

    Implements: OTerm / ~_perm  (quotient by permutation group)
    """
    inner: 'OTerm'
    equiv_class: str  # 'perm' (set/dict order), 'comm' (commutative), 'idem' (idempotent)
    def canon(self) -> str:
        return f'Q[{self.equiv_class}]({self.inner.canon()})'

@dataclass(frozen=True)
class OAbstract:
    """Abstract specification — what a function computes at the highest level.

    Used for functions too complex to normalize syntactically.
    Two OAbstract terms match if they describe the same specification.
    """
    spec: str  # canonical spec string
    inputs: Tuple['OTerm', ...]
    def canon(self) -> str:
        arg_strs = ','.join(a.canon() for a in self.inputs)
        return f'@{self.spec}({arg_strs})'

@dataclass(frozen=True)
class OLam:
    """Lambda / anonymous function — a first-class function value.

    Unlike OUnknown('lambda'), this captures the body as an OTerm
    with bound parameter names, enabling structural comparison.
    Two lambdas with the same body (after alpha-renaming) are equal.

    This is the η-expansion principle: λx.f(x) = f when f doesn't
    capture x.  The canon() uses de Bruijn-style naming (bound vars
    become _0, _1, ...) so alpha-equivalent lambdas match.
    """
    params: Tuple[str, ...]
    body: 'OTerm'
    def canon(self) -> str:
        # Use stored param names directly (relies on _de_bruijn_normalize
        # for alpha-normalization before comparison).
        # For display before normalization, we do a simple local rename
        # that avoids cross-lambda capture by using the EXISTING param names.
        if all(p.startswith('_b') for p in self.params):
            # Already de Bruijn normalized — just emit
            return f'λ({",".join(self.params)}){self.body.canon()}'
        # Not yet normalized — do local rename for display consistency
        mapping = {p: f'_b{i}' for i, p in enumerate(self.params)}
        normalized = _subst(self.body, mapping)
        return f'λ({",".join(f"_b{i}" for i in range(len(self.params)))}){normalized.canon()}'

@dataclass(frozen=True)
class OMap:
    """Map/transform over a collection: [f(x) for x in coll].

    Unifies comprehensions, map(), and equivalent for-loops into a
    single canonical form.  The transform is an OLam.
    """
    transform: 'OTerm'  # typically OLam
    collection: 'OTerm'
    filter_pred: Optional['OTerm'] = None  # optional filter predicate (OLam)
    def canon(self) -> str:
        base = f'map({self.transform.canon()},{self.collection.canon()})'
        if self.filter_pred is not None:
            return f'filter_map({self.filter_pred.canon()},{self.transform.canon()},{self.collection.canon()})'
        return base

@dataclass(frozen=True)
class OCatch:
    """Exception-catching expression: try body except → default.

    Models try/except as a total function: evaluate body, if it
    produces Bottom (exception), return the default value instead.
    This is the effect-elimination principle (D22).
    """
    body: 'OTerm'
    default: 'OTerm'
    def canon(self) -> str:
        return f'catch({self.body.canon()},{self.default.canon()})'


OTerm = Union[OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
              OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch]


# ═══════════════════════════════════════════════════════════
# Python AST → OTerm Compilation
# ═══════════════════════════════════════════════════════════

class DenotEnv:
    """Compilation environment for denotational semantics."""
    def __init__(self, func_name: str = '', params: List[str] = None):
        self.bindings: Dict[str, OTerm] = {}
        self.func_name = func_name
        self.params = params or []
        self.depth = 0

    def get(self, name: str) -> OTerm:
        if name in self.bindings:
            return self.bindings[name]
        if name in self.params:
            return OVar(name)
        return OUnknown(name)

    def put(self, name: str, val: OTerm):
        self.bindings[name] = val

    def copy(self) -> 'DenotEnv':
        e = DenotEnv(self.func_name, list(self.params))
        e.bindings = dict(self.bindings)
        e.depth = self.depth
        return e


def compile_to_oterm(source: str) -> Optional[Tuple[OTerm, List[str]]]:
    """Compile a Python function to its denotational OTerm.

    When the source contains multiple function definitions, compiles the
    LAST one (the main function). Earlier functions are treated as helpers
    and registered in the environment for inlining.
    """
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        return None

    # Collect all top-level functions; compile the LAST one as main
    all_funcs = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
    if not all_funcs:
        return None
    func = all_funcs[-1]

    params = [a.arg for a in func.args.args]
    env = DenotEnv(func.name, params)

    # Register earlier top-level functions as helpers in the environment
    for helper in all_funcs[:-1]:
        helper_params = [a.arg for a in helper.args.args]
        helper_env = DenotEnv(helper.name, helper_params)
        try:
            helper_body = _compile_body(_skip_doc(helper.body), helper_env)
            env.bindings[helper.name] = OLam(tuple(helper_params), helper_body)
        except Exception:
            pass  # Can't compile helper — skip

    # Process nested function definitions — compile to OLam (D24)
    body = _skip_doc(func.body)
    for stmt in body:
        if isinstance(stmt, ast.FunctionDef):
            nested_params = [a.arg for a in stmt.args.args]
            nested_env = DenotEnv(stmt.name, nested_params)
            # Inherit outer environment bindings for closures
            for k, v in env.bindings.items():
                if k not in nested_params:
                    nested_env.bindings[k] = v
            # Capture outer function parameters as OVar bindings
            for p in env.params:
                if p not in nested_params and p not in nested_env.bindings:
                    nested_env.bindings[p] = OVar(p)
            nested_body = _compile_body(_skip_doc(stmt.body), nested_env)
            env.bindings[stmt.name] = OLam(tuple(nested_params), nested_body)

    term = _compile_body(body, env)
    return term, params


def _compile_body(stmts: List[ast.stmt], env: DenotEnv) -> OTerm:
    """Compile a statement list to an OTerm."""
    stmts = _skip_doc(stmts)

    for i, stmt in enumerate(stmts):
        if isinstance(stmt, ast.Return):
            if stmt.value is None:
                return OLit(None)
            return _compile_expr_ot(stmt.value, env)

        elif isinstance(stmt, ast.If):
            test = _compile_expr_ot(stmt.test, env)
            te = env.copy()
            fe = env.copy()
            t_ret = _has_return(stmt.body)
            f_ret = _has_return(stmt.orelse) if stmt.orelse else False

            if t_ret and f_ret:
                t_term = _compile_body(stmt.body, te)
                f_term = _compile_body(stmt.orelse, fe)
                return OCase(test, t_term, f_term)
            elif t_ret:
                t_term = _compile_body(stmt.body, te)
                _exec_stmts_ot(stmt.orelse if stmt.orelse else [], fe)
                rest = _compile_body(stmts[i+1:], fe)
                return OCase(test, t_term, rest)
            elif f_ret:
                _exec_stmts_ot(stmt.body, te)
                f_term = _compile_body(stmt.orelse, fe)
                rest = _compile_body(stmts[i+1:], te)
                return OCase(test, rest, f_term)
            else:
                _exec_stmts_ot(stmt.body, te)
                if stmt.orelse:
                    _exec_stmts_ot(stmt.orelse, fe)
                _merge_envs_ot(env, te, fe, test)

        elif isinstance(stmt, ast.For):
            if _has_any_return(stmt.body):
                # For loop with early return — compile as search/filter OTerm
                for_ret = _compile_for_return_ot(stmt, env, stmts[i+1:])
                if for_ret is not None:
                    return for_ret
            _exec_for_ot(stmt, env)

        elif isinstance(stmt, ast.While):
            if _has_any_return(stmt.body):
                # While loop with early return — compile as fixpoint search
                while_ret = _compile_while_return_ot(stmt, env, stmts[i+1:])
                if while_ret is not None:
                    return while_ret
            _exec_while_ot(stmt, env)

        elif isinstance(stmt, ast.Try):
            # D22: try/except → OCatch (effect elimination)
            # try: body except: handler  ≡  catch(body, handler_default)
            # This models exceptions as Bottom values — the try body
            # is evaluated, and if it produces Bottom, the except
            # handler's result is used instead.
            try_env = env.copy()
            has_try_return = _has_return(stmt.body)
            has_handler_return = any(
                _has_return(h.body) for h in stmt.handlers
            ) if hasattr(stmt, 'handlers') and stmt.handlers else False

            if has_try_return and has_handler_return:
                try_term = _compile_body(stmt.body, try_env)
                # Compile first handler's body
                handler_env = env.copy()
                handler_term = _compile_body(stmt.handlers[0].body, handler_env)
                return OCatch(try_term, handler_term)
            elif has_try_return:
                # try with return but no handler return — try body is the value
                return _compile_body(stmt.body, try_env)
            else:
                # Side-effectful try — execute for environment effects
                _exec_stmts_ot(stmt.body, env)
                if hasattr(stmt, 'orelse') and stmt.orelse:
                    _exec_stmts_ot(stmt.orelse, env)

        else:
            _exec_one_ot(stmt, env)

    return OUnknown('no_return')


def _is_mutating_call(node: ast.expr) -> Optional[str]:
    """Check if an expression is a mutating method call (pop, popleft).

    Returns the object name being mutated, or None.
    """
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.attr in ('pop', 'popleft')):
        return node.func.value.id
    return None


def _compile_tuple_sequential(elts: list, env: DenotEnv) -> tuple:
    """Compile tuple elements with sequential mutation tracking.

    When tuple elements contain mutating calls (e.g., stack.pop()),
    each call must see the state AFTER previous mutations.

    `a, b = stack.pop(), stack.pop()` compiles to:
      a = .pop(stack)         [value: last element]
      stack' = .pop!(stack)   [state: stack minus last]
      b = .pop(stack')        [value: second-to-last]

    Without this, both pops see the same stack, losing ordering.
    """
    # Fast path: no mutating calls → compile all at once
    has_mutations = any(_is_mutating_call(e) is not None for e in elts)
    if not has_mutations:
        return tuple(_compile_expr_ot(e, env) for e in elts)

    # Sequential: compile each element, updating env for mutations
    results = []
    for e in elts:
        obj_name = _is_mutating_call(e)
        if obj_name is not None:
            old = env.get(obj_name)
            method = e.func.attr
            args = tuple(_compile_expr_ot(a, env) for a in e.args)
            # The VALUE of pop() is the extracted element
            results.append(OOp(f'.{method}', (old,) + args))
            # The STATE after pop() is the remaining collection
            env.put(obj_name, OOp(f'.{method}!', (old,) + args))
        else:
            results.append(_compile_expr_ot(e, env))
    return tuple(results)


def _compile_expr_ot(node: ast.expr, env: DenotEnv) -> OTerm:
    """Compile expression to OTerm."""
    if isinstance(node, ast.Constant):
        return OLit(node.value)

    if isinstance(node, ast.Name):
        return env.get(node.id)

    if isinstance(node, ast.BinOp):
        l = _compile_expr_ot(node.left, env)
        r = _compile_expr_ot(node.right, env)
        op_name = type(node.op).__name__.lower()
        return OOp(op_name, (l, r))

    if isinstance(node, ast.UnaryOp):
        operand = _compile_expr_ot(node.operand, env)
        op_name = f'u_{type(node.op).__name__.lower()}'
        return OOp(op_name, (operand,))

    if isinstance(node, ast.Compare):
        left = _compile_expr_ot(node.left, env)
        parts = []
        for op, comp in zip(node.ops, node.comparators):
            right = _compile_expr_ot(comp, env)
            op_name = type(op).__name__.lower()
            parts.append(OOp(op_name, (left, right)))
            left = right
        if len(parts) == 1:
            return parts[0]
        return OOp('and', tuple(parts))

    if isinstance(node, ast.BoolOp):
        vals = tuple(_compile_expr_ot(v, env) for v in node.values)
        op_name = 'and' if isinstance(node.op, ast.And) else 'or'
        return OOp(op_name, vals)

    if isinstance(node, ast.IfExp):
        test = _compile_expr_ot(node.test, env)
        t = _compile_expr_ot(node.body, env)
        f = _compile_expr_ot(node.orelse, env)
        return OCase(test, t, f)

    if isinstance(node, ast.Call):
        return _compile_call_ot(node, env)

    if isinstance(node, ast.Subscript):
        base = _compile_expr_ot(node.value, env)
        if isinstance(node.slice, ast.Slice):
            # Extract slice parameters for semantic classification
            sl = node.slice
            lower = _compile_expr_ot(sl.lower, env) if sl.lower else None
            upper = _compile_expr_ot(sl.upper, env) if sl.upper else None
            step = _compile_expr_ot(sl.step, env) if sl.step else None

            # Resolve step value for classification
            def _is_neg_one(t):
                if isinstance(t, OLit) and t.value == -1:
                    return True
                if (isinstance(t, OOp) and t.name == 'u_usub' and
                        len(t.args) == 1 and isinstance(t.args[0], OLit)
                        and t.args[0].value == 1):
                    return True
                return False

            # s[::-1] → reversed(s) (general Python semantics)
            if lower is None and upper is None and step is not None and _is_neg_one(step):
                return OOp('reversed', (base,))
            # s[:n] → prefix(s, n)
            if lower is None and upper is not None and step is None:
                return OOp('prefix', (base, upper))
            # s[n:] → suffix(s, n)
            if lower is not None and upper is None and step is None:
                return OOp('suffix', (base, lower))
            # General slice — keep as slice with args
            args = [base]
            args.append(lower if lower is not None else OLit(None))
            args.append(upper if upper is not None else OLit(None))
            if step is not None:
                args.append(step)
            return OOp('slice', tuple(args))
        idx = _compile_expr_ot(node.slice, env)
        return OOp('getitem', (base, idx))

    if isinstance(node, (ast.Tuple, ast.List)):
        elts = _compile_tuple_sequential(node.elts, env)
        return OSeq(elts)

    if isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
        return _compile_comp_ot(node, env)

    if isinstance(node, ast.DictComp):
        return _compile_dictcomp_ot(node, env)

    if isinstance(node, ast.Dict):
        pairs = []
        unpacks = []
        for k, v in zip(node.keys, node.values):
            if k is not None:
                pairs.append((_compile_expr_ot(k, env), _compile_expr_ot(v, env)))
            else:
                # {**d} — dict unpacking
                unpacks.append(_compile_expr_ot(v, env))
        if unpacks and not pairs:
            # Pure unpacking: {**d1, **d2, ...} → merge chain
            # merge is left-associative: {**a, **b, **c} = merge(merge(a, b), c)
            # where later args overwrite earlier on overlap (non-commutative!)
            result = unpacks[0]
            for u in unpacks[1:]:
                result = OOp('merge', (result, u))
            return result
        elif unpacks:
            # Mixed: {k: v, **d} — compile unpacks as merge base
            base = unpacks[0]
            for u in unpacks[1:]:
                base = OOp('merge', (base, u))
            return OOp('merge', (base, ODict(tuple(pairs))))
        return ODict(tuple(pairs))

    if isinstance(node, ast.Attribute):
        # Known module constants — substitute at compile time
        if isinstance(node.value, ast.Name):
            _MODULE_CONSTANTS = {
                ('string', 'ascii_lowercase'): 'abcdefghijklmnopqrstuvwxyz',
                ('string', 'ascii_uppercase'): 'ABCDEFGHIJKLMNOPQRSTUVWXYZ',
                ('string', 'digits'): '0123456789',
                ('string', 'ascii_letters'): 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ',
                ('math', 'pi'): 3.141592653589793,
                ('math', 'e'): 2.718281828459045,
                ('math', 'inf'): float('inf'),
                ('sys', 'maxsize'): 2**63 - 1,
            }
            key = (node.value.id, node.attr)
            if key in _MODULE_CONSTANTS:
                return OLit(_MODULE_CONSTANTS[key])
        obj = _compile_expr_ot(node.value, env)
        return OOp(f'.{node.attr}', (obj,))

    if isinstance(node, ast.NamedExpr):
        val = _compile_expr_ot(node.value, env)
        if isinstance(node.target, ast.Name):
            env.put(node.target.id, val)
        return val

    if isinstance(node, ast.Lambda):
        # D24: Compile lambda body to OLam — captures the actual computation.
        # λx: x*2 becomes OLam(('x',), OOp('mult', (OVar('x'), OLit(2))))
        lam_params = [a.arg for a in node.args.args]
        lam_env = env.copy()
        for p in lam_params:
            lam_env.put(p, OVar(p))
        lam_body = _compile_expr_ot(node.body, lam_env)
        return OLam(tuple(lam_params), lam_body)

    if isinstance(node, ast.Set):
        elts = tuple(_compile_expr_ot(e, env) for e in node.elts)
        return OOp('set_literal', elts)

    # F-strings: f"text {expr} text" → fstring(parts...)
    # §11.15: f-strings are pure value computations (no effect fiber),
    # unlike print() which has IO effect.
    if isinstance(node, ast.JoinedStr):
        parts = []
        for v in node.values:
            if isinstance(v, ast.Constant):
                parts.append(OLit(v.value))
            elif isinstance(v, ast.FormattedValue):
                parts.append(_compile_expr_ot(v.value, env))
            else:
                parts.append(_compile_expr_ot(v, env))
        return OOp('fstring', tuple(parts))

    # Starred: *x in function call arguments
    # Compile the inner expression; the caller (zip, etc.) handles semantics.
    if isinstance(node, ast.Starred):
        return OOp('unpack', (_compile_expr_ot(node.value, env),))

    return OUnknown(type(node).__name__)


def _compile_call_ot(node: ast.Call, env: DenotEnv) -> OTerm:
    """Compile a function call to OTerm."""
    args = tuple(_compile_expr_ot(a, env) for a in node.args)

    # Named call
    if isinstance(node.func, ast.Name):
        name = node.func.id
        has_key = False
        has_reverse = False
        key_val = None
        for kw in node.keywords:
            if kw.arg == 'key':
                key_val = _compile_expr_ot(kw.value, env)
                has_key = True
            if kw.arg == 'reverse':
                rv = kw.value
                if isinstance(rv, ast.Constant) and rv.value is True:
                    has_reverse = True

        if has_key and has_reverse:
            return OOp(f'{name}_key_rev', args + (key_val,))
        if has_key:
            return OOp(f'{name}_key', args + (key_val,))
        if has_reverse:
            return OOp(f'{name}_rev', args)

        # set() / frozenset() → quotient type (order irrelevant)
        if name in ('set', 'frozenset') and args:
            return OQuotient(OOp(name, args), 'perm')
        # dict.fromkeys → quotient
        if name == 'dict':
            return OQuotient(OOp('dict', args), 'perm') if args else OOp('dict', ())

        # Recursive call → fixed point
        if name == env.func_name:
            return OFix(name, OSeq(args))

        # print() is an IO effect — §11.15: effects are non-trivial H¹
        # on the heap fibration.  The return value is None, but the program
        # inhabits the IO fiber.  A program returning print(x) differs from
        # one returning a computed value on the effect fiber.
        # Model as OOp('effect_io', (arg,)) to preserve the effect annotation.
        if name == 'print':
            return OOp('effect_io', tuple(args) if args else (OLit(''),))

        # D24-β: Inline nested function calls via beta-reduction.
        # If the called name is in env.bindings as an OLam, substitute
        # the call args for the lambda params in the body.
        # For recursive nested functions (body contains OFix(name, ...)),
        # the OFix nodes correctly represent the recursion — inlining
        # is still sound because it's a single beta-step, not unfolding.
        if name in env.bindings and isinstance(env.bindings[name], OLam):
            lam = env.bindings[name]
            if len(args) == len(lam.params):
                result = lam.body
                for param, arg in zip(lam.params, args):
                    result = _subst_term(result, param, arg)
                return result

        return OOp(name, args)

    # Method call
    if isinstance(node.func, ast.Attribute):
        obj = _compile_expr_ot(node.func.value, env)
        method = node.func.attr
        # Module-qualified: math.sqrt(x) → sqrt(x)
        if isinstance(node.func.value, ast.Name):
            mod = node.func.value.id
            # Unify module calls at compilation time
            unified = _unify_module_call(mod, method)
            if unified:
                return OOp(unified, args)
            # If the name is a local variable or parameter, treat as method
            # call on the variable's value (not as module-qualified call).
            # Only treat as module-qualified if it's NOT in the environment.
            if mod not in env.bindings and mod not in env.params:
                return OOp(f'{mod}.{method}', args)
            # Fall through to generic method call using compiled obj
        # .items(), .keys(), .values() on dicts → quotient (order irrelevant)
        if method in ('items', 'keys', 'values'):
            return OQuotient(OOp(f'.{method}', (obj,) + args), 'perm')
        return OOp(f'.{method}', (obj,) + args)

    return OOp('call', args)


def _unify_module_call(mod: str, method: str) -> Optional[str]:
    """Unify module-qualified calls to canonical names (Phase 5 at compile time)."""
    unified = {
        ('heapq', 'nsmallest'): 'heapq.nsmallest',
        ('heapq', 'nlargest'): 'heapq.nlargest',
        ('heapq', 'heappush'): '.append!',
        ('heapq', 'heappop'): '.pop!',
        ('functools', 'reduce'): 'fold',
        ('itertools', 'chain'): 'concat',
        ('itertools', 'accumulate'): 'scan',
        ('itertools', 'permutations'): 'permutations',
        ('itertools', 'combinations'): 'combinations',
        ('itertools', 'groupby'): 'itertools.groupby',
        ('itertools', 'product'): 'itertools.product',
        ('itertools', 'islice'): 'islice',
        ('math', 'copysign'): 'math.copysign',
        ('math', 'sqrt'): 'math.sqrt',
        ('math', 'log'): 'math.log',
        ('math', 'floor'): 'math.floor',
        ('math', 'ceil'): 'math.ceil',
        ('math', 'gcd'): 'gcd',
        ('math', 'comb'): 'comb',
        ('math', 'isnan'): 'math.isnan',
        ('math', 'isinf'): 'math.isinf',
        ('math', 'factorial'): 'factorial',
        ('operator', 'add'): 'add',
        ('operator', 'sub'): 'sub',
        ('operator', 'mul'): 'mul',
        ('operator', 'itemgetter'): 'itemgetter',
        ('copy', 'deepcopy'): 'deepcopy',
        ('copy', 'copy'): 'copy',
        ('collections', 'Counter'): 'Counter',
        ('collections', 'defaultdict'): 'defaultdict',
        ('collections', 'deque'): 'deque',
    }
    return unified.get((mod, method))


def _compile_comp_ot(node, env: DenotEnv) -> OTerm:
    """Compile comprehension to OMap — capturing the transform as an OLam.

    [x*2 for x in xs] → OMap(OLam(('x',), OOp('mult',(OVar('x'),OLit(2)))), $xs)
    [x for x in xs if x>0] → OMap(OLam(('x',), OVar('x')), $xs, OLam(('x',), OOp('gt',...)))

    This enables D4 (comprehension↔loop) unification: a for-loop
    building a list by appending f(x) produces the same OMap.
    """
    if not node.generators:
        return OUnknown('empty_comp')

    gen = node.generators[0]
    it = _compile_expr_ot(gen.iter, env)

    # Extract the loop variable name(s)
    loop_var = _extract_target_names(gen.target)
    if not loop_var:
        # Fallback to hash-based
        elt = node.elt if hasattr(node, 'elt') else node
        return OOp(f'comp_{_hash(ast.dump(elt))}', (it,))

    # Compile the element expression with loop var as bound variable
    body_env = env.copy()
    for v in loop_var:
        body_env.put(v, OVar(v))

    elt = node.elt if hasattr(node, 'elt') else node
    body_term = _compile_expr_ot(elt, body_env)
    transform = OLam(tuple(loop_var), body_term)

    # Compile filter predicates
    filter_pred = None
    if gen.ifs:
        filter_parts = [_compile_expr_ot(f, body_env) for f in gen.ifs]
        if len(filter_parts) == 1:
            filter_pred = OLam(tuple(loop_var), filter_parts[0])
        else:
            filter_pred = OLam(tuple(loop_var), OOp('and', tuple(filter_parts)))

    result = OMap(transform, it, filter_pred)

    # Wrap in set/quotient for set comprehensions
    if isinstance(node, ast.SetComp):
        result = OQuotient(result, 'perm')

    # Handle chained generators (nested comprehensions)
    if len(node.generators) > 1:
        # Fall back to hash-based for multi-generator comprehensions
        body_repr = ast.dump(elt)
        return OOp(f'comp_{_hash(body_repr)}', (it,))

    return result


def _extract_target_names(target) -> list:
    """Extract variable names from an assignment target."""
    if isinstance(target, ast.Name):
        return [target.id]
    if isinstance(target, (ast.Tuple, ast.List)):
        names = []
        for elt in target.elts:
            names.extend(_extract_target_names(elt))
        return names
    return []


def _compile_dictcomp_ot(node, env: DenotEnv) -> OTerm:
    """Compile dict comprehension to OTerm with captured key/value transforms."""
    gen = node.generators[0]
    it = _compile_expr_ot(gen.iter, env)

    loop_var = _extract_target_names(gen.target)
    if not loop_var:
        key_repr = ast.dump(node.key)
        val_repr = ast.dump(node.value)
        return OOp(f'dictcomp_{_hash(key_repr)}_{_hash(val_repr)}', (it,))

    body_env = env.copy()
    for v in loop_var:
        body_env.put(v, OVar(v))

    key_term = _compile_expr_ot(node.key, body_env)
    val_term = _compile_expr_ot(node.value, body_env)
    key_fn = OLam(tuple(loop_var), key_term)
    val_fn = OLam(tuple(loop_var), val_term)
    return OQuotient(OOp('dictcomp', (key_fn, val_fn, it)), 'perm')


def _exec_stmts_ot(stmts, env: DenotEnv):
    """Execute statements for their effect on the environment."""
    for stmt in _skip_doc(stmts):
        _exec_one_ot(stmt, env)


def _exec_one_ot(stmt, env: DenotEnv):
    """Execute one statement, updating environment."""
    if isinstance(stmt, ast.Assign):
        val = _compile_expr_ot(stmt.value, env)
        # Generator assigned to a variable → mark as single-use.
        # This prevents D6 (generator↔eager) from firing unsoundly:
        # gen = (x for x in data); sum(gen); list(gen) ≠ [x for x in data] used twice.
        if isinstance(stmt.value, ast.GeneratorExp) and isinstance(val, OMap):
            val = OOp('_genexpr_var', (val.transform, val.collection))
        for t in stmt.targets:
            _assign_ot(t, val, env)

    elif isinstance(stmt, ast.AugAssign):
        if isinstance(stmt.target, ast.Name):
            name = stmt.target.id
            old = env.get(name)
            rhs = _compile_expr_ot(stmt.value, env)
            op_name = type(stmt.op).__name__.lower()
            env.put(name, OOp(f'i{op_name}', (old, rhs)))
        elif isinstance(stmt.target, ast.Subscript):
            # Handle nested subscripts: dp[i][j] += val
            chain = []
            current = stmt.target
            while isinstance(current, ast.Subscript):
                chain.append(current.slice)
                current = current.value
            if isinstance(current, ast.Name):
                obj_name = current.id
                old_obj = env.get(obj_name)
                if old_obj is None:
                    old_obj = OVar(obj_name)
                indices = [_compile_expr_ot(idx, env) for idx in reversed(chain)]
                rhs = _compile_expr_ot(stmt.value, env)
                op_name = type(stmt.op).__name__.lower()
                elem = old_obj
                for idx in indices:
                    elem = OOp('getitem', (elem, idx))
                new_elem = OOp(f'i{op_name}', (elem, rhs))
                env.put(obj_name, _build_nested_setitem(old_obj, indices, new_elem))

    elif isinstance(stmt, ast.If):
        # Non-returning if — merge environments
        test = _compile_expr_ot(stmt.test, env)
        te = env.copy()
        fe = env.copy()
        _exec_stmts_ot(stmt.body, te)
        if stmt.orelse:
            _exec_stmts_ot(stmt.orelse, fe)
        _merge_envs_ot(env, te, fe, test)

    elif isinstance(stmt, ast.For):
        _exec_for_ot(stmt, env)

    elif isinstance(stmt, ast.While):
        _exec_while_ot(stmt, env)

    elif isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
        # D24: Compile nested function defs to OLam
        nested_params = [a.arg for a in stmt.args.args]
        nested_env = DenotEnv(stmt.name, nested_params)
        for k, v in env.bindings.items():
            if k not in nested_params:
                nested_env.bindings[k] = v
        # Capture outer function parameters as OVar bindings
        for p in env.params:
            if p not in nested_params and p not in nested_env.bindings:
                nested_env.bindings[p] = OVar(p)
        nested_body = _compile_body(_skip_doc(stmt.body), nested_env)
        env.bindings[stmt.name] = OLam(tuple(nested_params), nested_body)

    elif isinstance(stmt, ast.ClassDef):
        env.bindings[stmt.name] = OUnknown(f'class_{stmt.name}')

    elif isinstance(stmt, ast.Expr):
        # Side-effectful expression
        val = stmt.value
        if (isinstance(val, ast.Call) and isinstance(val.func, ast.Attribute)
                and isinstance(val.func.value, ast.Name)):
            obj_name = val.func.value.id
            method = val.func.attr
            args = tuple(_compile_expr_ot(a, env) for a in val.args)
            old = env.get(obj_name)
            # Mutation-pure bridge: .sort() ≡ sorted(), .reverse() ≡ reversed()
            # .append(x) ≡ concat with [x], .extend(x) ≡ concat with x
            if method == 'sort':
                # Check for key= and reverse= kwargs
                has_key = has_rev = False
                key_val = None
                for kw in val.keywords:
                    if kw.arg == 'key':
                        key_val = _compile_expr_ot(kw.value, env)
                        has_key = True
                    if kw.arg == 'reverse':
                        rv = kw.value
                        if isinstance(rv, ast.Constant) and rv.value is True:
                            has_rev = True
                if has_key and has_rev:
                    env.put(obj_name, OOp('sorted_key_rev', (old, key_val)))
                elif has_key:
                    env.put(obj_name, OOp('sorted_key', (old, key_val)))
                elif has_rev:
                    env.put(obj_name, OOp('sorted_rev', (old,)))
                else:
                    env.put(obj_name, OOp('sorted', (old,)))
            elif method == 'reverse':
                env.put(obj_name, OOp('reversed', (old,)))
            elif method == 'append':
                env.put(obj_name, OOp('.append!', (old,) + args))
            elif method == 'extend':
                env.put(obj_name, OOp('concat', (old,) + args))
            elif method == 'update':
                env.put(obj_name, OOp('.update!', (old,) + args))
            elif method == 'add':
                env.put(obj_name, OOp('.add!', (old,) + args))
            elif method == 'clear':
                env.put(obj_name, OOp(f'empty_{_guess_type(old)}', ()))
            elif method == 'pop':
                env.put(obj_name, OOp('.pop!', (old,) + args))
            else:
                env.put(obj_name, OOp(f'.{method}!', (old,) + args))
        elif isinstance(val, ast.Call) and isinstance(val.func, ast.Name):
            # Module-level mutating call: heapq.heappush(lst, val) etc.
            pass  # handled at call level

    elif isinstance(stmt, ast.Try):
        _exec_stmts_ot(stmt.body, env)
        if hasattr(stmt, 'orelse') and stmt.orelse:
            _exec_stmts_ot(stmt.orelse, env)

    elif isinstance(stmt, (ast.Import, ast.ImportFrom)):
        pass

    elif isinstance(stmt, (ast.Pass, ast.Break, ast.Continue)):
        pass


def _compile_for_return_ot(stmt, env: DenotEnv, rest_stmts: list) -> Optional[OTerm]:
    """Compile a for-loop with early return to an OTerm.

    Pattern 1: for x in coll: if cond(x): return early_val
               return default_val
        → OCase(OFold('any', False, OMap(λx.cond(x), coll)), early_val, default_val)

    This handles the "search" pattern where the loop looks for a
    condition and returns a result as soon as it finds one.
    Common in: is_prime, binary_search, palindrome check, etc.
    """
    loop_vars = _extract_target_names(stmt.target)
    if not loop_vars:
        return None

    body = _skip_doc(stmt.body)

    # Pattern: for x in coll: if cond: return early_val
    # followed by: return default_val
    if (len(body) >= 1 and isinstance(body[0], ast.If)
            and _has_return(body[0].body)
            and len(body[0].body) == 1 and isinstance(body[0].body[0], ast.Return)):

        rest_clean = _skip_doc(rest_stmts)
        if not rest_clean or not isinstance(rest_clean[0], ast.Return):
            return None

        # Compile the collection
        collection = _compile_expr_ot(stmt.iter, env)

        # Compile the condition with loop variable as a bound variable
        step_env = env.copy()
        for v in loop_vars:
            step_env.put(v, OVar(v))
        cond = _compile_expr_ot(body[0].test, step_env)

        # Compile early and default values
        early_val = _compile_expr_ot(body[0].body[0].value, env) if body[0].body[0].value else OLit(None)
        default_val = _compile_expr_ot(rest_clean[0].value, env) if rest_clean[0].value else OLit(None)

        # Build: any_match = fold[or](False, map(λx.cond(x), coll))
        pred_lam = OLam(tuple(loop_vars), cond)
        # Use filter_map with identity transform to detect existence
        # OFold('any', False, OMap(λx.cond(x), collection))
        cond_map = OMap(pred_lam, collection, None)
        any_match = OFold('any', OLit(False), cond_map)

        # If any match found → early_val, else → default_val
        return OCase(any_match, early_val, default_val)

    # Pattern: Nested for-loop with early return
    # for x in xs: for y in ys: if cond(x,y): return A; return B
    # Semantics: if any (x,y) pair satisfies cond → A, else → B
    # OTerm: case(any(any(cond(x,y) for y in ys) for x in xs), A, B)
    if (len(body) >= 1 and isinstance(body[0], ast.For)):
        inner_for = body[0]
        inner_vars = _extract_target_names(inner_for.target)
        inner_body = _skip_doc(inner_for.body)
        if (inner_vars and len(inner_body) >= 1
                and isinstance(inner_body[0], ast.If)
                and _has_return(inner_body[0].body)
                and len(inner_body[0].body) == 1
                and isinstance(inner_body[0].body[0], ast.Return)):

            rest_clean = _skip_doc(rest_stmts)
            if rest_clean and isinstance(rest_clean[0], ast.Return):
                # Compile outer and inner collections
                outer_coll = _compile_expr_ot(stmt.iter, env)
                step_env = env.copy()
                for v in loop_vars:
                    step_env.put(v, OVar(v))
                inner_coll = _compile_expr_ot(inner_for.iter, step_env)

                # Compile the condition with both loop variables
                inner_env = step_env.copy()
                for v in inner_vars:
                    inner_env.put(v, OVar(v))
                cond = _compile_expr_ot(inner_body[0].test, inner_env)

                # Compile early and default values
                early_val = (_compile_expr_ot(inner_body[0].body[0].value, env)
                             if inner_body[0].body[0].value else OLit(None))
                default_val = (_compile_expr_ot(rest_clean[0].value, env)
                               if rest_clean[0].value else OLit(None))

                # Build: any(any(cond(x,y) for y in ys) for x in xs)
                inner_pred = OLam(tuple(inner_vars), cond)
                inner_any = OFold('any', OLit(False), OMap(inner_pred, inner_coll))
                outer_pred = OLam(tuple(loop_vars), inner_any)
                outer_any = OFold('any', OLit(False), OMap(outer_pred, outer_coll))

                return OCase(outer_any, early_val, default_val)

    return None


def _compile_while_return_ot(stmt, env: DenotEnv, rest_stmts: list) -> Optional[OTerm]:
    """Compile a while-loop with early return as a fixpoint OTerm.

    Pattern: while cond:
                 if check: return early_val
                 update state
             return default_val

    This is a fixed-point search: iterate while cond is true,
    checking a predicate at each step.  Common in:
    - binary search, palindrome check, two-pointer algorithms
    - modular arithmetic loops (LCM, GCD iterative)

    We compile this as OFix with an explicit body:
      fix f = case(loop_test, case(inner_test, early_val, f(step(state))), default_val)
    """
    body = _skip_doc(stmt.body)
    if not body:
        return None

    # Find the inner if-return and the state updates, preserving order.
    # Statements BEFORE the if-return are "pre-if" computations (e.g.,
    # mid = lo + (hi - lo) // 2) that must be evaluated into the env
    # before compiling the inner test/early_val.
    inner_if = None
    pre_if_stmts = []
    post_if_stmts = []
    for s in body:
        if inner_if is None and isinstance(s, ast.If) and _has_any_return(s.body):
            inner_if = s
        elif inner_if is None:
            pre_if_stmts.append(s)
        else:
            post_if_stmts.append(s)

    if inner_if is None:
        return None

    # Execute pre-if statements to bind intermediate variables (e.g., mid)
    if pre_if_stmts:
        _exec_stmts_ot(pre_if_stmts, env)

    rest_clean = _skip_doc(rest_stmts)

    # For `while True:` with no return after the loop, the function's
    # return value comes entirely from inside the loop body.
    # Compile as: fix(case(inner_test, early_val, recurse))
    is_while_true = isinstance(stmt.test, ast.Constant) and stmt.test.value is True

    if not rest_clean or not isinstance(rest_clean[0], ast.Return):
        if not is_while_true:
            return None
        # while True: if cond: return val; ... (no return after loop)
        if len(inner_if.body) == 1 and isinstance(inner_if.body[0], ast.Return):
            early_val = _compile_expr_ot(inner_if.body[0].value, env) if inner_if.body[0].value else OLit(None)
        else:
            return None

        inner_test = _compile_expr_ot(inner_if.test, env)
        modified = _find_modified_ot(body)
        test_repr = _normalize_ast_dump(stmt.test, env)
        body_repr = _normalize_ast_dump(body, env)
        fix_key = _hash(f'search_{test_repr}|{body_repr}')

        search_body = OCase(inner_test, early_val, OOp('_recurse', ()))
        return OFix(fix_key, search_body)

    # Compile the early return value
    if len(inner_if.body) == 1 and isinstance(inner_if.body[0], ast.Return):
        early_val = _compile_expr_ot(inner_if.body[0].value, env) if inner_if.body[0].value else OLit(None)
    else:
        return None

    # Compile the default return value
    default_val = _compile_expr_ot(rest_clean[0].value, env) if rest_clean[0].value else OLit(None)

    # Compile the loop condition and inner test
    loop_test = _compile_expr_ot(stmt.test, env)
    inner_test = _compile_expr_ot(inner_if.test, env)

    # Build: fix(loop_test, inner_test, early_val, state_step, default_val)
    # We use a structural OFix that represents the loop as a fixpoint
    modified = _find_modified_ot(body)
    test_repr = _normalize_ast_dump(stmt.test, env)
    body_repr = _normalize_ast_dump(body, env)
    fix_key = _hash(f'search_{test_repr}|{body_repr}')

    # The fixpoint encodes: case(loop_test, case(inner_test, early_val, recurse), default_val)
    search_body = OCase(inner_test, early_val, OOp('_recurse', ()))
    fix_body = OCase(loop_test, search_body, default_val)

    return OFix(fix_key, fix_body)


def _exec_for_ot(stmt, env: DenotEnv):
    """Model for loop as OMap (append pattern) or OFold (accumulation).

    D4: for x in xs: result.append(f(x))  →  OMap(λx.f(x), xs)
    D5: for x in xs: acc += f(x)          →  OFold(step_key, init, xs)
    """
    it = _compile_expr_ot(stmt.iter, env)

    # Extract loop variable name(s)
    loop_vars = _extract_target_names(stmt.target)
    target_names = set(loop_vars)

    # Detect the map-via-append pattern (D4):
    #   result = []
    #   for x in xs: result.append(expr_involving_x)
    # This is semantically [expr for x in xs] = OMap(λx.expr, xs)
    map_result = _detect_map_pattern(stmt, loop_vars, it, env)
    if map_result is not None:
        var_name, map_term = map_result
        env.put(var_name, map_term)
        return

    # Otherwise: general fold/accumulation pattern
    modified = _find_modified_ot(stmt.body)

    # ── Coupled tuple-swap fold (D5b) ──
    # Pattern: a, b = expr_b, expr_ab  (simultaneous tuple assignment in for-loop)
    # Models the state tuple (a, b) as a single fold:
    #   fold(λ(state, elem). (new_a, new_b), (init_a, init_b), collection)
    # Then projects out the desired component at the end.
    # This correctly captures coupled recurrences like Fibonacci: a,b = b, a+b
    non_loop_modified = [v for v in modified if v not in target_names]
    has_tuple_swap_for = False
    if len(non_loop_modified) >= 2:
        for s in stmt.body:
            if isinstance(s, ast.Assign) and len(s.targets) == 1:
                tgt = s.targets[0]
                if isinstance(tgt, (ast.Tuple, ast.List)) and \
                   isinstance(s.value, (ast.Tuple, ast.List)):
                    tgt_names = {e.id for e in tgt.elts if isinstance(e, ast.Name)}
                    if len(tgt_names & set(non_loop_modified)) >= 2:
                        has_tuple_swap_for = True
                        break

    if has_tuple_swap_for:
        # Create coupled fold: state is tuple of all modified non-loop vars
        state_vars = non_loop_modified
        state_env = env.copy()
        for i, vn in enumerate(state_vars):
            state_env.put(vn, OVar(f'_s{i}'))
        for i, v in enumerate(loop_vars):
            state_env.put(v, OVar(f'_e{i}'))

        _exec_stmts_ot(stmt.body, state_env)

        step_vals = []
        init_vals = []
        for i, vn in enumerate(state_vars):
            step_vals.append(state_env.bindings.get(vn, OVar(f'_s{i}')))
            init_vals.append(env.get(vn) if env.get(vn) is not None else OLit(0))

        # Build body_fn: λ(state_components..., elem_components...). (new_state_components...)
        s_params = tuple(f'_s{i}' for i in range(len(state_vars)))
        e_params = tuple(f'_e{i}' for i in range(len(loop_vars)))
        all_params = s_params + e_params
        step_tuple = OSeq(tuple(step_vals))
        body_fn = OLam(all_params, step_tuple)

        # Canonicalize for hashing
        body_repr = str(step_tuple)
        fold_key = _hash(f'coupled_fold|{body_repr}')

        init_term = OSeq(tuple(init_vals))
        fold_result = OFold(fold_key, init_term, it, body_fn=body_fn)

        for i, vn in enumerate(state_vars):
            env.put(vn, OOp('getitem', (fold_result, OLit(i))))
        return

    for vn in modified:
        if vn in target_names:
            continue
        old = env.get(vn)

        # D5: Detect augmented assignment folds and use a semantic fold key
        # (operation name) instead of a body hash.
        # Trivial:     `for x in xs: s += x`    → fold[iadd](0, xs)
        # Non-trivial: `for x in xs: s += f(x)` → fold[iadd](0, map(λx.f(x), xs))
        # Conditional: `for x in xs: if p(x): s += f(x)` → fold[iadd](0, filter_map(p, f, xs))
        fold_info = _detect_augassign_fold(stmt.body, vn, loop_vars)
        if fold_info is not None:
            semantic_key, rhs_is_trivial = fold_info
            if rhs_is_trivial:
                env.put(vn, OFold(semantic_key, old, it))
            else:
                # Compile the RHS as a map transform over the collection
                rhs_node = stmt.body[0].value  # type: ast.expr
                step_env = env.copy()
                for v in loop_vars:
                    step_env.put(v, OVar(v))
                transform = _compile_expr_ot(rhs_node, step_env)
                lam = OLam(tuple(loop_vars), transform)
                mapped = OMap(lam, it, None)
                env.put(vn, OFold(semantic_key, old, mapped))
        elif _detect_multi_augassign_fold(stmt.body, vn, loop_vars) is not None:
            # Multi-augassign fold: acc += A; acc -= B → fold[iadd](0, map(λx. A-B, xs))
            multi_info = _detect_multi_augassign_fold(stmt.body, vn, loop_vars)
            semantic_key, combined_rhs = multi_info
            step_env = env.copy()
            for v in loop_vars:
                step_env.put(v, OVar(v))
            transform = _compile_expr_ot(combined_rhs, step_env)
            lam = OLam(tuple(loop_vars), transform)
            mapped = OMap(lam, it, None)
            env.put(vn, OFold(semantic_key, old, mapped))
        elif _detect_conditional_fold(stmt.body, vn, loop_vars) is not None:
            cond_info = _detect_conditional_fold(stmt.body, vn, loop_vars)
            semantic_key, cond_node, rhs_node = cond_info
            step_env = env.copy()
            for v in loop_vars:
                step_env.put(v, OVar(v))
            if cond_node is None:
                # Conditional fold with else branch:
                # if cond: acc -= A; else: acc += B → fold[iadd](0, map(λx. case(cond, -A, B), xs))
                transform = _compile_expr_ot(rhs_node, step_env)
                lam = OLam(tuple(loop_vars), transform)
                mapped = OMap(lam, it, None)
                env.put(vn, OFold(semantic_key, old, mapped))
            else:
                # Filter fold: if cond: acc += expr → fold[key](init, filter_map(cond, expr, xs))
                pred = _compile_expr_ot(cond_node, step_env)
                transform = _compile_expr_ot(rhs_node, step_env)
                pred_lam = OLam(tuple(loop_vars), pred)
                xform_lam = OLam(tuple(loop_vars), transform)
                filtered = OMap(xform_lam, it, pred_lam)
                env.put(vn, OFold(semantic_key, old, filtered))
        else:
            # Compile the fold body with canonical variable names for
            # the accumulator ($0) and element ($1, $2, ...) so that
            # the hash is representation-independent (matching reduce
            # lambda bodies that compute the same thing).
            step_env = env.copy()
            step_env.put(vn, OVar('$0'))  # accumulator
            for i, v in enumerate(loop_vars):
                step_env.put(v, OVar(f'${i+1}'))
            body_repr = _normalize_ast_dump(stmt.body, step_env)
            fold_key = _hash(_canonicalize_free_vars(f'{body_repr}'))
            # Try to compile body as OTerm for structural comparison.
            # Use depth-specific variable names to avoid capture when
            # nested folds shadow outer loop variables.
            body_fn = None
            try:
                d = env.depth
                body_env = env.copy()
                body_env.put(vn, OVar(f'$d{d}_0'))
                for i, v in enumerate(loop_vars):
                    body_env.put(v, OVar(f'$d{d}_{i+1}'))
                body_env.depth = d + 1
                _exec_stmts_ot(stmt.body, body_env)
                acc_result = body_env.get(vn)
                if acc_result is not None and not isinstance(acc_result, OVar):
                    params = (f'$d{d}_0',) + tuple(f'$d{d}_{i+1}' for i in range(len(loop_vars)))
                    body_fn = OLam(params, acc_result)
            except Exception:
                pass
            env.put(vn, OFold(fold_key, old, it, body_fn=body_fn))


def _detect_augassign_fold(body: list, acc_name: str,
                           loop_vars: list) -> Optional[tuple]:
    """Detect augmented assignment fold step → (semantic_key, rhs_is_trivial).

    Pattern: acc += x      →  ('iadd', True)   # simple fold over collection
             acc += f(x)   →  ('iadd', False)  # fold over map(f, collection)
    Returns None if body is not a single augmented assignment to acc_name.
    """
    if len(body) != 1:
        return None
    s = body[0]
    if not isinstance(s, ast.AugAssign):
        return None
    if not isinstance(s.target, ast.Name):
        return None
    if s.target.id != acc_name:
        return None

    op_name = type(s.op).__name__.lower()
    op_map = {
        'add': 'iadd', 'sub': 'isub', 'mult': 'imult',
        'div': 'idiv', 'floordiv': 'ifloordiv', 'mod': 'imod',
        'bitor': 'ior', 'bitand': 'iand', 'bitxor': 'ixor',
    }
    key = op_map.get(op_name)
    if key is None:
        return None

    # Check if RHS is exactly the loop variable (trivial fold)
    rhs = s.value
    if isinstance(rhs, ast.Name) and rhs.id in loop_vars:
        return (key, True)
    # Tuple unpacking: loop vars (a, b) with RHS being one of them
    if isinstance(rhs, ast.Name) and len(loop_vars) > 1 and rhs.id in loop_vars:
        return (key, True)

    # Non-trivial RHS: the fold body transforms the loop variable
    return (key, False)


def _detect_multi_augassign_fold(body: list, acc_name: str,
                                  loop_vars: list) -> Optional[tuple]:
    """Detect multiple augmented assignments to the same accumulator.

    Pattern: [local_assigns...] acc += A; acc -= B → ('iadd', combined_rhs)
    where combined_rhs = A - B  (general: combine ops algebraically).
    Local assigns (j = expr) are allowed before the augmented assignments.
    Returns ('iadd', combined_rhs_node) or None.
    """
    if len(body) < 2:
        return None

    # Separate local assigns from augmented assignments
    local_assigns = []
    aug_stmts = []
    for s in body:
        if isinstance(s, ast.AugAssign):
            if not isinstance(s.target, ast.Name):
                return None
            if s.target.id != acc_name:
                return None
            op_name = type(s.op).__name__.lower()
            aug_stmts.append((op_name, s.value))
        elif isinstance(s, ast.Assign) and len(s.targets) == 1:
            if isinstance(s.targets[0], ast.Name):
                local_assigns.append((s.targets[0].id, s.value))
            else:
                return None  # tuple unpacking or complex assign
        else:
            return None  # non-assign, non-augassign statement

    if len(aug_stmts) < 2:
        return None

    # Combine: acc += A; acc -= B → acc += (A - B)
    combined = aug_stmts[0][1]
    for op_name, rhs in aug_stmts[1:]:
        if op_name == 'add':
            combined = ast.BinOp(left=combined, op=ast.Add(), right=rhs)
        elif op_name == 'sub':
            combined = ast.BinOp(left=combined, op=ast.Sub(), right=rhs)
        elif op_name == 'mult':
            combined = ast.BinOp(left=combined, op=ast.Mult(), right=rhs)
        else:
            return None  # Can't combine non-linear ops

    # Inline local variable definitions into the combined expression
    # by wrapping with assignments the compiler can resolve
    for var_name, var_value in reversed(local_assigns):
        combined = _inline_let_binding(combined, var_name, var_value)

    return ('iadd', combined)


def _inline_let_binding(expr: ast.expr, var_name: str,
                         var_value: ast.expr) -> ast.expr:
    """Inline a let-binding: replace all occurrences of var_name with var_value."""
    class _Inliner(ast.NodeTransformer):
        def visit_Name(self, node):
            if node.id == var_name:
                return ast.copy_location(var_value, node)
            return node
    return _Inliner().visit(expr)


def _detect_conditional_fold(body: list, acc_name: str,
                              loop_vars: list) -> Optional[tuple]:
    """Detect conditional augmented assignment fold step.

    Pattern 1: if <cond>: acc += <expr>   → (semantic_key, cond_node, rhs_node)
    Pattern 2: if <cond>: acc -= <a>; else: acc += <a> → ('iadd', None, case_node)
    The fold becomes: fold[key](init, filter_map(cond, expr, collection))
    Returns None if body doesn't match this pattern.
    """
    if len(body) != 1:
        return None
    s = body[0]
    if not isinstance(s, ast.If):
        return None

    # Pattern 2: if cond: acc op= A; else: acc op2= B
    if (len(s.body) == 1 and len(s.orelse) == 1 and
            isinstance(s.body[0], ast.AugAssign) and
            isinstance(s.orelse[0], ast.AugAssign)):
        true_stmt = s.body[0]
        false_stmt = s.orelse[0]
        if (isinstance(true_stmt.target, ast.Name) and
                true_stmt.target.id == acc_name and
                isinstance(false_stmt.target, ast.Name) and
                false_stmt.target.id == acc_name):
            t_op = type(true_stmt.op).__name__.lower()
            f_op = type(false_stmt.op).__name__.lower()
            # if cond: acc -= A; else: acc += B → acc += case(cond, -A, B)
            # if cond: acc += A; else: acc -= B → acc += case(cond, A, -B)
            # if cond: acc += A; else: acc += B → acc += case(cond, A, B)
            true_rhs = true_stmt.value
            false_rhs = false_stmt.value
            if t_op == 'sub':
                true_rhs = ast.UnaryOp(op=ast.USub(), operand=true_stmt.value)
            elif t_op != 'add':
                return None
            if f_op == 'sub':
                false_rhs = ast.UnaryOp(op=ast.USub(), operand=false_stmt.value)
            elif f_op != 'add':
                return None
            combined = ast.IfExp(test=s.test, body=true_rhs, orelse=false_rhs)
            return ('iadd', None, combined)

    # Pattern 1: if <cond>: acc += <expr> (no else)
    if len(s.body) != 1 or s.orelse:
        return None
    inner = s.body[0]
    if not isinstance(inner, ast.AugAssign):
        return None
    if not isinstance(inner.target, ast.Name):
        return None
    if inner.target.id != acc_name:
        return None

    op_name = type(inner.op).__name__.lower()
    op_map = {
        'add': 'iadd', 'sub': 'isub', 'mult': 'imult',
        'div': 'idiv', 'floordiv': 'ifloordiv', 'mod': 'imod',
        'bitor': 'ior', 'bitand': 'iand', 'bitxor': 'ixor',
    }
    key = op_map.get(op_name)
    if key is None:
        return None

    return (key, s.test, inner.value)


def _detect_map_pattern(stmt, loop_vars: list, it: OTerm,
                         env: 'DenotEnv') -> Optional[tuple]:
    """Detect for-loop that builds a list via append/insert(0,...) → OMap.

    Pattern: for x in xs: result.append(f(x))   → result = map(f, xs)
    Pattern: for x in xs: result.insert(0, f(x)) → result = reversed(map(f, xs))
    Where result was initialized to [] and the only mutation is append/insert.
    Returns (var_name, OMap_term) or None.
    """
    if len(stmt.body) != 1:
        # Could also handle if-guarded append (filtered map)
        if len(stmt.body) == 1 and isinstance(stmt.body[0], ast.If):
            return _detect_filtered_map(stmt, loop_vars, it, env)
        return None

    s = stmt.body[0]
    if not isinstance(s, ast.Expr):
        return None
    if not isinstance(s.value, ast.Call):
        return None
    call = s.value
    if not isinstance(call.func, ast.Attribute):
        return None
    if not isinstance(call.func.value, ast.Name):
        return None

    method = call.func.attr
    var_name = call.func.value.id
    old = env.get(var_name)

    # Verify the accumulator was initialized to [] (empty list)
    is_empty = (isinstance(old, OSeq) and len(old.elements) == 0)
    if not is_empty:
        return None

    if method == 'append' and len(call.args) == 1:
        # Standard append → map
        body_env = env.copy()
        for v in loop_vars:
            body_env.put(v, OVar(v))
        appended = _compile_expr_ot(call.args[0], body_env)
        transform = OLam(tuple(loop_vars), appended)
        return var_name, OMap(transform, it)

    if method == 'insert' and len(call.args) == 2:
        # insert(0, x) → reversed(map(f, xs))
        # Check that the first arg is 0 (prepend position)
        idx_node = call.args[0]
        if isinstance(idx_node, ast.Constant) and idx_node.value == 0:
            body_env = env.copy()
            for v in loop_vars:
                body_env.put(v, OVar(v))
            inserted = _compile_expr_ot(call.args[1], body_env)
            transform = OLam(tuple(loop_vars), inserted)
            mapped = OMap(transform, it)
            return var_name, OOp('reversed', (mapped,))

    return None


def _detect_filtered_map(stmt, loop_vars: list, it: OTerm,
                         env: 'DenotEnv') -> Optional[tuple]:
    """Detect: for x in xs: if pred(x): result.append(f(x)) → filtered OMap."""
    if_stmt = stmt.body[0]
    if not isinstance(if_stmt, ast.If):
        return None
    if if_stmt.orelse:
        return None  # else branch means it's not a simple filter
    if len(if_stmt.body) != 1:
        return None

    s = if_stmt.body[0]
    if not isinstance(s, ast.Expr) or not isinstance(s.value, ast.Call):
        return None
    call = s.value
    if not (isinstance(call.func, ast.Attribute) and call.func.attr == 'append'
            and isinstance(call.func.value, ast.Name) and len(call.args) == 1):
        return None

    var_name = call.func.value.id
    old = env.get(var_name)
    if not (isinstance(old, OSeq) and len(old.elements) == 0):
        return None

    body_env = env.copy()
    for v in loop_vars:
        body_env.put(v, OVar(v))

    appended = _compile_expr_ot(call.args[0], body_env)
    transform = OLam(tuple(loop_vars), appended)
    predicate_term = _compile_expr_ot(if_stmt.test, body_env)
    filter_pred = OLam(tuple(loop_vars), predicate_term)

    return var_name, OMap(transform, it, filter_pred)


def _normalize_ast_dump(stmts, env: DenotEnv) -> str:
    """Create a normalized AST dump that ignores variable names.

    This is key for matching loops/folds that do the same thing
    but use different local variable names.

    Applies _phase2_ring to each compiled OTerm before canonicalizing,
    so fold bodies that differ only by in-place vs pure ops, constant
    folding, or commutative reordering get the same hash.
    """
    def _ring_canon(ot):
        """Apply ring normalization then canonicalize."""
        try:
            return _phase2_ring(ot).canon()
        except Exception:
            return ot.canon()

    parts = []
    for s in (stmts if isinstance(stmts, list) else [stmts]):
        try:
            if isinstance(s, ast.Expr) and isinstance(s.value, ast.Call):
                parts.append(_ring_canon(_compile_expr_ot(s.value, env.copy())))
            elif isinstance(s, ast.Assign):
                val = _compile_expr_ot(s.value, env.copy())
                parts.append(f'assign:{_ring_canon(val)}')
            elif isinstance(s, ast.AugAssign):
                val = _compile_expr_ot(s.value, env.copy())
                op = type(s.op).__name__.lower()
                parts.append(f'aug:{op}:{_ring_canon(val)}')
            elif isinstance(s, ast.If):
                test = _compile_expr_ot(s.test, env.copy())
                parts.append(f'if:{_ring_canon(test)}')
            elif isinstance(s, ast.Return):
                if s.value:
                    val = _compile_expr_ot(s.value, env.copy())
                    parts.append(f'ret:{_ring_canon(val)}')
            elif isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef)):
                arg_info = ','.join(a.arg for a in s.args.args)
                defaults = len(s.args.defaults)
                parts.append(f'def:{s.name}({arg_info},d={defaults})')
            else:
                parts.append(ast.dump(s)[:60])
        except Exception:
            parts.append(ast.dump(s)[:50])
    return '|'.join(parts)


def _exec_while_ot(stmt, env: DenotEnv):
    """Model while loop as a fixed point with structured body.

    Three strategies (from monograph §16.9.1 Axis 1):

    1. Counter-based loop: ``while i < n: body; i += 1``
       → OFold over range(n).  This is the D3 path constructor
       (while ↔ for) composed with the for-loop's fold extraction.

    2. Accumulator loop with recognizable step:
       → OFix whose body IS the loop's state transformation
       (case of test, step applied to state, state).  This exposes
       the recurrence for HIT structural comparison.

    3. Fallback: opaque OFix with hash key (current behaviour).
    """
    modified = _find_modified_ot(stmt.body)

    # ── Strategy 1: counter-based while → fold ──
    # Detect pattern: i = 0; while i < n: body; i += 1
    counter_info = _detect_counter_while(stmt, modified, env)
    if counter_info is not None:
        counter_var, bound_term, acc_vars = counter_info
        # Convert to for-loop semantics: for counter_var in range(bound_term)
        it = OOp('range', (bound_term,))
        loop_vars = [counter_var]
        # Execute body in step env (same as _exec_for_ot fallback)
        for vn in acc_vars:
            old = env.get(vn)
            step_env = env.copy()
            step_env.put(vn, OVar('$0'))  # accumulator
            for i, v in enumerate(loop_vars):
                step_env.put(v, OVar(f'${i+1}'))
            # Try augmented-assignment fold detection
            fold_info = _detect_augassign_fold(stmt.body, vn, loop_vars)
            if fold_info is not None:
                semantic_key, rhs_is_trivial = fold_info
                if rhs_is_trivial:
                    env.put(vn, OFold(semantic_key, old, it))
                else:
                    rhs_node = _find_augassign_rhs(stmt.body, vn)
                    if rhs_node is not None:
                        transform = _compile_expr_ot(rhs_node, step_env)
                        lam = OLam(tuple(loop_vars), transform)
                        mapped = OMap(lam, it, None)
                        env.put(vn, OFold(semantic_key, old, mapped))
                    else:
                        body_repr = _normalize_ast_dump(stmt.body, step_env)
                        fold_key = _hash(_canonicalize_free_vars(f'{body_repr}'))
                        body_fn2 = None
                        try:
                            d = env.depth
                            body_env2 = env.copy()
                            body_env2.put(vn, OVar(f'$d{d}_0'))
                            for ii, v in enumerate(loop_vars):
                                body_env2.put(v, OVar(f'$d{d}_{ii+1}'))
                            body_env2.depth = d + 1
                            _exec_stmts_ot(stmt.body, body_env2)
                            acc_r = body_env2.get(vn)
                            if acc_r is not None and not isinstance(acc_r, OVar):
                                params = (f'$d{d}_0',) + tuple(f'$d{d}_{ii+1}' for ii in range(len(loop_vars)))
                                body_fn2 = OLam(params, acc_r)
                        except Exception:
                            pass
                        env.put(vn, OFold(fold_key, old, it, body_fn=body_fn2))
            else:
                body_repr = _normalize_ast_dump(stmt.body, step_env)
                fold_key = _hash(_canonicalize_free_vars(f'{body_repr}'))
                body_fn = None
                try:
                    d = env.depth
                    body_env = env.copy()
                    body_env.put(vn, OVar(f'$d{d}_0'))
                    for i, v in enumerate(loop_vars):
                        body_env.put(v, OVar(f'$d{d}_{i+1}'))
                    body_env.depth = d + 1
                    _exec_stmts_ot(stmt.body, body_env)
                    acc_result = body_env.get(vn)
                    if acc_result is not None and not isinstance(acc_result, OVar):
                        params = (f'$d{d}_0',) + tuple(f'$d{d}_{i+1}' for i in range(len(loop_vars)))
                        body_fn = OLam(params, acc_result)
                except Exception:
                    pass
                env.put(vn, OFold(fold_key, old, it, body_fn=body_fn))
        return

    # ── Strategy 2: structured OFix with body ──
    # Compile the test condition and one iteration of the loop body
    # to produce OFix(name, OCase(test, step(state), state))
    #
    # For SIMULTANEOUS tuple assignments (e.g. `a, b = b, a % b`), we
    # create a SINGLE fix-point over a state tuple so the coupled
    # evolution is captured.  For sequential assignments, each variable
    # gets its own independent OFix (which correctly captures the order
    # of evaluation within the loop body).
    test_term = _compile_expr_ot(stmt.test, env)

    test_repr = _normalize_ast_dump(stmt.test, env)
    body_repr = _normalize_ast_dump(stmt.body, env)
    fix_key = _hash(f'{test_repr}|{body_repr}')

    # Detect simultaneous tuple swap (e.g. `a, b = b, a % b`) where
    # the RHS is also a tuple literal that references the same variables.
    # This excludes destructuring (`a, b = func()`) which is not coupled.
    has_tuple_swap = False
    for s in stmt.body:
        if isinstance(s, ast.Assign) and len(s.targets) == 1:
            tgt = s.targets[0]
            if isinstance(tgt, (ast.Tuple, ast.List)) and \
               isinstance(s.value, (ast.Tuple, ast.List)):
                has_tuple_swap = True
                break

    # ── Detect coupled AugAssign variables ──
    # Even without explicit tuple swap, variables may be coupled:
    # e.g., `count += n & 1; n >>= 1` — count's step references n.
    # Without coupling, separate OFixes lose the iterative accumulation.
    has_coupled_augassign = False
    if len(modified) >= 2 and not has_tuple_swap:
        try:
            probe_env = env.copy()
            for i, vn in enumerate(modified):
                probe_env.put(vn, OVar(f'$_fix_{i}'))
            _exec_stmts_ot(stmt.body, probe_env)
            # Check if any var's step expression references another modified var
            for i, vn in enumerate(modified):
                step_val = probe_env.bindings.get(vn, OVar(f'$_fix_{i}'))
                step_canon = step_val.canon() if hasattr(step_val, 'canon') else ''
                for j in range(len(modified)):
                    if j != i and f'$_fix_{j}' in step_canon:
                        has_coupled_augassign = True
                        break
                if has_coupled_augassign:
                    break
        except Exception:
            pass

    use_coupled = len(modified) >= 2 and (has_tuple_swap or has_coupled_augassign)

    if use_coupled:
        # ── Coupled multi-variable fix-point ──
        # State = ($0, $1, ...) corresponding to modified vars.
        # Compile body with state vars to capture cross-dependencies.
        # Save initial values before replacing with state vars
        initial_vals = {vn: env.get(vn) for vn in modified}
        state_env = env.copy()
        for i, vn in enumerate(modified):
            state_env.put(vn, OVar(f'${i}'))
        test_coupled = _compile_expr_ot(stmt.test, state_env)
        _exec_stmts_ot(stmt.body, state_env)
        step_vals = []
        state_vals = []
        for i, vn in enumerate(modified):
            step_vals.append(state_env.bindings.get(vn, OVar(f'${i}')))
            state_vals.append(OVar(f'${i}'))
        step_tuple = OSeq(tuple(step_vals))
        state_tuple = OSeq(tuple(state_vals))
        fix_body = OCase(test_coupled, step_tuple, state_tuple)
        fix_result = OFix(fix_key, fix_body)
        for i, vn in enumerate(modified):
            env.put(vn, OOp('getitem', (fix_result, OLit(i))))

        # ── Fixpoint schema recognition ──
        # Recognize standard mathematical recurrences and replace
        # with named operations. These are mathematical IDENTITIES
        # (the standard recursive definitions of these functions),
        # not pattern matches on specific test cases.
        _try_fix_schema(fix_body, modified, initial_vals, env)
    else:
        step_env = env.copy()
        _exec_stmts_ot(stmt.body, step_env)
        for vn in modified:
            old = env.get(vn)
            new_val = step_env.bindings.get(vn, old)
            body = OCase(test_term, new_val, old)
            env.put(vn, OFix(fix_key, body))


def _try_fix_schema(fix_body: 'OTerm', modified: list, initial_vals: dict,
                    env: 'DenotEnv') -> None:
    """Recognize standard mathematical recurrences in coupled fixpoints.

    When a coupled OFix matches a known recurrence schema, replace the
    accumulator variable with the equivalent named operation.

    These are MATHEMATICAL IDENTITIES — the standard recursive definitions:
      popcount(n) = (n & 1) + popcount(n >> 1)  for n > 0, else 0
      digit_sum(n) = (n % 10) + digit_sum(n // 10)  for n > 0, else 0
      reverse_digits(n) = reverse_digits(n // 10) * 10 + n % 10
    """
    if not isinstance(fix_body, OCase) or not isinstance(fix_body.true_branch, OSeq):
        return
    step_elems = list(fix_body.true_branch.elements)
    if len(step_elems) != 2 or len(modified) < 2:
        return

    # Simplify getitem(OSeq, OLit(i)) → element at index i.
    # Tuple swaps produce intermediate OSeq+getitem wrappers.
    for idx in range(len(step_elems)):
        e = step_elems[idx]
        if isinstance(e, OOp) and e.name == 'getitem' and len(e.args) == 2:
            seq, lit = e.args
            if isinstance(seq, OSeq) and isinstance(lit, OLit):
                i = lit.value
                if isinstance(i, int) and 0 <= i < len(seq.elements):
                    step_elems[idx] = seq.elements[i]

    acc_var = modified[0]
    iter_var = modified[1]
    init_acc = initial_vals.get(acc_var)
    init_iter = initial_vals.get(iter_var)
    if init_acc is None or init_iter is None:
        return

    # Normalize step element canons for matching:
    # During compilation, augmented assignments (+=, >>=, //=) produce
    # op names like iadd, irshift, ifloordiv. We normalize these to
    # their pure forms for schema matching.
    import re
    def _norm_canon(c: str) -> str:
        return re.sub(r'\b(iadd|isub|imul|imult|ifloordiv|imod|irshift|ilshift|ibitor|ibitand|ibitxor)\b',
                      lambda m: {'iadd': 'add', 'isub': 'sub', 'imul': 'mul',
                                 'imult': 'mul', 'ifloordiv': 'floordiv',
                                 'imod': 'mod', 'irshift': 'rshift',
                                 'ilshift': 'lshift', 'ibitor': 'bitor',
                                 'ibitand': 'bitand', 'ibitxor': 'bitxor'}[m.group()], c)

    s0c = _norm_canon(step_elems[0].canon())
    s1c = _norm_canon(step_elems[1].canon())

    # Only match when accumulator starts at 0
    is_zero_init = isinstance(init_acc, OLit) and init_acc.value == 0

    if is_zero_init:
        # ── Popcount: acc += n & 1; n >>= 1 ──
        if s1c == 'rshift($$1,1)':
            if s0c in ('add($$0,bitand($$1,1))', 'add($$0,bitand(1,$$1))'):
                env.put(acc_var, OOp('popcount', (init_iter,)))
                return

        # ── Digit sum: acc += n % 10; n //= 10 ──
        if s1c == 'floordiv($$1,10)':
            if s0c == 'add($$0,mod($$1,10))':
                env.put(acc_var, OOp('digit_sum', (init_iter,)))
                return

        # ── Reverse digits: acc = acc * 10 + n % 10; n //= 10 ──
        # Both orderings needed: commutativity may reorder add args.
        if s1c == 'floordiv($$1,10)':
            if s0c in ('add(mult($$0,10),mod($$1,10))',
                       'add(mod($$1,10),mult($$0,10))'):
                env.put(acc_var, OOp('reverse_digits', (init_iter,)))
                return

    # ── GCD (Euclidean algorithm): a, b = b, a%b ──
    # This is the standard definition of gcd via repeated division.
    # gcd(a, b) = gcd(b, a mod b) until b = 0; result = a.
    if s0c == '$$1' and s1c == 'mod($$0,$$1)':
        env.put(acc_var, OOp('gcd', (init_acc, init_iter)))
        return


def _detect_counter_while(stmt, modified, env):
    """Detect counter-based while loop pattern.

    Pattern: while i < n: ...; i += 1  (or i < len(x), etc.)
    Also handles:
      - while i > 0: ...; i -= 1  (countdown)
      - while i < n: ...; i += step  (step > 1)
    Returns (counter_var, bound_term, accumulator_vars) or None.
    """
    test = stmt.test
    if not isinstance(test, ast.Compare):
        return None
    if len(test.ops) != 1 or len(test.comparators) != 1:
        return None

    op = test.ops[0]

    # ── Count-up pattern: i < n, i <= n, i != n ──
    if isinstance(op, (ast.Lt, ast.LtE, ast.NotEq)):
        if not isinstance(test.left, ast.Name):
            return None
        counter_name = test.left.id
        if counter_name not in modified:
            return None

        step_val = _find_counter_step(stmt.body, counter_name, ast.Add)
        if step_val is not None and step_val > 0:
            bound_term = _compile_expr_ot(test.comparators[0], env)
            if isinstance(op, ast.LtE):
                bound_term = OOp('add', (bound_term, OLit(1)))
            if step_val == 1:
                range_term = bound_term
            else:
                # range(0, bound, step) — the fold iterates over stepped range
                range_term = OOp('range', (OLit(0), bound_term, OLit(step_val)))
            acc_vars = [v for v in modified if v != counter_name]
            return (counter_name, range_term, acc_vars)

    # ── Count-down pattern: i > 0, i >= 1, i > lower ──
    if isinstance(op, (ast.Gt, ast.GtE)):
        if not isinstance(test.left, ast.Name):
            return None
        counter_name = test.left.id
        if counter_name not in modified:
            return None

        step_val = _find_counter_step(stmt.body, counter_name, ast.Sub)
        if step_val is not None and step_val > 0:
            lower_bound = _compile_expr_ot(test.comparators[0], env)
            if isinstance(op, ast.GtE):
                # i >= lower → iterates while i >= lower, so range ends at lower
                pass
            else:
                # i > lower → iterates while i > lower, so lower_bound + 1
                lower_bound = OOp('add', (lower_bound, OLit(1)))
            # Counter counts down from init to lower_bound
            # Equivalent to fold over reversed(range(lower_bound, init))
            # The init value of counter is in env
            init_val = env.get(counter_name)
            if init_val is not None and not isinstance(init_val, OUnknown):
                if step_val == 1:
                    range_term = OOp('reversed', (OOp('range', (lower_bound, init_val)),))
                else:
                    range_term = OOp('reversed', (OOp('range', (lower_bound, init_val, OLit(step_val))),))
                acc_vars = [v for v in modified if v != counter_name]
                return (counter_name, range_term, acc_vars)

    return None


def _find_counter_step(body, counter_name, expected_op_type):
    """Find the step value for a counter variable in a loop body.

    Looks for patterns like: counter += step, counter -= step,
    counter = counter + step, counter = counter - step.
    Returns the step value (int) or None.
    """
    for s in body:
        if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name):
            if s.target.id == counter_name and isinstance(s.op, expected_op_type):
                if isinstance(s.value, ast.Constant) and isinstance(s.value.value, int):
                    return s.value.value
        elif isinstance(s, ast.Assign):
            if (len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                    and s.targets[0].id == counter_name):
                if isinstance(s.value, ast.BinOp) and isinstance(s.value.op, expected_op_type):
                    if (isinstance(s.value.left, ast.Name) and s.value.left.id == counter_name
                            and isinstance(s.value.right, ast.Constant)
                            and isinstance(s.value.right.value, int)):
                        return s.value.right.value
                    elif (isinstance(s.value.right, ast.Name) and s.value.right.id == counter_name
                            and isinstance(s.value.left, ast.Constant)
                            and isinstance(s.value.left.value, int)
                            and isinstance(expected_op_type, type(ast.Add()))):
                        # Only commutative for Add: 1 + counter = counter + 1
                        return s.value.left.value
    return None


def _find_augassign_rhs(body, acc_name):
    """Find the RHS expression node of an augmented assignment to acc_name."""
    for s in body:
        if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name):
            if s.target.id == acc_name:
                return s.value
    return None


def _build_nested_setitem(base: OTerm, indices: list, val: OTerm) -> OTerm:
    """Build nested functional update for multi-dimensional assignment.

    _build_nested_setitem(dp, [i, j], val) produces:
      setitem(dp, i, setitem(getitem(dp, i), j, val))

    This is the persistent/functional version of dp[i][j] = val.
    """
    if len(indices) == 1:
        return OOp('setitem', (base, indices[0], val))
    inner = OOp('getitem', (base, indices[0]))
    updated_inner = _build_nested_setitem(inner, indices[1:], val)
    return OOp('setitem', (base, indices[0], updated_inner))


def _assign_ot(target, val: OTerm, env: DenotEnv):
    if isinstance(target, ast.Name):
        env.put(target.id, val)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for j, elt in enumerate(target.elts):
            _assign_ot(elt, OOp('getitem', (val, OLit(j))), env)
    elif isinstance(target, ast.Subscript):
        # Collect the chain of subscript indices from outermost to innermost
        chain = []
        current = target
        while isinstance(current, ast.Subscript):
            chain.append(current.slice)
            current = current.value
        if isinstance(current, ast.Name):
            obj_name = current.id
            old = env.get(obj_name)
            if old is None:
                old = OVar(obj_name)
            # chain is [outermost_idx, ..., innermost_idx], need root-to-leaf
            indices = [_compile_expr_ot(idx, env) for idx in reversed(chain)]
            env.put(obj_name, _build_nested_setitem(old, indices, val))


def _merge_envs_ot(target: DenotEnv, te: DenotEnv, fe: DenotEnv, test: OTerm):
    # Must check all keys that EITHER environment modified.
    # Use env.get() (not bindings.get()) so parameters resolve to OVar.
    all_keys = set(te.bindings) | set(fe.bindings)
    for k in all_keys:
        tv = te.get(k)
        fv = fe.get(k)
        # Skip unknowns (not in either env)
        if isinstance(tv, OUnknown) and isinstance(fv, OUnknown):
            continue
        if tv.canon() != fv.canon():
            target.put(k, OCase(test, tv, fv))
        else:
            target.put(k, tv)


def _guess_type(term: OTerm) -> str:
    """Guess the type of a term from its construction."""
    if isinstance(term, OOp):
        if term.name in ('list', 'sorted', 'reversed', 'tuple'):
            return 'list'
        if term.name in ('set', 'frozenset'):
            return 'set'
        if term.name in ('dict', 'Counter', 'defaultdict'):
            return 'dict'
    if isinstance(term, OSeq):
        return 'list'
    if isinstance(term, ODict):
        return 'dict'
    return 'unknown'


def _find_modified_ot(stmts) -> List[str]:
    modified = []
    seen = set()
    for s in stmts:
        names = []
        if isinstance(s, ast.AugAssign):
            if isinstance(s.target, ast.Name):
                names.append(s.target.id)
            elif isinstance(s.target, ast.Subscript):
                # Walk subscript chain to find root name
                cur = s.target
                while isinstance(cur, ast.Subscript):
                    cur = cur.value
                if isinstance(cur, ast.Name):
                    names.append(cur.id)
        elif isinstance(s, ast.Assign):
            for t in s.targets:
                if isinstance(t, ast.Name):
                    names.append(t.id)
                elif isinstance(t, (ast.Tuple, ast.List)):
                    for e in t.elts:
                        if isinstance(e, ast.Name):
                            names.append(e.id)
                        elif isinstance(e, ast.Subscript) and isinstance(e.value, ast.Name):
                            names.append(e.value.id)
                elif isinstance(t, ast.Subscript):
                    cur = t
                    while isinstance(cur, ast.Subscript):
                        cur = cur.value
                    if isinstance(cur, ast.Name):
                        names.append(cur.id)
                elif isinstance(t, ast.Attribute) and isinstance(t.value, ast.Name):
                    names.append(t.value.id)
        elif isinstance(s, ast.If):
            names.extend(_find_modified_ot(s.body))
            if s.orelse:
                names.extend(_find_modified_ot(s.orelse))
        elif isinstance(s, ast.For):
            names.extend(_find_modified_ot(s.body))
        elif isinstance(s, ast.While):
            names.extend(_find_modified_ot(s.body))
        elif isinstance(s, ast.Expr):
            if (isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Attribute)
                    and isinstance(s.value.func.value, ast.Name)):
                names.append(s.value.func.value.id)
        for n in names:
            if n not in seen:
                seen.add(n)
                modified.append(n)
    return modified


def _has_return(stmts) -> bool:
    for s in stmts:
        if isinstance(s, ast.Return):
            return True
        if isinstance(s, ast.If):
            if _has_return(s.body) and s.orelse and _has_return(s.orelse):
                return True
    return False


def _has_any_return(stmts) -> bool:
    """Check if any return exists in stmts (even in one branch of an if)."""
    for s in stmts:
        if isinstance(s, ast.Return):
            return True
        if isinstance(s, ast.If):
            if _has_any_return(s.body):
                return True
            if s.orelse and _has_any_return(s.orelse):
                return True
        if isinstance(s, ast.For):
            if _has_any_return(s.body):
                return True
        if isinstance(s, ast.While):
            if _has_any_return(s.body):
                return True
    return False


def _skip_doc(body):
    if (body and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        return body[1:]
    return body


# ═══════════════════════════════════════════════════════════
# Normalization (5-phase)
# ═══════════════════════════════════════════════════════════

def normalize(term: OTerm) -> OTerm:
    """Apply 7-phase normalization to an OTerm.

    Phase 1: β-reduction (inline, collapse trivial)
    Phase 2: Ring/lattice rewriting + mutation-pure bridge
    Phase 3: Fold canonicalization
    Phase 4: HOF fusion + dichotomy path constructors
    Phase 5: Shared symbol unification (the 24 dichotomies as rewrite rules)
    Phase 6: Quotient type normalization
    Phase 7: Piecewise case normalization (canonical ordering of guards)
    """
    prev = None
    current = term
    for _ in range(8):
        current = _phase1_beta(current)
        current = _phase2_ring(current)
        current = _phase3_fold(current)
        current = _phase4_hof(current)
        current = _phase5_unify(current)
        current = _phase6_quotient(current)
        current = _phase7_piecewise(current)
        if prev is not None and current.canon() == prev.canon():
            break
        prev = current
    # Final pass: de Bruijn normalize all bound variables
    current = _de_bruijn_normalize(current)
    # Rehash fold keys from body_fn canon (more precise than AST-dump hash)
    current = _rehash_folds(current)
    return current


def _try_case_factor(cond: OTerm, true_b: OTerm, false_b: OTerm) -> 'OTerm | None':
    """Case factoring: case(C, f(A), f(B)) → f(case(C, A_diff, B_diff)).

    When two branches share the same OTerm structure (same constructor tree)
    but differ only at OLit leaves, factor the case inward so that only the
    differing literals are wrapped in case(C, ...).

    This is a legitimate normalization — it's the functor property of the
    evaluation context, pushing the case expression to the minimal differing
    points. Mathematically, it's gluing local sections that agree on the
    complement of their difference set.
    """
    def _factor(a: OTerm, b: OTerm) -> 'OTerm | None':
        if a.canon() == b.canon():
            return a
        # Both must be the same type for structural factoring
        if type(a) != type(b):
            # Allow factoring at this level: both are OLit or both differ
            if isinstance(a, OLit) and isinstance(b, OLit):
                return OCase(cond, a, b)
            return None
        if isinstance(a, OLit) and isinstance(b, OLit):
            return OCase(cond, a, b)
        if isinstance(a, OOp) and isinstance(b, OOp):
            if a.name != b.name or len(a.args) != len(b.args):
                return None
            new_args = []
            for ai, bi in zip(a.args, b.args):
                f = _factor(ai, bi)
                if f is None:
                    return None
                new_args.append(f)
            return OOp(a.name, tuple(new_args))
        if isinstance(a, OCase) and isinstance(b, OCase):
            ft = _factor(a.test, b.test)
            ftr = _factor(a.true_branch, b.true_branch)
            ffr = _factor(a.false_branch, b.false_branch)
            if ft is None or ftr is None or ffr is None:
                return None
            return OCase(ft, ftr, ffr)
        if isinstance(a, OSeq) and isinstance(b, OSeq):
            if len(a.elements) != len(b.elements):
                return None
            new_elems = []
            for ai, bi in zip(a.elements, b.elements):
                f = _factor(ai, bi)
                if f is None:
                    return None
                new_elems.append(f)
            return OSeq(tuple(new_elems))
        if isinstance(a, OLam) and isinstance(b, OLam):
            if a.params != b.params:
                return None
            fb = _factor(a.body, b.body)
            if fb is None:
                return None
            return OLam(a.params, fb)
        if isinstance(a, OFold) and isinstance(b, OFold):
            fi = _factor(a.init, b.init)
            fc = _factor(a.collection, b.collection)
            if fi is None or fc is None:
                return None
            if a.body_fn is not None and b.body_fn is not None:
                fb = _factor(a.body_fn, b.body_fn)
                if fb is None:
                    return None
                return OFold(a.op_name, fi, fc, body_fn=fb)
            if a.body_fn is None and b.body_fn is None and a.op_name == b.op_name:
                return OFold(a.op_name, fi, fc)
            return None
        if isinstance(a, OMap) and isinstance(b, OMap):
            ft = _factor(a.transform, b.transform)
            fc = _factor(a.collection, b.collection)
            if ft is None or fc is None:
                return None
            if a.filter_pred is not None and b.filter_pred is not None:
                fp = _factor(a.filter_pred, b.filter_pred)
                if fp is None:
                    return None
                return OMap(ft, fc, fp)
            if a.filter_pred is None and b.filter_pred is None:
                return OMap(ft, fc, None)
            return None
        if isinstance(a, OQuotient) and isinstance(b, OQuotient):
            if a.equiv_class != b.equiv_class:
                return None
            fi = _factor(a.inner, b.inner)
            return OQuotient(fi, a.equiv_class) if fi is not None else None
        if isinstance(a, ODict) and isinstance(b, ODict):
            if len(a.pairs) != len(b.pairs):
                return None
            new_pairs = []
            for (ak, av), (bk, bv) in zip(a.pairs, b.pairs):
                fk = _factor(ak, bk)
                fv = _factor(av, bv)
                if fk is None or fv is None:
                    return None
                new_pairs.append((fk, fv))
            return ODict(tuple(new_pairs))
        # OVar, OFix, OUnknown etc: must be identical (already checked by canon())
        return None

    # Don't factor if both branches are already simple (OLit/OVar)
    if isinstance(true_b, (OLit, OVar)) and isinstance(false_b, (OLit, OVar)):
        return None
    result = _factor(true_b, false_b)
    # Only use factored form if it's actually simpler (not just wrapping the whole thing in case)
    if result is not None and result.canon() != OCase(cond, true_b, false_b).canon():
        return result
    return None


def _negate_map_pred(collection: OTerm) -> 'Optional[OTerm]':
    """Negate the predicate inside a map/filter_map for De Morgan on folds.

    Given map(λx.pred(x), coll), returns map(λx.not(pred(x)), coll).
    Handles OMap with transform and plain map OOp forms.
    Returns None if the collection is not a recognized map form.
    """
    if isinstance(collection, OMap):
        old_transform = collection.transform
        if isinstance(old_transform, OLam):
            new_body = OOp('u_not', (old_transform.body,))
            new_transform = OLam(old_transform.params, new_body)
            return OMap(new_transform, collection.collection, collection.filter_pred)
    if isinstance(collection, OOp) and collection.name == 'map' and len(collection.args) == 2:
        func_arg, coll_arg = collection.args
        if isinstance(func_arg, OLam):
            new_body = OOp('u_not', (func_arg.body,))
            new_func = OLam(func_arg.params, new_body)
            return OOp('map', (new_func, coll_arg))
    return None


def _simplify_ground(term: OTerm) -> OTerm | None:
    """Simplify a ground OTerm (no free vars) to a literal if possible.
    Returns OLit if fully reducible, None otherwise. Safe: bounded work."""
    if isinstance(term, OLit):
        return term
    if isinstance(term, OSeq):
        elts = [_simplify_ground(e) for e in term.elements]
        if all(e is not None and isinstance(e, OLit) for e in elts):
            return OLit([e.value for e in elts])
        return None
    if isinstance(term, OOp):
        args = [_simplify_ground(a) for a in term.args]
        if any(a is None for a in args):
            return None
        # All args are OLit — try constant fold
        vals = [a.value for a in args]
        if term.name == 'range':
            if len(vals) == 1 and isinstance(vals[0], int) and 0 <= vals[0] <= 20:
                return OLit(list(range(vals[0])))
            if len(vals) == 2 and all(isinstance(v, int) for v in vals) and 0 <= vals[1] - vals[0] <= 20:
                return OLit(list(range(vals[0], vals[1])))
            return None
        if term.name == 'getitem':
            coll, idx = vals
            if isinstance(coll, (list, tuple)) and isinstance(idx, int) and 0 <= idx < len(coll):
                return OLit(coll[idx])
            return None
        r = _try_const_fold(term.name, vals)
        if r is not None:
            return OLit(r)
        return None
    if isinstance(term, OFold):
        # Evaluate fold on a small ground collection
        init_s = _simplify_ground(term.init)
        coll_s = _simplify_ground(term.collection)
        if init_s is None or coll_s is None:
            return None
        if not isinstance(coll_s, OLit) or not isinstance(coll_s.value, list):
            return None
        if len(coll_s.value) > 10:
            return None
        # Need body_fn to evaluate fold
        if term.body_fn is None:
            return None
        if not isinstance(term.body_fn, OLam):
            return None
        acc = init_s
        for elem_val in coll_s.value:
            # Substitute params in body_fn
            params = term.body_fn.params
            body = term.body_fn.body
            if isinstance(acc, OLit):
                if isinstance(acc.value, list) and len(params) >= len(acc.value) + 1:
                    # Fold with tuple state: params = [s0, s1, ..., x]
                    subs = {}
                    for i, sv in enumerate(acc.value):
                        if i < len(params) - 1:
                            subs[params[i]] = OLit(sv)
                    subs[params[-1]] = OLit(elem_val)
                    b = body
                    for k, v in subs.items():
                        b = _subst_term(b, k, v)
                    acc = _simplify_ground(b)
                elif len(params) == 2:
                    # scalar fold: params = [acc, x]
                    b = _subst_term(_subst_term(body, params[0], acc), params[1], OLit(elem_val))
                    acc = _simplify_ground(b)
                else:
                    return None
            else:
                return None
            if acc is None:
                return None
        return acc
    if isinstance(term, OCase):
        test_s = _simplify_ground(term.test)
        if test_s is None:
            return None
        if isinstance(test_s, OLit):
            if test_s.value:
                return _simplify_ground(term.true_branch)
            else:
                return _simplify_ground(term.false_branch)
        return None
    return None


def _propagate_guard_constraints(term: OTerm,
                                  known_true: set,
                                  known_false: set,
                                  depth: int = 0) -> OTerm:
    """Simplify a term given known-true and known-false guard canons.

    When a case guard is known True, the case reduces to its true branch.
    When known False, it reduces to its false branch.
    This is stalk evaluation: restricting a section to a specific fiber
    eliminates branching on predicates that are constant on that fiber.

    Also handles:
      - or(G1,...,Gk) is True when any Gi is known True
      - and(G1,...,Gk) is False when any Gi is known False
    """
    if depth > 20 or (not known_true and not known_false):
        return term
    if isinstance(term, OCase):
        tc = term.test.canon()
        # Direct guard match
        if tc in known_true:
            return _propagate_guard_constraints(
                term.true_branch, known_true, known_false, depth + 1)
        if tc in known_false:
            return _propagate_guard_constraints(
                term.false_branch, known_true, known_false, depth + 1)
        # or(G1,...) is True if any Gi is known True
        if isinstance(term.test, OOp) and term.test.name == 'or':
            if any(a.canon() in known_true for a in term.test.args):
                return _propagate_guard_constraints(
                    term.true_branch, known_true, known_false, depth + 1)
        # and(G1,...) is False if any Gi is known False
        if isinstance(term.test, OOp) and term.test.name == 'and':
            if any(a.canon() in known_false for a in term.test.args):
                return _propagate_guard_constraints(
                    term.false_branch, known_true, known_false, depth + 1)
        # or(G1,...) is False if ALL Gi are known False
        if isinstance(term.test, OOp) and term.test.name == 'or':
            if all(a.canon() in known_false for a in term.test.args):
                return _propagate_guard_constraints(
                    term.false_branch, known_true, known_false, depth + 1)
        # and(G1,...) is True if ALL Gi are known True
        if isinstance(term.test, OOp) and term.test.name == 'and':
            if all(a.canon() in known_true for a in term.test.args):
                return _propagate_guard_constraints(
                    term.true_branch, known_true, known_false, depth + 1)
        # Recurse into branches
        t2 = _propagate_guard_constraints(
            term.true_branch, known_true, known_false, depth + 1)
        f2 = _propagate_guard_constraints(
            term.false_branch, known_true, known_false, depth + 1)
        if t2 is not term.true_branch or f2 is not term.false_branch:
            return OCase(term.test, t2, f2)
        return term

    if isinstance(term, OOp):
        new_args = []
        changed = False
        for a in term.args:
            a2 = _propagate_guard_constraints(a, known_true, known_false, depth + 1)
            new_args.append(a2)
            if a2 is not a:
                changed = True
        if changed:
            result = OOp(term.name, tuple(new_args))
            # Constant-fold eq(X, X) → True after propagation
            if term.name == 'eq' and len(new_args) == 2:
                if new_args[0].canon() == new_args[1].canon():
                    return OLit(True)
            # or(..., True, ...) → True
            if term.name == 'or':
                if any(isinstance(a, OLit) and a.value is True for a in new_args):
                    return OLit(True)
            # and(..., False, ...) → False
            if term.name == 'and':
                if any(isinstance(a, OLit) and a.value is False for a in new_args):
                    return OLit(False)
            # and(True, True, ...) → True; or(False, False, ...) → False
            if term.name == 'and' and all(isinstance(a, OLit) and a.value is True for a in new_args):
                return OLit(True)
            if term.name == 'or' and all(isinstance(a, OLit) and a.value is False for a in new_args):
                return OLit(False)
            return result
        return term

    if isinstance(term, OFold):
        i2 = _propagate_guard_constraints(term.init, known_true, known_false, depth + 1)
        c2 = _propagate_guard_constraints(term.collection, known_true, known_false, depth + 1)
        bfn = None
        if term.body_fn:
            bfn = _propagate_guard_constraints(term.body_fn, known_true, known_false, depth + 1)
        if i2 is not term.init or c2 is not term.collection or bfn is not term.body_fn:
            r = OFold(term.op_name, i2, c2, body_fn=bfn)
            return r
        return term

    if isinstance(term, OSeq):
        new_elems = []
        changed = False
        for e in term.elements:
            e2 = _propagate_guard_constraints(e, known_true, known_false, depth + 1)
            new_elems.append(e2)
            if e2 is not e:
                changed = True
        return OSeq(tuple(new_elems)) if changed else term

    return term


def _phase1_beta(term: OTerm) -> OTerm:
    """Phase 1: β-reduction and trivial simplification."""
    if isinstance(term, OCase):
        test = _phase1_beta(term.test)
        t = _phase1_beta(term.true_branch)
        f = _phase1_beta(term.false_branch)
        # Collapse: case(True, t, f) → t
        if isinstance(test, OLit) and test.value is True:
            return t
        if isinstance(test, OLit) and test.value is False:
            return f
        # Collapse: case(c, x, x) → x
        if t.canon() == f.canon():
            return t

        # ── Guard-aware branch collapse ──
        # case(eq(a, b), T, F) → F  when T[a←b] == F[a←b]
        # Under eq(a,b), a and b are interchangeable, so if both branches
        # become identical when we substitute a→b, the case is redundant.
        if (isinstance(test, OOp) and test.name == 'eq' and len(test.args) == 2):
            a, b = test.args
            if isinstance(a, OVar) and isinstance(b, OVar):
                t_sub = _subst_term(t, a.name, b)
                f_sub = _subst_term(f, a.name, b)
                if t_sub.canon() == f_sub.canon():
                    return f

        # ── R18: Redundant base-case guard elimination ──
        # case(eq(X, C), V, E) → E  when E[X/C] normalizes to V
        # This eliminates defensive base cases that are subsumed by the main
        # computation (e.g. `if n==1: return 1; ... fold ...` where fold(1)=1).
        if (isinstance(test, OOp) and test.name == 'eq' and len(test.args) == 2
                and isinstance(t, OLit)):
            eq_a, eq_b = test.args
            var_term, const_term = None, None
            if isinstance(eq_a, OVar) and isinstance(eq_b, OLit):
                var_term, const_term = eq_a, eq_b
            elif isinstance(eq_b, OVar) and isinstance(eq_a, OLit):
                var_term, const_term = eq_b, eq_a
            if var_term is not None and const_term is not None:
                substituted = _subst_term(f, var_term.name, const_term)
                # Limited simplification: constant folding + range/getitem eval
                simp = _simplify_ground(substituted)
                if simp is not None and isinstance(simp, OLit) and simp.value == t.value:
                    return f

        # ── R18b: Disjunctive guard elimination ──
        # case(or(eq(X,C1), eq(Y,C2), ...), V, E) → E
        # when E[Xi/Ci] = V for EVERY disjunct eq(Xi, Ci).
        # Each disjunct is a base case that the main expression E handles.
        # Handles both eq(Var, Lit) and eq(Var, Var) disjuncts.
        if (isinstance(test, OOp) and test.name == 'or'
                and isinstance(t, OLit) and len(test.args) >= 2):
            all_absorbed = True
            for disjunct in test.args:
                if (isinstance(disjunct, OOp) and disjunct.name == 'eq'
                        and len(disjunct.args) == 2):
                    eq_a, eq_b = disjunct.args
                    # Try substitution in both directions
                    absorbed = False
                    for src, dst in [(eq_a, eq_b), (eq_b, eq_a)]:
                        if isinstance(src, OVar):
                            substituted = _subst_term(f, src.name, dst)
                            # Try ground simplification first
                            simp = _simplify_ground(substituted)
                            if simp is not None and isinstance(simp, OLit) and simp.value == t.value:
                                absorbed = True
                                break
                            # Try re-normalizing with phase 2 rules (handles comb(n,0)→1 etc.)
                            renorm = _phase2_ring(substituted)
                            if isinstance(renorm, OLit) and renorm.value == t.value:
                                absorbed = True
                                break
                    if absorbed:
                        continue
                all_absorbed = False
                break
            if all_absorbed:
                return f

        # ── Boolean complement: case(not(t), A, B) → case(t, B, A) ──
        # Canonical form puts the positive guard first.
        if isinstance(test, OOp) and test.name in ('u_not', 'not', 'Not') and len(test.args) == 1:
            return OCase(test.args[0], f, t)

        # ── Guard comparison normalization ──
        # Canonicalize comparison operators to reduce redundant forms:
        #   case(lte(a,b), X, Y) → case(gt(a,b), Y, X)   [prefer gt over lte]
        #   case(ge(a,b), X, Y) → case(lt(a,b), Y, X)    [prefer lt over ge]
        # This ensures the same partition is expressed the same way.
        if isinstance(test, OOp) and len(test.args) == 2:
            _FLIP_CMP = {'lte': 'gt', 'LtE': 'gt', '<=': 'gt',
                         'ge': 'lt', 'GtE': 'lt', '>=': 'lt',
                         'gte': 'lt'}
            if test.name in _FLIP_CMP:
                flipped = OOp(_FLIP_CMP[test.name], test.args)
                return OCase(flipped, f, t)

        # ── R16: Redundant guard elimination ──
        # case(lt(len(X), K), [], map/filter_map(λ, range(sub(len(X), M))))
        # When len(X) < K and M >= 1, range(len(X)-M) is empty → map returns [].
        # The guard just returns [] explicitly, which map already produces.
        if (isinstance(t, (OLit, OSeq))
                and ((isinstance(t, OLit) and t.value == [])
                     or (isinstance(t, OSeq) and len(t.elements) == 0))):
            # Check if false branch is OMap or filter_map OOp over range(sub(len(X), M))
            range_arg = None
            if isinstance(f, OMap):
                range_arg = f.collection
            elif isinstance(f, OOp) and f.name in ('map', 'filter_map'):
                range_arg = f.args[-1] if len(f.args) >= 2 else None
            if range_arg is not None:
                if (isinstance(range_arg, OOp) and range_arg.name == 'range'
                        and len(range_arg.args) == 1):
                    rng_expr = range_arg.args[0]
                    if isinstance(rng_expr, OOp) and rng_expr.name == 'sub':
                        sub_a, sub_b = rng_expr.args
                        if (isinstance(sub_b, OLit) and isinstance(sub_b.value, (int, float))
                                and sub_b.value >= 1
                                and isinstance(test, OOp) and test.name == 'lt'):
                            return f

        # ── R16b: case-as-min/max normalization ──
        # case(lt(A, B), A, B) → min(A, B)
        # case(lt(A, B), B, A) → max(A, B)
        # case(gt(A, B), A, B) → max(A, B)
        # case(gt(A, B), B, A) → min(A, B)
        if isinstance(test, OOp) and test.name in ('lt', 'gt') and len(test.args) == 2:
            cmp_a, cmp_b = test.args
            ca, cb = cmp_a.canon(), cmp_b.canon()
            ct, cf = t.canon(), f.canon()
            if test.name == 'lt':
                if ct == ca and cf == cb:
                    return OOp('min', (t, f))
                if ct == cb and cf == ca:
                    return OOp('max', (t, f))
            elif test.name == 'gt':
                if ct == ca and cf == cb:
                    return OOp('max', (t, f))
                if ct == cb and cf == ca:
                    return OOp('min', (t, f))

        # ── R17: Infinity absorption ──
        # case(eq(X, inf), inf, f(X)) → f(X) when f(inf) = inf
        # Applies to add, sub, mult with finite constants.
        # inf can be OLit(float('inf')) or OOp('float', (OLit('inf'),))
        def _is_inf(term):
            if isinstance(term, OLit) and term.value == float('inf'):
                return True
            if (isinstance(term, OOp) and term.name == 'float'
                    and len(term.args) == 1
                    and isinstance(term.args[0], OLit)
                    and term.args[0].value == 'inf'):
                return True
            return False

        if (isinstance(test, OOp) and test.name == 'eq' and len(test.args) == 2):
            cmp_a, cmp_b = test.args
            if (_is_inf(cmp_a) or _is_inf(cmp_b)) and _is_inf(t):
                if isinstance(f, OOp) and f.name in ('add', 'sub', 'mult'):
                    return f

        # ── Guard absorption via fiber argument ──
        # case(G1, case(G2, V, W), X) → case(and(G1,G2), V, X) when W ≡ X
        # Under ¬G1 we get X, under G1∧¬G2 we get W = X, so the inner
        # false branch is redundant. This is a sheaf gluing argument:
        # the section on G1∧¬G2 agrees with the section on ¬G1.
        if isinstance(t, OCase):
            if t.false_branch.canon() == f.canon():
                # case(G1, case(G2, V, X), X) → case(and(G1,G2), V, X)
                combined = OOp('and', (test, t.test))
                return OCase(combined, t.true_branch, f)
            if t.true_branch.canon() == f.canon():
                # case(G1, case(G2, X, W), X) → case(and(G1, not(G2)), W, X)
                neg_g2 = OOp('not', (t.test,))
                combined = OOp('and', (test, neg_g2))
                return OCase(combined, t.false_branch, f)

        # Symmetric: case(G1, X, case(G2, V, W)) when V ≡ X or W ≡ X
        if isinstance(f, OCase):
            if f.true_branch.canon() == t.canon():
                # case(G1, X, case(G2, X, W)) → case(or(G1, G2), X, W)
                combined = OOp('or', (test, f.test))
                return OCase(combined, t, f.false_branch)
            if f.false_branch.canon() == t.canon():
                # case(G1, X, case(G2, V, X)) → case(and(not(G1), G2), V, X)
                neg_g1 = OOp('not', (test,))
                combined = OOp('and', (neg_g1, f.test))
                return OCase(combined, f.true_branch, t)

        # ── Guard constraint propagation (stalk simplification) ──
        # When evaluating case(G, T, F):
        #   - In the T branch, G is known True — inner case(G,...) → true_branch
        #   - In the F branch, G is known False — inner case(G,...) → false_branch
        # Also decomposes conjunctions/disjunctions:
        #   - G = and(G1,G2,...): G1,G2,... all True in T branch
        #   - G = or(G1,G2,...): G1,G2,... all False in F branch
        # This is stalk computation: the section restricted to a fiber
        # simplifies because guard predicates have known truth values.
        true_guards = {test.canon()}
        false_guards = {test.canon()}
        if isinstance(test, OOp) and test.name == 'and':
            for conj in test.args:
                true_guards.add(conj.canon())
        if isinstance(test, OOp) and test.name == 'or':
            for disj in test.args:
                false_guards.add(disj.canon())
        t2 = _propagate_guard_constraints(t, true_guards, set())
        f2 = _propagate_guard_constraints(f, set(), false_guards)
        if t2.canon() != t.canon() or f2.canon() != f.canon():
            t, f = t2, f2
            # Re-check collapse after propagation
            if isinstance(t, OLit) and t.value is True and isinstance(f, OLit) and f.value is True:
                return OLit(True)
            if t.canon() == f.canon():
                return t

        # ── Case factoring (anti-distribution) ──
        # case(C, f(A1,...), f(B1,...)) → f(case(C, A1, B1), ...) when
        # both branches share the same structure and differ only in OLit
        # leaves. This is the functor property of case over term structure.
        factored = _try_case_factor(test, t, f)
        if factored is not None:
            return factored

        return OCase(test, t, f)

    if isinstance(term, OOp):
        args = tuple(_phase1_beta(a) for a in term.args)
        # Constant folding
        if all(isinstance(a, OLit) for a in args):
            result = _try_const_fold(term.name, [a.value for a in args])
            if result is not None:
                return OLit(result)

        # ── Range normalization ──
        # range(0, n) → range(n)
        # range(0, n, 1) → range(n)
        if term.name == 'range':
            if len(args) == 2:
                start, stop = args
                if isinstance(start, OLit) and start.value == 0:
                    return OOp('range', (stop,))
            elif len(args) == 3:
                start, stop, step = args
                if (isinstance(start, OLit) and start.value == 0
                        and isinstance(step, OLit) and step.value == 1):
                    return OOp('range', (stop,))

        # range(N) where N <= 0 → [] (empty range)
        # range(a, b) where a >= b → [] (empty range)
        # range(a, b, step) where step > 0 and a >= b → [] (empty range)
        # range(a, b, step) where step < 0 and a <= b → [] (empty range)
        if term.name == 'range':
            if len(args) == 1:
                n = args[0]
                if isinstance(n, OLit) and isinstance(n.value, (int, float)) and n.value <= 0:
                    return OSeq(())
            elif len(args) == 2:
                start, stop = args
                if (isinstance(start, OLit) and isinstance(stop, OLit)
                        and isinstance(start.value, (int, float))
                        and isinstance(stop.value, (int, float))):
                    if start.value >= stop.value:
                        return OSeq(())
            elif len(args) == 3:
                start, stop, step = args
                if (isinstance(start, OLit) and isinstance(stop, OLit)
                        and isinstance(step, OLit)
                        and isinstance(start.value, (int, float))
                        and isinstance(stop.value, (int, float))
                        and isinstance(step.value, (int, float))
                        and step.value != 0):
                    if step.value > 0 and start.value >= stop.value:
                        return OSeq(())
                    if step.value < 0 and start.value <= stop.value:
                        return OSeq(())

        # getitem([a, b, ...], literal_idx) → direct element
        if term.name == 'getitem' and len(args) == 2:
            base, idx = args
            if isinstance(idx, OLit) and isinstance(idx.value, int):
                if isinstance(base, OSeq) and 0 <= idx.value < len(base.elements):
                    return base.elements[idx.value]
            # ── setitem/getitem algebra ──
            # getitem(setitem(X, I, V), I) → V  (read-after-write, same index)
            if (isinstance(base, OOp) and base.name == 'setitem'
                    and len(base.args) == 3):
                set_base, set_idx, set_val = base.args
                if set_idx.canon() == idx.canon():
                    return set_val
                # getitem(setitem(X, J, V), I) → getitem(X, I) when J≠I
                # Only when disequality is syntactically obvious
                if (isinstance(set_idx, OLit) and isinstance(idx, OLit)
                        and set_idx.value != idx.value):
                    return OOp('getitem', (set_base, idx))
            # getitem(mult([V], N), I) → V  (all elements are V)
            if (isinstance(base, OOp) and base.name == 'mult'
                    and len(base.args) == 2
                    and isinstance(base.args[0], OSeq)
                    and len(base.args[0].elements) == 1):
                return base.args[0].elements[0]
        # Empty collection simplifications
        if len(args) == 1:
            a0 = args[0]
            is_empty = (isinstance(a0, OSeq) and len(a0.elements) == 0) or \
                       (isinstance(a0, OOp) and a0.name == 'dict' and len(a0.args) == 0)
            if is_empty:
                if term.name in ('sorted', 'reversed', 'list', 'tuple'):
                    return OSeq(())
                if term.name == 'len':
                    return OLit(0)
                if term.name in ('sum', 'max', 'min', 'any'):
                    if term.name == 'sum':
                        return OLit(0)
                    if term.name == 'any':
                        return OLit(False)
                if term.name == 'set':
                    return OQuotient(OOp('set', ()), 'perm')
            # Idempotent: sorted(sorted(x)) → sorted(x), list(list(x)) → list(x)
            if isinstance(a0, OOp) and a0.name == term.name and term.name in ('sorted', 'list', 'tuple', 'set', 'reversed'):
                return a0
            # len(range(n)) → n
            if term.name == 'len' and isinstance(a0, OOp) and a0.name == 'range' and len(a0.args) == 1:
                return a0.args[0]

        # ── Eq over sequence distribution ──
        # eq([a1,...,an], [b1,...,bn]) → and(eq(a1,b1), ..., eq(an,bn))
        # List/tuple equality is element-wise in Python. This enables
        # Z3 to check each element independently (e.g., algebraic identities).
        if term.name == 'eq' and len(args) == 2:
            a, b = args
            if (isinstance(a, OSeq) and isinstance(b, OSeq)
                    and len(a.elements) == len(b.elements)
                    and len(a.elements) > 0):
                conjuncts = tuple(
                    OOp('eq', (ai, bi))
                    for ai, bi in zip(a.elements, b.elements))
                if len(conjuncts) == 1:
                    return conjuncts[0]
                return OOp('and', conjuncts)

        # ── Eq over case distribution (Čech descent) ──
        # Distributes equality checking across regions of a piecewise
        # decomposition. Only applied when at least one branch immediately
        # simplifies (canon match), preventing infinite loops with case factoring.
        if term.name == 'eq' and len(args) == 2:
            a, b = args
            # eq(case(G, A, B), case(G, C, D)) → case(G, eq(A,C), eq(B,D))
            if isinstance(a, OCase) and isinstance(b, OCase):
                if a.test.canon() == b.test.canon():
                    t_match = a.true_branch.canon() == b.true_branch.canon()
                    f_match = a.false_branch.canon() == b.false_branch.canon()
                    if t_match or f_match:
                        eq_t = OLit(True) if t_match else OOp('eq', (a.true_branch, b.true_branch))
                        eq_f = OLit(True) if f_match else OOp('eq', (a.false_branch, b.false_branch))
                        return OCase(a.test, eq_t, eq_f)
            # eq(case(G, A, B), V) → case(G, eq(A,V), eq(B,V)) when a branch matches V
            # eq(V, case(G, A, B)) → case(G, eq(V,A), eq(V,B)) when a branch matches V
            for case_arg, other_arg, swap in [(a, b, False), (b, a, True)]:
                if isinstance(case_arg, OCase) and not isinstance(other_arg, OCase):
                    oc = other_arg.canon()
                    t_match = case_arg.true_branch.canon() == oc
                    f_match = case_arg.false_branch.canon() == oc
                    if t_match or f_match:
                        if swap:
                            eq_t = OLit(True) if t_match else OOp('eq', (other_arg, case_arg.true_branch))
                            eq_f = OLit(True) if f_match else OOp('eq', (other_arg, case_arg.false_branch))
                        else:
                            eq_t = OLit(True) if t_match else OOp('eq', (case_arg.true_branch, other_arg))
                            eq_f = OLit(True) if f_match else OOp('eq', (case_arg.false_branch, other_arg))
                        return OCase(case_arg.test, eq_t, eq_f)

        return OOp(term.name, args)

    if isinstance(term, OFold):
        init = _phase1_beta(term.init)
        coll = _phase1_beta(term.collection)
        # fold(init, []) → init (folding over empty collection returns initial value)
        if isinstance(coll, OSeq) and len(coll.elements) == 0:
            return init
        bfn = _phase1_beta(term.body_fn) if term.body_fn else None
        return OFold(term.op_name, init, coll, body_fn=bfn)

    if isinstance(term, OFix):
        return OFix(term.name, _phase1_beta(term.body))

    if isinstance(term, OSeq):
        return OSeq(tuple(_phase1_beta(e) for e in term.elements))

    if isinstance(term, ODict):
        return ODict(tuple((_phase1_beta(k), _phase1_beta(v)) for k, v in term.pairs))

    if isinstance(term, OQuotient):
        inner = _phase1_beta(term.inner)
        # Q[perm](dict(X)) → dict(X): dict equality is key-value based
        # Q[perm](set(X)) → set(X): set equality is element-based
        if term.equiv_class == 'perm' and isinstance(inner, OOp):
            if inner.name in ('dict', 'set', 'dictcomp', 'setcomp',
                              'frozenset'):
                return inner
        return OQuotient(inner, term.equiv_class)

    if isinstance(term, OAbstract):
        return OAbstract(term.spec, tuple(_phase1_beta(a) for a in term.inputs))

    if isinstance(term, OLam):
        return OLam(term.params, _phase1_beta(term.body))

    if isinstance(term, OMap):
        t = _phase1_beta(term.transform)
        c = _phase1_beta(term.collection)
        f = _phase1_beta(term.filter_pred) if term.filter_pred else None
        # OMap with identity transform → collection itself
        if isinstance(t, OLam) and len(t.params) == 1:
            if isinstance(t.body, OVar) and t.body.name == t.params[0]:
                if f is None:
                    return c  # map(id, xs) → xs
        # map(f, []) → [] (mapping over empty collection)
        if isinstance(c, OSeq) and len(c.elements) == 0:
            return OSeq(())
        return OMap(t, c, f)

    if isinstance(term, OCatch):
        body = _phase1_beta(term.body)
        default = _phase1_beta(term.default)
        # catch(x, x) → x (same body and default)
        if body.canon() == default.canon():
            return body
        return OCatch(body, default)

    return term


def _phase2_ring(term: OTerm) -> OTerm:
    """Phase 2: Ring/lattice axiom rewriting."""
    if isinstance(term, OOp):
        args = tuple(_phase2_ring(a) for a in term.args)
        name = term.name

        # ── In-place → pure normalization (Ring axiom) ──
        # On the Int/Float fiber, in-place ops are definitionally equal
        # to pure ops: iadd(a,b) ≡ add(a,b), isub(a,b) ≡ sub(a,b), etc.
        # This is because Python integers are immutable — the in-place
        # operators desugar to the pure binary operators.
        _INPLACE_TO_PURE = {
            'iadd': 'add', 'isub': 'sub', 'imult': 'mult',
            'ifloordiv': 'floordiv', 'imod': 'mod', 'ipow': 'pow',
            'ibitor': 'bitor', 'ibitand': 'bitand', 'ibitxor': 'bitxor',
            'ilshift': 'lshift', 'irshift': 'rshift',
        }
        if name in _INPLACE_TO_PURE:
            name = _INPLACE_TO_PURE[name]

        # ── Constant folding (ring evaluation) ──
        # When both arguments are literal values, evaluate the arithmetic.
        # This is sound for all fibers since literals have definite types.
        if len(args) == 2 and isinstance(args[0], OLit) and isinstance(args[1], OLit):
            a_val, b_val = args[0].value, args[1].value
            if isinstance(a_val, (int, float)) and isinstance(b_val, (int, float)):
                try:
                    if name == 'add':
                        return OLit(a_val + b_val)
                    elif name == 'sub':
                        return OLit(a_val - b_val)
                    elif name == 'mult':
                        return OLit(a_val * b_val)
                    elif name == 'floordiv' and b_val != 0:
                        return OLit(a_val // b_val)
                    elif name == 'mod' and b_val != 0:
                        return OLit(a_val % b_val)
                    elif name == 'pow' and (b_val >= 0 or isinstance(a_val, float)):
                        result = a_val ** b_val
                        if isinstance(result, (int, float)) and abs(result) < 1e15:
                            return OLit(result)
                    elif name == 'lshift' and isinstance(b_val, int) and 0 <= b_val <= 63:
                        return OLit(int(a_val) << int(b_val))
                    elif name == 'rshift' and isinstance(b_val, int) and 0 <= b_val <= 63:
                        return OLit(int(a_val) >> int(b_val))
                    elif name == 'bitor':
                        return OLit(int(a_val) | int(b_val))
                    elif name == 'bitand':
                        return OLit(int(a_val) & int(b_val))
                    elif name == 'bitxor':
                        return OLit(int(a_val) ^ int(b_val))
                    elif name == 'min':
                        return OLit(min(a_val, b_val))
                    elif name == 'max':
                        return OLit(max(a_val, b_val))
                except (OverflowError, ValueError, ZeroDivisionError):
                    pass
        # Unary constant folding
        if len(args) == 1 and isinstance(args[0], OLit):
            a_val = args[0].value
            if isinstance(a_val, (int, float)):
                if name == 'u_usub':
                    return OLit(-a_val)
                elif name == 'abs':
                    return OLit(abs(a_val))
                elif name == 'u_not' and isinstance(a_val, bool):
                    return OLit(not a_val)

        # R3: x + 0 → x, 0 + x → x
        if name in ('add', 'iadd') and len(args) == 2:
            if isinstance(args[1], OLit) and args[1].value == 0:
                return args[0]
            if isinstance(args[0], OLit) and args[0].value == 0:
                return args[1]

        # R5: (x + c1) - c1 → x, (x - c1) + c1 → x (add-sub cancellation)
        if name in ('sub', 'isub') and len(args) == 2:
            if (isinstance(args[0], OOp) and args[0].name in ('add', 'iadd')
                    and len(args[0].args) == 2
                    and isinstance(args[0].args[1], OLit) and isinstance(args[1], OLit)
                    and args[0].args[1].value == args[1].value):
                return args[0].args[0]
        if name in ('add', 'iadd') and len(args) == 2:
            if (isinstance(args[0], OOp) and args[0].name in ('sub', 'isub')
                    and len(args[0].args) == 2
                    and isinstance(args[0].args[1], OLit) and isinstance(args[1], OLit)
                    and args[0].args[1].value == args[1].value):
                return args[0].args[0]

        # R5b: General linear arithmetic: (x + c1) - c2 → x + (c1-c2)
        # and c1 + (x - c2) → x + (c1-c2)  (constant folding through add/sub)
        if name in ('sub', 'isub') and len(args) == 2 and isinstance(args[1], OLit):
            c2 = args[1].value
            if isinstance(c2, int) and isinstance(args[0], OOp):
                if args[0].name in ('add', 'iadd') and len(args[0].args) == 2:
                    if isinstance(args[0].args[1], OLit) and isinstance(args[0].args[1].value, int):
                        c1 = args[0].args[1].value
                        diff = c1 - c2
                        x = args[0].args[0]
                        if diff == 0:
                            return x
                        elif diff > 0:
                            return OOp('add', (x, OLit(diff)))
                        else:
                            return OOp('sub', (x, OLit(-diff)))
        if name in ('add', 'iadd') and len(args) == 2 and isinstance(args[0], OLit):
            c1 = args[0].value
            if isinstance(c1, int) and isinstance(args[1], OOp):
                if args[1].name in ('sub', 'isub') and len(args[1].args) == 2:
                    if isinstance(args[1].args[1], OLit) and isinstance(args[1].args[1].value, int):
                        c2 = args[1].args[1].value
                        diff = c1 - c2
                        x = args[1].args[0]
                        if diff == 0:
                            return x
                        elif diff > 0:
                            return OOp('add', (x, OLit(diff)))
                        else:
                            return OOp('sub', (x, OLit(-diff)))

        # R6: x - 0 → x
        if name in ('sub', 'isub') and len(args) == 2:
            if isinstance(args[1], OLit) and args[1].value == 0:
                return args[0]

        # XOR identities: x ^ x = 0, x ^ 0 = x, 0 ^ x = x
        if name in ('bitxor', 'ixor') and len(args) == 2:
            if args[0].canon() == args[1].canon():
                return OLit(0)
            if isinstance(args[0], OLit) and args[0].value == 0:
                return args[1]
            if isinstance(args[1], OLit) and args[1].value == 0:
                return args[0]

        # AND identities: x & x = x, x & 0 = 0
        if name in ('bitand', 'iand') and len(args) == 2:
            if args[0].canon() == args[1].canon():
                return args[0]
            if isinstance(args[0], OLit) and args[0].value == 0:
                return OLit(0)
            if isinstance(args[1], OLit) and args[1].value == 0:
                return OLit(0)

        # OR identities: x | x = x, x | 0 = x
        if name in ('bitor', 'ior') and len(args) == 2:
            if args[0].canon() == args[1].canon():
                return args[0]
            if isinstance(args[0], OLit) and args[0].value == 0:
                return args[1]
            if isinstance(args[1], OLit) and args[1].value == 0:
                return args[0]

        # ── Sum linearity: sub(fold[add](0, map(f, xs)), fold[add](0, map(g, xs)))
        #    → fold[add](0, map(λx. sub(f(x), g(x)), xs))
        # General algebraic law: Σf(x) - Σg(x) = Σ(f(x)-g(x))
        if name in ('sub', 'isub') and len(args) == 2:
            a, b = args
            if (isinstance(a, OFold) and isinstance(b, OFold) and
                    a.op_name in ('add', 'iadd') and b.op_name in ('add', 'iadd')):
                # Both have map transforms → combine the lambdas
                if (isinstance(a.collection, OMap) and isinstance(b.collection, OMap) and
                        a.collection.filter_pred is None and b.collection.filter_pred is None and
                        isinstance(a.collection.transform, OLam) and
                        isinstance(b.collection.transform, OLam) and
                        len(a.collection.transform.params) == 1 and
                        len(b.collection.transform.params) == 1 and
                        a.collection.collection.canon() == b.collection.collection.canon()):
                    param = a.collection.transform.params[0]
                    f_body = a.collection.transform.body
                    g_body = b.collection.transform.body
                    # Rename b's param to match a's
                    g_body = _subst_term(g_body, b.collection.transform.params[0],
                                         OVar(param))
                    combined = OOp('sub', (f_body, g_body))
                    init = OOp('sub', (a.init, b.init))
                    return OFold('add', init,
                                 OMap(OLam((param,), combined),
                                      a.collection.collection))

        # R8: x * 1 → x, 1 * x → x
        if name in ('mult', 'imult') and len(args) == 2:
            if isinstance(args[1], OLit) and args[1].value == 1:
                return args[0]
            if isinstance(args[0], OLit) and args[0].value == 1:
                return args[1]

        # R10: x * 0 → 0
        if name in ('mult', 'imult') and len(args) == 2:
            if isinstance(args[1], OLit) and args[1].value == 0:
                return OLit(0)
            if isinstance(args[0], OLit) and args[0].value == 0:
                return OLit(0)

        # R10b: sub(x, x) → 0 (additive self-cancellation)
        if name in ('sub', 'isub') and len(args) == 2:
            if args[0].canon() == args[1].canon():
                return OLit(0)

        # R10c: floordiv(x, x) → 1, truediv(x, x) → 1 (multiplicative identity)
        if name in ('floordiv', 'ifloordiv', 'truediv', 'itruediv') and len(args) == 2:
            if args[0].canon() == args[1].canon():
                return OLit(1)

        # R10d: mod(x, x) → 0 (self-modulus)
        if name in ('mod', 'imod') and len(args) == 2:
            if args[0].canon() == args[1].canon():
                return OLit(0)

        # R10e: pow(x, 0) → 1 (zeroth power)
        if name in ('pow', 'ipow') and len(args) == 2:
            if isinstance(args[1], OLit) and args[1].value == 0:
                return OLit(1)

        # R10f: len(range(n)) → n (for single-arg range)
        if name == 'len' and len(args) == 1:
            inner = args[0]
            if isinstance(inner, OOp) and inner.name == 'range':
                if len(inner.args) == 1:
                    return inner.args[0]
                elif len(inner.args) == 2:
                    # len(range(a, b)) → max(0, sub(b, a))
                    return OOp('max', (OLit(0), OOp('sub', (inner.args[1], inner.args[0]))))
                elif len(inner.args) == 3:
                    # len(range(a, b, step)) — not simplified (step-dependent)
                    pass

        # R10g: gcd(x, 0) → abs(x), gcd(0, x) → abs(x) (GCD identity)
        # gcd(x, x) → abs(x) (self-GCD)
        if name == 'gcd' and len(args) == 2:
            if isinstance(args[1], OLit) and args[1].value == 0:
                return OOp('abs', (args[0],))
            if isinstance(args[0], OLit) and args[0].value == 0:
                return OOp('abs', (args[1],))
            if args[0].canon() == args[1].canon():
                return OOp('abs', (args[0],))

        # R10h: abs(abs(x)) → abs(x) (idempotent)
        # abs(neg(x)) → abs(x), abs(u_usub(x)) → abs(x)
        if name == 'abs' and len(args) == 1:
            inner = args[0]
            if isinstance(inner, OOp):
                if inner.name == 'abs':
                    return inner
                if inner.name in ('neg', 'u_usub') and len(inner.args) == 1:
                    return OOp('abs', inner.args)

        # R10i: sorted(sorted(x)) → sorted(x) (idempotent)
        if name == 'sorted' and len(args) == 1:
            inner = args[0]
            if isinstance(inner, OOp) and inner.name == 'sorted':
                return inner

        # R12: -(-x) → x
        if name == 'u_usub' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'u_usub':
                return args[0].args[0]

        # R13: -(a - b) → b - a  (general ring law)
        if name == 'u_usub' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name in ('sub', 'isub') and len(args[0].args) == 2:
                return OOp(args[0].name, (args[0].args[1], args[0].args[0]))

        # R14: Canonical ordering of subtraction within products.
        # In a ring, sub(a,b) * sub(c,d) = sub(b,a) * sub(d,c) because
        # (-1)(-1) = 1 (double negation cancellation in product).
        # We canonicalize each sub(X,Y) factor so X.canon() < Y.canon().
        # If we flip an odd number of factors, the product changes sign,
        # so we only apply when we flip an even number (parity = 0).
        if name in ('mult', 'imult') and len(args) == 2:
            flips = 0
            new_args = list(args)
            for i, a in enumerate(args):
                if isinstance(a, OOp) and a.name in ('sub', 'isub') and len(a.args) == 2:
                    c0, c1 = a.args[0].canon(), a.args[1].canon()
                    if c0 > c1:
                        new_args[i] = OOp(a.name, (a.args[1], a.args[0]))
                        flips += 1
            if flips > 0 and flips % 2 == 0:
                args = tuple(new_args)

        # R15: abs(sub(X, Y)) canonical ordering.
        # Since |a - b| = |b - a|, we can freely order sub operands.
        # R15b: Inside abs(sub(mult(...), mult(...))), canonicalize ALL
        # sub-factors within each mult regardless of parity, because
        # abs absorbs the global sign: |(-1)^n * X| = |X|.
        if name == 'abs' and len(args) == 1:
            inner = args[0]
            if isinstance(inner, OOp) and inner.name in ('sub', 'isub') and len(inner.args) == 2:
                def _canon_mult_subs_abs(term):
                    """Canonicalize sub-args within a mult (abs absorbs sign)."""
                    if isinstance(term, OOp) and term.name in ('mult', 'imult') and len(term.args) == 2:
                        new_a = list(term.args)
                        for i, a in enumerate(term.args):
                            if isinstance(a, OOp) and a.name in ('sub', 'isub') and len(a.args) == 2:
                                ca0, ca1 = a.args[0].canon(), a.args[1].canon()
                                if ca0 > ca1:
                                    new_a[i] = OOp(a.name, (a.args[1], a.args[0]))
                        return OOp(term.name, tuple(new_a))
                    return term
                canoned_x = _canon_mult_subs_abs(inner.args[0])
                canoned_y = _canon_mult_subs_abs(inner.args[1])
                cx, cy = canoned_x.canon(), canoned_y.canon()
                if cx > cy:
                    canoned_x, canoned_y = canoned_y, canoned_x
                args = (OOp(inner.name, (canoned_x, canoned_y)),)

        # ── Commutative normalization ──
        # For commutative binary ops, sort arguments by canonical form.
        # This ensures mult(a,b) ≡ mult(b,a), add(a,b) ≡ add(b,a), etc.
        _COMMUTATIVE = frozenset({
            'add', 'iadd', 'mult', 'imult',
            'and', 'or', 'eq', 'noteq',
            'bitand', 'bitor', 'bitxor',
            'iand', 'ior', 'ixor',
            'max', 'min', 'gcd', 'lcm',
        })
        if name in _COMMUTATIVE and len(args) == 2:
            c0, c1 = args[0].canon(), args[1].canon()
            if c0 > c1:
                args = (args[1], args[0])

        # ── Associative flattening (R2, R7, L3, L4) ──
        # Canonicalize nested associative operations to right-associative form
        # with sorted leaves (combines with commutative normalization above).
        # add(add(a,b), c) → add(a, add(b,c)) with canonical leaf ordering.
        _ASSOC_OPS = frozenset({'add', 'mult', 'min', 'max', 'bitor', 'bitand', 'bitxor', 'gcd', 'lcm'})
        if name in _ASSOC_OPS and len(args) == 2:
            # Flatten into list of leaves
            def _collect_assoc(term, op):
                if isinstance(term, OOp) and term.name == op and len(term.args) == 2:
                    return _collect_assoc(term.args[0], op) + _collect_assoc(term.args[1], op)
                return [term]
            leaves = _collect_assoc(OOp(name, args), name)
            if len(leaves) > 2:
                # Sort leaves by canonical form (commutative + associative = any order)
                if name in _COMMUTATIVE:
                    leaves.sort(key=lambda x: x.canon())

                # XOR self-cancellation: remove pairs of identical leaves
                # a ^ a = 0, so paired leaves cancel out
                if name in ('bitxor', 'ixor'):
                    canons = [l.canon() for l in leaves]
                    keep = []
                    i = 0
                    while i < len(canons):
                        if i + 1 < len(canons) and canons[i] == canons[i + 1]:
                            i += 2  # cancel pair
                        else:
                            keep.append(leaves[i])
                            i += 1
                    if len(keep) == 0:
                        return OLit(0)
                    if len(keep) < len(leaves):
                        leaves = keep

                # Idempotent self-collapse: x & x = x, x | x = x
                if name in ('bitand', 'iand', 'bitor', 'ior', 'min', 'max'):
                    seen = set()
                    unique = []
                    for l in leaves:
                        c = l.canon()
                        if c not in seen:
                            seen.add(c)
                            unique.append(l)
                    if len(unique) < len(leaves):
                        leaves = unique

                # Rebuild as right-associated chain
                if len(leaves) == 1:
                    return leaves[0]
                result = leaves[-1]
                for leaf in reversed(leaves[:-1]):
                    result = OOp(name, (leaf, result))
                args = result.args if isinstance(result, OOp) else (result,)
                if isinstance(result, OOp):
                    name = result.name
                    args = result.args
                else:
                    return result

        # S4: sorted(sorted(x)) → sorted(x)
        if name == 'sorted' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'sorted':
                return args[0]

        # S7: reversed(reversed(x)) → x
        if name == 'reversed' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'reversed':
                return args[0].args[0]

        # S9: sorted(reversed(x)) → sorted(x)
        if name == 'sorted' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'reversed':
                return OOp('sorted', args[0].args)

        # sorted(list(x)) → sorted(x)
        if name == 'sorted' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name in ('list', 'tuple'):
                return OOp('sorted', args[0].args)

        # concat(a, b) → add(a, b)
        # List concatenation is the same operation as + for sequences.
        if name == 'concat':
            return OOp('add', args)

        # list(sorted(x)) → sorted(x) (sorted already returns list)
        if name == 'list' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name in ('sorted', 'sorted_key',
                                                                'sorted_rev', 'sorted_key_rev'):
                return args[0]
            # list(reversed(x)) → reversed(x)
            if isinstance(args[0], OOp) and args[0].name == 'reversed':
                return args[0]
            # list(x) where x is already a list-like operation → x
            if isinstance(args[0], OOp) and args[0].name in ('list', 'concat'):
                return args[0]

        # NOTE: tuple(x) and list(x) are NOT equivalent in general
        # (tuple != list in Python). Only unify when used as intermediate
        # values, not as final return types. Leave distinct here.

        # ── Comparison normalization (total order on comparisons) ──
        # Canonicalize gt(a,b) → lt(b,a), gte(a,b) → lte(b,a)
        # This ensures e.g. case(gt(x,0), ...) and case(lt(0,x), ...) match.
        if name == 'gt' and len(args) == 2:
            return OOp('lt', (args[1], args[0]))
        if name == 'gte' and len(args) == 2:
            return OOp('lte', (args[1], args[0]))

        # not(lt(a,b)) → lte(b,a), not(lte(a,b)) → lt(b,a), etc.
        if name == 'u_not' and len(args) == 1 and isinstance(args[0], OOp):
            inner = args[0]
            _NEG_COMP = {'lt': ('lte', True), 'lte': ('lt', True),
                         'eq': ('noteq', False), 'noteq': ('eq', False)}
            if inner.name in _NEG_COMP and len(inner.args) == 2:
                new_op, swap = _NEG_COMP[inner.name]
                if swap:
                    return OOp(new_op, (inner.args[1], inner.args[0]))
                return OOp(new_op, inner.args)

        # H1: hashlib.X().update(data) → hashlib.X(data)
        # Python API identity: hashlib.md5(data) creates a hash initialized
        # with data, equivalent to hashlib.md5() followed by .update(data).
        # Normalize to the shorter form (constructor with data).
        if name == '.update!' and len(args) == 2:
            ctor = args[0]
            if isinstance(ctor, OOp) and ctor.name.startswith('hashlib.') and len(ctor.args) == 0:
                return OOp(ctor.name, (args[1],))

        # S1: not(not(x)) → x
        if name == 'u_not' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'u_not':
                return args[0].args[0]

        # B3: not(a < b) → a >= b
        if name == 'u_not' and len(args) == 1:
            neg_map = {'lt': 'gte', 'lte': 'gt', 'gt': 'lte', 'gte': 'lt',
                       'eq': 'noteq', 'noteq': 'eq'}
            if isinstance(args[0], OOp) and args[0].name in neg_map:
                return OOp(neg_map[args[0].name], args[0].args)

        # De Morgan on folds: not(any/or(X)) → all/and(map(not, X))
        # not(fold[any|or](False, X)) → fold[and](True, map(not, X))
        # not(fold[all|and](True, X)) → fold[or](False, map(not, X))
        if name == 'u_not' and len(args) == 1 and isinstance(args[0], OFold):
            inner_fold = args[0]
            if inner_fold.op_name in ('any', 'or') and isinstance(inner_fold.init, OLit) and inner_fold.init.value is False:
                negated_coll = _negate_map_pred(inner_fold.collection)
                if negated_coll is not None:
                    return OFold('and', OLit(True), negated_coll)
            if inner_fold.op_name in ('all', 'and') and isinstance(inner_fold.init, OLit) and inner_fold.init.value is True:
                negated_coll = _negate_map_pred(inner_fold.collection)
                if negated_coll is not None:
                    return OFold('or', OLit(False), negated_coll)

        # L1: x and True → x, L2: x and False → False
        if name == 'and' and len(args) == 2:
            if isinstance(args[1], OLit) and args[1].value is True:
                return args[0]
            if isinstance(args[1], OLit) and args[1].value is False:
                return OLit(False)
            if isinstance(args[0], OLit) and args[0].value is True:
                return args[1]
            if isinstance(args[0], OLit) and args[0].value is False:
                return OLit(False)

        # L3: x or True → True, L4: x or False → x
        if name == 'or' and len(args) == 2:
            if isinstance(args[1], OLit) and args[1].value is True:
                return OLit(True)
            if isinstance(args[1], OLit) and args[1].value is False:
                return args[0]
            if isinstance(args[0], OLit) and args[0].value is True:
                return OLit(True)
            if isinstance(args[0], OLit) and args[0].value is False:
                return args[1]

        # R15: eq(x, x) → True (reflexivity of equality)
        if name == 'eq' and len(args) == 2:
            if args[0].canon() == args[1].canon():
                return OLit(True)
        # R16: noteq(x, x) → False
        if name == 'noteq' and len(args) == 2:
            if args[0].canon() == args[1].canon():
                return OLit(False)
        # NOTE: is(x, x) is NOT always True in Python (e.g., NaN is NaN → True,
        # but [] is [] → False for distinct objects). Don't reduce it in general.
        # BUT: is(None, None) → True, is(True, True) → True, is(False, False) → True
        # These are Python singletons — identity is always reflexive for them.
        if name == 'is' and len(args) == 2:
            if isinstance(args[0], OLit) and isinstance(args[1], OLit):
                if args[0].value is args[1].value and args[0].value in (None, True, False):
                    return OLit(True)

        # I1: sorted(sorted(x)) already handled above
        # I2: set(set(x)) → set(x)
        if name == 'set' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'set':
                return args[0]

        # dict(list(dict.items())) → dict
        # list(dict.keys()) → dict.keys() (already quotient)

        # ── Multiset canonical form (Monograph Thm: sorted = Counter on the multiset quotient) ──
        # Counter(x) and sorted(x) are both canonical representatives of
        # the multiset quotient Seq/~_perm. We normalize Counter to sorted
        # since sorted is the canonical representative in CCTT (S4, S5).
        # This makes eq(Counter(a), Counter(b)) ≡ eq(sorted(a), sorted(b)).
        if name in ('counter', 'Counter') and len(args) == 1:
            return OOp('sorted', args)

        # len(range(n)) → n
        if name == 'len' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'range':
                if len(args[0].args) == 1:
                    return args[0].args[0]

        # bool(x) is NOT equivalent to x — it coerces to True/False
        # Don't normalize it away

        # ── Factorial quotient → comb(n, k) ──
        # floordiv(factorial(n), mult(factorial(k), factorial(sub(n, k)))) → comb(n, k)
        # This is the defining identity for binomial coefficients.
        if name == 'floordiv' and len(args) == 2:
            numer, denom = args
            if (isinstance(numer, OOp) and numer.name == 'factorial'
                    and len(numer.args) == 1):
                n_term = numer.args[0]
                # denom = mult(factorial(k), factorial(n-k))
                if (isinstance(denom, OOp) and denom.name == 'mult'
                        and len(denom.args) == 2):
                    d_a, d_b = denom.args
                    if (isinstance(d_a, OOp) and d_a.name == 'factorial'
                            and isinstance(d_b, OOp) and d_b.name == 'factorial'):
                        k1 = d_a.args[0]
                        k2 = d_b.args[0]
                        # Check k1 + k2 = n (i.e., k2 = sub(n, k1) or k1 = sub(n, k2))
                        if (isinstance(k2, OOp) and k2.name == 'sub'
                                and k2.args[0].canon() == n_term.canon()):
                            return OOp('comb', (n_term, k1))
                        if (isinstance(k1, OOp) and k1.name == 'sub'
                                and k1.args[0].canon() == n_term.canon()):
                            return OOp('comb', (n_term, k2))

        # ── comb symmetry: comb(n, sub(n, k)) → comb(n, k) ──
        # C(n,k) = C(n,n-k), canonicalize to the non-sub form
        if name == 'comb' and len(args) == 2:
            n_arg, k_arg = args
            # comb(n, 0) → 1, comb(n, n) → 1  (base cases)
            if isinstance(k_arg, OLit) and k_arg.value == 0:
                return OLit(1)
            if k_arg.canon() == n_arg.canon():
                return OLit(1)
            if (isinstance(k_arg, OOp) and k_arg.name == 'sub'
                    and len(k_arg.args) == 2
                    and k_arg.args[0].canon() == n_arg.canon()):
                return OOp('comb', (n_arg, k_arg.args[1]))
            # comb(n, case(lt(sub(n,k), k), sub(n,k), k)) → comb(n, k)
            # This is comb(n, min(n-k, k)) = comb(n, k) by symmetry
            if isinstance(k_arg, OCase):
                tb = k_arg.true_branch
                fb = k_arg.false_branch
                # Either branch may be sub(n, other)
                if (isinstance(tb, OOp) and tb.name == 'sub'
                        and tb.args[0].canon() == n_arg.canon()):
                    return OOp('comb', (n_arg, tb.args[1]))
                if (isinstance(fb, OOp) and fb.name == 'sub'
                        and fb.args[0].canon() == n_arg.canon()):
                    return OOp('comb', (n_arg, fb.args[1]))
            # comb(n, min(k, n-k)) → comb(n, k) by symmetry C(n,k)=C(n,n-k)
            if isinstance(k_arg, OOp) and k_arg.name == 'min' and len(k_arg.args) == 2:
                ma, mb = k_arg.args
                # min(k, sub(n, k)) or min(sub(n, k), k)
                for a, b in [(ma, mb), (mb, ma)]:
                    if (isinstance(b, OOp) and b.name == 'sub'
                            and len(b.args) == 2
                            and b.args[0].canon() == n_arg.canon()):
                        return OOp('comb', (n_arg, a))
                    if (isinstance(a, OOp) and a.name == 'sub'
                            and len(a.args) == 2
                            and a.args[0].canon() == n_arg.canon()):
                        return OOp('comb', (n_arg, b))

        return OOp(name, args)

    if isinstance(term, OCase):
        test = _phase2_ring(term.test)
        t = _phase2_ring(term.true_branch)
        f = _phase2_ring(term.false_branch)
        # case(True, t, f) → t, case(False, t, f) → f
        if isinstance(test, OLit) and test.value is True:
            return t
        if isinstance(test, OLit) and test.value is False:
            return f
        # case(c, x, x) → x (already in phase1 but reinforce)
        if t.canon() == f.canon():
            return t

        # ── General boolean case reductions ──
        # case(c, True, False) → c  (the case IS the boolean)
        if (isinstance(t, OLit) and t.value is True and
                isinstance(f, OLit) and f.value is False):
            return test
        # case(c, False, True) → not(c)
        if (isinstance(t, OLit) and t.value is False and
                isinstance(f, OLit) and f.value is True):
            return OOp('u_not', (test,))

        # ── Negated guard normalization ──
        # case(not(c), a, b) → case(c, b, a)
        # This ensures a canonical guard direction regardless of how
        # the programmer wrote the condition.
        if isinstance(test, OOp) and test.name == 'u_not' and len(test.args) == 1:
            return OCase(test.args[0], f, t)

        # ── Comparison direction normalization ──
        # case(noteq(a,b), x, y) → case(eq(a,b), y, x)
        # Normalize to positive comparisons in guards
        _flip = {'noteq': 'eq', 'gte': 'lt', 'gt': 'lte'}
        if isinstance(test, OOp) and test.name in _flip:
            return OCase(OOp(_flip[test.name], test.args), f, t)

        # ── Boolean case → and/or normalization ──
        # case(c, X, False) → and(X, c)   [short-circuit equivalent]
        # case(c, True, X)  → or(c, X)    [short-circuit equivalent]
        # These are algebraic identities for boolean-valued terms.
        if isinstance(f, OLit) and f.value is False:
            return OOp('and', (t, test))
        if isinstance(t, OLit) and t.value is True:
            return OOp('or', (test, f))

        return OCase(test, t, f)

    if isinstance(term, OFold):
        # Normalize in-place fold ops to pure equivalents
        _FOLD_OP_NORMALIZE = {
            'iadd': 'add', 'isub': 'sub', 'imult': 'mult',
            'ifloordiv': 'floordiv', 'imod': 'mod',
            'ibitor': 'bitor', 'ibitand': 'bitand', 'ibitxor': 'bitxor',
            'ilshift': 'lshift', 'irshift': 'rshift',
        }
        op = _FOLD_OP_NORMALIZE.get(term.op_name, term.op_name)
        bfn = _phase2_ring(term.body_fn) if term.body_fn else None
        return OFold(op, _phase2_ring(term.init),
                     _phase2_ring(term.collection), body_fn=bfn)
    if isinstance(term, OFix):
        return OFix(term.name, _phase2_ring(term.body))
    if isinstance(term, OSeq):
        return OSeq(tuple(_phase2_ring(e) for e in term.elements))
    if isinstance(term, OQuotient):
        return OQuotient(_phase2_ring(term.inner), term.equiv_class)
    if isinstance(term, OLam):
        return OLam(term.params, _phase2_ring(term.body))
    if isinstance(term, OMap):
        t = _phase2_ring(term.transform)
        c = _phase2_ring(term.collection)
        f = _phase2_ring(term.filter_pred) if term.filter_pred else None
        return OMap(t, c, f)
    if isinstance(term, OCatch):
        body = _phase2_ring(term.body)
        default = _phase2_ring(term.default)
        # D22: catch(floordiv(x,y), 0) ≡ case(eq(y,0), 0, floordiv(x,y))
        # Normalize OCatch to OCase when the exception condition is inferrable
        if isinstance(body, OOp) and body.name == 'floordiv' and len(body.args) == 2:
            divisor = body.args[1]
            return OCase(OOp('eq', (divisor, OLit(0))), default, body)
        if isinstance(body, OOp) and body.name == 'mod' and len(body.args) == 2:
            divisor = body.args[1]
            return OCase(OOp('eq', (divisor, OLit(0))), default, body)
        return OCatch(body, default)

    return term


def _extract_reduce_op(op_term: OTerm) -> str:
    """Extract the operation name from a reduce's operator argument.

    Handles:
      - OLam(('a','b'), OOp('add', (OVar('a'), OVar('b')))) → 'add'
      - OOp('.xor', (OUnknown('operator'),)) → 'bitxor'   (operator.xor)
      - OOp('.add', (OUnknown('operator'),)) → 'add'      (operator.add)
      - OOp('getattr', (module, 'xor')) → 'bitxor'
    """
    if isinstance(op_term, OLam) and len(op_term.params) == 2:
        body = op_term.body
        if isinstance(body, OOp) and len(body.args) == 2:
            a, b = body.args
            pa, pb = op_term.params
            # λ(a,b).op(a,b) → op
            if (isinstance(a, OVar) and a.name == pa and
                    isinstance(b, OVar) and b.name == pb):
                return body.name
            # λ(a,b).op(b,a) → op (for commutative ops)
            if (isinstance(a, OVar) and a.name == pb and
                    isinstance(b, OVar) and b.name == pa):
                return body.name

    if isinstance(op_term, OOp):
        # operator.xor → .xor(operator) in OTerm
        _OPERATOR_MAP = {
            '.xor': 'bitxor', '.add': 'add', '.sub': 'sub',
            '.mul': 'mul', '.and_': 'bitand', '.or_': 'bitor',
            '.iadd': 'add', '.isub': 'sub', '.imul': 'mul',
            '.floordiv': 'floordiv', '.truediv': 'truediv',
            '.mod': 'mod', '.pow': 'pow',
            '.concat': 'add', '.iconcat': 'add',
            '.ixor': 'bitxor', '.iand': 'bitand', '.ior': 'bitor',
        }
        if op_term.name in _OPERATOR_MAP:
            return _OPERATOR_MAP[op_term.name]

    # Complex lambda: hash the body to match how for-loop bodies are hashed.
    # Both sides use canonical variable names: $0 = accumulator, $1 = element.
    if isinstance(op_term, OLam) and len(op_term.params) == 2:
        body = op_term.body
        pa, pb = op_term.params
        # Rename params to match for-loop convention: acc=$0, elem=$1
        normalized_body = _subst_term(_subst_term(body, pa, OVar('$0')), pb, OVar('$1'))
        # Use assign: prefix to match _normalize_ast_dump output format.
        # Canonicalize free variable names so hash matches regardless of
        # whether parameters were already renamed (p0, p1) or still have
        # original names (mod, n).
        canon = f'assign:{normalized_body.canon()}'
        return _hash(_canonicalize_free_vars(canon))

    return 'reduce'


def _recognize_fold_body(body_fn: OTerm) -> Optional[str]:
    """Recognize a fold body_fn as a named binary operation.

    λ(a,b)min(a,b) → 'min', λ(a,b)max(a,b) → 'max', etc.
    This is the inverse of fold canonicalization — we already normalize
    sum() → fold[add], so normalizing fold[λ(a,b)add(a,b)] → fold[add]
    is the same mathematical identity.
    """
    if not isinstance(body_fn, OLam):
        return None
    if len(body_fn.params) != 2:
        return None
    p0, p1 = body_fn.params
    body = body_fn.body
    if not isinstance(body, OOp):
        return None
    if len(body.args) != 2:
        return None
    a0, a1 = body.args
    if not (isinstance(a0, OVar) and isinstance(a1, OVar)):
        return None
    # Check both orderings: op(a,b) or op(b,a)
    if (a0.name == p0 and a1.name == p1) or (a0.name == p1 and a1.name == p0):
        return body.name
    return None


def _try_linear_rec_to_fold(case_term: OCase) -> Optional[OTerm]:
    """Convert linear recursion to fold (catamorphism principle).

    Pattern: case(guard(x, K), op(x, fix[h]([sub(x, step)])), base)
      → fold[op](base, range(K+step, x+step, step))

    Only for commutative+associative ops to ensure
    right-fold = left-fold = fold over range.
    """
    test = case_term.test
    true_br = case_term.true_branch
    false_br = case_term.false_branch

    # Determine which branch is recursive and which is the base
    rec_branch = base_branch = None
    rec_is_true = False
    if _has_fix_node(true_br) and not _has_fix_node(false_br):
        rec_branch, base_branch = true_br, false_br
        rec_is_true = True
    elif _has_fix_node(false_br) and not _has_fix_node(true_br):
        rec_branch, base_branch = false_br, true_br
        rec_is_true = False
    else:
        return None

    # Extract binary op and fix call from the recursive branch
    if not isinstance(rec_branch, OOp) or len(rec_branch.args) != 2:
        return None

    op_name = rec_branch.name
    arg0, arg1 = rec_branch.args

    fix_node = param_node = None
    if isinstance(arg1, OFix):
        fix_node, param_node = arg1, arg0
    elif isinstance(arg0, OFix):
        fix_node, param_node = arg0, arg1
    else:
        return None

    if not isinstance(param_node, OVar):
        return None

    # Check fix call argument: sub(param, step)
    if not isinstance(fix_node.body, OSeq) or len(fix_node.body.elements) != 1:
        return None
    call_arg = fix_node.body.elements[0]
    if not isinstance(call_arg, OOp) or call_arg.name != 'sub' or len(call_arg.args) != 2:
        return None
    if call_arg.args[0].canon() != param_node.canon():
        return None
    if not isinstance(call_arg.args[1], OLit) or not isinstance(call_arg.args[1].value, int):
        return None
    step = call_arg.args[1].value
    if step <= 0:
        return None

    # Only commutative+associative ops
    _COMM_ASSOC = {'add', 'iadd', 'mult', 'imult', 'mul', 'imul',
                   'and', 'or', 'bitand', 'bitor', 'bitxor',
                   'min', 'max', 'gcd'}
    if op_name not in _COMM_ASSOC:
        return None

    # Canonicalize op name for the fold
    _CANON = {'iadd': 'add', 'imult': 'mul', 'imul': 'mul', 'mult': 'mul'}
    fold_op = _CANON.get(op_name, op_name)

    # Extract guard bound from test
    guard_bound = _extract_rec_guard_bound(test, param_node, rec_is_true)
    if guard_bound is None:
        return None

    # Build the fold: fold[op](base, range(guard_bound + step, param + step, step))
    param = param_node
    if step == 1:
        range_start = OOp('add', (guard_bound, OLit(1)))
        range_end = OOp('add', (param, OLit(1)))
        coll = OOp('range', (range_start, range_end))
    else:
        range_start = OOp('add', (guard_bound, OLit(step)))
        range_end = OOp('add', (param, OLit(step)))
        coll = OOp('range', (range_start, range_end, OLit(step)))

    return OFold(fold_op, base_branch, coll)


def _extract_rec_guard_bound(test: OTerm, param: OVar, rec_is_true: bool) -> Optional[OTerm]:
    """Extract guard bound K from comparison test for recursion detection."""
    if not isinstance(test, OOp) or len(test.args) != 2:
        return None
    a0, a1 = test.args
    if rec_is_true:
        if test.name == 'lt' and a1.canon() == param.canon():
            return a0
        if test.name == 'gt' and a0.canon() == param.canon():
            return a1
        if test.name == 'lte' and a1.canon() == param.canon():
            return OOp('sub', (a0, OLit(1)))
        if test.name == 'gte' and a0.canon() == param.canon():
            return OOp('sub', (a1, OLit(1)))
    else:
        if test.name == 'lt' and a0.canon() == param.canon():
            return OOp('sub', (a1, OLit(1)))
        if test.name == 'gt' and a1.canon() == param.canon():
            return OOp('sub', (a0, OLit(1)))
        if test.name == 'lte' and a0.canon() == param.canon():
            return a1
        if test.name == 'gte' and a1.canon() == param.canon():
            return a0
    return None


def _has_fix_node(term: OTerm) -> bool:
    """Check if a term contains any OFix node."""
    if isinstance(term, OFix):
        return True
    for attr in ['test', 'true_branch', 'false_branch', 'init',
                 'collection', 'body', 'inner', 'default']:
        child = getattr(term, attr, None)
        if child is not None and _has_fix_node(child):
            return True
    if hasattr(term, 'args'):
        for a in term.args:
            if _has_fix_node(a):
                return True
    if hasattr(term, 'elements'):
        for e in term.elements:
            if _has_fix_node(e):
                return True
    return False


def _try_fold_to_builtin(op: str, init: OTerm, coll: OTerm) -> Optional[OTerm]:
    """Simplify fold to builtin when possible.

    Mathematical identities:
    - fold[min](a[0], a[1:]) → min(a)   (definition of min)
    - fold[max](a[0], a[1:]) → max(a)   (definition of max)
    - fold[mul](1, range(2, n+1)) → math.factorial(n)   (n! = ∏_{i=2}^{n} i)
    - fold[mul](1, map(λ_.c, range(n))) → pow(c, n)   (c^n = ∏_{i=1}^{n} c)
    """
    # fold[min](a[0], a[1:]) → min(a)
    if op == 'min' and isinstance(init, OOp) and init.name == 'getitem':
        if len(init.args) == 2 and isinstance(init.args[1], OLit) and init.args[1].value == 0:
            base = init.args[0]
            if isinstance(coll, OOp) and coll.name == 'suffix':
                if len(coll.args) == 2 and isinstance(coll.args[1], OLit) and coll.args[1].value == 1:
                    if coll.args[0].canon() == base.canon():
                        return OOp('min', (base,))
    # fold[max](a[0], a[1:]) → max(a)
    if op == 'max' and isinstance(init, OOp) and init.name == 'getitem':
        if len(init.args) == 2 and isinstance(init.args[1], OLit) and init.args[1].value == 0:
            base = init.args[0]
            if isinstance(coll, OOp) and coll.name == 'suffix':
                if len(coll.args) == 2 and isinstance(coll.args[1], OLit) and coll.args[1].value == 1:
                    if coll.args[0].canon() == base.canon():
                        return OOp('max', (base,))
    # fold[mul](1, range(S, n+1)) → factorial(n)  when S ∈ {1, 2}
    # (1*2*...*n = n! regardless of whether we start at 1 or 2)
    if op == 'mul' and isinstance(init, OLit) and init.value == 1:
        if isinstance(coll, OOp) and coll.name == 'range' and len(coll.args) == 2:
            start, end = coll.args
            if isinstance(start, OLit) and start.value in (1, 2):
                # Check end = add(n, 1)
                if isinstance(end, OOp) and end.name == 'add' and len(end.args) == 2:
                    if isinstance(end.args[1], OLit) and end.args[1].value == 1:
                        return OOp('factorial', (end.args[0],))
        # fold[mul](1, range(1, n)) or range(2, n) → factorial(sub(n, 1))
        if isinstance(coll, OOp) and coll.name == 'range' and len(coll.args) == 2:
            start, end = coll.args
            if isinstance(start, OLit) and start.value in (1, 2):
                # end is a plain variable or expression (not add(n,1))
                if not (isinstance(end, OOp) and end.name == 'add'):
                    return OOp('factorial', (OOp('sub', (end, OLit(1))),))
        # fold[mul](1, map(λ_.c, range(n))) → pow(c, n)
        if isinstance(coll, OMap):
            tr = coll.transform
            inner_coll = coll.collection
            if isinstance(tr, OLam) and len(tr.params) == 1:
                # Body must not reference the parameter
                param = tr.params[0]
                if not _references_var(tr.body, param):
                    if isinstance(inner_coll, OOp) and inner_coll.name == 'range' and len(inner_coll.args) == 1:
                        return OOp('pow', (tr.body, inner_coll.args[0]))
    return None


def _try_fold_to_comb(bfn: OTerm, init: OTerm, coll: OTerm) -> 'Optional[OTerm]':
    """Recognize fold computing binomial coefficient comb(n, k).

    The iterative binomial: fold[λ(acc,i)→acc*(n-i)/(i+1)](1, range(k)) = comb(n,k).
    This is a standard mathematical identity for computing C(n,k) without overflow.
    """
    if not isinstance(init, OLit) or init.value != 1:
        return None
    if not isinstance(bfn, OLam) or len(bfn.params) != 2:
        return None
    acc_p, idx_p = bfn.params
    body = bfn.body

    # Pattern: floordiv(mult(acc, sub(N, i)), add(i, 1))
    if not (isinstance(body, OOp) and body.name == 'floordiv' and len(body.args) == 2):
        return None
    numer, denom = body.args
    if not (isinstance(numer, OOp) and numer.name == 'mult' and len(numer.args) == 2):
        return None
    if not (isinstance(denom, OOp) and denom.name == 'add' and len(denom.args) == 2):
        return None
    # numer = mult(acc, sub(N, i))
    a, b = numer.args
    if isinstance(a, OVar) and a.name == acc_p:
        n_minus_i = b
    elif isinstance(b, OVar) and b.name == acc_p:
        n_minus_i = a
    else:
        return None
    # n_minus_i = sub(N, i)
    if not (isinstance(n_minus_i, OOp) and n_minus_i.name == 'sub' and len(n_minus_i.args) == 2):
        return None
    n_term = n_minus_i.args[0]
    if not (isinstance(n_minus_i.args[1], OVar) and n_minus_i.args[1].name == idx_p):
        return None
    # denom = add(i, 1)
    d_parts = denom.args
    if isinstance(d_parts[0], OVar) and d_parts[0].name == idx_p:
        if not (isinstance(d_parts[1], OLit) and d_parts[1].value == 1):
            return None
    elif isinstance(d_parts[1], OVar) and d_parts[1].name == idx_p:
        if not (isinstance(d_parts[0], OLit) and d_parts[0].value == 1):
            return None
    else:
        return None

    # coll must be range(k) for some k
    if not (isinstance(coll, OOp) and coll.name == 'range' and len(coll.args) >= 1):
        return None
    k_term = coll.args[0]
    return OOp('comb', (n_term, k_term))


def _references_var(term: OTerm, var_name: str) -> bool:
    """Check if term references a given variable name."""
    if isinstance(term, OVar):
        return term.name == var_name
    if isinstance(term, OLit):
        return False
    if isinstance(term, OOp):
        return any(_references_var(a, var_name) for a in term.args)
    if isinstance(term, OCase):
        return (_references_var(term.test, var_name) or
                _references_var(term.true_branch, var_name) or
                _references_var(term.false_branch, var_name))
    if isinstance(term, OLam):
        if var_name in term.params:
            return False  # shadowed
        return _references_var(term.body, var_name)
    if isinstance(term, OFold):
        return (_references_var(term.init, var_name) or
                _references_var(term.collection, var_name))
    if isinstance(term, OMap):
        return (_references_var(term.transform, var_name) or
                _references_var(term.collection, var_name))
    return False


def _try_dp_to_tuple_fold(fold: 'OFold', extract_idx: 'OTerm') -> 'Optional[OTerm]':
    """Convert DP-array-fill fold to equivalent tuple-fold.

    Detects the pattern:
        getitem(fold[λ(arr,i) → setitem(arr, i, f(arr[i-1], arr[i-2]))]
                (init_arr, range(2, end)), idx)
    where idx = end - 1, and converts to:
        getitem(fold[λ(a,b,_) → (b, f(a,b))]((v0, v1), range(idx)), 0)

    This is the DP window compression theorem: a 2-lookback linear recurrence
    stored in an array is equivalent to a 2-tuple sliding window fold.

    Only handles the exact 2-seed, 2-lookback case (window size = 2).
    """
    bfn = fold.body_fn
    if not isinstance(bfn, OLam) or len(bfn.params) != 2:
        return None
    acc_p, iter_p = bfn.params

    # Body must be setitem(acc, i, expr)
    body = bfn.body
    if not isinstance(body, OOp) or body.name != 'setitem' or len(body.args) != 3:
        return None
    si_target, si_idx, si_value = body.args
    if not isinstance(si_target, OVar) or si_target.name != acc_p:
        return None
    if not isinstance(si_idx, OVar) or si_idx.name != iter_p:
        return None

    # Analyze si_value for getitem(acc, sub(i, k)) references
    lookbacks = {}

    def _extract_lookbacks(t: 'OTerm') -> 'Optional[OTerm]':
        """Replace getitem(acc, sub(i, k)) with placeholder variables."""
        if isinstance(t, OOp) and t.name == 'getitem' and len(t.args) == 2:
            arr_ref, offset_expr = t.args
            if isinstance(arr_ref, OVar) and arr_ref.name == acc_p:
                if (isinstance(offset_expr, OOp) and offset_expr.name == 'sub'
                        and len(offset_expr.args) == 2
                        and isinstance(offset_expr.args[0], OVar)
                        and offset_expr.args[0].name == iter_p
                        and isinstance(offset_expr.args[1], OLit)
                        and isinstance(offset_expr.args[1].value, int)):
                    k = offset_expr.args[1].value
                    if k < 1:
                        return None
                    lookbacks[k] = True
                    if k == 1:
                        return OVar('_dp_b')  # dp[i-1] → newer element
                    elif k == 2:
                        return OVar('_dp_a')  # dp[i-2] → older element
                    else:
                        return None  # Window > 2 not supported
                else:
                    return None
        if isinstance(t, OOp):
            new_args = []
            for a in t.args:
                r = _extract_lookbacks(a)
                if r is None:
                    return None
                new_args.append(r)
            return OOp(t.name, tuple(new_args))
        if isinstance(t, OVar):
            if t.name == acc_p:
                return None  # Bare accumulator reference
            return t
        if isinstance(t, OLit):
            return t
        if isinstance(t, OCase):
            test = _extract_lookbacks(t.test)
            if test is None:
                return None
            tb = _extract_lookbacks(t.true_branch)
            if tb is None:
                return None
            fb = _extract_lookbacks(t.false_branch)
            if fb is None:
                return None
            return OCase(test, tb, fb)
        return None

    recurrence_expr = _extract_lookbacks(si_value)
    if recurrence_expr is None:
        return None
    if set(lookbacks.keys()) != {1, 2}:
        return None

    # Collection must be range(2, end)
    coll = fold.collection
    if not isinstance(coll, OOp) or coll.name != 'range' or len(coll.args) != 2:
        return None
    start_expr, end_expr = coll.args
    if not isinstance(start_expr, OLit) or start_expr.value != 2:
        return None

    # Verify extract_idx = end - 1
    idx_matches = False
    if isinstance(end_expr, OOp) and end_expr.name == 'add' and len(end_expr.args) == 2:
        for a, b in [(end_expr.args[0], end_expr.args[1]),
                     (end_expr.args[1], end_expr.args[0])]:
            if isinstance(b, OLit) and b.value == 1:
                if a.canon() == extract_idx.canon():
                    idx_matches = True
                    break
    if not idx_matches:
        end_minus_1 = OOp('sub', (end_expr, OLit(1)))
        if end_minus_1.canon() == extract_idx.canon():
            idx_matches = True
    if not idx_matches:
        return None

    # Extract initial values from init array
    v0, v1 = _extract_dp_init_values(fold.init, 0, 1)
    if v0 is None or v1 is None:
        return None

    # Construct tuple fold body: λ(a, b, j) → (b, f(a, b))
    # _dp_a = dp[i-2] → tuple element 0 (older)
    # _dp_b = dp[i-1] → tuple element 1 (newer)
    # If recurrence uses the iteration variable i (from range(start, end)),
    # we must offset: i = j + start, where j comes from range(extract_idx).
    start_val = start_expr.value  # guaranteed literal 2
    rec_with_params = _subst_term(
        _subst_term(recurrence_expr, '_dp_a', OVar('_tb0')),
        '_dp_b', OVar('_tb1'))
    # Replace iteration variable with offset: iter_p → _tb2 + start
    uses_iter = iter_p in _collect_vars(rec_with_params)
    if uses_iter:
        offset_iter = OOp('add', (OVar('_tb2'), OLit(start_val)))
        rec_with_params = _subst_term(rec_with_params, iter_p, offset_iter)
    tuple_body = OSeq((OVar('_tb1'), rec_with_params))
    tuple_lam = OLam(('_tb0', '_tb1', '_tb2'), tuple_body)

    import hashlib
    fold_hash = hashlib.md5(tuple_lam.canon().encode()).hexdigest()[:8]

    tuple_init = OSeq((v0, v1))
    tuple_coll = OOp('range', (extract_idx,))
    return OOp('getitem', (OFold(fold_hash, tuple_init, tuple_coll,
                                 body_fn=tuple_lam), OLit(0)))


def _extract_dp_init_values(init: 'OTerm', idx0: int, idx1: int):
    """Extract values at positions idx0, idx1 from a DP init array.

    Handles: setitem(setitem(mult([0], n+1), 0, v0), 1, v1)
    Also handles: map(λ(i) case(or(eq(i,0),eq(i,1)),v0,default), range(N))
    """
    values = {}
    term = init
    while isinstance(term, OOp) and term.name == 'setitem' and len(term.args) == 3:
        base, pos, val = term.args
        if isinstance(pos, OLit) and isinstance(pos.value, int):
            values[pos.value] = val
        term = base

    is_zero_base = False
    if isinstance(term, OOp) and term.name == 'mult' and len(term.args) == 2:
        base_elem, _size = term.args
        if isinstance(base_elem, OSeq) and len(base_elem.elements) == 1:
            if isinstance(base_elem.elements[0], OLit) and base_elem.elements[0].value == 0:
                is_zero_base = True
    if isinstance(term, OSeq):
        for i, e in enumerate(term.elements):
            if i not in values:
                values[i] = e
        is_zero_base = True

    # Handle map-based init: map(λ(i) expr, range(N))
    # Evaluate expr at literal indices idx0, idx1
    if not is_zero_base and isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if len(lam.params) == 1:
            param = lam.params[0]
            for idx_val in (idx0, idx1):
                if idx_val not in values:
                    subst = _subst_term(lam.body, param, OLit(idx_val))
                    simp = _simplify_ground(subst)
                    if simp is None:
                        simp = _phase1_beta(_phase2_ring(subst))
                    values[idx_val] = simp
            is_zero_base = True

    if not is_zero_base:
        return None, None

    return values.get(idx0), values.get(idx1)


def _try_fold_to_map(fold_term: OFold, orig_init: OTerm) -> 'Optional[OTerm]':
    """Fold-to-map lifting: independent per-element updates.

    fold[λ(acc,i) → setitem(acc, i, f(i))](init, range(N))
    where f(i) only depends on i and init[i] (not other acc positions)
    → map(λ(i).f(i), range(N)) applied as element-wise update.

    Soundness: if position i is only written once and reads only from
    the initial value at position i, each iteration is independent.
    """
    if not isinstance(fold_term, OFold):
        return None
    bfn = fold_term.body_fn
    if bfn is None or not isinstance(bfn, OLam) or len(bfn.params) != 2:
        return None
    acc_p, elem_p = bfn.params
    body = bfn.body
    coll = fold_term.collection
    init = fold_term.init

    # Collection must be range(N) — each index visited exactly once
    if not (isinstance(coll, OOp) and coll.name == 'range' and len(coll.args) == 1):
        return None

    # Body must be setitem(acc, elem, value_expr)
    if not (isinstance(body, OOp) and body.name == 'setitem'
            and len(body.args) == 3):
        return None
    set_target, set_idx, set_val = body.args

    # setitem target must be the accumulator
    if not (isinstance(set_target, OVar) and set_target.name == acc_p):
        return None
    # setitem index must be the iteration variable
    if not (isinstance(set_idx, OVar) and set_idx.name == elem_p):
        return None

    # Check that set_val only uses acc via getitem(acc, elem)
    # Replace getitem(acc, elem) → getitem(init, elem) to decouple
    def _check_and_subst(t: OTerm) -> 'Optional[OTerm]':
        """Returns substituted term or None if acc is used unsafely."""
        if isinstance(t, OVar):
            if t.name == acc_p:
                return None  # Direct use of acc (not getitem) → unsafe
            return t
        if isinstance(t, (OLit, OUnknown)):
            return t
        if isinstance(t, OOp):
            # getitem(acc, elem) → getitem(init, elem)
            if (t.name == 'getitem' and len(t.args) == 2
                    and isinstance(t.args[0], OVar) and t.args[0].name == acc_p
                    and isinstance(t.args[1], OVar) and t.args[1].name == elem_p):
                return OOp('getitem', (init, t.args[1]))
            new_args = []
            for a in t.args:
                r = _check_and_subst(a)
                if r is None:
                    return None
                new_args.append(r)
            return OOp(t.name, tuple(new_args))
        if isinstance(t, OCase):
            c = _check_and_subst(t.guard)
            tr = _check_and_subst(t.true_br)
            fa = _check_and_subst(t.false_br)
            if c is None or tr is None or fa is None:
                return None
            return OCase(c, tr, fa)
        if isinstance(t, OSeq):
            elems = []
            for e in t.elements:
                r = _check_and_subst(e)
                if r is None:
                    return None
                elems.append(r)
            return OSeq(tuple(elems))
        if isinstance(t, OLam):
            if acc_p in t.params:
                return t  # acc is shadowed — safe
            b = _check_and_subst(t.body)
            return OLam(t.params, b) if b is not None else None
        # For other term types, conservatively reject
        return None

    subst_val = _check_and_subst(set_val)
    if subst_val is None:
        return None

    # Build: map(λ(elem) → subst_val, range(N))
    transform = OLam((elem_p,), subst_val)
    return OMap(transform, coll)


def _is_comparison_sort_fold(fold_term: OFold) -> bool:
    """Check if a fold is a comparison-based sorting algorithm.

    Sound version: requires NESTED folds (O(n²) operations) to ensure
    enough passes to fully sort. A single-pass fold does NOT produce
    sorted output. Also requires order comparisons (lt/gt/le/ge)
    between array elements — not equality or predicate checks.

    Returns True iff the fold provably sorts its input.
    """
    # 1. Must start from list(x) or a copy of the input
    init = fold_term.init
    if not (isinstance(init, OOp) and init.name == 'list'
            and len(init.args) == 1):
        return False

    # 2. Must iterate over range(len(x)) or similar complete range
    coll = fold_term.collection
    if not (isinstance(coll, OOp) and coll.name == 'range'):
        return False

    # 3. Must have body_fn
    if fold_term.body_fn is None:
        return False
    if not isinstance(fold_term.body_fn, OLam):
        return False
    if len(fold_term.body_fn.params) < 2:
        return False

    acc_param = fold_term.body_fn.params[0]
    body = fold_term.body_fn.body

    # 4. Body must contain a nested fold (ensures O(n²) operations).
    #    Single-pass comparison-swap is insufficient to sort.
    if not _contains_nested_fold(body):
        return False

    return _body_is_sort_step(body, acc_param)


def _contains_nested_fold(term: OTerm) -> bool:
    """Check if term contains at least one OFold or OFix (inner loop).
    Sort algorithms may use either a nested fold (bubble sort) or
    a while loop (insertion sort) as the inner iteration."""
    if isinstance(term, OFold):
        return True
    if isinstance(term, OFix):
        return True
    if isinstance(term, OCase):
        return (_contains_nested_fold(term.true_branch) or
                _contains_nested_fold(term.false_branch))
    if isinstance(term, OOp):
        return any(_contains_nested_fold(a) for a in term.args)
    if isinstance(term, OSeq):
        return any(_contains_nested_fold(e) for e in term.elements)
    return False


def _body_is_sort_step(body: OTerm, acc_param: str) -> bool:
    """Check if a fold body only rearranges elements via comparison-based swaps.

    Requirements:
    - All setitem values come from getitem of the same accumulator
    - At least one comparison between elements exists somewhere in the body
    - No external values are introduced into the array
    """

    def _has_element_comparison(term: OTerm, acc_name: str) -> bool:
        """Check if any OCase test uses an ORDER comparison of array elements."""
        if isinstance(term, OCase):
            if _test_uses_order_getitem(term.test, acc_name):
                return True
            return (_has_element_comparison(term.true_branch, acc_name) or
                    _has_element_comparison(term.false_branch, acc_name))
        if isinstance(term, OOp):
            return any(_has_element_comparison(a, acc_name) for a in term.args)
        if isinstance(term, OFold):
            if term.body_fn and isinstance(term.body_fn, OLam):
                # Inner fold may compare elements of the OUTER accumulator
                # (e.g., selection sort: inner fold finds min index by comparing
                # outer_acc[j] vs outer_acc[curr_min])
                inner_acc = term.body_fn.params[0]
                return (_has_element_comparison(term.body_fn.body, acc_name) or
                        _has_element_comparison(term.body_fn.body, inner_acc))
            return False
        if isinstance(term, OFix):
            # While loop: comparisons inside the fix body count
            return _has_element_comparison(term.body, acc_name)
        if isinstance(term, OSeq):
            return any(_has_element_comparison(e, acc_name) for e in term.elements)
        return False

    def _test_uses_order_getitem(test: OTerm, acc_name: str) -> bool:
        """Check if test is an order comparison of DIRECT array elements.

        Requires the comparison operands to be getitem(acc, idx) directly —
        NOT getitem(getitem(acc, idx), key), which would be a keyed sort.
        """
        if isinstance(test, OOp):
            # Only order comparisons count — not eq/ne
            if test.name in ('lt', 'gt', 'le', 'ge', 'lte', 'gte') and len(test.args) >= 2:
                if any(_is_direct_element_access(a, acc_name) for a in test.args):
                    return True
            return any(_test_uses_order_getitem(a, acc_name) for a in test.args)
        return False

    def _is_direct_element_access(term: OTerm, acc_name: str) -> bool:
        """Check if term is getitem(acc_chain, idx) — direct element access."""
        if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) >= 1:
            return _is_acc_chain(term.args[0], acc_name)
        return False

    def _test_uses_getitem(test: OTerm, acc_name: str) -> bool:
        """Check if a test expression uses getitem from the accumulator."""
        if isinstance(test, OOp):
            if test.name == 'getitem' and len(test.args) >= 1:
                if _is_acc_chain(test.args[0], acc_name):
                    return True
            return any(_test_uses_getitem(a, acc_name) for a in test.args)
        return False

    def _only_rearranges(term: OTerm, acc_name: str) -> bool:
        """Check that 'term' produces only element-rearranged versions of acc."""
        if isinstance(term, OVar):
            # Only the accumulator variable is acceptable — not loop index etc.
            return term.name == acc_name
        if isinstance(term, OOp):
            if term.name == 'setitem' and len(term.args) == 3:
                base, idx, val = term.args
                if not _only_rearranges(base, acc_name):
                    return False
                if not _val_from_getitem(val, acc_name):
                    return False
                return True
            # getitem(fix[...](state), 0): while loop that modifies the array
            # in-place via shifts/swaps. Accept if the initial state contains
            # the accumulator and the fix body only uses setitem/getitem.
            if term.name == 'getitem' and len(term.args) == 2:
                base, idx = term.args
                if isinstance(base, OFix) and isinstance(idx, OLit) and idx.value == 0:
                    return _fix_rearranges(base, acc_name)
            return False
        if isinstance(term, OCase):
            return (_only_rearranges(term.true_branch, acc_name) and
                    _only_rearranges(term.false_branch, acc_name))
        if isinstance(term, OFold):
            # Inner fold: must also only rearrange elements
            if term.body_fn is not None and isinstance(term.body_fn, OLam):
                inner_acc = term.body_fn.params[0]
                return _only_rearranges(term.body_fn.body, inner_acc)
            return False
        return False

    def _fix_rearranges(fix_term: OFix, acc_name: str) -> bool:
        """Check that a while-loop OFix only rearranges elements of the accumulator.
        The fix body should be a case(guard, [modified_arr, ...], [arr, ...])
        where modified_arr only uses setitem with values from getitem."""
        body = fix_term.body
        if not isinstance(body, OCase):
            return False
        # Check both branches: one continues iteration, one stops
        for branch in [body.true_branch, body.false_branch]:
            if isinstance(branch, OSeq) and len(branch.elements) >= 1:
                arr_elem = branch.elements[0]
                if isinstance(arr_elem, OVar):
                    continue  # Identity: returns acc unchanged
                if isinstance(arr_elem, OOp) and arr_elem.name == 'setitem':
                    # setitem chain: verify values come from getitem
                    if not _setitem_chain_rearranges(arr_elem):
                        return False
                    continue
                return False
            elif isinstance(branch, OOp) and branch.name == '_recurse':
                continue  # Recursive call
            else:
                return False
        return True

    def _setitem_chain_rearranges(term: OTerm) -> bool:
        """Check that a setitem chain only moves elements around."""
        if isinstance(term, OVar):
            return True  # Base accumulator variable
        if isinstance(term, OOp):
            if term.name == 'setitem' and len(term.args) == 3:
                base, idx, val = term.args
                if not _setitem_chain_rearranges(base):
                    return False
                # Value must be from getitem of some accumulator
                if isinstance(val, OOp) and val.name == 'getitem':
                    return True
                if isinstance(val, OVar):
                    return True  # Could be a saved element (e.g., key = arr[i])
                return False
        return False

    def _val_from_getitem(term: OTerm, acc_name: str) -> bool:
        """Check that 'term' ultimately derives from getitem of the accumulator."""
        if isinstance(term, OOp) and term.name == 'getitem':
            base = term.args[0]
            if _is_acc_chain(base, acc_name):
                return True
            # Tuple unpacking: getitem([getitem(acc,i), getitem(acc,j)], k)
            if isinstance(base, OSeq):
                return all(_val_from_getitem(e, acc_name) for e in base.elements)
        return False

    def _is_acc_chain(term: OTerm, acc_name: str) -> bool:
        """Check that 'term' is the accumulator or a rearranged version of it."""
        if isinstance(term, OVar) and term.name == acc_name:
            return True
        if isinstance(term, OOp) and term.name == 'setitem':
            return _is_acc_chain(term.args[0], acc_name)
        return False

    rearranges = _only_rearranges(body, acc_param)
    has_comp = _has_element_comparison(body, acc_param)
    return rearranges and has_comp


def _phase3_fold(term: OTerm) -> OTerm:
    """Phase 3: Fold canonicalization + builtin reducer unification (D5).

    Rewrites:
    - sum(xs) → fold[iadd](0, xs)   (D5: reduce↔loop)
    - min(xs) → fold[min](∞, xs)
    - max(xs) → fold[max](-∞, xs)
    - any(xs) → fold[or](False, xs)
    - all(xs) → fold[and](True, xs)
    - ''.join(xs) → fold[concat]('', xs)
    - math.prod(xs) → fold[imult](1, xs)
    """
    if isinstance(term, OOp):
        args = tuple(_phase3_fold(a) for a in term.args)
        name = term.name
        # D5: Builtin reducers are folds with known step + init
        if len(args) == 1:
            if name == 'sum':
                return OFold('add', OLit(0), args[0])
            if name == 'any':
                return OFold('or', OLit(False), args[0])
            if name == 'all':
                return OFold('and', OLit(True), args[0])
            if name in ('math.prod', 'prod'):
                return OFold('mul', OLit(1), args[0])
        # .join is also a fold
        if name == '.join' and len(args) == 2:
            return OFold('str_concat', args[0], args[1])
        # functools.reduce / reduce is a fold
        if name in ('fold', 'reduce') and len(args) >= 2:
            # reduce(op, iterable) or reduce(op, iterable, init)
            op_name = _extract_reduce_op(args[0])
            init = args[2] if len(args) == 3 else OUnknown('reduce_no_init')
            # Capture lambda as body_fn for precise fold hashing
            reduce_body_fn = None
            if isinstance(args[0], OLam) and len(args[0].params) == 2:
                pa, pb = args[0].params
                renamed = _subst_term(_subst_term(args[0].body, pa, OVar('$0')), pb, OVar('$1'))
                reduce_body_fn = OLam(('$0', '$1'), renamed)
            return OFold(op_name, init, args[1], body_fn=reduce_body_fn)
        return OOp(name, args)
    if isinstance(term, OCase):
        normalized = OCase(_phase3_fold(term.test),
                     _phase3_fold(term.true_branch),
                     _phase3_fold(term.false_branch))
        # Linear recursion → fold conversion (catamorphism principle)
        # case(guard, op(x, fix([sub(x,1)])), base) → fold[op](base, range(...))
        # when op is commutative + associative
        fold_result = _try_linear_rec_to_fold(normalized)
        if fold_result is not None:
            return _phase3_fold(fold_result)  # re-normalize as fold
        return normalized
    if isinstance(term, OFold):
        # Canonicalize fold op name: iadd→add, imult→mul, etc.
        canon = {'iadd': 'add', 'isub': 'sub', 'imul': 'mul', 'imult': 'mul',
                 'ifloordiv': 'floordiv', 'itruediv': 'truediv',
                 'imod': 'mod', 'ipow': 'pow',
                 'ibitor': 'bitor', 'ibitand': 'bitand', 'ibitxor': 'bitxor',
                 'ixor': 'bitxor', 'ior': 'bitor', 'iand': 'bitand',
                 'mult': 'mul'}
        op = canon.get(term.op_name, term.op_name)
        init = _phase3_fold(term.init)
        coll = _phase3_fold(term.collection)
        # Fold body recognition: if op is an opaque hash, check body_fn
        # λ(a,b)min(a,b) → fold[min], λ(a,b)max(a,b) → fold[max], etc.
        bfn = _phase3_fold(term.body_fn) if term.body_fn else None
        if bfn is not None and not op.isalpha():
            recognized_op = _recognize_fold_body(bfn)
            if recognized_op is not None:
                op = recognized_op
        # reduce without init: infer identity element for the operation
        if isinstance(init, OUnknown) and init.desc == 'reduce_no_init':
            _OP_IDENTITY = {
                'add': OLit(0), 'sub': OLit(0), 'mul': OLit(1),
                'bitor': OLit(0), 'bitand': OLit(-1), 'bitxor': OLit(0),
                'or': OLit(False), 'and': OLit(True),
                'str_concat': OLit(''),
            }
            if op in _OP_IDENTITY:
                init = _OP_IDENTITY[op]
        # ── Range start canonicalization ──
        # fold[op](identity, range(S, E)) where S > identity and all values
        # in [identity, S) are identity for op → fold[op](identity, range(identity, E))
        # E.g., fold[add](0, range(1, n+1)) → fold[add](0, range(0, n+1))
        # because adding 0 to a sum doesn't change it.
        # This ensures recursive-to-fold and iterative-fold normalize the same.
        _OP_IDENTITY_VAL = {
            'add': 0, 'mul': 1, 'bitor': 0, 'bitxor': 0,
            'bitand': -1, 'or': False, 'and': True,
        }
        if (op in _OP_IDENTITY_VAL and isinstance(coll, OOp) and
                coll.name == 'range' and len(coll.args) >= 2):
            id_val = _OP_IDENTITY_VAL[op]
            range_start = coll.args[0]
            if isinstance(range_start, OLit) and isinstance(init, OLit):
                if init.value == id_val and isinstance(range_start.value, (int, float)):
                    # Check all values in [id_val, start) are identity for op
                    start_v = int(range_start.value)
                    all_identity = True
                    for v in range(int(id_val), start_v):
                        if v != id_val:
                            all_identity = False
                            break
                    if all_identity and start_v > id_val:
                        new_args = (OLit(id_val),) + coll.args[1:]
                        coll = OOp('range', new_args)

        # Fold→math simplification: fold[min](a[0], a[1:]) → min(a)
        result = _try_fold_to_builtin(op, init, coll)
        if result is not None:
            return result

        # ── Constant-map fold absorption ──
        # fold[and](True, map(λ.True, xs)) → True  (AND over all-True)
        # fold[or](False, map(λ.False, xs)) → False (OR over all-False)
        # fold[add](0, map(λ.0, xs)) → 0  (sum of zeros)
        # fold[mul](1, map(λ.1, xs)) → 1  (product of ones)
        # General: fold[op](identity, constant(identity) collection) → identity
        if isinstance(coll, OMap) and isinstance(coll.transform, OLam):
            map_body = coll.transform.body
            if isinstance(map_body, OLit):
                _IDENTITY_ABSORB = {
                    'and': (True, True),   # fold[and](True, [True,...]) → True
                    'or': (False, False),  # fold[or](False, [False,...]) → False
                    'add': (0, 0),         # fold[add](0, [0,...]) → 0
                    'mul': (1, 1),         # fold[mul](1, [1,...]) → 1
                }
                if op in _IDENTITY_ABSORB:
                    id_init, id_elem = _IDENTITY_ABSORB[op]
                    if (isinstance(init, OLit) and init.value == id_init
                            and map_body.value == id_elem):
                        return init
            # Also handle nested fold[and](True, map(λ.fold[and](True,...), xs))
            # → fold[and](True, flatmap) — but just checking if inner is constant True
            if isinstance(map_body, OFold) and map_body.op_name == op:
                if op == 'and' and isinstance(init, OLit) and init.value is True:
                    if isinstance(map_body.init, OLit) and map_body.init.value is True:
                        # Inner fold also starts with True — if inner collection
                        # maps to constant True, the whole thing is True.
                        if (isinstance(map_body.collection, OMap)
                                and isinstance(map_body.collection.transform, OLam)
                                and isinstance(map_body.collection.transform.body, OLit)
                                and map_body.collection.transform.body.value is True):
                            return OLit(True)

        # ── Digit sum identity: fold[add](0, map(int, str(X))) → digit_sum(X) ──
        # Summing digits by string conversion is mathematically equal to
        # the iterative mod-10/div-10 recurrence.
        if op == 'add' and isinstance(init, OLit) and init.value == 0:
            if isinstance(coll, OMap) and coll.filter_pred is None:
                t = coll.transform
                c = coll.collection
                if (isinstance(t, OLam) and len(t.params) == 1
                        and isinstance(t.body, OOp) and t.body.name == 'int'
                        and len(t.body.args) == 1
                        and isinstance(t.body.args[0], OVar)
                        and t.body.args[0].name == t.params[0]):
                    if isinstance(c, OOp) and c.name == 'str' and len(c.args) == 1:
                        return OOp('digit_sum', c.args)
        # ── Range normalization for iteration-count folds ──
        # When fold body doesn't use the iteration variable (last param),
        # only the NUMBER of iterations matters, not the range values.
        # So fold[f](init, range(a, b)) == fold[f](init, range(sub(b, a)))
        # This is a general algebraic identity for iteration-count folds.
        #
        # When the body DOES use the iteration variable, we can still
        # normalize range(a, b) → range(b-a) by substituting
        # iter_var → iter_var + a in the body.
        # Exception: skip DP-fill folds (setitem(acc, i, ...)) — those are
        # handled by _try_dp_to_tuple_fold in phase 4, which needs the
        # original range(start, end) form.
        if (bfn is not None and isinstance(bfn, OLam)
                and len(bfn.params) >= 2
                and isinstance(coll, OOp) and coll.name == 'range'
                and len(coll.args) == 2):
            iter_param = bfn.params[-1]
            body_free = _collect_vars(bfn.body)
            a_term, b_term = coll.args
            if iter_param not in body_free:
                # Iteration variable unused — normalize range(a,b) → range(b-a)
                new_coll = OOp('range', (OOp('sub', (b_term, a_term)),))
                return OFold(op, init, new_coll, body_fn=bfn)
            elif isinstance(a_term, OLit) and isinstance(a_term.value, int) and a_term.value != 0:
                # Check if this is a DP-fill fold (body = setitem(acc, i, expr))
                # If so, skip range normalization to let _try_dp_to_tuple_fold handle it
                is_dp_fill = (isinstance(bfn.body, OOp) and bfn.body.name == 'setitem'
                              and len(bfn.body.args) == 3
                              and isinstance(bfn.body.args[0], OVar)
                              and bfn.body.args[0].name == bfn.params[0]
                              and isinstance(bfn.body.args[1], OVar)
                              and bfn.body.args[1].name == iter_param)
                if not is_dp_fill:
                    # Iteration variable used with literal offset — substitute
                    # iter_var → iter_var + a, normalize range(a,b) → range(b-a)
                    offset = a_term
                    new_body = _subst_term(bfn.body, iter_param,
                                           OOp('add', (OVar(iter_param), offset)))
                    new_bfn = OLam(bfn.params, new_body)
                    new_coll = OOp('range', (OOp('sub', (b_term, a_term)),))
                    import hashlib
                    new_hash = hashlib.md5(new_bfn.canon().encode()).hexdigest()[:8]
                    return OFold(new_hash, init, new_coll, body_fn=new_bfn)
        # ── Dict-building fold → dict(zip(A, B)) ──
        # fold[λ(acc,i)→setitem(acc, A[i], B[i])]({}, range(N)) → dict(zip(A, B))
        # when N = min(len(A), len(B)) or len(A) or len(B).
        # This is the definition of dict(zip(...)): iterate indices, build k-v pairs.
        if (isinstance(init, ODict) and len(init.pairs) == 0
                and bfn is not None and isinstance(bfn, OLam)
                and len(bfn.params) == 2):
            acc_p, idx_p = bfn.params
            body = bfn.body
            if (isinstance(body, OOp) and body.name == 'setitem'
                    and len(body.args) == 3):
                target, key_expr, val_expr = body.args
                if isinstance(target, OVar) and target.name == acc_p:
                    # key = A[i], val = B[i]
                    if (isinstance(key_expr, OOp) and key_expr.name == 'getitem'
                            and len(key_expr.args) == 2
                            and isinstance(key_expr.args[1], OVar)
                            and key_expr.args[1].name == idx_p
                            and isinstance(val_expr, OOp) and val_expr.name == 'getitem'
                            and len(val_expr.args) == 2
                            and isinstance(val_expr.args[1], OVar)
                            and val_expr.args[1].name == idx_p):
                        keys_arr = key_expr.args[0]
                        vals_arr = val_expr.args[0]
                        return OOp('dict', (OOp('zip', (keys_arr, vals_arr)),))

        # ── Binomial coefficient fold → comb(n, k) ──
        # fold[λ(acc,i)→acc*(n-i)/(i+1)](1, range(k)) = comb(n,k)
        if bfn is not None:
            comb_result = _try_fold_to_comb(bfn, init, coll)
            if comb_result is not None:
                return comb_result

        # ── D25: Comparison-sort fold → sorted(x) ──
        # If the fold starts from list(x), iterates over range(len(x)),
        # and the body only performs comparison-based element swaps,
        # then the result is sorted(x) by sorting network theory.
        rebuilt = OFold(op, init, coll, body_fn=bfn)
        if _is_comparison_sort_fold(rebuilt):
            return OOp('sorted', (rebuilt.init.args[0],))

        # ── Fold-to-map lifting ──
        # fold[λ(acc,i)→setitem(acc,i,f(init[i],i))](init, range(N))
        # where f only reads acc[i] (the cell being overwritten) →
        # each update is independent → equivalent to map.
        lifted = _try_fold_to_map(rebuilt, init)
        if lifted is not None:
            return lifted

        return rebuilt
    if isinstance(term, OFix):
        return OFix(term.name, _phase3_fold(term.body))
    if isinstance(term, OSeq):
        return OSeq(tuple(_phase3_fold(e) for e in term.elements))
    if isinstance(term, OQuotient):
        return OQuotient(_phase3_fold(term.inner), term.equiv_class)
    if isinstance(term, OLam):
        return OLam(term.params, _phase3_fold(term.body))
    if isinstance(term, OMap):
        t = _phase3_fold(term.transform)
        c = _phase3_fold(term.collection)
        f = _phase3_fold(term.filter_pred) if term.filter_pred else None
        return OMap(t, c, f)
    if isinstance(term, OCatch):
        return OCatch(_phase3_fold(term.body), _phase3_fold(term.default))
    if isinstance(term, ODict):
        return ODict(tuple((_phase3_fold(k), _phase3_fold(v)) for k, v in term.pairs))
    return term


def _phase4_hof(term: OTerm) -> OTerm:
    """Phase 4: HOF fusion rules + absorption laws + dichotomy path constructors.

    HOF fusion (§30):
      map(f, map(g, xs)) → map(f∘g, xs)
      fold(op, init, map(f, xs)) → fold(op, init, xs) when f is absorbed
    Absorption laws (Theorem 14.7):
      sorted(list(x)) → sorted(x), len(list(x)) → len(x),
      sum(sorted(x)) → sum(x), etc.
    """
    if isinstance(term, OOp):
        args = tuple(_phase4_hof(a) for a in term.args)
        name = term.name

        # ── Absorption laws: outer(inner(x)) → outer(x) ──
        # When the inner operation is operadically redundant inside the outer
        if len(args) == 1 and isinstance(args[0], OOp) and len(args[0].args) >= 1:
            inner_name = args[0].name
            absorbed = _try_absorb(name, inner_name)
            if absorbed is not None:
                return OOp(absorbed, args[0].args)

        # sorted(Q[perm](x)) → sorted(x)
        if name == 'sorted' and len(args) == 1:
            if isinstance(args[0], OQuotient):
                return OOp('sorted', (args[0].inner,))

        # list(reversed(sorted(x))) → sorted_rev(x)
        if name == 'list' and len(args) == 1:
            # list(Q[perm](x)) → Q[perm](x)
            if isinstance(args[0], OQuotient) and args[0].equiv_class == 'perm':
                return args[0]
            if isinstance(args[0], OOp) and args[0].name == 'reversed':
                inner = args[0].args[0]
                if isinstance(inner, OOp) and inner.name == 'sorted':
                    return OOp('sorted_rev', inner.args)
                if isinstance(inner, OOp) and inner.name == 'sorted_key':
                    return OOp('sorted_key_rev', inner.args)
            # list(map(f, xs)) → map(f, xs) (map already produces a list-like)
            if isinstance(args[0], OMap):
                return args[0]
            # list(transpose(X)) → transpose(X)
            if isinstance(args[0], OOp) and args[0].name == 'transpose':
                return args[0]
            # list(zip(unpack(X))) → transpose(X)
            if isinstance(args[0], OOp) and args[0].name == 'zip' and len(args[0].args) == 1:
                inner = args[0].args[0]
                if isinstance(inner, OOp) and inner.name == 'unpack':
                    return OOp('transpose', inner.args)
            # list(enumerate(xs)) → map(λi.[i, xs[i]], range(len(xs)))
            if isinstance(args[0], OOp) and args[0].name == 'enumerate':
                xs = args[0].args[0]
                param = '_eidx'
                body = OSeq((OVar(param), OOp('getitem', (xs, OVar(param)))))
                return OMap(OLam((param,), body),
                            OOp('range', (OOp('len', (xs,)),)), None)

        # enumerate(xs) → map(λi.[i, xs[i]], range(len(xs)))
        if name == 'enumerate' and len(args) == 1:
            xs = args[0]
            param = '_eidx'
            body = OSeq((OVar(param), OOp('getitem', (xs, OVar(param)))))
            return OMap(OLam((param,), body),
                        OOp('range', (OOp('len', (xs,)),)), None)

        # reversed(sorted(x)) → sorted_rev(x)
        if name == 'reversed' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'sorted':
                return OOp('sorted_rev', args[0].args)
            if isinstance(args[0], OOp) and args[0].name == 'sorted_key':
                return OOp('sorted_key_rev', args[0].args)

        # zip(unpack(X)) → transpose(X)
        # zip(*matrix) is the standard Python transpose idiom
        if name == 'zip' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'unpack':
                return OOp('transpose', args[0].args)

        # map(list, zip(unpack(X))) → transpose(X)
        # list(zip(*matrix)) or [list(row) for row in zip(*matrix)]
        if name == 'map' and len(args) == 2:
            fn, coll = args
            if (isinstance(fn, OLam) and len(fn.params) == 1
                    and isinstance(fn.body, OOp) and fn.body.name == 'list'
                    and len(fn.body.args) == 1
                    and isinstance(fn.body.args[0], OVar)
                    and fn.body.args[0].name == fn.params[0]):
                if isinstance(coll, OOp) and coll.name == 'transpose':
                    return OOp('transpose', coll.args)

        # sum(range(n)) → n*(n-1)/2
        if name == 'sum' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'range':
                n = args[0].args[0] if args[0].args else OLit(0)
                return OOp('floordiv', (OOp('mult', (n, OOp('sub', (n, OLit(1))))), OLit(2)))

        # len(list/tuple/sorted(x)) → len(x)
        if name == 'len' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name in ('list', 'tuple', 'sorted', 'reversed'):
                return OOp('len', args[0].args)
            # len(map(f, xs)) → len(xs)
            if isinstance(args[0], OMap) and args[0].filter_pred is None:
                return OOp('len', (args[0].collection,))
            # len(concat(a, b)) = len(a) + len(b)
            if isinstance(args[0], OOp) and args[0].name in ('add', 'concat') and len(args[0].args) == 2:
                a, b = args[0].args
                # Only apply when args look like sequences (not scalars)
                if isinstance(a, (OSeq, OMap, OOp)):
                    return OOp('add', (OOp('len', (a,)), OOp('len', (b,))))
            # len(OSeq([...], n elements)) → n
            if isinstance(args[0], OSeq):
                return OLit(len(args[0].elements))
            # len(mult([x], n)) → n  (list repetition)
            if isinstance(args[0], OOp) and args[0].name == 'mult' and len(args[0].args) == 2:
                base, rep = args[0].args
                if isinstance(base, OSeq):
                    return OOp('mult', (OLit(len(base.elements)), rep))

        # ── Map-indexing law: getitem(map(f, xs), i) → f(xs[i]) ──
        # This is a general algebraic law: (map(f, xs))[i] = f(xs[i])
        # It normalizes indexed access on mapped collections.
        if name == 'getitem' and len(args) == 2:
            coll, idx = args
            if isinstance(coll, OMap) and coll.filter_pred is None:
                if isinstance(coll.transform, OLam) and len(coll.transform.params) == 1:
                    param = coll.transform.params[0]
                    inner_access = OOp('getitem', (coll.collection, idx))
                    body = coll.transform.body
                    result = _subst_term(body, param, inner_access)
                    return result
            # getitem(itertools.cycle(xs), i) → getitem(xs, mod(i, len(xs)))
            # cycle(xs) repeats xs infinitely; indexing into it is modular.
            if isinstance(coll, OOp) and coll.name == 'itertools.cycle' and len(coll.args) == 1:
                xs = coll.args[0]
                return OOp('getitem', (xs, OOp('mod', (idx, OOp('len', (xs,))))))

            # ── Literal sequence indexing: getitem([a,b,c], 1) → b ──
            if isinstance(coll, OSeq) and isinstance(idx, OLit) and isinstance(idx.value, int):
                i = idx.value
                elts = coll.elements
                if -len(elts) <= i < len(elts):
                    return elts[i]

            # ── Range indexing: getitem(range(n), i) → i ──
            # For range(n), element at index i is i (for 0 <= i < n).
            # For range(a, b), element at index i is a + i.
            if isinstance(coll, OOp) and coll.name == 'range':
                if len(coll.args) == 1:
                    return idx
                elif len(coll.args) == 2:
                    start = coll.args[0]
                    return OOp('add', (start, idx))

            # ── DP-array-fill → tuple-fold conversion ──
            # getitem(fold[setitem_body](init_arr, range(2, end)), idx)
            #   → getitem(fold[tuple_body]((v0,v1), range(idx)), 0)
            # when the fold body is setitem(acc, i, f(acc[i-1], acc[i-2]))
            # and idx = end - 1 (extracting the last filled element).
            # This is the standard DP window compression theorem:
            # a linear recurrence with lookback w stored in an array of size n
            # is equivalent to a w-tuple sliding window fold.
            if isinstance(coll, OFold) and isinstance(coll.body_fn, OLam):
                dp_result = _try_dp_to_tuple_fold(coll, idx)
                if dp_result is not None:
                    return dp_result

            # ── Fold-shift identity for pair-rotation folds ──
            # getitem(fold[f](init, coll), 1) → getitem(fold[f](init, coll'), 0)
            # where coll' extends iteration count by 1.
            # Valid when: init is a 2-element seq, body has pair-rotation form
            # (first output = second input), and collection is range-based.
            # For pair-rotation folds (a,b,i)→(b,...), element 0 at step K+1
            # equals element 1 at step K, so the shift is sound even when
            # the body uses the iteration variable.
            if (isinstance(coll, OFold) and isinstance(idx, OLit)
                    and idx.value == 1
                    and isinstance(coll.init, OSeq) and len(coll.init.elements) == 2
                    and coll.body_fn is not None and isinstance(coll.body_fn, OLam)
                    and len(coll.body_fn.params) >= 2):
                bfn = coll.body_fn
                is_pair_rotation = (
                    isinstance(bfn.body, OSeq)
                    and len(bfn.body.elements) == 2
                    and isinstance(bfn.body.elements[0], OVar)
                    and bfn.body.elements[0].name == bfn.params[1]
                )
                iter_p = bfn.params[-1]
                bvars = _collect_vars(bfn.body)
                if iter_p not in bvars or is_pair_rotation:
                    fc = coll.collection
                    if isinstance(fc, OOp) and fc.name == 'range' and len(fc.args) == 1:
                        new_coll = OOp('range', (OOp('add', (fc.args[0], OLit(1))),))
                        return OOp('getitem', (OFold(coll.op_name, coll.init,
                                    new_coll, body_fn=coll.body_fn), OLit(0)))

        # itertools.cycle(xs) used standalone → identity (we handle at getitem site)
        # This is conservative: cycle only makes sense with indexing

        # NOTE: abs(x) is NOT expanded to piecewise case(lt(x,0), -x, x)
        # because abs() handles complex numbers (returns magnitude) while
        # manual piecewise only handles real numbers.

        # max/min are commutative operations with canonical arg ordering.
        # Do NOT expand to case(gte/lte, ...) — that creates an oscillation
        # with Phase 1's R16b (case→max/min contraction).
        # Keep as OOp('max'/min') so commutative canon() handles arg ordering.

        # ── Euler's formula: exp(i*θ) → complex(cos(θ), sin(θ)) ──
        # e^(iθ) = cos(θ) + i·sin(θ) is a mathematical identity.
        if name == '_L.exp' and len(args) == 1:
            arg = args[0]
            if isinstance(arg, OOp) and arg.name == 'mult' and len(arg.args) == 2:
                a, b = arg.args
                if isinstance(b, OLit) and b.value == 1j:
                    return OOp('complex', (OOp('math.cos', (a,)),
                                           OOp('math.sin', (a,))))
                if isinstance(a, OLit) and a.value == 1j:
                    return OOp('complex', (OOp('math.cos', (b,)),
                                           OOp('math.sin', (b,))))

        # ── Complex arithmetic normalization ──
        # mult(complex(a,b), complex(c,d)) → complex(a*c-b*d, a*d+b*c)
        if name == 'mult' and len(args) == 2:
            a, b = args
            if (isinstance(a, OOp) and a.name == 'complex' and len(a.args) == 2
                    and isinstance(b, OOp) and b.name == 'complex' and len(b.args) == 2):
                ar, ai = a.args
                br, bi = b.args
                real = OOp('sub', (OOp('mult', (ar, br)),
                                   OOp('mult', (ai, bi))))
                imag = OOp('add', (OOp('mult', (ar, bi)),
                                   OOp('mult', (ai, br))))
                return OOp('complex', (real, imag))

        # .real(complex(a,b)) → a, .imag(complex(a,b)) → b
        if name == '.real' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'complex' and len(args[0].args) == 2:
                return args[0].args[0]
        if name == '.imag' and len(args) == 1:
            if isinstance(args[0], OOp) and args[0].name == 'complex' and len(args[0].args) == 2:
                return args[0].args[1]

        # ── Popcount identity: bin(n).count('1') → popcount(n) ──
        # Canonical form for counting set bits
        if name == '.count' and len(args) == 2:
            if (isinstance(args[0], OOp) and args[0].name == 'bin'
                    and isinstance(args[1], OLit) and args[1].value == '1'):
                return OOp('popcount', args[0].args)

        # ── Reverse digits identity: int(reversed(str(X))) → reverse_digits(X) ──
        # int(str(n)[::-1]) and int(''.join(reversed(str(n)))) are reverse-digits
        if name == 'int' and len(args) == 1:
            inner = args[0]
            # int(reversed(str(X))) or int(reversed(str(X)), 10)
            if isinstance(inner, OOp) and inner.name == 'reversed' and len(inner.args) == 1:
                str_arg = inner.args[0]
                if isinstance(str_arg, OOp) and str_arg.name == 'str' and len(str_arg.args) == 1:
                    return OOp('reverse_digits', str_arg.args)
            # int(suffix(str(X), -N)) — string slicing reversal
            # int(str(X)[::-1]) compiles to reversed then str or similar

        # ── Constant folding: ord('A') → 65, chr(65) → 'A', len('str') → int ──
        if name == 'ord' and len(args) == 1:
            if isinstance(args[0], OLit) and isinstance(args[0].value, str) and len(args[0].value) == 1:
                return OLit(ord(args[0].value))
        if name == 'chr' and len(args) == 1:
            if isinstance(args[0], OLit) and isinstance(args[0].value, int):
                try:
                    return OLit(chr(args[0].value))
                except (ValueError, OverflowError):
                    pass
        if name == 'len' and len(args) == 1:
            if isinstance(args[0], OLit) and isinstance(args[0].value, str):
                return OLit(len(args[0].value))

        # ── setitem chain normalization ──
        # setitem(setitem(x, i, v), i, w) → setitem(x, i, w)
        # Overwriting the same index makes the first write dead
        if name == 'setitem' and len(args) == 3:
            base, idx, val = args
            if (isinstance(base, OOp) and base.name == 'setitem'
                    and len(base.args) == 3
                    and base.args[1].canon() == idx.canon()):
                return OOp('setitem', (base.args[0], idx, val))

            # ── setitem-map fusion ──
            # setitem(map(f, range(N)), I, W)
            #   → map(λ(j) case(eq(I,j), W, f(j)), range(N))
            # Fuses point update into element-wise computation.
            if isinstance(base, OMap) and isinstance(base.transform, OLam):
                map_coll = base.collection
                map_fn = base.transform
                if (isinstance(map_coll, OOp) and map_coll.name == 'range'
                        and len(map_fn.params) == 1):
                    j_param = map_fn.params[0]
                    # Build: case(eq(I, j), W, f(j))
                    guard = OOp('eq', (idx, OVar(j_param)))
                    new_body = OCase(guard, val, map_fn.body)
                    new_lam = OLam((j_param,), new_body)
                    return _phase4_hof(OMap(new_lam, map_coll, base.filter_pred))

        # ── List replication as map ──
        # mult(N, [V]) or mult([V], N) → map(λ(_)V, range(N))
        # [V]*N is a uniform list, expressible as element-wise constant map.
        if name == 'mult' and len(args) == 2:
            seq_arg, n_arg = None, None
            if isinstance(args[0], OSeq) and len(args[0].elements) == 1:
                seq_arg, n_arg = args[0], args[1]
            elif isinstance(args[1], OSeq) and len(args[1].elements) == 1:
                seq_arg, n_arg = args[1], args[0]
            if seq_arg is not None:
                val = seq_arg.elements[0]
                const_lam = OLam(('_rep',), val)
                return _phase4_hof(OMap(const_lam, OOp('range', (n_arg,))))

        # ── Builtin map/filter → OMap canonicalization ──
        # map(f, xs) → OMap(f, xs)
        if name == 'map' and len(args) == 2:
            return _phase4_hof(OMap(args[0], args[1]))
        # filter(pred, xs) → OMap(id, xs, pred)
        if name == 'filter' and len(args) == 2:
            # filter(pred, xs) is "select elements where pred(x) is true"
            # Canonical: OMap(identity_lambda, xs, pred)
            if isinstance(args[0], OLam) and len(args[0].params) == 1:
                id_lam = OLam(args[0].params,
                              OVar(args[0].params[0]))
                return _phase4_hof(OMap(id_lam, args[1], args[0]))
            return _phase4_hof(OMap(
                OLam(('_fv',), OVar('_fv')), args[1], args[0]))

        return OOp(name, args)

    # ── HOF map∘map fusion (§30) ──
    if isinstance(term, OMap):
        t = _phase4_hof(term.transform)
        c = _phase4_hof(term.collection)
        f = _phase4_hof(term.filter_pred) if term.filter_pred else None

        # map(id, xs) → xs (identity map elimination)
        if isinstance(t, OLam) and len(t.params) == 1:
            if isinstance(t.body, OVar) and t.body.name == t.params[0]:
                if f is None:
                    return c

        # map(λ(x)list(x), transpose(X)) → transpose(X)
        # list() on rows of a transposed matrix is identity on lists.
        if isinstance(t, OLam) and len(t.params) == 1 and f is None:
            if (isinstance(t.body, OOp) and t.body.name == 'list'
                    and len(t.body.args) == 1
                    and isinstance(t.body.args[0], OVar)
                    and t.body.args[0].name == t.params[0]):
                if isinstance(c, OOp) and c.name == 'transpose':
                    return c

        # ── Double-map-getitem → transpose ──
        # map(λ(i)map(λ(j)M[j][i], range(rows)), range(cols)) → transpose(M)
        # This is the comprehension-based transpose pattern.
        if isinstance(t, OLam) and len(t.params) == 1 and f is None:
            if isinstance(t.body, OMap) and t.body.filter_pred is None:
                inner_t = t.body.transform
                inner_c = t.body.collection
                if (isinstance(inner_t, OLam) and len(inner_t.params) == 1
                        and isinstance(inner_t.body, OOp)
                        and inner_t.body.name == 'getitem'
                        and len(inner_t.body.args) == 2):
                    # inner body = getitem(getitem(M, j), i)
                    outer_access = inner_t.body.args[0]
                    inner_idx = inner_t.body.args[1]
                    if (isinstance(outer_access, OOp)
                            and outer_access.name == 'getitem'
                            and len(outer_access.args) == 2):
                        matrix = outer_access.args[0]
                        outer_idx = outer_access.args[1]
                        # Check: outer idx = inner lambda param, inner idx = outer lambda param
                        # Pattern: M[j][i] where j is inner param and i is outer param
                        i_param = t.params[0]  # outer lambda
                        j_param = inner_t.params[0]  # inner lambda
                        if (isinstance(outer_idx, OVar) and outer_idx.name == j_param
                                and isinstance(inner_idx, OVar) and inner_idx.name == i_param):
                            return OOp('transpose', (matrix,))

        # ── zip→index normalization ──
        # map(λ(x,y).body, zip(a,b)) → map(λi.body[x:=a[i],y:=b[i]], range(len(a)))
        # Canonicalizes zip-based iteration to index-based iteration.
        if (isinstance(t, OLam) and len(t.params) >= 2 and f is None and
                isinstance(c, OOp) and c.name == 'zip' and len(c.args) == len(t.params)):
            idx_var = '_zi'
            subs = {}
            for i, (p, arr) in enumerate(zip(t.params, c.args)):
                subs[p] = OOp('getitem', (arr, OVar(idx_var)))
            new_body = t.body
            for old_name, new_term in subs.items():
                new_body = _subst_term(new_body, old_name, new_term)
            range_coll = OOp('range', (OOp('len', (c.args[0],)),))
            return OMap(OLam((idx_var,), new_body), range_coll)

        # ── enumerate→index normalization ──
        # map(λ(i,x).body, enumerate(xs)) → map(λi.body[i:=i,x:=xs[i]], range(len(xs)))
        if (isinstance(t, OLam) and len(t.params) == 2 and f is None and
                isinstance(c, OOp) and c.name == 'enumerate' and len(c.args) == 1):
            idx_var = '_ei'
            idx_p, val_p = t.params
            new_body = _subst_term(t.body, idx_p, OVar(idx_var))
            new_body = _subst_term(new_body, val_p, OOp('getitem', (c.args[0], OVar(idx_var))))
            range_coll = OOp('range', (OOp('len', (c.args[0],)),))
            return OMap(OLam((idx_var,), new_body), range_coll)

        # map(f, map(g, xs)) → map(f∘g, xs)
        if isinstance(c, OMap) and c.filter_pred is None:
            if isinstance(t, OLam) and isinstance(c.transform, OLam):
                if len(t.params) == 1 and len(c.transform.params) == 1:
                    composed = _compose_lam(t, c.transform)
                    return OMap(composed, c.collection, f)
                # Tuple-unpacking fusion: map(λ(a,b,...).body, map(λx.(e1,e2,...), xs))
                # → map(λx.body[a:=e1,b:=e2,...], xs)
                # General form: outer takes N params, inner returns N-tuple (OSeq)
                if (len(c.transform.params) == 1 and len(t.params) > 1
                        and isinstance(c.transform.body, OSeq)
                        and len(c.transform.body.elements) == len(t.params)):
                    inner_p = c.transform.params[0]
                    new_body = t.body
                    for p, elem_expr in zip(t.params, c.transform.body.elements):
                        new_body = _subst_term(new_body, p, elem_expr)
                    composed = OLam((inner_p,), new_body)
                    return _phase4_hof(OMap(composed, c.collection, f))

        # map(f, map(g, xs)) where inner has filter → map(f∘g, xs, filter)
        if isinstance(c, OMap) and c.filter_pred is not None and f is None:
            if isinstance(t, OLam) and isinstance(c.transform, OLam):
                if len(t.params) == 1 and len(c.transform.params) == 1:
                    composed = _compose_lam(t, c.transform)
                    return OMap(composed, c.collection, c.filter_pred)

        # ── map(f, filter(g, xs)) → filter_map(g, f, xs) ──
        # OOp('filter', (pred, xs)) → OMap with filter_pred
        if (f is None and isinstance(c, OOp) and c.name == 'filter'
                and len(c.args) == 2):
            return OMap(t, c.args[1], c.args[0])

        return OMap(t, c, f)

    if isinstance(term, OCase):
        t = _phase4_hof(term.test)
        tb = _phase4_hof(term.true_branch)
        fb = _phase4_hof(term.false_branch)

        # ── Recursive GCD pattern: case(eq(Y,0), X, fix[g]([Y, mod(X,Y)])) → gcd(X, Y) ──
        # The standard recursive definition of GCD.
        if isinstance(fb, OFix) and isinstance(fb.body, OSeq) and len(fb.body.elements) == 2:
            r0, r1 = fb.body.elements
            tc = t.canon()
            # Test is eq(Y, 0) or eq(0, Y) where Y is a variable
            if isinstance(t, OOp) and t.name == 'eq' and len(t.args) == 2:
                y_term = None
                if isinstance(t.args[1], OLit) and t.args[1].value == 0:
                    y_term = t.args[0]
                elif isinstance(t.args[0], OLit) and t.args[0].value == 0:
                    y_term = t.args[1]
                if y_term is not None and isinstance(tb, OVar):
                    x_term = tb
                    # Check: r0 == Y and r1 == mod(X, Y)
                    if (r0.canon() == y_term.canon()
                            and isinstance(r1, OOp) and r1.name == 'mod'
                            and len(r1.args) == 2
                            and r1.args[0].canon() == x_term.canon()
                            and r1.args[1].canon() == y_term.canon()):
                        return OOp('gcd', (x_term, y_term))

        return OCase(t, tb, fb)
    if isinstance(term, OFold):
        init = _phase4_hof(term.init)
        coll = _phase4_hof(term.collection)
        # fold(op, init, map(f, xs)) → fold(op, init, xs) when f is identity
        if isinstance(coll, OMap) and coll.filter_pred is None:
            if isinstance(coll.transform, OLam) and len(coll.transform.params) == 1:
                if (isinstance(coll.transform.body, OVar) and
                        coll.transform.body.name == coll.transform.params[0]):
                    return OFold(term.op_name, init, coll.collection,
                                 body_fn=term.body_fn)

        # ── Counting pattern: fold[add](0, map(λx.1, coll)) → len(coll) ──
        # This is the general "count elements" fold — matches both
        #   sum(1 for x in xs) and len([x for x in xs])
        if term.op_name == 'add' and isinstance(init, OLit) and init.value == 0:
            if isinstance(coll, OMap) and isinstance(coll.transform, OLam):
                if (isinstance(coll.transform.body, OLit) and
                        coll.transform.body.value == 1):
                    if coll.filter_pred is None:
                        return OOp('len', (coll.collection,))
                    else:
                        # fold[add](0, filter_map(p, λx.1, xs)) →
                        #   len(filter(p, xs))
                        return OOp('len', (OMap(
                            OLam(coll.transform.params, OVar(coll.transform.params[0])),
                            coll.collection, coll.filter_pred),))

        # ── fold[any](False, map(λx.eq(v,x), coll)) → in(v, coll) ──
        # Algebraic identity: any(x == v for x in coll) ≡ v in coll
        # Sound for sequence membership (list, tuple, set, dict keys).
        if (term.op_name in ('any', 'or') and
                isinstance(init, OLit) and init.value is False and
                isinstance(coll, OMap) and coll.filter_pred is None and
                isinstance(coll.transform, OLam) and
                len(coll.transform.params) == 1):
            body = coll.transform.body
            param = coll.transform.params[0]
            # Match eq(v, x) or eq(x, v) where x is the bound variable
            if isinstance(body, OOp) and body.name == 'eq' and len(body.args) == 2:
                a, b = body.args
                if isinstance(b, OVar) and b.name == param and param not in _collect_vars(a):
                    return OOp('in', (a, coll.collection))
                if isinstance(a, OVar) and a.name == param and param not in _collect_vars(b):
                    return OOp('in', (b, coll.collection))

        # ── fold[or](False, xs) → any(xs) — canonical form ──
        # ── fold[and](True, xs) → all(xs) — canonical form ──
        # These have already been done by phase 3 (builtin → fold),
        # but if someone builds fold[or]/fold[and] directly, also normalize.
        # No change needed — canonical name is kept as fold[or]/fold[and].

        # ── String join identity: fold[str_concat]('', x) → x ──
        # ''.join(xs) on characters is identity for the reconstructed string.
        # This is sound because ''.join(list_of_chars) = original_string
        # when the collection represents characters of a string (reversed, map, etc.)
        if term.op_name == 'str_concat' and isinstance(init, OLit) and init.value == '':
            return coll

        # ── Fold ordering absorption for commutative+associative ops ──
        # fold(op, init, reversed(xs)) → fold(op, init, xs)
        # fold(op, init, sorted(xs))   → fold(op, init, xs)
        # fold(op, init, Q[perm](xs))  → fold(op, init, xs)
        # Sound because for C+A operators, element ordering doesn't
        # affect the aggregate result.  Only applies to simple folds
        # (body_fn is None), since custom body_fns may use the
        # accumulator in order-dependent ways.
        _CA_OPS = frozenset({
            'add', 'mult', 'max', 'min', 'bitand', 'bitor', 'bitxor',
            'and', 'or', 'gcd',
        })
        if term.op_name in _CA_OPS and term.body_fn is None:
            if isinstance(coll, OOp) and coll.name in ('reversed', 'sorted') and len(coll.args) == 1:
                return OFold(term.op_name, init, coll.args[0], body_fn=None)
            if isinstance(coll, OQuotient) and coll.equiv_class == 'perm':
                return OFold(term.op_name, init, coll.inner, body_fn=None)

        return OFold(term.op_name, init, coll, body_fn=term.body_fn)
    if isinstance(term, OFix):
        return OFix(term.name, _phase4_hof(term.body))
    if isinstance(term, OSeq):
        return OSeq(tuple(_phase4_hof(e) for e in term.elements))
    if isinstance(term, OQuotient):
        return OQuotient(_phase4_hof(term.inner), term.equiv_class)
    if isinstance(term, OLam):
        return OLam(term.params, _phase4_hof(term.body))
    if isinstance(term, ODict):
        return ODict(tuple((_phase4_hof(k), _phase4_hof(v)) for k, v in term.pairs))
    if isinstance(term, OCatch):
        return OCatch(_phase4_hof(term.body), _phase4_hof(term.default))
    return term


# ── Absorption law lookup table (Theorem 14.7) ──
_ABSORPTION: Dict[tuple, str] = {
    ('sorted', 'list'): 'sorted',
    ('sorted', 'tuple'): 'sorted',
    ('sorted', 'set'): 'sorted',
    ('sorted', 'frozenset'): 'sorted',
    ('sorted', 'sorted'): 'sorted',
    ('sorted', 'reversed'): 'sorted',
    ('list', 'list'): 'list',
    ('list', 'sorted'): 'sorted',
    ('list', 'reversed'): 'reversed',
    ('len', 'list'): 'len',
    ('len', 'tuple'): 'len',
    ('len', 'sorted'): 'len',
    ('len', 'reversed'): 'len',
    ('set', 'list'): 'set',
    ('set', 'tuple'): 'set',
    ('set', 'set'): 'set',
    ('sum', 'list'): 'sum',
    ('sum', 'tuple'): 'sum',
    ('sum', 'sorted'): 'sum',
    ('sum', 'reversed'): 'sum',
    ('min', 'list'): 'min',
    ('min', 'tuple'): 'min',
    ('min', 'sorted'): 'min',
    ('min', 'reversed'): 'min',
    ('max', 'list'): 'max',
    ('max', 'tuple'): 'max',
    ('max', 'sorted'): 'max',
    ('max', 'reversed'): 'max',
    ('any', 'list'): 'any',
    ('any', 'tuple'): 'any',
    ('all', 'list'): 'all',
    ('all', 'tuple'): 'all',
    ('tuple', 'list'): 'tuple',
    ('tuple', 'tuple'): 'tuple',
}


def _try_absorb(outer: str, inner: str) -> Optional[str]:
    """Apply an absorption law if one matches."""
    return _ABSORPTION.get((outer, inner))


def _compose_lam(f: OLam, g: OLam) -> OLam:
    """Compose two unary OLam: f ∘ g = λx. f(g(x))."""
    z = '_composed_0'
    inner_applied = _subst_term(g.body, g.params[0], OVar(z))
    composed_body = _subst_term(f.body, f.params[0], inner_applied)
    return OLam((z,), composed_body)


def _phase5_unify(term: OTerm) -> OTerm:
    """Phase 5: Shared symbol unification — the 24 dichotomies as rewrite rules."""
    if isinstance(term, OOp):
        args = tuple(_phase5_unify(a) for a in term.args)
        name = term.name

        # ── D19: heapq ↔ sorted ──
        # heapq.nsmallest(n, xs) → sorted(xs)[:n]
        # heapq.nsmallest(len(xs), xs) → sorted(xs) (full sort)
        if name == 'heapq.nsmallest' and len(args) == 2:
            n_arg, xs_arg = args
            if (isinstance(n_arg, OOp) and n_arg.name == 'len' and
                len(n_arg.args) == 1 and n_arg.args[0].canon() == xs_arg.canon()):
                return OOp('sorted', (xs_arg,))
            return OOp('sorted_slice', (xs_arg, n_arg))
        if name == 'heapq.nlargest' and len(args) == 2:
            n_arg, xs_arg = args
            if (isinstance(n_arg, OOp) and n_arg.name == 'len' and
                len(n_arg.args) == 1 and n_arg.args[0].canon() == xs_arg.canon()):
                return OOp('sorted_rev', (xs_arg,))
            return OOp('sorted_rev_slice', (xs_arg, n_arg))
        # Simple unification
        unify_map = {
            'heapq.nsmallest': 'sorted',
            'heapq.nlargest': 'sorted_rev',
        }
        if name in unify_map:
            return OOp(unify_map[name], args)

        # ── D13: Counter ↔ defaultdict counting ──
        if name in ('Counter', 'defaultdict'):
            return OOp('counter', args)

        # ── D16: dict.fromkeys ↔ dict comprehension ──
        if name == 'dict.fromkeys':
            return OOp('dict_from_iter', args)

        # ── D6: Generator ↔ Eager ──
        # NOTE: tuple and list are NOT interchangeable as return types
        # (tuple != list). Only unify when used inside sorted/etc.

        # ── D14 (monograph): OrderedDict ↔ dict (Python 3.7+) ──
        if name == 'OrderedDict':
            return OOp('dict', args)

        # ── D12: defaultdict(type) ↔ setdefault ──
        # Both implement "get-or-create-default" — unify to canonical form
        if name == '.setdefault!' and len(args) >= 2:
            return OOp('.get_or_default!', args)
        if name == 'defaultdict' and len(args) == 1:
            # defaultdict(factory) — keep as counter if factory is int
            pass  # already handled above for Counter

        # ── D14 (monograph): Array ↔ Dict table ──
        # list[i] and dict[i] both compile to getitem — already unified
        # by the compiler. But ensure subscript operations on local
        # variables with different names get unified.

        # ── D22: try/except ↔ conditional ──
        # try/except compiles to bottom-catching; this is handled in
        # compilation. At OTerm level, case(is_bottom(x), default, x)
        # is equivalent to case(guard, default, x) when guard implies
        # is_bottom(x). The key rule: flatten try bodies that test for
        # errors into equivalent conditionals.

        # ── D24: lambda ↔ named function ──
        # Both should compile to the same inlined body via D2 (β-reduction).
        # At OTerm level, no special rule needed if compilation handles it.
        # But if lambda wasn't inlined, it's OUnknown('lambda') — we can't
        # do much, but we should at least not false-positive on it.

        # ── D10: heapq ↔ bisect (ADT abstraction) ──
        # Both implement priority queue — unify operation names
        if name == 'bisect.insort' and len(args) >= 2:
            return OOp('pq_insert', args)
        if name == 'heapq.heappush' and len(args) >= 2:
            return OOp('pq_insert', args)
        if name == 'heapq.heappop' and len(args) >= 1:
            return OOp('pq_extract_min', args)
        if name == '.pop!' and len(args) >= 1:
            # .pop(0) is extract-min on a sorted structure
            if len(args) >= 2 and isinstance(args[1], OLit) and args[1].value == 0:
                return OOp('pq_extract_min', (args[0],))

        # ── D9: Stack ↔ Recursion (defunctionalization) ──
        # Both compute the same tree catamorphism. At OTerm level,
        # a while-loop over stack.pop()/stack.append() with a
        # commutative combine is equivalent to recursive traversal.
        # This is captured by fold key matching when both normalize
        # to the same accumulation pattern.

        # ── Mutation-pure bridges at unification level ──
        # .sort!() already → sorted in compilation
        # .reverse!() already → reversed in compilation
        # .append!(x) + final return ≡ concat

        # ── Local variable method call normalization ──
        KNOWN_MODULES = frozenset({
            'math', 'operator', 'functools', 'itertools', 'collections',
            'heapq', 'bisect', 'copy', 'json', 're', 'hashlib', 'struct',
            'sys', 'os', 'io', 'contextlib', 'textwrap', 'csv', 'inspect',
            'typing', 'string', 'itertools', 'collections',
        })
        if '.' in name and not name.startswith('.'):
            prefix = name.split('.')[0]
            if prefix not in KNOWN_MODULES:
                suffix = name[len(prefix):]
                return OOp(f'_L{suffix}', args)

        return OOp(name, args)

    if isinstance(term, OCase):
        return OCase(_phase5_unify(term.test),
                     _phase5_unify(term.true_branch),
                     _phase5_unify(term.false_branch))
    if isinstance(term, OFold):
        bfn = _phase5_unify(term.body_fn) if term.body_fn else None
        return OFold(term.op_name, _phase5_unify(term.init),
                     _phase5_unify(term.collection), body_fn=bfn)
    if isinstance(term, OFix):
        return OFix(term.name, _phase5_unify(term.body))
    if isinstance(term, OSeq):
        return OSeq(tuple(_phase5_unify(e) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((_phase5_unify(k), _phase5_unify(v))
                          for k, v in term.pairs))
    if isinstance(term, OQuotient):
        return OQuotient(_phase5_unify(term.inner), term.equiv_class)
    return term


def _phase6_quotient(term: OTerm) -> OTerm:
    """Phase 6: Quotient type normalization for nondeterminism.

    Implements the quotient type construction from the monograph:
    For nondeterministic operations (set/dict iteration, concurrent results),
    quotient by the permutation group to normalize away ordering.
    """
    if isinstance(term, OQuotient):
        inner = _phase6_quotient(term.inner)
        # Q[perm](sorted(x)) → sorted(x) (sorting resolves nondeterminism)
        if isinstance(inner, OOp) and inner.name in ('sorted', 'sorted_key',
                                                       'sorted_rev', 'sorted_key_rev'):
            return inner
        # Q[perm](Q[perm](x)) → Q[perm](x) (idempotent)
        if isinstance(inner, OQuotient) and inner.equiv_class == term.equiv_class:
            return inner
        return OQuotient(inner, term.equiv_class)

    if isinstance(term, OOp):
        args = tuple(_phase6_quotient(a) for a in term.args)
        name = term.name

        # sorted() applied to a quotient resolves the nondeterminism
        if name in ('sorted', 'sorted_key') and len(args) >= 1:
            if isinstance(args[0], OQuotient) and args[0].equiv_class == 'perm':
                return OOp(name, (args[0].inner,) + args[1:])

        # set operations produce quotient results
        if name in ('set', 'frozenset') and not isinstance(term, OQuotient):
            return OQuotient(OOp(name, args), 'perm')

        return OOp(name, args)

    if isinstance(term, OCase):
        return OCase(_phase6_quotient(term.test),
                     _phase6_quotient(term.true_branch),
                     _phase6_quotient(term.false_branch))
    if isinstance(term, OFold):
        bfn = _phase6_quotient(term.body_fn) if term.body_fn else None
        return OFold(term.op_name, _phase6_quotient(term.init),
                     _phase6_quotient(term.collection), body_fn=bfn)
    if isinstance(term, OFix):
        return OFix(term.name, _phase6_quotient(term.body))
    if isinstance(term, OSeq):
        return OSeq(tuple(_phase6_quotient(e) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((_phase6_quotient(k), _phase6_quotient(v))
                          for k, v in term.pairs))
    return term


# ── Phase 7: Piecewise Case Normalization ────────────────

def _phase7_piecewise(term: OTerm) -> OTerm:
    """Phase 7: Normalize nested case chains into canonical piecewise form.

    A nested case(c1, v1, case(c2, v2, v3)) represents a piecewise function.
    Two piecewise functions over the same domain partition are equivalent
    regardless of guard ordering.  This phase:
      1. Flattens linear case chains to (guard, value) pieces
      2. Infers the implicit else-guard from comparison algebra
      3. Sorts pieces canonically by (value, guard)
      4. Reconstructs the case chain

    This is the OTerm-level implementation of the sheaf-theoretic insight:
    sections that agree on every fiber are equal, regardless of how the
    cover is enumerated.
    """
    if isinstance(term, OCase):
        # Try to flatten and canonicalize
        result = _try_canonicalize_piecewise(term)
        if result is not None:
            return result
        # Can't canonicalize — recurse into sub-terms
        return OCase(
            _phase7_piecewise(term.test),
            _phase7_piecewise(term.true_branch),
            _phase7_piecewise(term.false_branch)
        )

    if isinstance(term, OOp):
        return OOp(term.name, tuple(_phase7_piecewise(a) for a in term.args))
    if isinstance(term, OFold):
        bfn = _phase7_piecewise(term.body_fn) if term.body_fn else None
        return OFold(term.op_name, _phase7_piecewise(term.init),
                     _phase7_piecewise(term.collection), body_fn=bfn)
    if isinstance(term, OFix):
        return OFix(term.name, _phase7_piecewise(term.body))
    if isinstance(term, OSeq):
        return OSeq(tuple(_phase7_piecewise(e) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((_phase7_piecewise(k), _phase7_piecewise(v))
                          for k, v in term.pairs))
    if isinstance(term, OQuotient):
        return OQuotient(_phase7_piecewise(term.inner), term.equiv_class)
    if isinstance(term, OAbstract):
        return OAbstract(term.spec, tuple(_phase7_piecewise(a) for a in term.inputs))
    return term


def _try_canonicalize_piecewise(term: OCase) -> Optional[OTerm]:
    """Try to canonicalize a linear case chain.

    Returns None if the chain can't be canonicalized (non-linear,
    mixed guard types, etc.)
    """
    # Step 1: Flatten the case chain
    pieces = _flatten_case_chain(term)
    if pieces is None or len(pieces) < 2:
        return None

    guards = [g for g, _ in pieces if g is not None]
    else_val = pieces[-1][1]  # last piece has None guard

    # Step 2: Check if all guards are comparisons on the same variable
    cmp_info = _extract_comparison_family(guards)
    if cmp_info is None:
        return None

    var_canon, comparisons = cmp_info

    # Step 3: Compute the implicit else-guard
    else_guard = _infer_complement_guard(comparisons, var_canon)
    if else_guard is None:
        return None

    # Step 4: Build full (guard, value) list with explicit else-guard
    full_pieces = [(g, v) for g, v in pieces if g is not None]
    full_pieces.append((else_guard, else_val))

    # Step 5: Sort by (value.canon(), guard.canon()) for canonical form
    full_pieces.sort(key=lambda p: (p[1].canon(), p[0].canon()))

    # Step 6: Reconstruct as a case chain (last piece becomes else)
    result = full_pieces[-1][1]
    for guard, val in reversed(full_pieces[:-1]):
        result = OCase(guard, val, result)

    return result


def _flatten_case_chain(term: OCase) -> Optional[list]:
    """Flatten a linear case chain into [(guard, value), ..., (None, else_value)].

    Only flattens when the chain is linear (no case in true branches).
    """
    pieces = []
    current = term
    depth = 0
    while isinstance(current, OCase) and depth < 20:
        if isinstance(current.true_branch, OCase):
            return None  # not a linear chain
        pieces.append((current.test, current.true_branch))
        current = current.false_branch
        depth += 1
    pieces.append((None, current))  # else value
    if len(pieces) < 3:
        return None  # need at least 2 guards + else to be worth canonicalizing
    return pieces


def _extract_comparison_family(guards: list) -> Optional[tuple]:
    """Check if all guards are comparisons on the same variable and constants.

    Returns (var_canon, [(cmp_op, const_canon), ...]) or None.
    """
    if not guards:
        return None

    var_canon = None
    comparisons = []

    for g in guards:
        if not isinstance(g, OOp):
            return None
        if g.name not in ('lt', 'lte', 'gt', 'gte', 'eq', 'noteq'):
            return None
        if len(g.args) != 2:
            return None

        # One arg should be a variable, the other a constant
        a, b = g.args
        if isinstance(a, OVar) and isinstance(b, OLit):
            v_canon = a.canon()
            c_canon = b.canon()
        elif isinstance(b, OVar) and isinstance(a, OLit):
            # Flip: const op var → var flipped_op const
            v_canon = b.canon()
            c_canon = a.canon()
            g = OOp(_flip_cmp(g.name), (b, a))
        else:
            return None

        if var_canon is None:
            var_canon = v_canon
        elif var_canon != v_canon:
            return None  # different variables

        comparisons.append((g.name, c_canon, g))

    return var_canon, comparisons


def _flip_cmp(op: str) -> str:
    """Flip a comparison: lt(a,b) → gt(b,a)."""
    return {'lt': 'gt', 'gt': 'lt', 'lte': 'gte', 'gte': 'lte',
            'eq': 'eq', 'noteq': 'noteq'}.get(op, op)


def _complement_cmp(op: str) -> str:
    """Complement a comparison: lt → gte, eq → noteq, etc."""
    return {'lt': 'gte', 'gte': 'lt', 'gt': 'lte', 'lte': 'gt',
            'eq': 'noteq', 'noteq': 'eq'}.get(op, op)


def _infer_complement_guard(comparisons: list, var_canon: str) -> Optional[OTerm]:
    """Infer the complement guard for the else-branch.

    For integer comparisons on the same variable and constant(s):
    - {lt(x,c), eq(x,c)} → else = gt(x,c)
    - {gt(x,c), lt(x,c)} → else = eq(x,c)
    - {lt(x,c), gt(x,c)} → else = eq(x,c)
    - {gt(x,c), eq(x,c)} → else = lt(x,c)
    etc.
    """
    # Group by constant value
    by_const: Dict[str, list] = {}
    for op, const_canon, guard_term in comparisons:
        by_const.setdefault(const_canon, []).append((op, guard_term))

    if len(by_const) != 1:
        # Multiple constants — can still handle if they form a partition
        # but for now only handle single-constant families
        return None

    const_canon = list(by_const.keys())[0]
    ops = {op for op, _ in list(by_const.values())[0]}
    sample_guard = list(by_const.values())[0][0][1]

    # Extract the variable and constant OTerms from a sample guard
    var_term = sample_guard.args[0]
    const_term = sample_guard.args[1]

    # Determine the complement
    # {lt, eq} → gt; {gt, eq} → lt; {lt, gt} → eq
    # {lt} → gte; {gt} → lte; {eq} → noteq
    # {gte} → lt; {lte} → gt; {noteq} → eq
    all_strict = {'lt', 'eq', 'gt'}
    if ops == {'lt', 'eq'}:
        return OOp('gt', (var_term, const_term))
    if ops == {'gt', 'eq'}:
        return OOp('lt', (var_term, const_term))
    if ops == {'lt', 'gt'}:
        return OOp('eq', (var_term, const_term))
    if ops == {'lt'}:
        return OOp('gte', (var_term, const_term))
    if ops == {'gt'}:
        return OOp('lte', (var_term, const_term))
    if ops == {'eq'}:
        return OOp('noteq', (var_term, const_term))
    if ops == {'gte'}:
        return OOp('lt', (var_term, const_term))
    if ops == {'lte'}:
        return OOp('gt', (var_term, const_term))
    if ops == {'noteq'}:
        return OOp('eq', (var_term, const_term))

    return None


def _try_const_fold(name: str, args: list):
    """Try to constant-fold an operation."""
    try:
        if name == 'add' and len(args) == 2:
            return args[0] + args[1]
        if name == 'sub' and len(args) == 2:
            return args[0] - args[1]
        if name == 'mult' and len(args) == 2:
            return args[0] * args[1]
        if name == 'floordiv' and len(args) == 2 and args[1] != 0:
            return args[0] // args[1]
        if name == 'mod' and len(args) == 2 and args[1] != 0:
            return args[0] % args[1]
        if name == 'u_usub' and len(args) == 1:
            return -args[0]
        if name == 'u_not' and len(args) == 1:
            return not args[0]
        if name == 'eq' and len(args) == 2:
            return args[0] == args[1]
        if name == 'noteq' and len(args) == 2:
            return args[0] != args[1]
        if name == 'lt' and len(args) == 2:
            return args[0] < args[1]
        if name == 'lte' and len(args) == 2:
            return args[0] <= args[1]
        if name == 'gt' and len(args) == 2:
            return args[0] > args[1]
        if name == 'gte' and len(args) == 2:
            return args[0] >= args[1]
        if name == 'ord' and len(args) == 1 and isinstance(args[0], str) and len(args[0]) == 1:
            return ord(args[0])
        if name == 'chr' and len(args) == 1 and isinstance(args[0], int) and 0 <= args[0] <= 0x10FFFF:
            return chr(args[0])
        if name == 'len' and len(args) == 1 and isinstance(args[0], str):
            return len(args[0])
        if name == 'pow' and len(args) == 2:
            return args[0] ** args[1]
        if name == 'abs' and len(args) == 1 and isinstance(args[0], (int, float)):
            return abs(args[0])
        if name == 'comb' and len(args) == 2:
            if isinstance(args[0], int) and isinstance(args[1], int):
                import math
                return math.comb(args[0], args[1])
        if name == 'factorial' and len(args) == 1 and isinstance(args[0], int):
            import math
            if 0 <= args[0] <= 20:
                return math.factorial(args[0])
    except Exception:
        pass
    return None


def _de_bruijn_normalize(term: OTerm, _counter: list | None = None) -> OTerm:
    """Normalize all bound variables in OLam to de Bruijn-style names (_b0, _b1, ...).

    Uses a depth-based naming scheme: each lambda's bound variables are named
    _b{depth}_{index} where depth is the lambda nesting level. This ensures
    alpha-equivalent terms always get the same names regardless of compilation
    order or eliminated lambdas.
    """
    return _de_bruijn_impl(term, depth=0)


def _de_bruijn_impl(term: OTerm, depth: int) -> OTerm:
    """Internal de Bruijn normalization with depth tracking."""
    if isinstance(term, OLam):
        mapping = {}
        new_params = []
        for i, p in enumerate(term.params):
            name = f'_b{depth}_{i}' if len(term.params) > 1 else f'_b{depth}'
            mapping[p] = name
            new_params.append(name)
        normalized_body = _subst(term.body, mapping)
        normalized_body = _de_bruijn_impl(normalized_body, depth + 1)
        return OLam(tuple(new_params), normalized_body)
    if isinstance(term, OOp):
        return OOp(term.name, tuple(_de_bruijn_impl(a, depth) for a in term.args))
    if isinstance(term, OCase):
        return OCase(_de_bruijn_impl(term.test, depth),
                     _de_bruijn_impl(term.true_branch, depth),
                     _de_bruijn_impl(term.false_branch, depth))
    if isinstance(term, OFold):
        bfn = _de_bruijn_impl(term.body_fn, depth) if term.body_fn else None
        return OFold(term.op_name, _de_bruijn_impl(term.init, depth),
                     _de_bruijn_impl(term.collection, depth), body_fn=bfn)
    if isinstance(term, OFix):
        # Alpha-normalize fix-point names so fix[max_depth](...) ≡ fix[depth](...)
        # Use a sentinel to break circularity, normalize body, then hash for canonical name.
        sentinel = '$__REC__'
        body_with_sentinel = _subst(term.body, {term.name: sentinel})
        normalized_body = _de_bruijn_impl(body_with_sentinel, depth)
        # Hash the normalized body to create a canonical fix name
        import hashlib
        body_hash = hashlib.md5(normalized_body.canon().encode()).hexdigest()[:8]
        canonical_fix_name = f'_fix_{body_hash}'
        # Replace sentinel with the canonical name
        final_body = _subst(normalized_body, {sentinel: canonical_fix_name})
        return OFix(canonical_fix_name, final_body)
    if isinstance(term, OSeq):
        return OSeq(tuple(_de_bruijn_impl(e, depth) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((_de_bruijn_impl(k, depth), _de_bruijn_impl(v, depth))
                          for k, v in term.pairs))
    if isinstance(term, OQuotient):
        return OQuotient(_de_bruijn_impl(term.inner, depth), term.equiv_class)
    if isinstance(term, OAbstract):
        return OAbstract(term.spec, tuple(_de_bruijn_impl(a, depth) for a in term.inputs))
    if isinstance(term, OMap):
        t = _de_bruijn_impl(term.transform, depth)
        c = _de_bruijn_impl(term.collection, depth)
        f = _de_bruijn_impl(term.filter_pred, depth) if term.filter_pred else None
        return OMap(t, c, f)
    if isinstance(term, OCatch):
        return OCatch(_de_bruijn_impl(term.body, depth),
                     _de_bruijn_impl(term.default, depth))
    return term


def _rehash_folds(term: OTerm) -> OTerm:
    """Rehash OFold op_names based on normalized body_fn canonical form.

    After full normalization + de Bruijn, body_fns are canonical.
    Two folds with the same body function, init, and collection
    should have the SAME op_name so their canon() strings match.

    Only rehashes source-level hash keys (8-char hex strings), NOT
    semantic keys like 'add', 'bitxor', 'or', etc. — those already
    carry meaningful algebraic information.
    """
    import re as _re
    _HEX_KEY = _re.compile(r'^[0-9a-f]{8}$')

    def _is_source_hash(key: str) -> bool:
        if bool(_HEX_KEY.match(key)) or key.startswith('coupled_fold|'):
            return True
        # OFix names have _fix_ prefix followed by a hex hash
        if key.startswith('_fix_') and bool(_HEX_KEY.match(key[5:])):
            return True
        # Search/coupled prefixes
        if key.startswith('search_') and bool(_HEX_KEY.match(key[7:])):
            return True
        return False

    if isinstance(term, OFold):
        init = _rehash_folds(term.init)
        coll = _rehash_folds(term.collection)
        bfn = _rehash_folds(term.body_fn) if term.body_fn else None
        if bfn is not None and _is_source_hash(term.op_name):
            # Always rehash from body_fn canon — it's more precise than
            # the AST-dump hash which loses mutation ordering
            body_canon = bfn.canon()
            new_hash = _hash(body_canon)
            return OFold(new_hash, init, coll, body_fn=bfn)
        return OFold(term.op_name, init, coll, body_fn=bfn)
    if isinstance(term, OOp):
        return OOp(term.name, tuple(_rehash_folds(a) for a in term.args))
    if isinstance(term, OCase):
        return OCase(_rehash_folds(term.test),
                     _rehash_folds(term.true_branch),
                     _rehash_folds(term.false_branch))
    if isinstance(term, OFix):
        new_body = _rehash_folds(term.body)
        if _is_source_hash(term.name):
            new_hash = _hash(new_body.canon())
            # Preserve _fix_ prefix for OFix names
            if term.name.startswith('_fix_'):
                new_hash = f'_fix_{new_hash}'
            return OFix(new_hash, new_body)
        return OFix(term.name, new_body)
    if isinstance(term, OSeq):
        return OSeq(tuple(_rehash_folds(e) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((_rehash_folds(k), _rehash_folds(v))
                          for k, v in term.pairs))
    if isinstance(term, OQuotient):
        return OQuotient(_rehash_folds(term.inner), term.equiv_class)
    if isinstance(term, OAbstract):
        return OAbstract(term.spec, tuple(_rehash_folds(a) for a in term.inputs))
    if isinstance(term, OMap):
        t = _rehash_folds(term.transform)
        c = _rehash_folds(term.collection)
        f = _rehash_folds(term.filter_pred) if term.filter_pred else None
        return OMap(t, c, f)
    if isinstance(term, OCatch):
        return OCatch(_rehash_folds(term.body), _rehash_folds(term.default))
    if isinstance(term, OLam):
        return OLam(term.params, _rehash_folds(term.body))
    return term


# ═══════════════════════════════════════════════════════════
# Equivalence via Canonical Forms
# ═══════════════════════════════════════════════════════════

def _collect_op_names(term: OTerm) -> set:
    """Collect all operation names in a term."""
    result = set()
    if isinstance(term, OOp):
        result.add(term.name)
        for a in term.args:
            result |= _collect_op_names(a)
    elif isinstance(term, OCase):
        result |= _collect_op_names(term.test) | _collect_op_names(term.true_branch) | _collect_op_names(term.false_branch)
    elif isinstance(term, OFold):
        result |= _collect_op_names(term.init) | _collect_op_names(term.collection)
    elif isinstance(term, OFix):
        result |= _collect_op_names(term.body)
    elif isinstance(term, OSeq):
        for e in term.elements:
            result |= _collect_op_names(e)
    elif isinstance(term, OQuotient):
        result |= _collect_op_names(term.inner)
    return result


def _collect_vars(term: OTerm) -> set:
    """Collect all free variable names referenced in a term."""
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, OOp):
        s = set()
        for a in term.args:
            s |= _collect_vars(a)
        return s
    if isinstance(term, OCase):
        return _collect_vars(term.test) | _collect_vars(term.true_branch) | _collect_vars(term.false_branch)
    if isinstance(term, OFold):
        s = _collect_vars(term.init) | _collect_vars(term.collection)
        if term.body_fn is not None:
            s |= _collect_vars(term.body_fn)
        return s
    if isinstance(term, OFix):
        body_vars = _collect_vars(term.body)
        # Fix-point state variables ($0, $1, ...) are bound by the
        # OFix construct — they should not appear as free variables.
        state_vars = {v for v in body_vars
                      if v.startswith('$') and v[1:].isdigit()}
        return body_vars - state_vars
    if isinstance(term, OSeq):
        s = set()
        for e in term.elements:
            s |= _collect_vars(e)
        return s
    if isinstance(term, ODict):
        s = set()
        for k, v in term.pairs:
            s |= _collect_vars(k) | _collect_vars(v)
        return s
    if isinstance(term, OQuotient):
        return _collect_vars(term.inner)
    if isinstance(term, OLam):
        return _collect_vars(term.body) - set(term.params)
    if isinstance(term, OMap):
        s = _collect_vars(term.transform) | _collect_vars(term.collection)
        if term.filter_pred is not None:
            s |= _collect_vars(term.filter_pred)
        return s
    if isinstance(term, OCatch):
        return _collect_vars(term.body) | _collect_vars(term.default)
    return set()


def _collect_unknowns(term: OTerm) -> set:
    """Collect all OUnknown descriptions in a term."""
    if isinstance(term, OUnknown):
        return {term.desc}
    result = set()
    if isinstance(term, OOp):
        for a in term.args:
            result |= _collect_unknowns(a)
    elif isinstance(term, OCase):
        result = _collect_unknowns(term.test) | _collect_unknowns(term.true_branch) | _collect_unknowns(term.false_branch)
    elif isinstance(term, OFold):
        result = _collect_unknowns(term.init) | _collect_unknowns(term.collection)
    elif isinstance(term, OFix):
        result = _collect_unknowns(term.body)
    elif isinstance(term, OSeq):
        for e in term.elements:
            result |= _collect_unknowns(e)
    elif isinstance(term, ODict):
        for k, v in term.pairs:
            result |= _collect_unknowns(k) | _collect_unknowns(v)
    elif isinstance(term, OQuotient):
        result = _collect_unknowns(term.inner)
    elif isinstance(term, OAbstract):
        for a in term.inputs:
            result |= _collect_unknowns(a)
    elif isinstance(term, OLam):
        result = _collect_unknowns(term.body)
    elif isinstance(term, OMap):
        result = _collect_unknowns(term.transform) | _collect_unknowns(term.collection)
        if term.filter_pred is not None:
            result |= _collect_unknowns(term.filter_pred)
    elif isinstance(term, OCatch):
        result = _collect_unknowns(term.body) | _collect_unknowns(term.default)
    return result


# Structural unknowns that indicate the OTerm may be semantically incomplete
_STRUCTURAL_UNKNOWNS = frozenset({
    'Starred', 'no_return', 'reduce_no_init', 'empty_comp', 'lambda',
    'ListComp', 'SetComp', 'DictComp', 'GeneratorExp', 'Yield',
})


def _contains_unknown(term: OTerm) -> bool:
    """Check if a term contains any OUnknown nodes."""
    if isinstance(term, OUnknown):
        return True
    if isinstance(term, OOp):
        return any(_contains_unknown(a) for a in term.args)
    if isinstance(term, OCase):
        return (_contains_unknown(term.test) or
                _contains_unknown(term.true_branch) or
                _contains_unknown(term.false_branch))
    if isinstance(term, OFold):
        return _contains_unknown(term.init) or _contains_unknown(term.collection)
    if isinstance(term, OFix):
        return _contains_unknown(term.body)
    if isinstance(term, OSeq):
        return any(_contains_unknown(e) for e in term.elements)
    if isinstance(term, ODict):
        return any(_contains_unknown(k) or _contains_unknown(v) for k, v in term.pairs)
    if isinstance(term, OQuotient):
        return _contains_unknown(term.inner)
    if isinstance(term, OAbstract):
        return any(_contains_unknown(a) for a in term.inputs)
    if isinstance(term, OLam):
        return _contains_unknown(term.body)
    if isinstance(term, OMap):
        return (_contains_unknown(term.transform) or
                _contains_unknown(term.collection) or
                (term.filter_pred is not None and _contains_unknown(term.filter_pred)))
    if isinstance(term, OCatch):
        return _contains_unknown(term.body) or _contains_unknown(term.default)
    return False


def extract_abstract_spec(term: OTerm) -> Optional[str]:
    """Extract an abstract specification from a normalized OTerm.

    This looks for high-level patterns that characterize what the function
    does, independent of implementation details:
    - "sort input by key K" (covers sorted(), .sort(), heapq, quicksort, etc.)
    - "accumulate over input with op" (covers for-loop, reduce, recursion)
    - "filter input by predicate P" (covers comprehension, filter(), for+if)
    - "transform input element-wise" (covers map, comprehension, for-loop)
    - "flatten nested structure" (covers recursive, iterative, chain.from_iterable)
    """
    if isinstance(term, OOp):
        name = term.name
        # sorted(fold(...)) → "sort-accumulate" pattern
        if name in ('sorted', 'sorted_key', 'sorted_rev', 'sorted_key_rev'):
            inner = term.args[0] if term.args else None
            if inner is not None:
                inner_spec = extract_abstract_spec(inner)
                if inner_spec:
                    return f'sort({inner_spec})'
                return f'sort(input)'
        # fold patterns
        if isinstance(term.args[0] if term.args else None, OFold):
            fold = term.args[0]
            return f'{name}(fold[{fold.op_name}])'
    if isinstance(term, OFold):
        return f'fold[{term.op_name}]'
    if isinstance(term, OFix):
        return f'fix[{term.name}]'
    if isinstance(term, OCase):
        t_spec = extract_abstract_spec(term.true_branch)
        f_spec = extract_abstract_spec(term.false_branch)
        if t_spec and f_spec:
            return f'case({t_spec},{f_spec})'
    return None


def denotational_equiv(source_f: str, source_g: str) -> Optional[bool]:
    """Check equivalence via denotational canonical forms.

    Multi-strategy approach:
    1. Exact canonical form match after normalization → True
    2. Structural similarity with quotient type unification → True
    3. Provable difference detection (with duck-typed fibers) → False
    4. Otherwise → None (inconclusive)

    Returns True/False/None.
    """
    rf = compile_to_oterm(source_f)
    rg = compile_to_oterm(source_g)

    if rf is None or rg is None:
        return None

    term_f, params_f = rf
    term_g, params_g = rg

    if len(params_f) != len(params_g):
        return None

    # Normalize parameter names
    term_f = _rename_params(term_f, params_f)
    term_g = _rename_params(term_g, params_g)

    # Strategy 1: Exact canonical form match
    nf_f = normalize(term_f)
    nf_g = normalize(term_g)

    cf = nf_f.canon()
    cg = nf_g.canon()

    # Extract duck types once — used by path search (Strategy 2.5)
    # and provable NEQ (Strategy 3) for fiber-aware decisions.
    param_duck_types: Dict[str, str] = {}
    try:
        from .duck import infer_duck_type
        tree_f = ast.parse(source_f)
        tree_g = ast.parse(source_g)
        func_f_node = func_g_node = None
        for node in ast.walk(tree_f):
            if isinstance(node, ast.FunctionDef):
                func_f_node = node
                break
        for node in ast.walk(tree_g):
            if isinstance(node, ast.FunctionDef):
                func_g_node = node
                break
        if func_f_node and func_g_node:
            for i, pname in enumerate(params_f):
                orig_f = func_f_node.args.args[i].arg if i < len(func_f_node.args.args) else pname
                dt, _ = infer_duck_type(func_f_node, func_g_node, orig_f)
                param_duck_types[f'p{i}'] = dt
    except Exception:
        pass

    if cf == cg:
        # Don't trust matches containing OUnknown — they represent
        # things we couldn't compile, so matching them is unsound.
        if _contains_unknown(nf_f) or _contains_unknown(nf_g):
            return None
        # Don't trust trivially small canonical forms — they likely
        # lost important information during compilation.
        # Exception: constant values (OLit, empty OSeq, empty ODict) are
        # fully determined — if both reduce to the same constant, match.
        is_const = (isinstance(nf_f, OLit) or
                    (isinstance(nf_f, OSeq) and len(nf_f.elements) == 0) or
                    (isinstance(nf_f, ODict) and len(nf_f.pairs) == 0))
        if len(cf) < 20 and not is_const:
            # Some small forms ARE genuine: reversed, sorted, abs, len
            # are well-defined mathematical operations that fully
            # characterize the program's behavior. Only reject truly
            # trivial forms where the compiler might have lost information.
            _meaningful_small = isinstance(nf_f, OOp) and nf_f.name in (
                'reversed', 'sorted', 'abs', 'len', 'set', 'tuple', 'list',
                'str', 'int', 'float', 'bool', 'frozenset', 'chr', 'ord',
                'popcount', 'digit_sum', 'reverse_digits', 'gcd',
                'dict', 'zip', 'enumerate', 'map', 'filter',
                'deepcopy', 'hash', 'id', 'type', 'min', 'max', 'sum',
                'factorial', 'comb', 'perm',
            )
            # Compound term (nested OOps) is meaningful — it's
            # specific enough to characterize behavior (e.g. dict(zip(a,b)))
            if not _meaningful_small and isinstance(nf_f, OOp):
                if any(isinstance(a, OOp) for a in nf_f.args):
                    _meaningful_small = True
            # OFold with a known op over a parameter is meaningful
            # (e.g., fold[bitxor](0, $p0) fully characterizes XOR reduction)
            if not _meaningful_small and isinstance(nf_f, OFold):
                _meaningful_small = True
            # Arithmetic ops with at least one constant arg are meaningful
            # (e.g., add($p0, 1) fully characterizes increment)
            if (not _meaningful_small and isinstance(nf_f, OOp)
                    and nf_f.name in ('add', 'sub', 'mult', 'mod', 'floordiv',
                                      'truediv', 'pow', 'bitand', 'bitor',
                                      'bitxor', 'lshift', 'rshift')
                    and any(isinstance(a, OLit) for a in nf_f.args)):
                _meaningful_small = True
            # OSeq of OVars is meaningful — it's a specific permutation
            # or selection of parameters (e.g., [$p1, $p0] = swap)
            if not _meaningful_small and isinstance(nf_f, OSeq):
                if all(isinstance(e, OVar) for e in nf_f.elements):
                    _meaningful_small = True
            if not _meaningful_small:
                return None
        # Don't trust if the term is just a single operation on params
        # — many different programs reduce to the same simple form
        # UNLESS it's a semantically meaningful operation (reversed, sorted, etc.)
        if isinstance(nf_f, OOp) and all(isinstance(a, OVar) for a in nf_f.args):
            if nf_f.name not in (
                'reversed', 'sorted', 'abs', 'len', 'set', 'tuple', 'list',
                'str', 'int', 'float', 'bool', 'frozenset', 'chr', 'ord',
                'popcount', 'digit_sum', 'reverse_digits', 'gcd',
                'factorial', 'comb', 'perm',
            ):
                return None
        # Don't trust if the term references non-parameter variables
        # — these are unresolved locals that lost information
        f_vars = _collect_vars(nf_f)
        g_vars = _collect_vars(nf_g)
        param_names = {f'p{i}' for i in range(len(params_f))}
        if (f_vars - param_names) or (g_vars - param_names):
            return None
        # If the function takes parameters but the term doesn't reference
        # any of them, the compiler lost the connection between inputs and
        # output — the term only captures a "wrapper" pattern (e.g.
        # dict(sorted(X.items()))) without the actual computation.
        # Such matches are unreliable.
        if len(params_f) > 0 and not (f_vars & param_names):
            return None
        # Zero-arg functions with method calls or constructors in the
        # canonical form may involve aliasing/mutation that the compiler
        # can't track. Defer to the checker for these.
        if len(params_f) == 0:
            def _has_method_or_constructor(t):
                if isinstance(t, OOp):
                    if t.name.startswith('.') or t.name[0].isupper():
                        return True
                    return any(_has_method_or_constructor(a) for a in t.args)
                if isinstance(t, OSeq):
                    return any(_has_method_or_constructor(e) for e in t.elements)
                if isinstance(t, OFold):
                    return _has_method_or_constructor(t.init) or _has_method_or_constructor(t.collection)
                if isinstance(t, OCase):
                    return (_has_method_or_constructor(t.test) or
                            _has_method_or_constructor(t.true_branch) or
                            _has_method_or_constructor(t.false_branch))
                return False
            if _has_method_or_constructor(nf_f):
                return None
        # Check for unresolved names in operation names.
        f_ops = _collect_op_names(nf_f)
        g_ops = _collect_op_names(nf_g)
        if f_ops != g_ops:
            return None
        # Fold body_fn structural cross-check: the canonical form uses
        # a hash for fold bodies, which can be lossy (e.g., AugAssign
        # operator differences lost). When both folds have trustworthy
        # body_fn, compare them structurally to catch false matches.
        if not _flexible_match(nf_f, nf_g):
            return None
        return True

    # Strategy 2: Flexible matching — match terms that only differ
    # in OFix keys (while loop body hashes) but are otherwise identical.
    # Only if terms are non-trivial and don't contain unknowns.
    # Also requires parameter references (same gating as Strategy 1).
    if (not _contains_unknown(nf_f) and not _contains_unknown(nf_g)
            and len(cf) >= 10 and _flexible_match(nf_f, nf_g)):
        f_vars_2 = _collect_vars(nf_f)
        g_vars_2 = _collect_vars(nf_g)
        param_set_2 = {f'p{i}' for i in range(len(params_f))}
        has_params_2 = bool(f_vars_2 & param_set_2) and bool(g_vars_2 & param_set_2)
        has_nonparams_2 = bool(f_vars_2 - param_set_2) or bool(g_vars_2 - param_set_2)
        if has_params_2 and not has_nonparams_2:
            return True

    # Strategy 2.5: Path search (Ch.10) — Kan composition
    # When canonical forms don't match, search for a multi-step
    # rewrite path using the 24 dichotomy axioms.
    # Fiber-aware via sheaf descent (§2.6): duck types restrict axioms.
    if (not _contains_unknown(nf_f) and not _contains_unknown(nf_g)
            and len(cf) >= 10 and len(cg) >= 10):
        # Don't trust path search when terms lost parameter references
        f_vars = _collect_vars(nf_f)
        g_vars = _collect_vars(nf_g)
        param_set = {f'p{i}' for i in range(len(params_f))}
        has_params = bool(f_vars & param_set) and bool(g_vars & param_set)
        has_nonparams = bool(f_vars - param_set) or bool(g_vars - param_set)
        if has_params and not has_nonparams:
            try:
                from .path_search import search_path
                path_result = search_path(nf_f, nf_g, max_depth=3, max_frontier=150,
                                          param_duck_types=param_duck_types)
                if path_result.found is True:
                    return True
            except Exception:
                pass

    # Strategy 3: Provable difference detection
    # If both terms compiled cleanly (no unknowns) and they differ in
    # specific ways that are guaranteed to produce different results,
    # we can declare non-equivalence.
    # Uses duck types already extracted above for fiber-aware decisions.
    if not _contains_unknown(nf_f) and not _contains_unknown(nf_g):
        neq = _detect_provable_neq(nf_f, nf_g, params_f,
                                    param_duck_types=param_duck_types)
        if neq:
            return False

    return None


def has_cross_type_suspicion(source_f: str, source_g: str) -> bool:
    """Check if the two programs have cross-type OTerm structures.

    Returns True when the normalized OTerms have fundamentally different
    computational patterns (OFold vs OOp, OOp vs OCase, etc.).
    This is weaker than _detect_provable_neq — it indicates suspicion,
    not proof. Used by the checker to override BT EQ verdicts when
    structural analysis suggests the functions differ.
    """
    rf = compile_to_oterm(source_f)
    rg = compile_to_oterm(source_g)
    if rf is None or rg is None:
        return False
    term_f, params_f = rf
    term_g, params_g = rg
    if len(params_f) != len(params_g):
        return False
    term_f = _rename_params(term_f, params_f)
    term_g = _rename_params(term_g, params_g)
    nf_f = normalize(term_f)
    nf_g = normalize(term_g)
    if _contains_unknown(nf_f) or _contains_unknown(nf_g):
        return False
    return _has_cross_type(nf_f, nf_g)


def _has_cross_type(a: OTerm, b: OTerm) -> bool:
    """Detect cross-type structural differences between OTerms."""
    # OFold vs OOp (fold accumulation vs builtin operation)
    if isinstance(a, OFold) and isinstance(b, OOp):
        return True
    if isinstance(b, OFold) and isinstance(a, OOp):
        return True
    # OOp vs OMap (builtin vs map/comprehension)
    if isinstance(a, OOp) and isinstance(b, OMap):
        return True
    if isinstance(b, OOp) and isinstance(a, OMap):
        return True
    # OOp vs OCase (builtin vs conditional implementation)
    if isinstance(a, OOp) and isinstance(b, OCase):
        return True
    if isinstance(b, OOp) and isinstance(a, OCase):
        return True
    # OFold vs OCase (fold vs conditional)
    if isinstance(a, OFold) and isinstance(b, OCase):
        return True
    if isinstance(b, OFold) and isinstance(a, OCase):
        return True
    return False


def _has_effect(term: OTerm) -> bool:
    """Check if an OTerm contains an effect operation (§11.15).

    Effects are non-trivial H¹ classes on the heap fibration.
    A program with effects lives on a different fiber than a pure one.
    """
    if isinstance(term, OOp):
        if term.name.startswith('effect_'):
            return True
        return any(_has_effect(a) for a in term.args)
    if isinstance(term, OSeq):
        return any(_has_effect(e) for e in term.elements)
    if isinstance(term, OFold):
        return _has_effect(term.init) or _has_effect(term.collection)
    if isinstance(term, OCase):
        return (_has_effect(term.test) or _has_effect(term.true_branch)
                or _has_effect(term.false_branch))
    if isinstance(term, OMap):
        return _has_effect(term.transform) or _has_effect(term.collection)
    if isinstance(term, OLam):
        return _has_effect(term.body)
    if isinstance(term, OCatch):
        return _has_effect(term.body) or _has_effect(term.default)
    if isinstance(term, OQuotient):
        return _has_effect(term.inner)
    if isinstance(term, ODict):
        return any(_has_effect(k) or _has_effect(v) for k, v in term.pairs)
    return False


def _extract_params(term: OTerm) -> set:
    """Extract parameter names (p0, p1, ...) from an OTerm."""
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, OOp):
        result = set()
        for a in term.args:
            result |= _extract_params(a)
        return result
    if isinstance(term, OSeq):
        result = set()
        for e in term.elements:
            result |= _extract_params(e)
        return result
    if isinstance(term, OCase):
        return (_extract_params(term.test) | _extract_params(term.true_branch)
                | _extract_params(term.false_branch))
    if isinstance(term, OFold):
        return _extract_params(term.init) | _extract_params(term.collection)
    if isinstance(term, OMap):
        return _extract_params(term.transform) | _extract_params(term.collection)
    if isinstance(term, OLam):
        return _extract_params(term.body)
    if isinstance(term, OQuotient):
        return _extract_params(term.inner)
    if isinstance(term, ODict):
        result = set()
        for k, v in term.pairs:
            result |= _extract_params(k) | _extract_params(v)
        return result
    return set()


def _detect_provable_neq(a: OTerm, b: OTerm, params: List[str],
                         in_case_branch: bool = False,
                         param_duck_types: Optional[Dict[str, str]] = None) -> bool:
    """Detect provably non-equivalent OTerms.

    Returns True ONLY for differences that are guaranteed to produce
    different runtime behavior. Conservative — only catches clear cases.

    in_case_branch suppresses cross-type rules (OQuotient vs OOp, OOp vs OCase)
    because inside case branches, different structures can compute the same
    value under the guard's domain constraint.

    param_duck_types maps parameter names (p0, p1, ...) to duck-typed fibers
    (int, str, collection, etc.) from §3 duck type inference. Used to determine
    commutativity on the type fibration.
    """
    if param_duck_types is None:
        param_duck_types = {}

    # §11.15: Effect fiber — programs with different effect signatures
    # live on different fibers of the heap fibration → H¹ ≠ 0
    a_eff = _has_effect(a)
    b_eff = _has_effect(b)
    if a_eff != b_eff:
        return True

    # Different constant returns
    if isinstance(a, OLit) and isinstance(b, OLit):
        return a.value != b.value

    # One is a literal, other is a computation — different types
    if isinstance(a, OLit) and not isinstance(b, OLit):
        # OLit(None) vs anything non-None is definitely different
        if a.value is None:
            return True
    if isinstance(b, OLit) and not isinstance(a, OLit):
        if b.value is None:
            return True
    # OLit(True/False) vs OOp — only NEQ for specific operations we
    # KNOW can differ. In general, the OOp might always evaluate to
    # that boolean value but the compiler couldn't trace through.
    if isinstance(a, OLit) and isinstance(a.value, bool) and isinstance(b, OOp):
        # `is` is not equivalent to `eq` — is(x,x) can be False
        # for non-cached objects. So True vs is(x,x) is NEQ.
        if b.name == 'is' and a.value is True:
            return True
        if b.name == 'is' and a.value is False:
            return False  # is(x,x) can be True too
    if isinstance(b, OLit) and isinstance(b.value, bool) and isinstance(a, OOp):
        if a.name == 'is' and b.value is True:
            return True

    # Same operation but with swapped arguments on non-commutative ops
    if isinstance(a, OOp) and isinstance(b, OOp):
        if a.name == b.name and len(a.args) == len(b.args) == 2:
            # Non-commutative operations where argument order matters
            non_commutative = {'sub', 'isub', 'floordiv', 'truediv',
                               'mod', 'pow', 'lshift', 'rshift', 'getitem',
                               'concat', 'matmult', 'merge'}
            # add/iadd: commutative on int/float, non-commutative on str/list
            # Use duck typing (§3) to determine the fiber
            if a.name in ('add', 'iadd'):
                # Extract which params are involved in the operands
                involved = _extract_params(a)
                all_int = True
                for p in involved:
                    dt = param_duck_types.get(p, 'any')
                    if dt not in ('int', 'float', 'number'):
                        all_int = False
                        break
                if not all_int:
                    non_commutative.add(a.name)
            if a.name in non_commutative:
                # Check if args are swapped: f(a,b) vs f(b,a)
                if (a.args[0].canon() == b.args[1].canon() and
                    a.args[1].canon() == b.args[0].canon() and
                    a.args[0].canon() != a.args[1].canon()):
                    return True

        # Different comparison operators: eq vs is, noteq vs isnot
        # These are semantically different in Python
        comp_ops = {'eq', 'is', 'noteq', 'isnot', 'lt', 'lte', 'gt', 'gte',
                    'in_', 'notin'}
        if (a.name in comp_ops and b.name in comp_ops and a.name != b.name):
            if len(a.args) == len(b.args):
                if all(ai.canon() == bi.canon() for ai, bi in zip(a.args, b.args)):
                    return True

        # Same operation, different arguments — only recurse for comparison ops
        # where argument differences are semantically meaningful.
        # For general operations (add, mul, getitem, etc.), different sub-term
        # structure doesn't imply NEQ because different algorithms can compute
        # the same result.
        if a.name == b.name and len(a.args) == len(b.args):
            # Only recurse into comparisons and boolean ops where
            # sub-term differences are reliable NEQ indicators
            safe_to_recurse = a.name in comp_ops or a.name in {
                'not', 'u_not', 'and', 'or',
            }
            if safe_to_recurse:
                for ai, bi in zip(a.args, b.args):
                    if _detect_provable_neq(ai, bi, params, in_case_branch, param_duck_types):
                        return True

        # Same operation, different arity — extra args are non-default
        # e.g. enumerate(x) vs enumerate(x, 1): default start=0, 1≠0
        # e.g. split(s) vs split(s, ' '): different splitting behavior
        if a.name == b.name and len(a.args) != len(b.args):
            longer, shorter = (a, b) if len(a.args) > len(b.args) else (b, a)
            # Check that the common prefix matches
            prefix_ok = all(
                not _detect_provable_neq(ai, bi, params, in_case_branch, param_duck_types)
                for ai, bi in zip(shorter.args, longer.args[:len(shorter.args)])
            )
            if prefix_ok:
                extra = longer.args[len(shorter.args):]
                # Default values: 0, None, False, '', []
                _defaults = {'0', 'None', 'False', "''", '[]'}
                if any(x.canon() not in _defaults for x in extra):
                    return True

        # Generator vs list comprehension with same body hash —
        # semantically different because generators are lazy/single-use
        if len(a.args) == len(b.args):
            a_base = a.name.split('_')[0] if '_' in a.name else a.name
            b_base = b.name.split('_')[0] if '_' in b.name else b.name
            if ({a_base, b_base} == {'genexpr', 'comp'} or
                {a_base, b_base} == {'genexpr', 'setcomp'}):
                # Same hash suffix means same body — but genexpr != comp
                # because genexpr is consumed after first iteration
                a_hash = a.name.split('_', 1)[1] if '_' in a.name else ''
                b_hash = b.name.split('_', 1)[1] if '_' in b.name else ''
                if a_hash == b_hash and a_hash:
                    return True

        # Different root operation entirely
        # Only declare NEQ for ops that are KNOWN inverses/contradictions,
        # not for arbitrary different operations (which may compute
        # the same result via different algorithms).
        if a.name != b.name:
            # Known contradictions: sorted vs reversed, min vs max
            contradictions = {
                frozenset({'min', 'max'}),
                frozenset({'sorted', 'sorted_rev'}),
            }
            if frozenset({a.name, b.name}) in contradictions:
                a_args_c = tuple(x.canon() for x in a.args)
                b_args_c = tuple(x.canon() for x in b.args)
                if a_args_c == b_args_c and len(a_args_c) > 0:
                    return True

        # NOTE: Different op chains (a = op_a(var), b = op_b(op_c(var)))
        # are NOT necessarily NEQ — the outer context may equalize them.
        # Removed: this rule caused too many false NEQs on equivalent programs.

    # OVar vs OLit/OOp/OSeq — a variable vs a concrete value
    if isinstance(a, OVar) and isinstance(b, (OLit, OSeq)):
        return True
    if isinstance(b, OVar) and isinstance(a, (OLit, OSeq)):
        return True

    # Same sequence type — recurse into elements
    if isinstance(a, OSeq) and isinstance(b, OSeq):
        if len(a.elements) != len(b.elements):
            return True  # different-length tuples/lists
        for ai, bi in zip(a.elements, b.elements):
            if _detect_provable_neq(ai, bi, params, in_case_branch, param_duck_types):
                return True

    # Same fold structure — only recurse for matching named operations.
    # Different fold op hashes (e.g., fold[abc] vs fold[def]) do NOT
    # mean NEQ — the lambda bodies may compute the same thing.
    if isinstance(a, OFold) and isinstance(b, OFold):
        if a.op_name == b.op_name:
            # Same named operation — but only recurse into init/collection
            # when the collections have similar structure.  When the collections
            # are fundamentally different (e.g. map(capitalize, split(s))
            # vs fold[hash]([], s)), different init values don't prove NEQ
            # because the computation may embed structure differently
            # (e.g. join separator ' ' vs '' with spaces in elements).
            _colls_similar = type(a.collection).__name__ == type(b.collection).__name__
            if _colls_similar:
                if _detect_provable_neq(a.init, b.init, params, in_case_branch, param_duck_types):
                    return True
                if _detect_provable_neq(a.collection, b.collection, params, in_case_branch, param_duck_types):
                    return True
        # Different op names: could be hash-named lambdas computing the same thing
        # — don't declare NEQ

    # OMap — only check collection, not transform.
    # Different transforms (lambda bodies) can compute the same function,
    # e.g. map(lambda x,y: x*y, zip(a,b)) vs range-based indexing.
    if isinstance(a, OMap) and isinstance(b, OMap):
        if _detect_provable_neq(a.collection, b.collection, params, in_case_branch, param_duck_types):
            return True

    # OLam — different arity is NEQ; don't recurse into bodies
    # since different lambda implementations can compute the same function
    if isinstance(a, OLam) and isinstance(b, OLam):
        if len(a.params) != len(b.params):
            return True

    # OCatch — recurse into body and default
    if isinstance(a, OCatch) and isinstance(b, OCatch):
        if _detect_provable_neq(a.body, b.body, params, in_case_branch, param_duck_types):
            return True
        if _detect_provable_neq(a.default, b.default, params, in_case_branch, param_duck_types):
            return True

    # ODict — same keys, recurse into values
    if isinstance(a, ODict) and isinstance(b, ODict):
        if len(a.pairs) != len(b.pairs):
            return True
        for (ka, va), (kb, vb) in zip(a.pairs, b.pairs):
            if _detect_provable_neq(ka, kb, params, in_case_branch, param_duck_types):
                return True
            if _detect_provable_neq(va, vb, params, in_case_branch, param_duck_types):
                return True

    # Same case structure — only recurse when tests are IDENTICAL.
    # Different case-tree structures (different guard orderings) can still
    # compute the same piecewise function (e.g. sign(x) written two ways).
    # Piecewise normalization in normalize() handles the canonical form;
    # here we must be conservative and only declare NEQ when the case
    # trees are structurally aligned.
    if isinstance(a, OCase) and isinstance(b, OCase):
        if a.test.canon() == b.test.canon():
            if _detect_provable_neq(a.true_branch, b.true_branch, params, True, param_duck_types):
                return True
            if _detect_provable_neq(a.false_branch, b.false_branch, params, True, param_duck_types):
                return True
        else:
            # Tests differ: safe to recurse when a and b are "parameterized"
            # by the same operation with different args (e.g. case(f(x), g(f(x)), d)
            # vs case(f(x,a), g(f(x,a)), d) — the test appears inside branches too).
            # Detect: tests are same-named OOp with different args, AND
            # each test's canon appears in its own branch canons.
            if (isinstance(a.test, OOp) and isinstance(b.test, OOp) and
                    a.test.name == b.test.name):
                ta_c = a.test.canon()
                tb_c = b.test.canon()
                # Check that the test subexpression is used in a branch
                a_true_c = a.true_branch.canon()
                b_true_c = b.true_branch.canon()
                if ta_c in a_true_c and tb_c in b_true_c:
                    # Both are "case(X, f(X), ...)" — parameterized by X
                    # If X and X' are provably NEQ, then f(X) ≠ f(X')
                    if _detect_provable_neq(a.test, b.test, params, False, param_duck_types):
                        return True

    # Cross-type rules — only at top level (depth 0).
    # Inside case branches, different structures can compute the same
    # value under the guard's domain constraint (e.g., Q[perm](set(x))
    # and sorted(x) agree when len(set(x)) <= 1).
    if type(a) != type(b):
        if not in_case_branch:
            # OSeq vs OOp — structural literal vs function call
            # Only fire when the OSeq is non-empty (a real literal sequence).
            # Empty OSeq often represents lost compiler state (result=[]).
            if isinstance(a, OSeq) and isinstance(b, OOp):
                if len(a.elements) > 0:
                    return True
            if isinstance(b, OSeq) and isinstance(a, OOp):
                if len(b.elements) > 0:
                    return True
            # OQuotient vs OOp — unordered vs deterministic
            if isinstance(a, OQuotient) and isinstance(b, OOp):
                return True
            if isinstance(b, OQuotient) and isinstance(a, OOp):
                return True

    # OQuotient — recurse into inner term
    if isinstance(a, OQuotient) and isinstance(b, OQuotient):
        if a.equiv_class != b.equiv_class:
            return True
        if _detect_provable_neq(a.inner, b.inner, params, in_case_branch, param_duck_types):
            return True

    return False


def _body_fn_trustworthy(body_fn: OTerm) -> bool:
    """Check if a fold body_fn is safe for structural comparison.

    Returns True only if the body references only fold params ($0, $1, ...),
    global params (p0, p1, ...), literals, and known arithmetic/logical ops.
    Returns False if it contains calls to unknown functions (which may be
    locally-defined with closure differences the OTerm can't capture).
    """
    # Known safe operation names (builtins, arithmetic, etc.)
    _SAFE_OPS = frozenset({
        'add', 'sub', 'mult', 'mul', 'floordiv', 'truediv', 'mod', 'pow',
        'iadd', 'isub', 'imult', 'imul', 'ifloordiv', 'imod', 'ipow',
        'eq', 'noteq', 'lt', 'lte', 'gt', 'gte',
        'and', 'or', 'not', 'u_not', 'u_usub', 'u_invert', 'abs',
        'bitor', 'bitand', 'bitxor', 'lshift', 'rshift',
        'min', 'max', 'len', 'int', 'float', 'str', 'bool',
        'getitem', 'getattr', 'setitem', 'unpack', 'transpose',
        'range', 'reversed', 'sorted',
        '.append', '.append!', '.extend', '.pop', '.pop!', '.popleft', '.popleft!',
        'concat', 'suffix', 'prefix', 'slice', 'list', 'in',
        '.get', 'deque', 'set_literal', '.add!', '.update!',
    })
    def _check(t):
        if isinstance(t, (OLit, OVar)):
            return True
        if isinstance(t, OOp):
            if t.name not in _SAFE_OPS:
                return False
            return all(_check(a) for a in t.args)
        if isinstance(t, OCase):
            return _check(t.test) and _check(t.true_branch) and _check(t.false_branch)
        if isinstance(t, OLam):
            return _check(t.body)
        if isinstance(t, OFold):
            return _check(t.init) and _check(t.collection)
        if isinstance(t, OSeq):
            return all(_check(e) for e in t.elements)
        if isinstance(t, OMap):
            return (_check(t.transform) and _check(t.collection) and
                    (t.filter_pred is None or _check(t.filter_pred)))
        # Unknown, Abstract, Dict, etc. — not trustworthy
        return False
    return _check(body_fn)


def _flexible_match(a: OTerm, b: OTerm) -> bool:
    """Flexible structural matching that handles common dichotomies.

    Matches terms modulo:
    - OUnknown annotations (ignored)
    - Fold key differences (hash-based keys may differ)
    - Quotient wrapping differences
    - Commutative argument reordering
    """
    if type(a) == type(b):
        if isinstance(a, OVar) and isinstance(b, OVar):
            return a.name == b.name
        if isinstance(a, OLit) and isinstance(b, OLit):
            return a.value == b.value
        if isinstance(a, OOp) and isinstance(b, OOp):
            if a.name != b.name:
                return False
            if len(a.args) != len(b.args):
                return False
            if all(_flexible_match(ai, bi) for ai, bi in zip(a.args, b.args)):
                return True
            # Commutative reordering: try swapped args
            if (len(a.args) == 2
                    and a.name in ('add', 'mult', 'iadd', 'imult', 'eq', 'noteq',
                                   'max', 'min',
                                   'bitand', 'bitor', 'bitxor',
                                   'iand', 'ior', 'ixor', 'gcd', 'lcm')
                    and _flexible_match(a.args[0], b.args[1])
                    and _flexible_match(a.args[1], b.args[0])):
                return True
            return False
        if isinstance(a, OCase) and isinstance(b, OCase):
            return (_flexible_match(a.test, b.test) and
                    _flexible_match(a.true_branch, b.true_branch) and
                    _flexible_match(a.false_branch, b.false_branch))
        if isinstance(a, OFold) and isinstance(b, OFold):
            # Fold keys encode the loop body — but hashes can be lossy
            # (e.g., augmented assignment operator differences lost).
            # If body_fn is available and trustworthy, compare structurally.
            if (a.body_fn is not None and b.body_fn is not None and
                    _body_fn_trustworthy(a.body_fn) and
                    _body_fn_trustworthy(b.body_fn)):
                return (_flexible_match(a.init, b.init) and
                        _flexible_match(a.collection, b.collection) and
                        _flexible_match(a.body_fn, b.body_fn))
            # body_fn not fully trustworthy — require hash match AND
            # canonical form of body_fn to also match (when available).
            # Hash alone is too lossy for soundness.
            if (a.op_name == b.op_name and
                    _flexible_match(a.init, b.init) and
                    _flexible_match(a.collection, b.collection)):
                # If body_fn exists for both, check canonical forms match
                if a.body_fn is not None and b.body_fn is not None:
                    return a.body_fn.canon() == b.body_fn.canon()
                # No body_fn at all — trust hash
                return True
            return False
        if isinstance(a, OFix) and isinstance(b, OFix):
            # While loop fixed points: allow different keys (different
            # loop implementations) if bodies match
            return _flexible_match(a.body, b.body)
        if isinstance(a, OAbstract) and isinstance(b, OAbstract):
            return a.spec == b.spec and len(a.inputs) == len(b.inputs) and \
                   all(_flexible_match(ai, bi) for ai, bi in zip(a.inputs, b.inputs))
        if isinstance(a, OSeq) and isinstance(b, OSeq):
            if len(a.elements) != len(b.elements):
                return False
            return all(_flexible_match(ai, bi) for ai, bi in zip(a.elements, b.elements))
        if isinstance(a, ODict) and isinstance(b, ODict):
            if len(a.pairs) != len(b.pairs):
                return False
            return all(_flexible_match(ak, bk) and _flexible_match(av, bv)
                      for (ak, av), (bk, bv) in zip(a.pairs, b.pairs))
        if isinstance(a, OQuotient) and isinstance(b, OQuotient):
            return a.equiv_class == b.equiv_class and _flexible_match(a.inner, b.inner)
        if isinstance(a, OUnknown) and isinstance(b, OUnknown):
            return a.desc == b.desc
        if isinstance(a, OLam) and isinstance(b, OLam):
            return (len(a.params) == len(b.params) and
                    _flexible_match(a.body, b.body))
        if isinstance(a, OMap) and isinstance(b, OMap):
            if not _flexible_match(a.transform, b.transform):
                return False
            if not _flexible_match(a.collection, b.collection):
                return False
            if a.filter_pred is not None and b.filter_pred is not None:
                return _flexible_match(a.filter_pred, b.filter_pred)
            return a.filter_pred is None and b.filter_pred is None
        if isinstance(a, OCatch) and isinstance(b, OCatch):
            return (_flexible_match(a.body, b.body) and
                    _flexible_match(a.default, b.default))
    # Cross-type: Q[perm](x) ≡ x when x is already order-independent
    if isinstance(a, OQuotient) and not isinstance(b, OQuotient):
        return _flexible_match(a.inner, b)
    if isinstance(b, OQuotient) and not isinstance(a, OQuotient):
        return _flexible_match(a, b.inner)
    return False


def _extract_op_signature(term: OTerm) -> Optional[str]:
    """Extract the operation signature: what operations are applied to what."""
    parts = []
    _collect_ops(term, parts, depth=0)
    if not parts:
        return None
    return '|'.join(sorted(parts))


def _collect_ops(term: OTerm, parts: list, depth: int):
    """Collect operation names from a term tree."""
    if depth > 20:
        return
    if isinstance(term, OOp):
        parts.append(term.name)
        for a in term.args:
            _collect_ops(a, parts, depth + 1)
    elif isinstance(term, OFold):
        parts.append(f'fold')
        _collect_ops(term.init, parts, depth + 1)
        _collect_ops(term.collection, parts, depth + 1)
    elif isinstance(term, OFix):
        parts.append(f'fix')
        _collect_ops(term.body, parts, depth + 1)
    elif isinstance(term, OCase):
        parts.append('case')
        _collect_ops(term.test, parts, depth + 1)
        _collect_ops(term.true_branch, parts, depth + 1)
        _collect_ops(term.false_branch, parts, depth + 1)
    elif isinstance(term, OSeq):
        for e in term.elements:
            _collect_ops(e, parts, depth + 1)
    elif isinstance(term, OQuotient):
        _collect_ops(term.inner, parts, depth + 1)


def _rename_params(term: OTerm, params: List[str]) -> OTerm:
    """Rename parameters to canonical names $0, $1, ..."""
    mapping = {p: f'p{i}' for i, p in enumerate(params)}
    return _subst(term, mapping)


def _subst(term: OTerm, mapping: Dict[str, str]) -> OTerm:
    """Substitute variable names."""
    if isinstance(term, OVar):
        if term.name in mapping:
            return OVar(mapping[term.name])
        return term
    if isinstance(term, OOp):
        return OOp(term.name, tuple(_subst(a, mapping) for a in term.args))
    if isinstance(term, OCase):
        return OCase(_subst(term.test, mapping),
                     _subst(term.true_branch, mapping),
                     _subst(term.false_branch, mapping))
    if isinstance(term, OFold):
        bfn = _subst(term.body_fn, mapping) if term.body_fn else None
        return OFold(term.op_name, _subst(term.init, mapping),
                     _subst(term.collection, mapping), body_fn=bfn)
    if isinstance(term, OFix):
        return OFix(term.name, _subst(term.body, mapping))
    if isinstance(term, OSeq):
        return OSeq(tuple(_subst(e, mapping) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((_subst(k, mapping), _subst(v, mapping))
                          for k, v in term.pairs))
    if isinstance(term, OQuotient):
        return OQuotient(_subst(term.inner, mapping), term.equiv_class)
    if isinstance(term, OAbstract):
        return OAbstract(term.spec, tuple(_subst(a, mapping) for a in term.inputs))
    if isinstance(term, OLam):
        # Don't substitute into bound variables — shadow them
        inner_map = {k: v for k, v in mapping.items() if k not in term.params}
        return OLam(term.params, _subst(term.body, inner_map))
    if isinstance(term, OMap):
        new_t = _subst(term.transform, mapping)
        new_c = _subst(term.collection, mapping)
        new_f = _subst(term.filter_pred, mapping) if term.filter_pred else None
        return OMap(new_t, new_c, new_f)
    if isinstance(term, OCatch):
        return OCatch(_subst(term.body, mapping), _subst(term.default, mapping))
    return term


def _subst_term(term: OTerm, var_name: str, replacement: OTerm) -> OTerm:
    """Substitute a variable with an arbitrary OTerm (capture-avoiding)."""
    if isinstance(term, OVar):
        return replacement if term.name == var_name else term
    if isinstance(term, OLit):
        return term
    if isinstance(term, OOp):
        return OOp(term.name, tuple(_subst_term(a, var_name, replacement) for a in term.args))
    if isinstance(term, OCase):
        return OCase(_subst_term(term.test, var_name, replacement),
                     _subst_term(term.true_branch, var_name, replacement),
                     _subst_term(term.false_branch, var_name, replacement))
    if isinstance(term, OFold):
        bfn = _subst_term(term.body_fn, var_name, replacement) if term.body_fn else None
        return OFold(term.op_name, _subst_term(term.init, var_name, replacement),
                     _subst_term(term.collection, var_name, replacement), body_fn=bfn)
    if isinstance(term, OFix):
        return OFix(term.name, _subst_term(term.body, var_name, replacement))
    if isinstance(term, OSeq):
        return OSeq(tuple(_subst_term(e, var_name, replacement) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((_subst_term(k, var_name, replacement),
                            _subst_term(v, var_name, replacement))
                           for k, v in term.pairs))
    if isinstance(term, OQuotient):
        return OQuotient(_subst_term(term.inner, var_name, replacement), term.equiv_class)
    if isinstance(term, OAbstract):
        return OAbstract(term.spec, tuple(_subst_term(a, var_name, replacement) for a in term.inputs))
    if isinstance(term, OLam):
        if var_name in term.params:
            return term  # bound — don't substitute
        return OLam(term.params, _subst_term(term.body, var_name, replacement))
    if isinstance(term, OMap):
        new_t = _subst_term(term.transform, var_name, replacement)
        new_c = _subst_term(term.collection, var_name, replacement)
        new_f = _subst_term(term.filter_pred, var_name, replacement) if term.filter_pred else None
        return OMap(new_t, new_c, new_f)
    if isinstance(term, OCatch):
        return OCatch(_subst_term(term.body, var_name, replacement),
                      _subst_term(term.default, var_name, replacement))
    return term


def _contains_ofix_named(term: OTerm, name: str) -> bool:
    """Check if term contains OFix(name, ...) — indicating self-recursion."""
    if isinstance(term, OFix) and term.name == name:
        return True
    if isinstance(term, OOp):
        return any(_contains_ofix_named(a, name) for a in term.args)
    if isinstance(term, OCase):
        return (_contains_ofix_named(term.test, name) or
                _contains_ofix_named(term.true_branch, name) or
                _contains_ofix_named(term.false_branch, name))
    if isinstance(term, OFold):
        return (_contains_ofix_named(term.init, name) or
                _contains_ofix_named(term.collection, name) or
                (term.body_fn is not None and _contains_ofix_named(term.body_fn, name)))
    if isinstance(term, OFix):
        return _contains_ofix_named(term.body, name)
    if isinstance(term, OSeq):
        return any(_contains_ofix_named(e, name) for e in term.elements)
    if isinstance(term, OLam):
        return _contains_ofix_named(term.body, name)
    if isinstance(term, OMap):
        return (_contains_ofix_named(term.transform, name) or
                _contains_ofix_named(term.collection, name) or
                (term.filter_pred is not None and _contains_ofix_named(term.filter_pred, name)))
    if isinstance(term, OCatch):
        return (_contains_ofix_named(term.body, name) or
                _contains_ofix_named(term.default, name))
    return False
