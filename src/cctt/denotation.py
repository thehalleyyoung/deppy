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
    def canon(self) -> str:
        arg_strs = ','.join(a.canon() for a in self.args)
        return f'{self.name}({arg_strs})'

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
        # skip inlining — the fixpoint structure needs special handling.
        if name in env.bindings and isinstance(env.bindings[name], OLam):
            lam = env.bindings[name]
            if len(args) == len(lam.params) and not _contains_ofix_named(lam.body, name):
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
        ('math', 'copysign'): 'math.copysign',
        ('math', 'sqrt'): 'math.sqrt',
        ('math', 'log'): 'math.log',
        ('math', 'floor'): 'math.floor',
        ('math', 'ceil'): 'math.ceil',
        ('math', 'gcd'): 'math.gcd',
        ('math', 'isnan'): 'math.isnan',
        ('math', 'isinf'): 'math.isinf',
        ('math', 'factorial'): 'math.factorial',
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
        elif (isinstance(stmt.target, ast.Subscript)
              and isinstance(stmt.target.value, ast.Name)):
            # dp[i] += val → dp = setitem(dp, i, iadd(dp[i], val))
            obj_name = stmt.target.value.id
            old_obj = env.get(obj_name)
            if old_obj is None:
                old_obj = OVar(obj_name)
            idx = _compile_expr_ot(stmt.target.slice, env)
            rhs = _compile_expr_ot(stmt.value, env)
            op_name = type(stmt.op).__name__.lower()
            old_elem = OOp('getitem', (old_obj, idx))
            new_elem = OOp(f'i{op_name}', (old_elem, rhs))
            env.put(obj_name, OOp('setitem', (old_obj, idx, new_elem)))

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

    # Find the inner if-return and the state updates
    inner_if = None
    update_stmts = []
    for s in body:
        if isinstance(s, ast.If) and _has_any_return(s.body):
            inner_if = s
        else:
            update_stmts.append(s)

    if inner_if is None:
        return None

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
            # Try to compile body as OTerm for structural comparison
            body_fn = None
            try:
                body_env = env.copy()
                body_env.put(vn, OVar('$0'))
                for i, v in enumerate(loop_vars):
                    body_env.put(v, OVar(f'${i+1}'))
                _exec_stmts_ot(stmt.body, body_env)
                acc_result = body_env.get(vn)
                if acc_result is not None and not isinstance(acc_result, OVar):
                    params = ('$0',) + tuple(f'${i+1}' for i in range(len(loop_vars)))
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
                            body_env2 = env.copy()
                            body_env2.put(vn, OVar('$0'))
                            for ii, v in enumerate(loop_vars):
                                body_env2.put(v, OVar(f'${ii+1}'))
                            _exec_stmts_ot(stmt.body, body_env2)
                            acc_r = body_env2.get(vn)
                            if acc_r is not None and not isinstance(acc_r, OVar):
                                params = ('$0',) + tuple(f'${ii+1}' for ii in range(len(loop_vars)))
                                body_fn2 = OLam(params, acc_r)
                        except Exception:
                            pass
                        env.put(vn, OFold(fold_key, old, it, body_fn=body_fn2))
            else:
                body_repr = _normalize_ast_dump(stmt.body, step_env)
                fold_key = _hash(_canonicalize_free_vars(f'{body_repr}'))
                body_fn = None
                try:
                    body_env = env.copy()
                    body_env.put(vn, OVar('$0'))
                    for i, v in enumerate(loop_vars):
                        body_env.put(v, OVar(f'${i+1}'))
                    _exec_stmts_ot(stmt.body, body_env)
                    acc_result = body_env.get(vn)
                    if acc_result is not None and not isinstance(acc_result, OVar):
                        params = ('$0',) + tuple(f'${i+1}' for i in range(len(loop_vars)))
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

    if len(modified) >= 2 and has_tuple_swap:
        # ── Coupled multi-variable fix-point ──
        # State = ($0, $1, ...) corresponding to modified vars.
        # Compile body with state vars to capture cross-dependencies.
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
    else:
        step_env = env.copy()
        _exec_stmts_ot(stmt.body, step_env)
        for vn in modified:
            old = env.get(vn)
            new_val = step_env.bindings.get(vn, old)
            body = OCase(test_term, new_val, old)
            env.put(vn, OFix(fix_key, body))


def _detect_counter_while(stmt, modified, env):
    """Detect counter-based while loop pattern.

    Pattern: while i < n: ...; i += 1  (or i < len(x), etc.)
    Returns (counter_var, bound_term, accumulator_vars) or None.
    """
    # The test must be a comparison: i < n, i <= n, i != n, etc.
    test = stmt.test
    if not isinstance(test, ast.Compare):
        return None
    if len(test.ops) != 1 or len(test.comparators) != 1:
        return None

    op = test.ops[0]
    if not isinstance(op, (ast.Lt, ast.LtE, ast.NotEq)):
        return None
    if not isinstance(test.left, ast.Name):
        return None

    counter_name = test.left.id
    if counter_name not in modified:
        return None

    # The counter must be incremented by 1 in the body
    has_increment = False
    for s in stmt.body:
        if isinstance(s, ast.AugAssign):
            if (isinstance(s.target, ast.Name) and s.target.id == counter_name
                    and isinstance(s.op, ast.Add)
                    and isinstance(s.value, ast.Constant) and s.value.value == 1):
                has_increment = True
        elif isinstance(s, ast.Assign):
            if (len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                    and s.targets[0].id == counter_name):
                if (isinstance(s.value, ast.BinOp) and isinstance(s.value.op, ast.Add)):
                    if (isinstance(s.value.left, ast.Name) and s.value.left.id == counter_name
                            and isinstance(s.value.right, ast.Constant) and s.value.right.value == 1):
                        has_increment = True
                    elif (isinstance(s.value.right, ast.Name) and s.value.right.id == counter_name
                            and isinstance(s.value.left, ast.Constant) and s.value.left.value == 1):
                        has_increment = True

    if not has_increment:
        return None

    bound_term = _compile_expr_ot(test.comparators[0], env)
    if isinstance(op, ast.LtE):
        bound_term = OOp('add', (bound_term, OLit(1)))

    acc_vars = [v for v in modified if v != counter_name]
    return (counter_name, bound_term, acc_vars)


def _find_augassign_rhs(body, acc_name):
    """Find the RHS expression node of an augmented assignment to acc_name."""
    for s in body:
        if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name):
            if s.target.id == acc_name:
                return s.value
    return None


def _assign_ot(target, val: OTerm, env: DenotEnv):
    if isinstance(target, ast.Name):
        env.put(target.id, val)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for j, elt in enumerate(target.elts):
            _assign_ot(elt, OOp('getitem', (val, OLit(j))), env)
    elif isinstance(target, ast.Subscript) and isinstance(target.value, ast.Name):
        # Indexed assignment: obj[key] = val → functional setitem
        obj_name = target.value.id
        old = env.get(obj_name)
        if old is None:
            old = OVar(obj_name)
        idx = _compile_expr_ot(target.slice, env)
        env.put(obj_name, OOp('setitem', (old, idx, val)))


def _merge_envs_ot(target: DenotEnv, te: DenotEnv, fe: DenotEnv, test: OTerm):
    for k in set(te.bindings) | set(fe.bindings):
        tv = te.bindings.get(k)
        fv = fe.bindings.get(k)
        if tv is not None and fv is not None:
            if tv.canon() != fv.canon():
                target.put(k, OCase(test, tv, fv))
            else:
                target.put(k, tv)
        elif tv is not None:
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
        if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name):
            names.append(s.target.id)
        elif isinstance(s, ast.Assign):
            for t in s.targets:
                if isinstance(t, ast.Name):
                    names.append(t.id)
                elif isinstance(t, (ast.Tuple, ast.List)):
                    names.extend(e.id for e in t.elts if isinstance(e, ast.Name))
                elif isinstance(t, ast.Subscript) and isinstance(t.value, ast.Name):
                    names.append(t.value.id)
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

        # getitem([a, b, ...], literal_idx) → direct element
        if term.name == 'getitem' and len(args) == 2:
            base, idx = args
            if isinstance(idx, OLit) and isinstance(idx.value, int):
                if isinstance(base, OSeq) and 0 <= idx.value < len(base.elements):
                    return base.elements[idx.value]
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
        return OQuotient(_phase1_beta(term.inner), term.equiv_class)

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
        # but [] is [] → False for distinct objects). Don't reduce it.

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
    # fold[mul](1, range(2, n+1)) → math.factorial(n)
    if op == 'mul' and isinstance(init, OLit) and init.value == 1:
        if isinstance(coll, OOp) and coll.name == 'range' and len(coll.args) == 2:
            start, end = coll.args
            if isinstance(start, OLit) and start.value == 2:
                # Check end = add(n, 1)
                if isinstance(end, OOp) and end.name == 'add' and len(end.args) == 2:
                    if isinstance(end.args[1], OLit) and end.args[1].value == 1:
                        return OOp('math.factorial', (end.args[0],))
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
        return OCase(_phase3_fold(term.test),
                     _phase3_fold(term.true_branch),
                     _phase3_fold(term.false_branch))
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
        # Fold→math simplification: fold[min](a[0], a[1:]) → min(a)
        result = _try_fold_to_builtin(op, init, coll)
        if result is not None:
            return result
        return OFold(op, init, coll, body_fn=bfn)
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

        # itertools.cycle(xs) used standalone → identity (we handle at getitem site)
        # This is conservative: cycle only makes sense with indexing

        # NOTE: abs(x) is NOT expanded to piecewise case(lt(x,0), -x, x)
        # because abs() handles complex numbers (returns magnitude) while
        # manual piecewise only handles real numbers.

        # max(a, b) → case(gte(a, b), a, b)
        if name == 'max' and len(args) == 2:
            return OCase(OOp('gte', (args[0], args[1])), args[0], args[1])

        # min(a, b) → case(lte(a, b), a, b)
        if name == 'min' and len(args) == 2:
            return OCase(OOp('lte', (args[0], args[1])), args[0], args[1])

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

        # ── setitem chain normalization ──
        # setitem(setitem(x, i, v), i, w) → setitem(x, i, w)
        # Overwriting the same index makes the first write dead
        if name == 'setitem' and len(args) == 3:
            base, idx, val = args
            if (isinstance(base, OOp) and base.name == 'setitem'
                    and len(base.args) == 3
                    and base.args[1].canon() == idx.canon()):
                return OOp('setitem', (base.args[0], idx, val))

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
        return OCase(_phase4_hof(term.test),
                     _phase4_hof(term.true_branch),
                     _phase4_hof(term.false_branch))
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
        return OFix(term.name, _de_bruijn_impl(term.body, depth))
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
        return bool(_HEX_KEY.match(key)) or key.startswith('coupled_fold|')

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
        return OFix(term.name, _rehash_folds(term.body))
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
        return _collect_vars(term.init) | _collect_vars(term.collection)
    if isinstance(term, OFix):
        return _collect_vars(term.body)
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
            )
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
        'getitem', 'getattr', 'range', 'reversed', 'sorted',
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
                # Try commutative equivalence
                if a.name in ('add', 'mult', 'iadd', 'imult', 'eq', 'noteq',
                              'and', 'or', 'max', 'min',
                              'bitand', 'bitor', 'bitxor',
                              'iand', 'ior', 'ixor', 'gcd', 'lcm'):
                    if b.name == a.name and len(a.args) == 2 and len(b.args) == 2:
                        if (_flexible_match(a.args[0], b.args[1]) and
                            _flexible_match(a.args[1], b.args[0])):
                            return True
                return False
            if len(a.args) != len(b.args):
                return False
            return all(_flexible_match(ai, bi) for ai, bi in zip(a.args, b.args))
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
