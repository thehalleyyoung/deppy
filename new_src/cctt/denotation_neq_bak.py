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
    op_name: str  # the accumulation operation
    init: 'OTerm'
    collection: 'OTerm'
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
        # Alpha-normalize: replace param names with positional indices
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
    """Compile a Python function to its denotational OTerm."""
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        return None

    func = None
    for n in tree.body:
        if isinstance(n, ast.FunctionDef):
            func = n
            break
    if func is None:
        return None

    params = [a.arg for a in func.args.args]
    env = DenotEnv(func.name, params)

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
            _exec_for_ot(stmt, env)

        elif isinstance(stmt, ast.While):
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
            return OOp('slice', (base,))
        idx = _compile_expr_ot(node.slice, env)
        return OOp('getitem', (base, idx))

    if isinstance(node, (ast.Tuple, ast.List)):
        elts = tuple(_compile_expr_ot(e, env) for e in node.elts)
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

    for vn in modified:
        if vn in target_names:
            continue
        old = env.get(vn)

        # D5: Detect simple augmented assignment folds and use a
        # semantic fold key (operation name) instead of a body hash.
        # This unifies `for x in xs: s += x` with `sum(xs)` since
        # both normalize to OFold('iadd', 0, xs).
        semantic_key = _detect_augassign_fold(stmt.body, vn, loop_vars)
        if semantic_key is not None:
            env.put(vn, OFold(semantic_key, old, it))
        else:
            step_env = env.copy()
            for v in loop_vars:
                step_env.put(v, OVar(v))
            body_repr = _normalize_ast_dump(stmt.body, step_env)
            fold_key = _hash(f'{body_repr}')
            env.put(vn, OFold(fold_key, old, it))


def _detect_augassign_fold(body: list, acc_name: str,
                           loop_vars: list) -> Optional[str]:
    """Detect a simple augmented assignment fold step → semantic key.

    Pattern: acc += expr  →  'iadd'
             acc *= expr  →  'imult'
             acc |= expr  →  'ior'
             acc &= expr  →  'iand'
    Only fires when the loop body is a single augmented assignment.
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

    # Check the RHS is just the loop variable (simple fold)
    # or a simple expression of the loop variable
    op_name = type(s.op).__name__.lower()
    op_map = {
        'add': 'iadd', 'sub': 'isub', 'mult': 'imult',
        'div': 'idiv', 'floordiv': 'ifloordiv', 'mod': 'imod',
        'bitor': 'ior', 'bitand': 'iand', 'bitxor': 'ixor',
    }
    return op_map.get(op_name)


def _detect_map_pattern(stmt, loop_vars: list, it: OTerm,
                        env: 'DenotEnv') -> Optional[tuple]:
    """Detect for-loop that builds a list via append → OMap.

    Pattern: for x in xs: result.append(f(x))
    Where result was initialized to [] and the only mutation is append.
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
    if call.func.attr != 'append':
        return None
    if not isinstance(call.func.value, ast.Name):
        return None
    if len(call.args) != 1:
        return None

    var_name = call.func.value.id
    old = env.get(var_name)

    # Verify the accumulator was initialized to [] (empty list)
    is_empty = (isinstance(old, OSeq) and len(old.elements) == 0)
    if not is_empty:
        return None

    # Compile the appended expression with loop vars as bound variables
    body_env = env.copy()
    for v in loop_vars:
        body_env.put(v, OVar(v))
    appended = _compile_expr_ot(call.args[0], body_env)
    transform = OLam(tuple(loop_vars), appended)

    return var_name, OMap(transform, it)


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
    """
    parts = []
    for s in (stmts if isinstance(stmts, list) else [stmts]):
        try:
            # Compile each statement to OTerm and use its canonical form
            # This normalizes away variable names
            if isinstance(s, ast.Expr) and isinstance(s.value, ast.Call):
                parts.append(_compile_expr_ot(s.value, env.copy()).canon())
            elif isinstance(s, ast.Assign):
                val = _compile_expr_ot(s.value, env.copy())
                parts.append(f'assign:{val.canon()}')
            elif isinstance(s, ast.AugAssign):
                val = _compile_expr_ot(s.value, env.copy())
                op = type(s.op).__name__.lower()
                parts.append(f'aug:{op}:{val.canon()}')
            elif isinstance(s, ast.If):
                test = _compile_expr_ot(s.test, env.copy())
                parts.append(f'if:{test.canon()}')
            elif isinstance(s, ast.Return):
                if s.value:
                    val = _compile_expr_ot(s.value, env.copy())
                    parts.append(f'ret:{val.canon()}')
            elif isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef)):
                # Include function signature (args, defaults) in hash
                # This distinguishes def f(): from def f(i=i):
                arg_info = ','.join(a.arg for a in s.args.args)
                defaults = len(s.args.defaults)
                parts.append(f'def:{s.name}({arg_info},d={defaults})')
            else:
                parts.append(ast.dump(s)[:60])
        except Exception:
            parts.append(ast.dump(s)[:50])
    return '|'.join(parts)


def _exec_while_ot(stmt, env: DenotEnv):
    """Model while loop as a fixed point."""
    modified = _find_modified_ot(stmt.body)
    test_repr = _normalize_ast_dump(stmt.test, env)
    body_repr = _normalize_ast_dump(stmt.body, env)
    fix_key = _hash(f'{test_repr}|{body_repr}')

    for vn in modified:
        old = env.get(vn)
        env.put(vn, OFix(fix_key, old))


def _assign_ot(target, val: OTerm, env: DenotEnv):
    if isinstance(target, ast.Name):
        env.put(target.id, val)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for j, elt in enumerate(target.elts):
            _assign_ot(elt, OOp('getitem', (val, OLit(j))), env)


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
    return current


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
        return OCase(test, t, f)

    if isinstance(term, OOp):
        args = tuple(_phase1_beta(a) for a in term.args)
        # Constant folding
        if all(isinstance(a, OLit) for a in args):
            result = _try_const_fold(term.name, [a.value for a in args])
            if result is not None:
                return OLit(result)
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
        return OOp(term.name, args)

    if isinstance(term, OFold):
        init = _phase1_beta(term.init)
        coll = _phase1_beta(term.collection)
        # fold(init, []) → init (folding over empty collection returns initial value)
        if isinstance(coll, OSeq) and len(coll.elements) == 0:
            return init
        return OFold(term.op_name, init, coll)

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
        return OCase(test, t, f)

    if isinstance(term, OFold):
        return OFold(term.op_name, _phase2_ring(term.init),
                     _phase2_ring(term.collection))
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
                return OFold('iadd', OLit(0), args[0])
            if name == 'any':
                return OFold('or', OLit(False), args[0])
            if name == 'all':
                return OFold('and', OLit(True), args[0])
            if name in ('math.prod', 'prod'):
                return OFold('imult', OLit(1), args[0])
        # .join is also a fold
        if name == '.join' and len(args) == 2:
            return OFold('str_concat', args[0], args[1])
        # functools.reduce is a fold
        if name == 'fold' and len(args) >= 2:
            # reduce(op, iterable) or reduce(op, iterable, init)
            if len(args) == 3:
                return OFold('reduce', args[2], args[1])
            return OFold('reduce', OUnknown('reduce_no_init'), args[1])
        return OOp(name, args)
    if isinstance(term, OCase):
        return OCase(_phase3_fold(term.test),
                     _phase3_fold(term.true_branch),
                     _phase3_fold(term.false_branch))
    if isinstance(term, OFold):
        return OFold(term.op_name, _phase3_fold(term.init),
                     _phase3_fold(term.collection))
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

        # NOTE: abs(x) is NOT expanded to piecewise case(lt(x,0), -x, x)
        # because abs() handles complex numbers (returns magnitude) while
        # manual piecewise only handles real numbers.

        # max(a, b) → case(gte(a, b), a, b)
        if name == 'max' and len(args) == 2:
            return OCase(OOp('gte', (args[0], args[1])), args[0], args[1])

        # min(a, b) → case(lte(a, b), a, b)
        if name == 'min' and len(args) == 2:
            return OCase(OOp('lte', (args[0], args[1])), args[0], args[1])

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

        # map(f, map(g, xs)) → map(f∘g, xs)
        if isinstance(c, OMap) and c.filter_pred is None:
            if isinstance(t, OLam) and isinstance(c.transform, OLam):
                if len(t.params) == 1 and len(c.transform.params) == 1:
                    composed = _compose_lam(t, c.transform)
                    return OMap(composed, c.collection, f)

        # map(f, map(g, xs)) where inner has filter → map(f∘g, xs, filter)
        if isinstance(c, OMap) and c.filter_pred is not None and f is None:
            if isinstance(t, OLam) and isinstance(c.transform, OLam):
                if len(t.params) == 1 and len(c.transform.params) == 1:
                    composed = _compose_lam(t, c.transform)
                    return OMap(composed, c.collection, c.filter_pred)

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
                    return OFold(term.op_name, init, coll.collection)
        return OFold(term.op_name, init, coll)
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
    inner_applied = _subst(g.body, {g.params[0]: OVar(z)})
    composed_body = _subst(f.body, {f.params[0]: inner_applied})
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
        return OFold(term.op_name, _phase5_unify(term.init),
                     _phase5_unify(term.collection))
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
        return OFold(term.op_name, _phase6_quotient(term.init),
                     _phase6_quotient(term.collection))
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
        return OFold(term.op_name, _phase7_piecewise(term.init),
                     _phase7_piecewise(term.collection))
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
    except Exception:
        pass
    return None


def _de_bruijn_normalize(term: OTerm) -> OTerm:
    """Normalize all bound variables in OLam to de Bruijn-style names (_b0, _b1, ...).

    Ensures alpha-equivalent terms produce identical canonical forms.
    """
    if isinstance(term, OLam):
        mapping = {p: f'_b{i}' for i, p in enumerate(term.params)}
        normalized_body = _subst(term.body, mapping)
        normalized_body = _de_bruijn_normalize(normalized_body)
        new_params = tuple(f'_b{i}' for i in range(len(term.params)))
        return OLam(new_params, normalized_body)
    if isinstance(term, OOp):
        return OOp(term.name, tuple(_de_bruijn_normalize(a) for a in term.args))
    if isinstance(term, OCase):
        return OCase(_de_bruijn_normalize(term.test),
                     _de_bruijn_normalize(term.true_branch),
                     _de_bruijn_normalize(term.false_branch))
    if isinstance(term, OFold):
        return OFold(term.op_name, _de_bruijn_normalize(term.init),
                     _de_bruijn_normalize(term.collection))
    if isinstance(term, OFix):
        return OFix(term.name, _de_bruijn_normalize(term.body))
    if isinstance(term, OSeq):
        return OSeq(tuple(_de_bruijn_normalize(e) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((_de_bruijn_normalize(k), _de_bruijn_normalize(v))
                          for k, v in term.pairs))
    if isinstance(term, OQuotient):
        return OQuotient(_de_bruijn_normalize(term.inner), term.equiv_class)
    if isinstance(term, OAbstract):
        return OAbstract(term.spec, tuple(_de_bruijn_normalize(a) for a in term.inputs))
    if isinstance(term, OMap):
        t = _de_bruijn_normalize(term.transform)
        c = _de_bruijn_normalize(term.collection)
        f = _de_bruijn_normalize(term.filter_pred) if term.filter_pred else None
        return OMap(t, c, f)
    if isinstance(term, OCatch):
        return OCatch(_de_bruijn_normalize(term.body),
                     _de_bruijn_normalize(term.default))
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
            return None
        # Don't trust if the term is just a single operation on params
        # — many different programs reduce to the same simple form
        if isinstance(nf_f, OOp) and all(isinstance(a, OVar) for a in nf_f.args):
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

        # Same operation, different arguments — recurse
        if a.name == b.name and len(a.args) == len(b.args):
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
        if a.name != b.name:
            # If both are simple ops on the same args, and the ops are
            # fundamentally different (not just aliased), it's NEQ
            a_args_c = tuple(x.canon() for x in a.args)
            b_args_c = tuple(x.canon() for x in b.args)
            if a_args_c == b_args_c and len(a_args_c) > 0:
                # Same args, different operation — definitely different
                # unless the operations are known aliases
                aliases = {
                    frozenset({'iadd', 'add'}),  # for immutable types
                    frozenset({'imult', 'mult'}),
                }
                if frozenset({a.name, b.name}) not in aliases:
                    return True

        # Different OOps with same-level args but one wraps in a
        # non-identity function: sorted(x) vs list(f(x)) where f ≠ sorted.
        # sorted produces a sorted list; list(f(x)) produces f(x) as a list
        # which has different ordering when f is not sorted.
        if a.name != b.name and len(a.args) == 1 and len(b.args) == 1:
            a0, b0 = a.args[0], b.args[0]
            # Check if one arg is a simple variable and the other wraps it
            if isinstance(a0, OVar) and isinstance(b0, OOp):
                # a = op_a(var), b = op_b(op_c(var))
                # Different transformation chains → NEQ
                if len(b0.args) == 1 and isinstance(b0.args[0], OVar):
                    if a0.canon() == b0.args[0].canon():
                        return True
            if isinstance(b0, OVar) and isinstance(a0, OOp):
                if len(a0.args) == 1 and isinstance(a0.args[0], OVar):
                    if b0.canon() == a0.args[0].canon():
                        return True

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

    # Same fold structure — recurse into components
    if isinstance(a, OFold) and isinstance(b, OFold):
        if a.op_name == b.op_name:
            if _detect_provable_neq(a.init, b.init, params, in_case_branch, param_duck_types):
                return True
            if _detect_provable_neq(a.collection, b.collection, params, in_case_branch, param_duck_types):
                return True
        else:
            # Different fold operations (e.g., iadd vs imult)
            return True

    # OMap — same transform structure, recurse
    if isinstance(a, OMap) and isinstance(b, OMap):
        if _detect_provable_neq(a.transform, b.transform, params, in_case_branch, param_duck_types):
            return True
        if _detect_provable_neq(a.collection, b.collection, params, in_case_branch, param_duck_types):
            return True

    # OLam — same body structure, recurse
    if isinstance(a, OLam) and isinstance(b, OLam):
        if len(a.params) != len(b.params):
            return True
        if _detect_provable_neq(a.body, b.body, params, in_case_branch, param_duck_types):
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
            # OOp vs OMap — different computation kinds
            # (e.g. _genexpr_var vs map: generator consumed once vs reusable list)
            if isinstance(a, OOp) and isinstance(b, OMap):
                return True
            if isinstance(b, OOp) and isinstance(a, OMap):
                return True
            # OFold vs OOp — iterative accumulation vs simple operation.
            # Only fire when the OOp is a known builtin/operation, not
            # an unresolved function call (which might wrap a fold internally).
            if isinstance(a, OFold) and isinstance(b, OOp):
                if not b.name.startswith('_') and not b.name.startswith('?'):
                    return True
            if isinstance(b, OFold) and isinstance(a, OOp):
                if not a.name.startswith('_') and not a.name.startswith('?'):
                    return True
            # OOp vs OCase — method/builtin call vs conditional
            if isinstance(a, OOp) and isinstance(b, OCase):
                if a.name.startswith('.') or a.name in (
                    'len', 'sum', 'sorted', 'list', 'set', 'tuple',
                    'map', 'filter', 'zip', 'enumerate', 'range',
                    'str', 'int', 'float', 'bool', 'type',
                ):
                    return True
            if isinstance(b, OOp) and isinstance(a, OCase):
                if b.name.startswith('.') or b.name in (
                    'len', 'sum', 'sorted', 'list', 'set', 'tuple',
                    'map', 'filter', 'zip', 'enumerate', 'range',
                    'str', 'int', 'float', 'bool', 'type',
                ):
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
                              'and', 'or', 'max', 'min'):
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
            # Fold keys encode the loop body — only match if keys are identical
            # (different loop bodies = different computations)
            return (a.op_name == b.op_name and
                    _flexible_match(a.init, b.init) and
                    _flexible_match(a.collection, b.collection))
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
        return OFold(term.op_name, _subst(term.init, mapping),
                     _subst(term.collection, mapping))
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
