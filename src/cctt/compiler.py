"""§2: AST Compiler — Python Source → Z3 PyObj Terms.

Compiles Python AST to presheaf sections (guard, term) pairs.
Implements all compilation rules E1-E12, S1-S9 from the monograph,
plus enhanced handling for:
  - Nested functions with closures (D2: β-reduction)
  - Generators and yield (D6: laziness adjunction)
  - Complex comprehensions with filters
  - Class definitions and method dispatch
  - Star args, walrus operator, global/nonlocal
  - Decorator patterns
  - Assert, delete, with statements
  - Multiple return values (tuples)
"""
from __future__ import annotations
import ast
import hashlib
import textwrap
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

from .theory import (
    Theory, _z3, _HAS_Z3,
    ADD, SUB, MUL, FLOORDIV, MOD, POW,
    LSHIFT, RSHIFT, BITOR, BITAND, BITXOR,
    LT, LE, GT, GE, EQ, NE, MAX, MIN,
    IADD, IMUL, NEG, ABS_, NOT, BOOL_, INT_, LEN_,
    GETITEM,
)

# Python builtins that get shared Z3 function symbols (univalence)
SHARED_BUILTINS = frozenset({
    'sorted', 'reversed', 'list', 'tuple', 'set', 'frozenset',
    'dict', 'sum', 'any', 'all', 'enumerate', 'zip', 'map',
    'filter', 'type', 'hash', 'id', 'repr', 'str', 'iter',
    'next', 'print', 'input', 'open', 'ord', 'chr',
    'float', 'complex', 'bytes', 'bytearray', 'memoryview',
    'object', 'super', 'property', 'classmethod', 'staticmethod',
    'isinstance', 'issubclass', 'callable', 'getattr', 'setattr',
    'hasattr', 'delattr', 'vars', 'dir',
})

# Module-level functions that get shared symbols
SHARED_MODULE_FUNCS = frozenset({
    'math.copysign', 'math.sqrt', 'math.log', 'math.floor', 'math.ceil',
    'math.gcd', 'math.isnan', 'math.isinf', 'math.factorial',
    'operator.add', 'operator.sub', 'operator.mul', 'operator.truediv',
    'operator.itemgetter', 'operator.attrgetter',
    'functools.reduce', 'functools.partial', 'functools.lru_cache',
    'itertools.chain', 'itertools.groupby', 'itertools.accumulate',
    'itertools.product', 'itertools.combinations', 'itertools.permutations',
    'itertools.starmap', 'itertools.zip_longest',
    'collections.Counter', 'collections.defaultdict', 'collections.OrderedDict',
    'collections.deque', 'collections.namedtuple',
    'heapq.heappush', 'heapq.heappop', 'heapq.heapify',
    'heapq.nsmallest', 'heapq.nlargest', 'heapq.merge',
    'bisect.bisect_left', 'bisect.bisect_right', 'bisect.insort',
    'copy.copy', 'copy.deepcopy',
    'json.dumps', 'json.loads',
    're.findall', 're.match', 're.sub', 're.split', 're.compile',
    'hashlib.sha256', 'hashlib.md5',
    'struct.pack', 'struct.unpack',
    'textwrap.dedent', 'textwrap.fill',
    'io.StringIO', 'io.BytesIO',
    'contextlib.suppress',
})


def _stable_hash(s: str) -> int:
    """Stable hash for AST content -> shared symbol key."""
    return int(hashlib.md5(s.encode()).hexdigest()[:8], 16)


@dataclass
class Env:
    """Compilation environment: variable name → Z3 PyObj term."""
    T: Theory
    bindings: Dict[str, Any] = field(default_factory=dict)
    func_name: str = ''
    is_rec: bool = False
    # Track nested function ASTs for inlining
    func_defs: Dict[str, ast.FunctionDef] = field(default_factory=dict)
    # Track class definitions
    class_defs: Dict[str, ast.ClassDef] = field(default_factory=dict)
    # Track imports for module-qualified names
    imports: Dict[str, str] = field(default_factory=dict)
    # Depth limit for recursion protection
    depth: int = 0

    def get(self, name: str) -> Optional[Any]:
        return self.bindings.get(name)

    def put(self, name: str, val: Any):
        self.bindings[name] = val

    def copy(self) -> 'Env':
        e = Env(self.T, dict(self.bindings), self.func_name, self.is_rec,
                dict(self.func_defs), dict(self.class_defs),
                dict(self.imports), self.depth)
        return e


@dataclass(frozen=True)
class Section:
    """A presheaf section: (guard, term) pair."""
    guard: Any
    term: Any


# ═══════════════════════════════════════════════════════════
# Expression Compilation (E1-E12)
# ═══════════════════════════════════════════════════════════

def compile_expr(node: ast.expr, env: Env) -> Any:
    """Compile a Python expression AST node to a Z3 PyObj term."""
    try:
        result = _compile_expr_inner(node, env)
        return _ensure_z3(result, env.T)
    except Exception:
        return env.T.fresh('_err')


def _compile_expr_inner(node: ast.expr, env: Env) -> Any:
    """Inner compile_expr — may raise on Z3 type errors."""
    T = env.T; S = T.S

    # E1: Literals
    if isinstance(node, ast.Constant):
        v = node.value
        if isinstance(v, bool): return T.mkbool(v)
        if isinstance(v, int): return T.mkint(v)
        if isinstance(v, str): return T.mkstr(v)
        if v is None: return T.mknone()
        if isinstance(v, float):
            if v != v:  # NaN
                return T.fresh('nan')
            if v == float('inf') or v == float('-inf'):
                return T.fresh('inf')
            # Approximate float as int when possible
            if v == int(v) and abs(v) < 2**31:
                return T.mkint(int(v))
            return T.fresh('float')
        return T.fresh('const')

    # E2: Variables
    if isinstance(node, ast.Name):
        name = node.id
        v = env.get(name)
        if v is not None:
            return v
        # Check if it's a known builtin/module
        if name in SHARED_BUILTINS:
            return T.fresh(f'builtin_{name}')
        if name in env.imports:
            return T.fresh(f'import_{name}')
        return T.fresh(f'var_{name}')

    # E3: Binary operations
    if isinstance(node, ast.BinOp):
        l, r = compile_expr(node.left, env), compile_expr(node.right, env)
        op_map = {
            ast.Add: ADD, ast.Sub: SUB, ast.Mult: MUL,
            ast.FloorDiv: FLOORDIV, ast.Mod: MOD, ast.Pow: POW,
            ast.LShift: LSHIFT, ast.RShift: RSHIFT,
            ast.BitOr: BITOR, ast.BitAnd: BITAND, ast.BitXor: BITXOR,
        }
        op = op_map.get(type(node.op))
        if op is not None:
            return T.binop(op, l, r)
        # MatMult, true division
        if isinstance(node.op, ast.Div):
            fn = T.shared_fn('truediv', 2)
            return fn(l, r)
        return T.fresh('binop')

    # E4: Unary operations
    if isinstance(node, ast.UnaryOp):
        a = compile_expr(node.operand, env)
        op_map = {ast.USub: NEG, ast.Not: NOT, ast.Invert: NOT}
        op = op_map.get(type(node.op))
        if op is not None:
            return T.unop(op, a)
        if isinstance(node.op, ast.UAdd):
            return a
        return T.fresh('unary')

    # E5: Comparisons (chained)
    if isinstance(node, ast.Compare):
        left = compile_expr(node.left, env)
        op_map = {ast.Eq: EQ, ast.NotEq: NE, ast.Lt: LT, ast.LtE: LE,
                  ast.Gt: GT, ast.GtE: GE}
        parts = []
        for op, comp in zip(node.ops, node.comparators):
            right = compile_expr(comp, env)
            op_id = op_map.get(type(op))
            if op_id is not None:
                parts.append(T.binop(op_id, left, right))
            elif isinstance(op, (ast.Is, ast.IsNot)):
                # is/is not → structural equality
                if isinstance(op, ast.Is):
                    parts.append(S.BoolObj(left == right))
                else:
                    parts.append(S.BoolObj(left != right))
            elif isinstance(op, (ast.In, ast.NotIn)):
                fn = T.shared_fn('contains', 2)
                if isinstance(op, ast.In):
                    parts.append(fn(right, left))
                else:
                    parts.append(T.unop(NOT, fn(right, left)))
            else:
                parts.append(T.fresh('cmp'))
            left = right
        if len(parts) == 1:
            return parts[0]
        # Chain: a < b < c → (a < b) and (b < c)
        result = parts[-1]
        for p in reversed(parts[:-1]):
            result = _z3.If(T.truthy(p), result, T.mkbool(False))
        return result

    # E6: Boolean operations (short-circuit, return values)
    if isinstance(node, ast.BoolOp):
        vals = [compile_expr(v, env) for v in node.values]
        if isinstance(node.op, ast.And):
            r = vals[-1]
            for v in reversed(vals[:-1]):
                r = _z3.If(T.truthy(v), r, v)
            return r
        else:  # Or
            r = vals[-1]
            for v in reversed(vals[:-1]):
                r = _z3.If(T.truthy(v), v, r)
            return r

    # E7: Conditional expression
    if isinstance(node, ast.IfExp):
        c = compile_expr(node.test, env)
        t = compile_expr(node.body, env)
        f = compile_expr(node.orelse, env)
        return _z3.If(T.truthy(c), t, f)

    # E8: Function calls
    if isinstance(node, ast.Call):
        return compile_call(node, env)

    # E9: Subscript
    if isinstance(node, ast.Subscript):
        base = compile_expr(node.value, env)
        if isinstance(node.slice, ast.Slice):
            fn = T.shared_fn('slice', 3)
            lower = compile_expr(node.slice.lower, env) if node.slice.lower else T.mknone()
            upper = compile_expr(node.slice.upper, env) if node.slice.upper else T.mknone()
            step = compile_expr(node.slice.step, env) if node.slice.step else T.mknone()
            return fn(base, lower, upper)
        idx = compile_expr(node.slice, env)
        return T.binop(GETITEM, base, idx)

    # E10: Tuple/List display
    if isinstance(node, (ast.Tuple, ast.List)):
        elts = [compile_expr(e, env) for e in node.elts]
        return T.mklist(*elts)

    # E11: Comprehension
    if isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
        return _compile_comprehension(node, env)

    # DictComp
    if isinstance(node, ast.DictComp):
        return _compile_dict_comp(node, env)

    # E12: Attribute access
    if isinstance(node, ast.Attribute):
        # Check for module-qualified names
        if isinstance(node.value, ast.Name):
            mod = node.value.id
            attr = node.attr
            qualified = f'{mod}.{attr}'
            # Module constants
            if qualified in ('math.inf', 'math.nan', 'math.pi', 'math.e',
                           'sys.maxsize', 'float.inf'):
                return T.fresh(f'const_{qualified}')
            # Module functions → shared symbol
            if qualified in SHARED_MODULE_FUNCS or mod in env.imports:
                # Will be resolved at call site
                pass
        obj = compile_expr(node.value, env)
        fn = T.shared_fn(f'attr_{node.attr}', 1)
        return fn(obj)

    # Dict literal
    if isinstance(node, ast.Dict):
        if not node.keys:
            return T.mkref()
        # Build dict as sequence of set operations
        d = T.mkref()
        for k, v in zip(node.keys, node.values):
            if k is None:  # **unpacking
                kv = compile_expr(v, env)
                fn = T.shared_fn('mut_update', 2)
                d = fn(d, kv)
            else:
                kc = compile_expr(k, env)
                vc = compile_expr(v, env)
                fn = T.shared_fn('mut___setitem__', 3)
                d = fn(d, kc, vc)
        return d

    # Set literal
    if isinstance(node, ast.Set):
        elts = [compile_expr(e, env) for e in node.elts]
        s = T.mkref()
        fn = T.shared_fn('mut_add', 2)
        for e in elts:
            s = fn(s, e)
        return s

    # Lambda
    if isinstance(node, ast.Lambda):
        # Store as function definition for potential inlining
        return T.fresh('lambda')

    # Starred (in calls)
    if isinstance(node, ast.Starred):
        return compile_expr(node.value, env)

    # F-string / JoinedStr
    if isinstance(node, ast.JoinedStr):
        parts = []
        for v in node.values:
            if isinstance(v, ast.Constant):
                parts.append(compile_expr(v, env))
            elif isinstance(v, ast.FormattedValue):
                parts.append(compile_expr(v.value, env))
            else:
                parts.append(compile_expr(v, env))
        if len(parts) == 1:
            return parts[0]
        # Join with str concat shared symbol
        r = parts[0]
        fn = T.shared_fn('str_concat', 2)
        for p in parts[1:]:
            r = fn(r, p)
        return r

    # Named expression (walrus operator)
    if isinstance(node, ast.NamedExpr):
        val = compile_expr(node.value, env)
        if isinstance(node.target, ast.Name):
            env.put(node.target.id, val)
        return val

    # Await
    if isinstance(node, ast.Await):
        return compile_expr(node.value, env)

    # Yield / YieldFrom
    if isinstance(node, (ast.Yield, ast.YieldFrom)):
        if node.value:
            return compile_expr(node.value, env)
        return T.mknone()

    return T.fresh(type(node).__name__)


def _compile_comprehension(node, env):
    """Compile list/set/generator comprehension using shared symbols."""
    T = env.T
    if not node.generators:
        return T.fresh('comp')

    gen = node.generators[0]
    it = compile_expr(gen.iter, env)

    # Build a canonical key from the comprehension body + filters
    elt_node = node.elt if hasattr(node, 'elt') else node
    body_dump = ast.dump(elt_node)
    filter_dump = '|'.join(ast.dump(f) for f in gen.ifs) if gen.ifs else ''
    target_dump = ast.dump(gen.target) if gen.target else ''

    # Use a normalized hash that captures the semantic operation
    key = _stable_hash(f'{body_dump}|{filter_dump}|{target_dump}')

    if gen.ifs:
        fn = T.shared_fn(f'comp_filt_{key}', 1)
    else:
        fn = T.shared_fn(f'comp_{key}', 1)

    result = fn(it)

    # Handle nested generators
    for extra_gen in node.generators[1:]:
        extra_it = compile_expr(extra_gen.iter, env)
        key2 = _stable_hash(f'nested_{key}_{ast.dump(extra_gen.iter)}')
        fn2 = T.shared_fn(f'comp_nest_{key2}', 2)
        result = fn2(result, extra_it)

    # SetComp wraps in set
    if isinstance(node, ast.SetComp):
        setfn = T.shared_fn('set', 1)
        result = setfn(result)

    return result


def _compile_dict_comp(node, env):
    """Compile dict comprehension."""
    T = env.T
    if not node.generators:
        return T.mkref()
    gen = node.generators[0]
    it = compile_expr(gen.iter, env)
    key_dump = ast.dump(node.key)
    val_dump = ast.dump(node.value)
    key = _stable_hash(f'dictcomp_{key_dump}|{val_dump}')
    fn = T.shared_fn(f'dictcomp_{key}', 1)
    return fn(it)


def compile_call(node: ast.Call, env: Env) -> Any:
    """Compile a function call with shared symbols + inlining."""
    T = env.T; S = T.S

    # Self-recursive call
    if isinstance(node.func, ast.Name) and node.func.id == env.func_name and env.is_rec:
        args = [compile_expr(a, env) for a in node.args]
        T._uid += 1
        fn = _z3.Function(f'rec_{env.func_name}_{T._uid}', *([S]*len(args)), S)
        return fn(*args)

    # Nested function: inline (D2 β-reduction)
    if isinstance(node.func, ast.Name):
        fname = node.func.id
        if fname in env.func_defs and env.depth < 3:
            fdef = env.func_defs[fname]
            r = inline_call(fdef, node.args, env)
            if r is not None:
                return r

    # Module-qualified calls: mod.func(args)
    if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name):
        mod = node.func.value.id
        method = node.func.attr
        qualified = f'{mod}.{method}'
        args = [compile_expr(a, env) for a in node.args]
        n = len(args)

        # Known module functions → shared symbols
        if qualified in SHARED_MODULE_FUNCS or mod in ('math', 'operator', 'functools',
            'itertools', 'collections', 'heapq', 'bisect', 'copy', 'json', 're',
            'hashlib', 'struct', 'textwrap', 'io', 'contextlib'):
            fn = T.shared_fn(f'call_{qualified}', n)
            if n > 0:
                return fn(*args)
            return T.fresh(f'call0_{qualified}')

    # Named calls
    if isinstance(node.func, ast.Name):
        name = node.func.id
        args = [compile_expr(a, env) for a in node.args]
        n = len(args)

        # Handle keyword arguments for builtins
        kwargs = {}
        for kw in node.keywords:
            if kw.arg is not None:
                try:
                    v = compile_expr(kw.value, env)
                    # Verify it's a valid Z3 expression
                    if hasattr(v, 'sort'):
                        kwargs[kw.arg] = v
                    else:
                        # Not a Z3 expr — use a hashed fresh symbol
                        h = _stable_hash(ast.dump(kw.value))
                        kwargs[kw.arg] = T.fresh(f'kw_{kw.arg}_{h}')
                except Exception:
                    h = _stable_hash(ast.dump(kw.value))
                    kwargs[kw.arg] = T.fresh(f'kw_{kw.arg}_{h}')

        # Builtins with native Z3 semantics
        if name == 'abs' and n == 1: return T.unop(ABS_, args[0])
        if name == 'int' and n == 1: return T.unop(INT_, args[0])
        if name == 'bool' and n == 1: return T.unop(BOOL_, args[0])
        if name == 'len' and n == 1: return T.unop(LEN_, args[0])
        if name == 'max':
            if n == 2: return T.binop(MAX, args[0], args[1])
            if n == 1:
                if 'key' in kwargs:
                    fn = T.shared_fn('max_key', 2)
                    return fn(args[0], kwargs['key'])
                fn = T.shared_fn('max', 1)
                return fn(args[0])
            if n > 2:
                r = args[0]
                for a in args[1:]:
                    r = T.binop(MAX, r, a)
                return r
        if name == 'min':
            if n == 2: return T.binop(MIN, args[0], args[1])
            if n == 1:
                if 'key' in kwargs:
                    fn = T.shared_fn('min_key', 2)
                    return fn(args[0], kwargs['key'])
                fn = T.shared_fn('min', 1)
                return fn(args[0])
            if n > 2:
                r = args[0]
                for a in args[1:]:
                    r = T.binop(MIN, r, a)
                return r
        if name == 'range':
            return T.fresh('range')
        if name == 'pow' and n >= 2:
            return T.binop(POW, args[0], args[1])
        if name == 'divmod' and n == 2:
            fn = T.shared_fn('divmod', 2)
            return fn(args[0], args[1])

        # isinstance → fiber projection
        if name == 'isinstance' and n == 2:
            obj = args[0]
            tag = _resolve_isinstance_tag(node.args[1], T, obj)
            if tag is not None:
                return tag

        # Shared builtins (univalence)
        if name in SHARED_BUILTINS:
            has_key = 'key' in kwargs
            has_reverse = 'reverse' in kwargs
            if name == 'sorted':
                if has_key and has_reverse:
                    fn = T.shared_fn('sorted_key_rev', n + 1)
                    return fn(*args, kwargs['key'])
                if has_key:
                    fn = T.shared_fn('sorted_key', n + 1)
                    return fn(*args, kwargs['key'])
                if has_reverse:
                    fn = T.shared_fn('sorted_rev', n)
                    return fn(*args)
            if name == 'max' and has_key and n >= 1:
                fn = T.shared_fn('max_key', n + 1)
                return fn(*args, kwargs['key'])
            if name == 'min' and has_key and n >= 1:
                fn = T.shared_fn('min_key', n + 1)
                return fn(*args, kwargs['key'])
            if n > 0:
                fn = T.shared_fn(name, n)
                return fn(*args)
            return T.fresh(f'call0_{name}')

        # Known imported names (Counter, defaultdict, deque, etc.)
        if name in ('Counter', 'defaultdict', 'OrderedDict', 'deque',
                    'namedtuple', 'partial', 'reduce', 'chain',
                    'groupby', 'accumulate', 'product', 'combinations',
                    'permutations'):
            fn = T.shared_fn(f'call_{name}', max(n, 1))
            if n > 0:
                return fn(*args)
            return T.mkref()

        # Class instantiation
        if name in env.class_defs:
            return T.mkref()

        # Generic: shared symbol by name
        if n > 0:
            fn = T.shared_fn(f'call_{name}', n)
            return fn(*args)
        return T.fresh(f'call0_{name}')

    # Method calls: shared symbols
    if isinstance(node.func, ast.Attribute):
        obj = compile_expr(node.func.value, env)
        method = node.func.attr
        args = [compile_expr(a, env) for a in node.args]
        n = len(args) + 1  # +1 for receiver
        fn = T.shared_fn(f'meth_{method}', n)
        return fn(obj, *args)

    # Dynamic call (f(x) where f is a variable)
    if isinstance(node.func, ast.Name):
        fv = env.get(node.func.id)
        if fv is not None:
            args = [compile_expr(a, env) for a in node.args]
            fn = T.shared_fn(f'dyncall_{node.func.id}', len(args) + 1)
            return fn(fv, *args)

    return T.fresh('call')


def _resolve_isinstance_tag(type_arg, T, obj):
    """Resolve isinstance type argument to a Z3 bool expression."""
    S = T.S
    tag_map = {
        'int': T.TInt, 'float': T.TInt, 'bool': T.TBool_,
        'str': T.TStr_, 'list': T.TPair_, 'tuple': T.TPair_,
        'dict': T.TRef_, 'set': T.TRef_,
    }

    if isinstance(type_arg, ast.Name):
        tag = tag_map.get(type_arg.id)
        if tag is not None:
            return S.BoolObj(T.tag(obj) == tag)
        # Unknown type — shared predicate
        fn = T.shared_fn(f'isinstance_{type_arg.id}', 1)
        return fn(obj)

    # isinstance(x, (int, str)) — tuple of types
    if isinstance(type_arg, ast.Tuple):
        conditions = []
        for elt in type_arg.elts:
            if isinstance(elt, ast.Name):
                tag = tag_map.get(elt.id)
                if tag is not None:
                    conditions.append(T.tag(obj) == tag)
        if conditions:
            if len(conditions) == 1:
                return S.BoolObj(conditions[0])
            return S.BoolObj(_z3.Or(*conditions))

    return None


def inline_call(func_node, call_args, env):
    """Inline a nested function call (D2 defunctionalization)."""
    params = [a.arg for a in func_node.args.args]
    if len(call_args) != len(params):
        return None
    if env.depth > 2:
        return None
    ce = env.copy()
    ce.depth += 1
    for p, a in zip(params, call_args):
        ce.put(p, compile_expr(a, env))
    secs = extract_sections(func_node.body, ce)
    if len(secs) == 1:
        return secs[0].term
    if not secs:
        return None
    r = secs[-1].term
    for s in reversed(secs[:-1]):
        r = _z3.If(s.guard, s.term, r)
    return r


# ═══════════════════════════════════════════════════════════
# Section Extraction (presheaf over control flow)
# ═══════════════════════════════════════════════════════════

def extract_sections(stmts: list, env: Env,
                     guard: Any = None) -> List[Section]:
    """Extract presheaf sections from a statement list."""
    T = env.T
    if guard is None:
        guard = _z3.BoolVal(True)
    stmts = _skip_doc(stmts)
    sections: List[Section] = []

    for i, stmt in enumerate(stmts):
        if isinstance(stmt, ast.Return):
            val = compile_expr(stmt.value, env) if stmt.value else T.mknone()
            sections.append(Section(guard=guard, term=val))
            return sections

        elif isinstance(stmt, ast.If):
            cond = T.truthy(compile_expr(stmt.test, env))
            tg, fg = _z3.And(guard, cond), _z3.And(guard, _z3.Not(cond))
            tr = _has_ret(stmt.body)
            fr = _has_ret(stmt.orelse) if stmt.orelse else False
            if tr:
                sections.extend(extract_sections(stmt.body, env.copy(), tg))
            if fr and stmt.orelse:
                sections.extend(extract_sections(stmt.orelse, env.copy(), fg))
            if tr and fr:
                return sections
            if tr:
                re = env.copy()
                if stmt.orelse:
                    exec_stmts(stmt.orelse, re)
                sections.extend(extract_sections(stmts[i+1:], re, fg))
                return sections
            if fr:
                re = env.copy()
                exec_stmts(stmt.body, re)
                sections.extend(extract_sections(stmts[i+1:], re, tg))
                return sections
            te, fe = env.copy(), env.copy()
            exec_stmts(stmt.body, te)
            if stmt.orelse:
                exec_stmts(stmt.orelse, fe)
            _merge_envs(env, te, fe, cond)

        elif isinstance(stmt, ast.For) and _has_ret(stmt.body):
            # For loop with early return — compile as fold/filter.
            # Pattern: for x in coll: if cond(x): return early_val
            #          ...rest... (typically: return default_val)
            # This is all(not cond(x) for x in coll) → default_val, else early_val.
            for_result = _compile_for_with_return(stmt, env, guard, stmts[i+1:])
            if for_result is not None:
                sections.extend(for_result)
                return sections
            # Fallback: exec the loop and continue
            exec_one(stmt, env)

        elif isinstance(stmt, ast.Try):
            _exec_try_sections(stmt, env, guard, sections, stmts, i)
            return sections

        else:
            exec_one(stmt, env)

    return sections


def _compile_for_with_return(stmt, env, guard, rest_stmts):
    """Compile a for-loop with early return as a fold/filter OTerm.

    Recognizes the common pattern:
        for x in collection:
            if condition(x):
                return early_value
        return default_value

    This is equivalent to:
        all(not condition(x) for x in collection) ? default_value : early_value

    In OTerm form, this becomes a fold over the collection with the
    loop predicate as a filter.

    Also handles the inverse pattern (returning True on match, False as default)
    and patterns with multiple conditions or accumulator updates.
    """
    T = env.T

    if not isinstance(stmt.target, ast.Name):
        return None
    loop_var = stmt.target.id

    body = _skip_doc(stmt.body)

    # Pattern 1: for x in coll: if cond(x): return val
    #            return default
    # Also: for x in coll: if not cond(x): return val
    if (len(body) == 1 and isinstance(body[0], ast.If)
            and _has_ret(body[0].body)
            and len(body[0].body) == 1 and isinstance(body[0].body[0], ast.Return)):

        rest_stmts_clean = _skip_doc(rest_stmts)
        if not rest_stmts_clean:
            return None
        # The default return must be the next statement
        if not isinstance(rest_stmts_clean[0], ast.Return):
            return None

        default_val = compile_expr(rest_stmts_clean[0].value, env) if rest_stmts_clean[0].value else T.mknone()
        early_val = compile_expr(body[0].body[0].value, env) if body[0].body[0].value else T.mknone()

        # Compile the collection
        collection = compile_expr(stmt.iter, env)

        # Compile the condition
        loop_env = env.copy()
        loop_env.put(loop_var, T.fresh(loop_var))
        cond = compile_expr(body[0].test, loop_env)

        # Build: fold[and](True, map(lambda x: not cond(x), collection))
        # If fold result is True → return default, else → return early
        # This is expressed as an OTerm using a filter_fold pattern.
        T._uid += 1
        uid = T._uid
        # Use a shared function to represent "any(cond(x) for x in coll)"
        body_hash = _stable_hash(f'forret_{ast.dump(body[0].test)}_{uid}')
        check_fn = T.shared_fn(f'any_match_{body_hash}', 1)
        any_match = check_fn(collection)

        # Result: if any_match then early_val else default_val
        result = _z3.If(T.truthy(any_match), early_val, default_val)
        return [Section(guard=guard, term=result)]

    # Pattern 2: for x in coll: if cond(x): return val_a; return val_b
    #   (with else: return val_b in the if statement)
    if (len(body) == 2 and isinstance(body[0], ast.If)
            and _has_ret(body[0].body) and isinstance(body[1], ast.Return)):
        # This is: each iteration checks cond, returns early if true,
        # otherwise continues. After all iterations, returns body[1].
        rest_stmts_clean = _skip_doc(rest_stmts)
        if rest_stmts_clean and isinstance(rest_stmts_clean[0], ast.Return):
            # Default is at the end
            pass
        # The default value is the return after the loop
        default_val = compile_expr(body[1].value, env) if body[1].value else T.mknone()
        early_val = compile_expr(body[0].body[0].value, env) if (
            len(body[0].body) == 1 and isinstance(body[0].body[0], ast.Return)
            and body[0].body[0].value) else T.mknone()

        collection = compile_expr(stmt.iter, env)
        T._uid += 1
        uid = T._uid
        body_hash = _stable_hash(f'forret2_{ast.dump(body[0].test)}_{uid}')
        check_fn = T.shared_fn(f'any_match_{body_hash}', 1)
        any_match = check_fn(collection)
        result = _z3.If(T.truthy(any_match), early_val, default_val)
        return [Section(guard=guard, term=result)]

    return None


def _exec_try_sections(stmt, env, guard, sections, stmts, i):
    """Handle try/except in section extraction mode."""
    T = env.T
    body_secs = extract_sections(stmt.body, env.copy(), guard)
    handler_sig = '|'.join(
        ast.dump(h.type) if h.type else '__bare__'
        for h in (stmt.handlers if hasattr(stmt, 'handlers') else []))

    for s in body_secs:
        if handler_sig:
            T._uid += 1
            ctx = _z3.Function(
                f'try_{_stable_hash(handler_sig)}_{T._uid}', T.S, T.S)
            sections.append(Section(guard=s.guard, term=ctx(s.term)))
        else:
            sections.append(s)

    # Also extract from handlers
    for handler in (stmt.handlers if hasattr(stmt, 'handlers') else []):
        he = env.copy()
        if handler.name:
            he.put(handler.name, T.fresh(f'exc_{handler.name}'))
        handler_secs = extract_sections(handler.body, he, guard)
        sections.extend(handler_secs)

    if hasattr(stmt, 'orelse') and stmt.orelse:
        exec_stmts(stmt.orelse, env)
    if hasattr(stmt, 'finalbody') and stmt.finalbody:
        exec_stmts(stmt.finalbody, env)
    sections.extend(extract_sections(stmts[i+1:], env, guard))


# ═══════════════════════════════════════════════════════════
# Statement Execution (S1-S9)
# ═══════════════════════════════════════════════════════════

def exec_stmts(stmts, env):
    for s in _skip_doc(stmts):
        exec_one(s, env)


def exec_one(stmt, env):
    T = env.T

    # S1: Assignment
    if isinstance(stmt, ast.Assign):
        val = compile_expr(stmt.value, env)
        for t in stmt.targets:
            _assign_target(t, val, env)

    # S2: Augmented assignment
    elif isinstance(stmt, ast.AugAssign):
        if isinstance(stmt.target, ast.Name):
            name = stmt.target.id
            old = env.get(name) if env.get(name) is not None else T.fresh(name)
            rhs = compile_expr(stmt.value, env)
            op_map = {ast.Add: IADD, ast.Mult: IMUL, ast.Sub: SUB,
                      ast.FloorDiv: FLOORDIV, ast.Mod: MOD,
                      ast.BitOr: BITOR, ast.BitAnd: BITAND, ast.BitXor: BITXOR,
                      ast.LShift: LSHIFT, ast.RShift: RSHIFT, ast.Pow: POW}
            op = op_map.get(type(stmt.op), ADD)
            env.put(name, T.binop(op, old, rhs))
        elif isinstance(stmt.target, ast.Subscript):
            # obj[key] += val → mutation
            base = compile_expr(stmt.target.value, env)
            idx = compile_expr(stmt.target.slice, env)
            rhs = compile_expr(stmt.value, env)
            fn = T.shared_fn('mut___setitem__', 3)
            old_val = T.binop(GETITEM, base, idx)
            op_map = {ast.Add: ADD, ast.Mult: MUL, ast.Sub: SUB}
            op = op_map.get(type(stmt.op), ADD)
            new_val = T.binop(op, old_val, rhs)
            # Update the base variable
            if isinstance(stmt.target.value, ast.Name):
                env.put(stmt.target.value.id, fn(base, idx, new_val))
        elif isinstance(stmt.target, ast.Attribute):
            obj = compile_expr(stmt.target.value, env)
            rhs = compile_expr(stmt.value, env)
            fn = T.shared_fn(f'mut_attr_{stmt.target.attr}', 2)
            if isinstance(stmt.target.value, ast.Name):
                env.put(stmt.target.value.id, fn(obj, rhs))

    # S5: For loop
    elif isinstance(stmt, ast.For):
        _exec_for(stmt, env)

    # S6: While loop
    elif isinstance(stmt, ast.While):
        _exec_while(stmt, env)

    # S4: If (non-returning)
    elif isinstance(stmt, ast.If):
        cond = T.truthy(compile_expr(stmt.test, env))
        te, fe = env.copy(), env.copy()
        exec_stmts(stmt.body, te)
        if stmt.orelse:
            exec_stmts(stmt.orelse, fe)
        _merge_envs(env, te, fe, cond)

    # S7: Function definition
    elif isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
        env.func_defs[stmt.name] = stmt
        env.put(stmt.name, ('__func__', stmt))

    # S7b: Class definition
    elif isinstance(stmt, ast.ClassDef):
        env.class_defs[stmt.name] = stmt
        env.put(stmt.name, ('__class__', stmt))

    # S8: Expression statement (mutation tracking)
    elif isinstance(stmt, ast.Expr):
        _exec_expr_stmt(stmt, env)

    # S9: Try/except (exec mode)
    elif isinstance(stmt, ast.Try):
        exec_stmts(stmt.body, env)
        for handler in (stmt.handlers if hasattr(stmt, 'handlers') else []):
            # Execute handler body in case it modifies env
            he = env.copy()
            if handler.name:
                he.put(handler.name, T.fresh(f'exc'))
            exec_stmts(handler.body, he)
        if hasattr(stmt, 'orelse') and stmt.orelse:
            exec_stmts(stmt.orelse, env)
        if hasattr(stmt, 'finalbody') and stmt.finalbody:
            exec_stmts(stmt.finalbody, env)

    # With statement
    elif isinstance(stmt, (ast.With, ast.AsyncWith)):
        for item in stmt.items:
            cm = compile_expr(item.context_expr, env)
            if item.optional_vars and isinstance(item.optional_vars, ast.Name):
                env.put(item.optional_vars.id, T.mkref())
        exec_stmts(stmt.body, env)

    # Import
    elif isinstance(stmt, (ast.Import, ast.ImportFrom)):
        _exec_import(stmt, env)

    # Assert
    elif isinstance(stmt, ast.Assert):
        pass  # Assertions don't affect return value

    # Delete
    elif isinstance(stmt, ast.Delete):
        for target in stmt.targets:
            if isinstance(target, ast.Name):
                env.bindings.pop(target.id, None)

    # Global/Nonlocal
    elif isinstance(stmt, (ast.Global, ast.Nonlocal)):
        pass  # Don't affect compilation

    # Pass/Break/Continue
    elif isinstance(stmt, (ast.Pass, ast.Break, ast.Continue)):
        pass

    # Raise
    elif isinstance(stmt, ast.Raise):
        pass  # Could model as Bottom


def _exec_expr_stmt(stmt, env):
    """Handle expression statements, tracking mutations."""
    T = env.T
    val = stmt.value

    # Method calls that mutate: obj.method(args)
    if (isinstance(val, ast.Call)
            and isinstance(val.func, ast.Attribute)
            and isinstance(val.func.value, ast.Name)):
        obj_name = val.func.value.id
        method = val.func.attr
        obj = env.get(obj_name)
        if obj is not None:
            args = [compile_expr(a, env) for a in val.args]
            fn = T.shared_fn(f'mut_{method}', len(args) + 1)
            env.put(obj_name, fn(obj, *args))
            return

    # Just compile the expression (may have side effects via walrus)
    compile_expr(val, env)


def _exec_import(stmt, env):
    """Track imports for module-qualified name resolution."""
    if isinstance(stmt, ast.Import):
        for alias in stmt.names:
            name = alias.asname if alias.asname else alias.name
            env.imports[name] = alias.name
    elif isinstance(stmt, ast.ImportFrom):
        module = stmt.module or ''
        for alias in stmt.names:
            name = alias.asname if alias.asname else alias.name
            env.imports[name] = f'{module}.{alias.name}'


def _ensure_z3(val, T):
    """Ensure val is a valid Z3 expression of sort PyObj."""
    if val is None:
        return T.fresh('_nil')
    try:
        if hasattr(val, 'sort') and val.sort() == T.S:
            return val
    except Exception:
        pass
    return T.fresh('_opaque')


def _assign_target(target, val, env):
    T = env.T
    val = _ensure_z3(val, T)
    if isinstance(target, ast.Name):
        env.put(target.id, val)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for j, elt in enumerate(target.elts):
            if isinstance(elt, ast.Starred):
                # *rest = val[j:]
                fn = T.shared_fn('slice_from', 2)
                _assign_target(elt.value, fn(val, T.mkint(j)), env)
            else:
                _assign_target(elt, T.binop(GETITEM, val, T.mkint(j)), env)
    elif isinstance(target, ast.Subscript):
        # obj[key] = val → mutation
        if isinstance(target.value, ast.Name):
            base = env.get(target.value.id)
            if base is None:
                base = T.fresh(target.value.id)
            try:
                idx = compile_expr(target.slice, env)
                idx = _ensure_z3(idx, T)
                fn = T.shared_fn('mut___setitem__', 3)
                env.put(target.value.id, fn(base, idx, val))
            except Exception:
                fn = T.shared_fn('mut___setitem__', 3)
                env.put(target.value.id, fn(base, T.fresh('_idx'), val))
    elif isinstance(target, ast.Attribute):
        if isinstance(target.value, ast.Name):
            base = env.get(target.value.id)
            if base is None:
                base = T.fresh(target.value.id)
            fn = T.shared_fn(f'mut_attr_{target.attr}', 2)
            env.put(target.value.id, fn(base, val))


def _exec_for(stmt, env):
    T = env.T
    # Handle tuple unpacking in for target
    if isinstance(stmt.target, (ast.Tuple, ast.List)):
        _exec_for_unpack(stmt, env)
        return

    if not isinstance(stmt.target, ast.Name):
        return
    lv = stmt.target.id
    start, stop = _extract_range(stmt.iter, env)

    if start is not None:
        _exec_range_for(stmt, env, lv, start, stop)
    else:
        _exec_iter_for(stmt, env, lv)


def _exec_range_for(stmt, env, lv, start, stop):
    """Handle for i in range(...)."""
    T = env.T
    modified = _find_modified(stmt.body)
    state = {vn: env.get(vn) for vn in modified if vn != lv and env.get(vn) is not None}
    if not state:
        return

    # Canonical fold: acc OP= loop_var
    if len(stmt.body) == 1 and len(state) == 1:
        s = stmt.body[0]
        an = next(iter(state))
        if (isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name)
                and s.target.id == an):
            # Check if RHS is just the loop variable
            if isinstance(s.value, ast.Name) and s.value.id == lv:
                op_map = {ast.Add: ADD, ast.Mult: MUL}
                op = op_map.get(type(s.op))
                if op is not None:
                    env.put(an, T.fold(op, start, stop, state[an]))
                    return
            # Check if RHS involves loop variable: acc += expr(i)
            # This is still a fold, just with a more complex step

    # General RecFunction fold
    T._uid += 1; uid = T._uid
    i_sym = _z3.Int(f'_li{uid}')
    for vn, init in state.items():
        rfn = _z3.RecFunction(f'lp_{vn}_{uid}', _z3.IntSort(), T.S)
        se = env.copy()
        se.put(lv, T.S.IntObj(i_sym))
        se.put(vn, rfn(i_sym + 1))
        exec_stmts(stmt.body, se)
        after = se.get(vn) if se.get(vn) is not None else T.fresh(f'lp_{vn}')
        try:
            _z3.RecAddDefinition(rfn, [i_sym], _z3.If(i_sym >= stop, init, after))
            env.put(vn, rfn(start))
        except Exception:
            env.put(vn, T.fresh(f'lp_{vn}'))


def _exec_iter_for(stmt, env, lv):
    """Handle for x in collection."""
    T = env.T
    it = compile_expr(stmt.iter, env)
    modified = _find_modified(stmt.body)
    state = {vn: env.get(vn) for vn in modified if vn != lv and env.get(vn) is not None}

    if not state:
        # No accumulator — just iterate for side effects
        # Model as shared function application
        body_hash = _stable_hash('|'.join(ast.dump(s) for s in stmt.body))
        fn = T.shared_fn(f'foreach_{body_hash}', 1)
        result = fn(it)
        return

    # Model as a fold over the collection
    T._uid += 1; uid = T._uid
    for vn, init in state.items():
        body_hash = _stable_hash(f'{vn}|{"|".join(ast.dump(s) for s in stmt.body)}')
        fn = T.shared_fn(f'fold_{body_hash}', 2)
        env.put(vn, fn(init, it))


def _exec_for_unpack(stmt, env):
    """Handle for (a, b) in collection."""
    T = env.T
    it = compile_expr(stmt.iter, env)
    modified = _find_modified(stmt.body)
    target_names = []
    if isinstance(stmt.target, (ast.Tuple, ast.List)):
        for elt in stmt.target.elts:
            if isinstance(elt, ast.Name):
                target_names.append(elt.id)
    state = {vn: env.get(vn) for vn in modified
             if vn not in target_names and env.get(vn) is not None}
    if not state:
        return

    T._uid += 1; uid = T._uid
    for vn, init in state.items():
        body_hash = _stable_hash(f'{vn}|unpack|{"|".join(ast.dump(s) for s in stmt.body)}')
        fn = T.shared_fn(f'fold_unpack_{body_hash}', 2)
        env.put(vn, fn(init, it))


def _exec_while(stmt, env):
    T = env.T
    modified = _find_modified(stmt.body)
    state = {vn: env.get(vn) for vn in modified if env.get(vn) is not None}
    if not state:
        return
    T._uid += 1; uid = T._uid
    ctr = _z3.Int(f'_wi{uid}')
    for vn, init in state.items():
        rfn = _z3.RecFunction(f'wh_{vn}_{uid}', _z3.IntSort(), T.S)
        se = env.copy()
        se.put(vn, rfn(ctr + 1))
        exec_stmts(stmt.body, se)
        cond = T.truthy(compile_expr(stmt.test, se))
        after = se.get(vn) if se.get(vn) is not None else T.fresh(f'wh_{vn}')
        try:
            _z3.RecAddDefinition(rfn, [ctr],
                _z3.If(ctr > 50, init, _z3.If(cond, after, init)))
            env.put(vn, rfn(_z3.IntVal(0)))
        except Exception:
            env.put(vn, T.fresh(f'wh_{vn}'))


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

def _merge_envs(target, te, fe, cond):
    for k in set(te.bindings) | set(fe.bindings):
        tv, fv = te.get(k), fe.get(k)
        if tv is None or fv is None:
            continue
        orig = target.get(k)
        if orig is not None and tv is orig and fv is orig:
            continue
        try:
            target.put(k, _z3.If(cond, tv, fv))
        except Exception:
            pass


def _extract_range(iter_expr, env):
    T = env.T; S = T.S
    if not (isinstance(iter_expr, ast.Call) and isinstance(iter_expr.func, ast.Name)
            and iter_expr.func.id == 'range'):
        return None, None
    args = iter_expr.args
    if len(args) == 1:
        v = compile_expr(args[0], env)
        r = _to_int_expr(v, S)
        if r is not None:
            return _z3.IntVal(0), r
        return None, None
    if len(args) >= 2:
        a, b = compile_expr(args[0], env), compile_expr(args[1], env)
        ra, rb = _to_int_expr(a, S), _to_int_expr(b, S)
        if ra is not None and rb is not None:
            return ra, rb
    return None, None


def _to_int_expr(term, S):
    if not hasattr(term, 'decl'):
        return None
    name = term.decl().name()
    if name == 'IntObj':
        return _z3.simplify(term.arg(0))
    if name == 'binop' and term.num_args() == 3:
        a_int = _to_int_expr(term.arg(1), S)
        b_int = _to_int_expr(term.arg(2), S)
        if a_int is not None and b_int is not None:
            try:
                op_num = int(str(_z3.simplify(term.arg(0))))
                if op_num == ADD: return a_int + b_int
                if op_num == SUB: return a_int - b_int
                if op_num == MUL: return a_int * b_int
            except Exception:
                pass
            return S.ival(term)
    if hasattr(term, 'sort') and str(term.sort()) == 'PyObj':
        return S.ival(term)
    return None


def _find_modified(stmts):
    modified, seen = [], set()
    for s in stmts:
        names = []
        if isinstance(s, ast.AugAssign):
            if isinstance(s.target, ast.Name):
                names.append(s.target.id)
        elif isinstance(s, ast.Assign):
            for t in s.targets:
                if isinstance(t, ast.Name):
                    names.append(t.id)
                elif isinstance(t, (ast.Tuple, ast.List)):
                    names.extend(e.id for e in t.elts if isinstance(e, ast.Name))
        elif isinstance(s, ast.If):
            names.extend(_find_modified(s.body))
            if s.orelse:
                names.extend(_find_modified(s.orelse))
        elif isinstance(s, ast.For):
            names.extend(_find_modified(s.body))
        elif isinstance(s, ast.While):
            names.extend(_find_modified(s.body))
        elif isinstance(s, ast.Expr):
            # Mutation via method call
            if (isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Attribute)
                    and isinstance(s.value.func.value, ast.Name)):
                names.append(s.value.func.value.id)
        elif isinstance(s, ast.Try):
            names.extend(_find_modified(s.body))
            for h in (s.handlers if hasattr(s, 'handlers') else []):
                names.extend(_find_modified(h.body))
        for n in names:
            if n not in seen:
                seen.add(n)
                modified.append(n)
    return modified


def _skip_doc(body):
    if (body and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        return body[1:]
    return body


def _has_ret(stmts):
    for s in stmts:
        if isinstance(s, ast.Return):
            return True
        if isinstance(s, ast.If) and _has_ret(s.body) and s.orelse and _has_ret(s.orelse):
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Nat-Eliminator Extraction
# ═══════════════════════════════════════════════════════════

def detect_canon_rec(body, func_name, param, env):
    """Extract the Nat-eliminator (catamorphism) from a recursive function."""
    T = env.T
    body = _skip_doc(body)
    if len(body) != 2:
        return None
    base_stmt, rec_stmt = body

    if not (isinstance(base_stmt, ast.If) and not base_stmt.orelse
            and len(base_stmt.body) == 1 and isinstance(base_stmt.body[0], ast.Return)
            and base_stmt.body[0].value is not None):
        return None
    bv = base_stmt.body[0].value
    if not (isinstance(bv, ast.Constant) and isinstance(bv.value, int)):
        return None
    base_val = bv.value

    test = base_stmt.test
    if not isinstance(test, ast.Compare) or len(test.ops) != 1:
        return None
    if not (isinstance(test.left, ast.Name) and test.left.id == param):
        return None
    c = test.comparators[0]
    if not isinstance(c, ast.Constant) or not isinstance(c.value, int):
        return None
    if isinstance(test.ops[0], ast.LtE):
        threshold = c.value
    elif isinstance(test.ops[0], ast.Lt):
        threshold = c.value - 1
    elif isinstance(test.ops[0], ast.Eq):
        threshold = c.value
    else:
        return None

    if not (isinstance(rec_stmt, ast.Return) and rec_stmt.value):
        return None
    rv = rec_stmt.value
    if not isinstance(rv, ast.BinOp):
        return None

    def is_param(n):
        return isinstance(n, ast.Name) and n.id == param

    def is_rec(n):
        return (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                and n.func.id == func_name and len(n.args) == 1
                and isinstance(n.args[0], ast.BinOp) and isinstance(n.args[0].op, ast.Sub)
                and isinstance(n.args[0].left, ast.Name) and n.args[0].left.id == param
                and isinstance(n.args[0].right, ast.Constant) and n.args[0].right.value == 1)

    _all_binops = {
        ast.Mult: MUL, ast.Add: ADD, ast.Sub: SUB,
        ast.FloorDiv: FLOORDIV, ast.Mod: MOD,
        ast.BitOr: BITOR, ast.BitAnd: BITAND, ast.BitXor: BITXOR,
    }
    op = _all_binops.get(type(rv.op))
    if op is None:
        return None
    if (is_param(rv.left) and is_rec(rv.right)) or (is_rec(rv.left) and is_param(rv.right)):
        p = env.get(param)
        if p is None:
            return None
        return T.fold(op, threshold, T.S.ival(p) + 1, T.mkint(base_val))
    return None


# ═══════════════════════════════════════════════════════════
# Top-Level Compilation
# ═══════════════════════════════════════════════════════════

def compile_func(source: str, T: Theory):
    """Compile a Python function source to (sections, params, func_node)."""
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        return None
    func = None
    env = Env(T)

    # Process top-level imports and assignments first
    for n in tree.body:
        if isinstance(n, (ast.Import, ast.ImportFrom)):
            _exec_import(n, env)
        elif isinstance(n, ast.Assign):
            exec_one(n, env)
        elif isinstance(n, ast.FunctionDef):
            if func is None:
                func = n
            else:
                # Helper function defined before main function
                env.func_defs[n.name] = n
                env.put(n.name, ('__func__', n))
        elif isinstance(n, ast.ClassDef):
            env.class_defs[n.name] = n
            env.put(n.name, ('__class__', n))

    if func is None:
        return None

    param_names = [a.arg for a in func.args.args]
    params = [_z3.Const(f'p{i}', T.S) for i in range(len(param_names))]
    env.func_name = func.name
    for p, v in zip(param_names, params):
        env.put(p, v)

    # Handle default argument values
    defaults = func.args.defaults
    if defaults:
        offset = len(param_names) - len(defaults)
        for i, d in enumerate(defaults):
            # Don't override provided params, but note defaults exist
            pass

    body = _skip_doc(func.body)

    # Process nested function definitions first
    for stmt in body:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            env.func_defs[stmt.name] = stmt
            env.put(stmt.name, ('__func__', stmt))
        elif isinstance(stmt, ast.ClassDef):
            env.class_defs[stmt.name] = stmt
            env.put(stmt.name, ('__class__', stmt))

    is_rec = any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                 and n.func.id == func.name for n in ast.walk(func))
    if is_rec:
        secs = _handle_recursion(func, body, env, param_names, params)
    else:
        secs = extract_sections(body, env)
    if not secs:
        return None
    return secs, params, func


def _handle_recursion(func, body, env, param_names, params):
    T = env.T
    # Canonical fold detection (Nat-eliminator)
    if len(param_names) == 1:
        canon = detect_canon_rec(body, func.name, param_names[0], env)
        if canon is not None:
            return [Section(guard=_z3.BoolVal(True), term=canon)]
    # General RecFunction
    T._uid += 1; uid = T._uid
    n = len(param_names)
    rfn = _z3.RecFunction(f'rec_{func.name}_{uid}', *([T.S]*n), T.S)
    sym = [_z3.FreshConst(T.S, f'_r{i}_{uid}') for i in range(n)]
    de = Env(T, func_name=func.name, is_rec=True,
             func_defs=dict(env.func_defs), class_defs=dict(env.class_defs),
             imports=dict(env.imports))
    for p, s in zip(param_names, sym):
        de.put(p, s)
    # Also register nested functions
    for stmt in body:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            de.func_defs[stmt.name] = stmt
            de.put(stmt.name, ('__func__', stmt))
    secs = extract_sections(body, de)
    if not secs:
        return []
    combined = secs[-1].term
    for s in reversed(secs[:-1]):
        combined = _z3.If(s.guard, s.term, combined)
    try:
        _z3.RecAddDefinition(rfn, sym, combined)
    except Exception:
        return []
    gt = rfn(*params)
    subst = list(zip(sym, params))
    return [Section(guard=_z3.substitute(s.guard, *subst) if subst else s.guard, term=gt)
            for s in secs]


# ═══════════════════════════════════════════════════════════
# §P3: Uninterpreted Function Chain Analyzer
# ═══════════════════════════════════════════════════════════

from .theory import OpacityClassifier, OpacityLevel  # noqa: E402


class ChainLink:
    """One link in a composed uninterpreted function chain."""
    __slots__ = ('fn_name', 'opacity', 'has_axioms')

    def __init__(self, fn_name: str, opacity: int, has_axioms: bool):
        self.fn_name = fn_name
        self.opacity = opacity
        self.has_axioms = has_axioms


class ChainAnalysis:
    """Full analysis of a composed function chain."""
    __slots__ = ('chain', 'total_opacity_transitions', 'reducible_by_axioms',
                 'reduced_chain', 'proof_result')

    def __init__(self, chain: list, total_opacity_transitions: int,
                 reducible_by_axioms: bool, reduced_chain: list,
                 proof_result: str = None):
        self.chain = chain
        self.total_opacity_transitions = total_opacity_transitions
        self.reducible_by_axioms = reducible_by_axioms
        self.reduced_chain = reduced_chain
        self.proof_result = proof_result

    @property
    def opacity_boundary_indices(self) -> list:
        boundaries = []
        for i in range(1, len(self.chain)):
            if self.chain[i].opacity != self.chain[i - 1].opacity:
                boundaries.append(i)
        return boundaries

    def __str__(self) -> str:
        names = [link.fn_name for link in self.chain]
        reduced = ' ∘ '.join(self.reduced_chain) if self.reduced_chain else '(empty)'
        return (f'Chain: {" ∘ ".join(names)}\n'
                f'  Transitions: {self.total_opacity_transitions}\n'
                f'  Reducible: {self.reducible_by_axioms}\n'
                f'  Reduced: {reduced}')


_ABSORPTION_RULES = {
    ('sorted', 'list'): 'sorted',
    ('sorted', 'tuple'): 'sorted',
    ('sorted', 'reversed'): 'sorted',
    ('sorted', 'sorted'): 'sorted',
    ('reversed', 'reversed'): '',
    ('list', 'list'): 'list',
    ('tuple', 'tuple'): 'tuple',
    ('set', 'set'): 'set',
    ('set', 'sorted'): 'set',
    ('set', 'reversed'): 'set',
    ('set', 'list'): 'set',
    ('set', 'tuple'): 'set',
    ('frozenset', 'frozenset'): 'frozenset',
}


def analyze_function_chain(T, fn_names: list) -> ChainAnalysis:
    """Analyze a chain of composed functions for opacity boundaries.

    Given [f, g, h], analyzes h(g(f(x))) — detects where the opacity
    level transitions, which axioms apply, and whether the chain
    can be algebraically reduced.
    """
    links = []
    for name in fn_names:
        report = OpacityClassifier.classify_detailed(name)
        links.append(ChainLink(name, report.level, report.has_axioms))

    transitions = 0
    for i in range(1, len(links)):
        if links[i].opacity != links[i - 1].opacity:
            transitions += 1

    # Algebraic reduction via absorption rules
    reduced = list(fn_names)
    changed = True
    while changed:
        changed = False
        new_reduced = []
        i = 0
        while i < len(reduced):
            if i + 1 < len(reduced):
                pair = (reduced[i + 1], reduced[i])
                if pair in _ABSORPTION_RULES:
                    replacement = _ABSORPTION_RULES[pair]
                    if replacement:
                        new_reduced.append(replacement)
                    i += 2
                    changed = True
                    continue
            new_reduced.append(reduced[i])
            i += 1
        reduced = new_reduced

    reducible = reduced != fn_names

    proof_result = None
    if _HAS_Z3 and len(fn_names) >= 2:
        x = _z3.Const('_chain_x', T.S)
        ax_var = _z3.Const('_chain_ax', T.S)

        fns = [T.shared_fn(name, 1) for name in fn_names]
        full_term = x
        for fn in fns:
            full_term = fn(full_term)

        if reduced:
            red_fns = [T.shared_fn(name, 1) for name in reduced]
            red_term = x
            for fn in red_fns:
                red_term = fn(red_term)

            solver = _z3.Solver()
            solver.set('timeout', 5000)
            for outer, inner in _ABSORPTION_RULES:
                if ((outer, 1) in T._shared_fns and
                        (inner, 1) in T._shared_fns):
                    fo = T._shared_fns[(outer, 1)]
                    fi = T._shared_fns[(inner, 1)]
                    result = _ABSORPTION_RULES[(outer, inner)]
                    if result == '':
                        solver.add(_z3.ForAll([ax_var],
                                             fo(fi(ax_var)) == ax_var))
                    elif result == outer:
                        solver.add(_z3.ForAll([ax_var],
                                             fo(fi(ax_var)) == fo(ax_var)))
                    elif result == inner:
                        solver.add(_z3.ForAll([ax_var],
                                             fo(fi(ax_var)) == fi(ax_var)))
                    else:
                        fr = T.shared_fn(result, 1)
                        solver.add(_z3.ForAll([ax_var],
                                             fo(fi(ax_var)) == fr(ax_var)))

            solver.add(full_term != red_term)
            r = solver.check()
            proof_result = ('reduced_equivalent'
                            if r == _z3.unsat else str(r))

    return ChainAnalysis(links, transitions, reducible, reduced, proof_result)


def analyze_uninterpreted_chain(T) -> dict:
    """Analyze sorted(list(set(x))) — the canonical chain example."""
    if not _HAS_Z3:
        return {}
    S = T.S
    p0 = _z3.Const('p0_chain', S)
    ax = _z3.Const('_ax_ch', S)

    sf = T.shared_fn('sorted', 1)
    lf = T.shared_fn('list', 1)
    setf = T.shared_fn('set', 1)

    chain = sf(lf(setf(p0)))
    direct = sf(p0)
    results = {}

    s1 = _z3.Solver()
    s1.set('timeout', 5000)
    s1.add(chain != direct)
    results['without_axioms'] = s1.check().r

    s2 = _z3.Solver()
    s2.set('timeout', 5000)
    s2.add(_z3.ForAll([ax], sf(lf(ax)) == sf(ax)))
    s2.add(chain != direct)
    results['with_sorted_absorbs_list'] = s2.check().r

    reduced = sf(setf(p0))
    s3 = _z3.Solver()
    s3.set('timeout', 5000)
    s3.add(_z3.ForAll([ax], sf(lf(ax)) == sf(ax)))
    s3.add(chain != reduced)
    results['chain_reduces'] = s3.check().r

    full_analysis = analyze_function_chain(T, ['set', 'list', 'sorted'])
    results['full_chain_analysis'] = str(full_analysis)
    return results


# ═══════════════════════════════════════════════════════════
# §P4: Z3 Theory Completeness Checker
# ═══════════════════════════════════════════════════════════

ALL_PYTHON_BUILTINS = frozenset({
    'sorted', 'reversed', 'list', 'tuple', 'set', 'frozenset',
    'dict', 'sum', 'any', 'all', 'enumerate', 'zip', 'map',
    'filter', 'type', 'hash', 'id', 'repr', 'str', 'iter',
    'next', 'print', 'input', 'open', 'ord', 'chr',
    'float', 'complex', 'bytes', 'bytearray', 'memoryview',
    'object', 'super', 'property', 'classmethod', 'staticmethod',
    'isinstance', 'issubclass', 'callable', 'getattr', 'setattr',
    'hasattr', 'delattr', 'vars', 'dir', 'len', 'abs', 'min', 'max',
    'range', 'slice', 'bool', 'int',
})


class CompletenessReport:
    """Report on the completeness of the Z3 theory."""
    __slots__ = ('axiomatized', 'opaque', 'recfunction_defined',
                 'total_builtins', 'coverage_pct')

    def __init__(self, axiomatized: list, opaque: list,
                 recfunction_defined: list, total_builtins: int,
                 coverage_pct: float):
        self.axiomatized = axiomatized
        self.opaque = opaque
        self.recfunction_defined = recfunction_defined
        self.total_builtins = total_builtins
        self.coverage_pct = coverage_pct

    def __str__(self) -> str:
        return (
            f'Theory Completeness: {self.coverage_pct:.1f}%\n'
            f'  RecFunction-defined: {", ".join(self.recfunction_defined)}\n'
            f'  Axiomatized: {", ".join(self.axiomatized)}\n'
            f'  Opaque ({len(self.opaque)}): '
            f'{", ".join(self.opaque[:10])}...'
        )


def check_theory_completeness(T) -> CompletenessReport:
    """Check which builtins have axioms vs remain fully opaque."""
    recfunction_defined = ['binop', 'unop', 'truthy', 'fold', 'tag']
    axiomatized = []
    opaque = []
    for name in sorted(ALL_PYTHON_BUILTINS):
        if name in OpacityClassifier.AXIOMATIZED_UNINTERPRETED:
            axiomatized.append(name)
        else:
            level = OpacityClassifier.classify(name)
            if level == OpacityLevel.UNINTERPRETED:
                opaque.append(name)
    total = len(ALL_PYTHON_BUILTINS) + len(recfunction_defined)
    covered = len(axiomatized) + len(recfunction_defined)
    pct = (covered / total * 100) if total else 0.0
    return CompletenessReport(axiomatized, opaque, recfunction_defined,
                              total, pct)


def check_active_axiom_coverage(T) -> dict:
    """For each shared function in T, report whether it has axiom coverage."""
    coverage = {}
    for (name, _arity) in sorted(T._shared_fns.keys()):
        coverage[name] = name in OpacityClassifier._AXIOM_MAP
    return coverage


# ═══════════════════════════════════════════════════════════
# §P11: Opacity Boundary Demonstration (Thm. 25.4)
# ═══════════════════════════════════════════════════════════

class OpacityBoundaryTest:
    """One test in the opacity boundary demonstration."""
    __slots__ = ('name', 'description', 'expected', 'actual', 'passed')

    def __init__(self, name: str, description: str, expected: str,
                 actual: str, passed: bool):
        self.name = name
        self.description = description
        self.expected = expected
        self.actual = actual
        self.passed = passed


def demonstrate_opacity_boundary(T) -> list:
    """Demonstrate the opacity boundary theorem (Thm. 25.4).

    Shows that uninterpreted functions can only prove equality via
    congruence, unless equational axioms are added.
    """
    if not _HAS_Z3:
        return []
    S = T.S
    results = []
    x = _z3.Const('x_ob', S)
    y = _z3.Const('y_ob', S)
    sf = T.shared_fn('sorted', 1)

    # T1: Congruence — same input ⇒ same output
    s = _z3.Solver()
    s.set('timeout', 5000)
    s.add(sf(x) != sf(x))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'congruence_self', 'f(x) == f(x) by congruence',
        'unsat', str(r), r == _z3.unsat))

    # T2: Different inputs may still map to same output
    s = _z3.Solver()
    s.set('timeout', 5000)
    s.add(x != y)
    s.add(sf(x) == sf(y))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'different_inputs_may_match',
        'x != y does not imply f(x) != f(y)',
        'sat', str(r), r == _z3.sat))

    # T3: Opaque function can match any concrete value
    s = _z3.Solver()
    s.set('timeout', 5000)
    s.add(sf(x) == S.IntObj(_z3.IntVal(42)))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'opaque_accepts_concrete',
        'f(x) == IntObj(42) is satisfiable for opaque f',
        'sat', str(r), r == _z3.sat))

    # T4: Idempotence axiom lifts partial opacity
    s = _z3.Solver()
    s.set('timeout', 5000)
    s.add(_z3.ForAll([x], sf(sf(x)) == sf(x)))
    y2 = _z3.Const('y_ob2', S)
    s.add(sf(sf(y2)) != sf(y2))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'idempotence_lifts_opacity',
        'with f∘f=f axiom, f(f(x)) == f(x) provable',
        'unsat', str(r), r == _z3.unsat))

    # T5: Without axioms, cannot prove f(f(x)) == f(x)
    s = _z3.Solver()
    s.set('timeout', 5000)
    s.add(sf(sf(x)) != sf(x))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'no_axiom_no_idempotence',
        'without axioms, f(f(x)) == f(x) is not provable',
        'sat', str(r), r == _z3.sat))

    # T6: Involution axiom for reversed
    rf = T.shared_fn('reversed', 1)
    s = _z3.Solver()
    s.set('timeout', 5000)
    s.add(_z3.ForAll([x], rf(rf(x)) == x))
    z = _z3.Const('z_ob', S)
    s.add(rf(rf(z)) != z)
    r = s.check()
    results.append(OpacityBoundaryTest(
        'involution_reversed',
        'with reversed∘reversed=id, rev(rev(x)) == x',
        'unsat', str(r), r == _z3.unsat))

    # T7: Functional extensionality does NOT hold for opaque fns
    gf = T.shared_fn('my_opaque', 1)
    s = _z3.Solver()
    s.set('timeout', 5000)
    s.add(sf(x) != gf(x))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'opaque_fns_distinguishable',
        'different opaque symbols are distinguishable',
        'sat', str(r), r == _z3.sat))

    # T8: Same symbol, different arity → different functions
    sf1 = T.shared_fn('testfn', 1)
    sf2 = T.shared_fn('testfn', 2)
    s = _z3.Solver()
    s.set('timeout', 5000)
    s.add(sf1(x) != sf2(x, y))
    r = s.check()
    results.append(OpacityBoundaryTest(
        'different_arity_distinguishable',
        'f/1 and f/2 are distinct symbols',
        'sat', str(r), r == _z3.sat))

    return results


# ═══════════════════════════════════════════════════════════
# Extended AST→Z3 helpers  (wired from proposals/g13_compilation)
# ═══════════════════════════════════════════════════════════

def compile_ann_assign(stmt, env):
    """Handle annotated assignment (x: int = 5) — compile value and bind."""
    if not isinstance(stmt, ast.AnnAssign):
        return
    if stmt.value is not None:
        val = compile_expr(stmt.value, env)
        val = _ensure_z3(val, env.T)
        _assign_target(stmt.target, val, env)


def compile_match_stmt(stmt, env):
    """Handle match/case statement (Python 3.10+) — bind pattern vars and exec arms."""
    T = env.T
    if not hasattr(ast, 'Match'):
        return
    subject = compile_expr(stmt.subject, env)
    for case in stmt.cases:
        ce = env.copy()
        _bind_match_pattern(case.pattern, subject, ce)
        exec_stmts(case.body, ce)
        for k, v in ce.bindings.items():
            if v is not env.get(k):
                env.put(k, v)


def _bind_match_pattern(pattern, subject, env):
    """Bind names from a match/case pattern into the compilation environment."""
    T = env.T
    if not hasattr(ast, 'MatchAs'):
        return
    if isinstance(pattern, ast.MatchAs):
        if pattern.name:
            env.put(pattern.name, subject)
    elif isinstance(pattern, ast.MatchValue):
        pass
    elif isinstance(pattern, ast.MatchSequence):
        for i, p in enumerate(pattern.patterns):
            elem = T.binop(GETITEM, subject, T.mkint(i))
            _bind_match_pattern(p, elem, env)
    elif isinstance(pattern, ast.MatchMapping):
        for key, p in zip(pattern.keys, pattern.patterns):
            k = compile_expr(key, env)
            v = T.binop(GETITEM, subject, k)
            _bind_match_pattern(p, v, env)
    elif isinstance(pattern, ast.MatchStar):
        if pattern.name:
            env.put(pattern.name, T.fresh(f'star_{pattern.name}'))
    elif isinstance(pattern, ast.MatchOr):
        if pattern.patterns:
            _bind_match_pattern(pattern.patterns[0], subject, env)


def compile_lambda_body(node, env):
    """Compile a lambda by building a Z3 function from its body.

    Instead of an opaque fresh symbol, creates a shared function keyed
    by the body's AST so that semantically identical lambdas share the
    same Z3 symbol.
    """
    T = env.T
    if not isinstance(node, ast.Lambda):
        return T.fresh('lambda')
    params = [a.arg for a in node.args.args]
    if not params:
        return compile_expr(node.body, env)
    sub = env.copy()
    sub.depth += 1
    syms = []
    for p in params:
        s = T.fresh(f'lam_{p}')
        sub.put(p, s)
        syms.append(s)
    body_val = compile_expr(node.body, sub)
    h = _stable_hash(ast.dump(node.body))
    fn = T.shared_fn(f'lambda_{h}', len(params))
    return fn(*syms)


def compile_assert_guard(stmt, env):
    """Compile an assert statement's test as a Z3 boolean guard.

    Returns a Z3 Bool that can be And-ed with section guards.
    """
    T = env.T
    if not isinstance(stmt, ast.Assert):
        return _z3.BoolVal(True)
    return T.truthy(compile_expr(stmt.test, env))


def try_fold_builtin(name, args, T):
    """Try to compile a reducer builtin (prod/any/all) as a Z3 fold.

    Returns a Z3 term or None.
    """
    _FOLD_TABLE = {
        'prod':      (MUL,    lambda t: t.mkint(1)),
        'math.prod': (MUL,    lambda t: t.mkint(1)),
        'any':       (BITOR,  lambda t: t.mkbool(False)),
        'all':       (BITAND, lambda t: t.mkbool(True)),
    }
    if name not in _FOLD_TABLE or len(args) != 1:
        return None
    op, mk_init = _FOLD_TABLE[name]
    fn = T.shared_fn(f'fold_{name}', 2)
    return fn(mk_init(T), args[0])
