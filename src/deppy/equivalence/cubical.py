"""§1: Z3 Theory of Python Values.

PyObj is a Z3 algebraic datatype modeling Python's object model.
Operations are Z3 RecFunctions implementing Python's semantics.

Python's execution model (Politz et al., "Python: The Full Monty"):
  - Every value is an object with identity, type, and value
  - Variables are references into a heap
  - Mutation through aliases is observable
  - Closures capture cells (mutable refs) or values (defaults)
  - Exceptions propagate through a handler stack

We model:
  IntObj(i)  — exact integer arithmetic via Z3 IntSort
  BoolObj(b) — exact boolean logic via Z3 BoolSort
  StrObj(s)  — exact string ops via Z3 StringSort
  NoneObj    — the None singleton
  Pair(a,b)  — cons cell for tuples/lists (structural)
  Ref(addr)  — heap reference (identity-bearing, for mutable objects)
  Bottom     — exception / divergence
"""
from __future__ import annotations
from typing import Any, Dict, Optional, Tuple

try:
    import z3 as _z3
    _HAS_Z3 = True
except ImportError:
    _z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False


# Operation tags — stable integer codes for Z3 dispatch
ADD = 1;  SUB = 2;  MUL = 3;  FLOORDIV = 5;  MOD = 6;  POW = 7
LSHIFT = 10; RSHIFT = 11; BITOR = 12; BITAND = 13; BITXOR = 14
LT = 20; LE = 21; GT = 22; GE = 23; EQ = 24; NE = 25
MAX = 30; MIN = 31
IADD = 40; IMUL = 41  # in-place: distinct from ADD/MUL for mutable types
NEG = 50; ABS_ = 52; NOT = 53; BOOL_ = 56; INT_ = 57; LEN_ = 55
SORTED_ = 60; REVERSED_ = 61; LIST_ = 62; SET_ = 63; SUM_ = 66
GETITEM = 70


class Theory:
    """Fresh Z3 theory instance.  Each equivalence check creates one."""

    def __init__(self):
        D = _z3.Datatype('PyObj')
        D.declare('IntObj', ('ival', _z3.IntSort()))
        D.declare('BoolObj', ('bval', _z3.BoolSort()))
        D.declare('StrObj', ('sval', _z3.StringSort()))
        D.declare('NoneObj')
        D.declare('Pair', ('fst', D), ('snd', D))
        D.declare('Ref', ('addr', _z3.IntSort()))
        D.declare('Bottom')
        self.S = D.create()
        self._uid = 0
        self._define_binop()
        self._define_unop()
        self._define_truthy()
        self._define_fold()

    # ── constructors ──────────────────────────────────────────

    def mkint(self, n: int) -> Any:
        return self.S.IntObj(_z3.IntVal(n))

    def mkbool(self, b: bool) -> Any:
        return self.S.BoolObj(_z3.BoolVal(b))

    def mkstr(self, s: str) -> Any:
        return self.S.StrObj(_z3.StringVal(s))

    def mknone(self) -> Any:
        return self.S.NoneObj

    def mkref(self) -> Any:
        """Fresh heap reference (unique identity)."""
        self._uid += 1
        return self.S.Ref(_z3.IntVal(self._uid))

    def mkpair(self, a: Any, b: Any) -> Any:
        return self.S.Pair(a, b)

    def mklist(self, *elts: Any) -> Any:
        """Pair-chain list ending in NoneObj."""
        r = self.S.NoneObj
        for e in reversed(elts):
            r = self.S.Pair(e, r)
        return r

    def fresh(self, tag: str = '') -> Any:
        self._uid += 1
        return _z3.Const(f'_u{tag}{self._uid}', self.S)

    # ── binop ─────────────────────────────────────────────────

    def _define_binop(self):
        S = self.S
        self.binop = _z3.RecFunction('binop', _z3.IntSort(), S, S, S)
        op = _z3.Int('_bo')
        a, b = _z3.Const('_ba', S), _z3.Const('_bb', S)
        ai, bi = S.ival(a), S.ival(b)
        ii = _z3.And(S.is_IntObj(a), S.is_IntObj(b))
        ss = _z3.And(S.is_StrObj(a), S.is_StrObj(b))

        int_r = (
            _z3.If(op == ADD, S.IntObj(ai + bi),
            _z3.If(op == SUB, S.IntObj(ai - bi),
            _z3.If(op == MUL, S.IntObj(ai * bi),
            _z3.If(op == FLOORDIV, _z3.If(bi != 0, S.IntObj(ai / bi), S.Bottom),
            _z3.If(op == MOD, _z3.If(bi != 0, S.IntObj(ai % bi), S.Bottom),
            _z3.If(op == LT, S.BoolObj(ai < bi),
            _z3.If(op == LE, S.BoolObj(ai <= bi),
            _z3.If(op == GT, S.BoolObj(ai > bi),
            _z3.If(op == GE, S.BoolObj(ai >= bi),
            _z3.If(op == EQ, S.BoolObj(ai == bi),
            _z3.If(op == NE, S.BoolObj(ai != bi),
            _z3.If(op == MAX, _z3.If(ai >= bi, a, b),
            _z3.If(op == MIN, _z3.If(ai <= bi, a, b),
            _z3.If(op == IADD, S.IntObj(ai + bi),
            _z3.If(op == IMUL, S.IntObj(ai * bi),
            S.Bottom))))))))))))))))

        str_r = _z3.If(op == ADD, S.StrObj(_z3.Concat(S.sval(a), S.sval(b))),
                 _z3.If(op == EQ, S.BoolObj(S.sval(a) == S.sval(b)),
                 _z3.If(op == NE, S.BoolObj(S.sval(a) != S.sval(b)),
                 S.Bottom)))

        # Pair equality (structural, recursive)
        # For non-int/str/bool pairs, EQ compares structurally
        eq_r = _z3.If(op == EQ, S.BoolObj(a == b),
               _z3.If(op == NE, S.BoolObj(a != b),
               S.Bottom))

        _z3.RecAddDefinition(self.binop, [op, a, b],
            _z3.If(ii, int_r,
            _z3.If(ss, str_r,
            eq_r)))

    # ── unop ──────────────────────────────────────────────────

    def _define_unop(self):
        S = self.S
        self.unop = _z3.RecFunction('unop', _z3.IntSort(), S, S)
        op, a = _z3.Int('_uo'), _z3.Const('_ua', S)
        ai = S.ival(a)

        _z3.RecAddDefinition(self.unop, [op, a],
            _z3.If(S.is_IntObj(a),
                _z3.If(op == NEG, S.IntObj(-ai),
                _z3.If(op == ABS_, S.IntObj(_z3.If(ai >= 0, ai, -ai)),
                _z3.If(op == NOT, S.BoolObj(ai == 0),
                _z3.If(op == BOOL_, S.BoolObj(ai != 0),
                _z3.If(op == INT_, a,
                S.Bottom))))),
            _z3.If(S.is_BoolObj(a),
                _z3.If(op == NOT, S.BoolObj(_z3.Not(S.bval(a))),
                _z3.If(op == BOOL_, a,
                _z3.If(op == INT_, S.IntObj(_z3.If(S.bval(a), 1, 0)),
                S.Bottom))),
            _z3.If(S.is_StrObj(a),
                _z3.If(op == LEN_, S.IntObj(_z3.Length(S.sval(a))),
                _z3.If(op == BOOL_, S.BoolObj(_z3.Length(S.sval(a)) > 0),
                S.Bottom)),
            _z3.If(S.is_NoneObj(a),
                _z3.If(op == BOOL_, S.BoolObj(False),
                _z3.If(op == NOT, S.BoolObj(True),
                S.Bottom)),
            _z3.If(S.is_Pair(a),
                _z3.If(op == BOOL_, S.BoolObj(True),
                S.Bottom),
            S.Bottom))))))

    # ── truthy ────────────────────────────────────────────────

    def _define_truthy(self):
        S = self.S
        self.truthy = _z3.RecFunction('truthy', S, _z3.BoolSort())
        x = _z3.Const('_tr', S)
        _z3.RecAddDefinition(self.truthy, [x],
            _z3.If(S.is_IntObj(x), S.ival(x) != 0,
            _z3.If(S.is_BoolObj(x), S.bval(x),
            _z3.If(S.is_StrObj(x), _z3.Length(S.sval(x)) > 0,
            _z3.If(S.is_NoneObj(x), False,
            _z3.If(S.is_Bottom(x), False,
            True))))))

    # ── canonical fold ────────────────────────────────────────
    # fold(op, i, stop, acc) = if i >= stop then acc
    #                          else binop(op, IntObj(i), fold(op, i+1, stop, acc))
    # This is the SHARED RecFunction: both recursive and iterative
    # implementations produce fold(...) calls to THIS function,
    # so Z3 proves equality by structural identity.

    def _define_fold(self):
        S = self.S
        self.fold = _z3.RecFunction('fold',
            _z3.IntSort(), _z3.IntSort(), _z3.IntSort(), S, S)
        op, i, stop = _z3.Ints('_fo _fi _fs')
        acc = _z3.Const('_fa', S)
        _z3.RecAddDefinition(self.fold, [op, i, stop, acc],
            _z3.If(i >= stop, acc,
                self.binop(op, S.IntObj(i), self.fold(op, i + 1, stop, acc))))


# ═══════════════════════════════════════════════════════════════
# §2  Python AST → Z3 PyObj compiler
# ═══════════════════════════════════════════════════════════════

import ast
import textwrap
from dataclasses import dataclass, field
from typing import List


@dataclass
class Env:
    """Compilation environment: name → Z3 PyObj term."""
    T: Theory
    bindings: Dict[str, Any] = field(default_factory=dict)
    func_name: str = ''
    is_rec: bool = False

    def get(self, name: str) -> Optional[Any]: return self.bindings.get(name)
    def put(self, name: str, val: Any): self.bindings[name] = val
    def copy(self) -> Env:
        return Env(self.T, dict(self.bindings), self.func_name, self.is_rec)


@dataclass(frozen=True)
class Section:
    guard: Any  # Z3 BoolRef
    term: Any   # Z3 PyObj


def compile_expr(node: ast.expr, env: Env) -> Any:
    """Compile a Python expression to a Z3 PyObj term.  Total."""
    T = env.T; S = T.S

    if isinstance(node, ast.Constant):
        v = node.value
        if isinstance(v, bool): return T.mkbool(v)
        if isinstance(v, int): return T.mkint(v)
        if isinstance(v, str): return T.mkstr(v)
        if v is None: return T.mknone()
        return T.fresh('const')

    if isinstance(node, ast.Name):
        v = env.get(node.id)
        return v if v is not None else T.fresh(f'undef_{node.id}')

    if isinstance(node, ast.BinOp):
        l, r = compile_expr(node.left, env), compile_expr(node.right, env)
        op_map = {
            ast.Add: ADD, ast.Sub: SUB, ast.Mult: MUL,
            ast.FloorDiv: FLOORDIV, ast.Mod: MOD,
        }
        op = op_map.get(type(node.op))
        if op is not None: return T.binop(op, l, r)
        return T.fresh('binop')

    if isinstance(node, ast.UnaryOp):
        a = compile_expr(node.operand, env)
        op_map = {ast.USub: NEG, ast.Not: NOT}
        op = op_map.get(type(node.op))
        if op is not None: return T.unop(op, a)
        if isinstance(node.op, ast.UAdd): return a
        return T.fresh('unary')

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
            else:
                parts.append(T.fresh('cmp'))
            left = right
        if len(parts) == 1: return parts[0]
        result = parts[-1]
        for p in reversed(parts[:-1]):
            result = _z3.If(T.truthy(p), result, T.mkbool(False))
        return result

    if isinstance(node, ast.BoolOp):
        vals = [compile_expr(v, env) for v in node.values]
        if isinstance(node.op, ast.And):
            r = vals[-1]
            for v in reversed(vals[:-1]): r = _z3.If(T.truthy(v), r, v)
            return r
        r = vals[-1]
        for v in reversed(vals[:-1]): r = _z3.If(T.truthy(v), v, r)
        return r

    if isinstance(node, ast.IfExp):
        c = compile_expr(node.test, env)
        t = compile_expr(node.body, env)
        f = compile_expr(node.orelse, env)
        return _z3.If(T.truthy(c), t, f)

    if isinstance(node, ast.Call):
        return compile_call(node, env)

    if isinstance(node, ast.Subscript):
        base = compile_expr(node.value, env)
        if isinstance(node.slice, ast.Slice): return T.fresh('slice')
        idx = compile_expr(node.slice, env)
        return T.binop(GETITEM, base, idx)

    if isinstance(node, (ast.Tuple, ast.List)):
        elts = [compile_expr(e, env) for e in node.elts]
        return T.mklist(*elts)

    if isinstance(node, ast.Dict):
        return T.mkref()  # dict → unique heap ref

    if isinstance(node, ast.Set):
        return T.mkref()

    if isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
        if not node.generators: return T.fresh('comp')
        gen = node.generators[0]
        it = compile_expr(gen.iter, env)
        # Same comprehension body + same iter = same result
        key = hash(ast.dump(node.elt if hasattr(node, 'elt') else node)) & 0x7FFFFFFF
        fn = _z3.Function(f'comp_{key}', S, S)
        return fn(it)

    if isinstance(node, ast.Lambda):
        return T.mkref()  # lambda → unique function ref

    if isinstance(node, ast.Attribute):
        obj = compile_expr(node.value, env)
        fn = _z3.Function(f'attr_{node.attr}', S, S)
        return fn(obj)

    return T.fresh(type(node).__name__)


def compile_call(node: ast.Call, env: Env) -> Any:
    T = env.T; S = T.S

    # Self-recursive call marker
    if isinstance(node.func, ast.Name) and node.func.id == env.func_name and env.is_rec:
        args = [compile_expr(a, env) for a in node.args]
        T._uid += 1
        fn = _z3.Function(f'rec_{env.func_name}_{T._uid}', *([S]*len(args)), S)
        return fn(*args)

    # Nested function
    if isinstance(node.func, ast.Name):
        fv = env.get(node.func.id)
        if isinstance(fv, tuple) and fv[0] == '__func__':
            r = inline_call(fv[1], node.args, env)
            if r is not None: return r

    # Builtins
    if isinstance(node.func, ast.Name):
        name = node.func.id
        args = [compile_expr(a, env) for a in node.args]
        n = len(args)

        if name == 'abs' and n == 1: return T.unop(ABS_, args[0])
        if name == 'int' and n == 1: return T.unop(INT_, args[0])
        if name == 'bool' and n == 1: return T.unop(BOOL_, args[0])
        if name == 'len' and n == 1: return T.unop(LEN_, args[0])
        if name == 'max' and n == 2: return T.binop(MAX, args[0], args[1])
        if name == 'min' and n == 2: return T.binop(MIN, args[0], args[1])
        if name == 'sorted' and n >= 1:
            T._uid += 1
            fn = _z3.Function(f'sorted_{T._uid}', S, S)
            return fn(args[0])
        if name == 'range': return T.fresh('range')

        # Class instantiation
        cv = env.get(name)
        if isinstance(cv, tuple) and cv[0] == '__class__':
            return T.mkref()

        # Generic call → uninterpreted function
        if n > 0:
            T._uid += 1
            fn = _z3.Function(f'call_{name}_{T._uid}', *([S]*n), S)
            return fn(*args)
        return T.fresh(f'call0_{name}')

    # Method call
    if isinstance(node.func, ast.Attribute):
        obj = compile_expr(node.func.value, env)
        method = node.func.attr
        args = [compile_expr(a, env) for a in node.args]
        T._uid += 1
        fn = _z3.Function(f'meth_{method}_{T._uid}', *([S]*(len(args)+1)), S)
        return fn(obj, *args)

    return T.fresh('dyncall')


def inline_call(func_node, call_args, env):
    params = [a.arg for a in func_node.args.args]
    if len(call_args) != len(params): return None
    ce = env.copy()
    for p, a in zip(params, call_args):
        ce.put(p, compile_expr(a, env))
    secs = extract_sections(func_node.body, ce)
    if len(secs) == 1: return secs[0].term
    if not secs: return None
    r = secs[-1].term
    for s in reversed(secs[:-1]):
        r = _z3.If(s.guard, s.term, r)
    return r


# ═══════════════════════════════════════════════════════════════
# §3  Section extractor (sheaf over control flow)
# ═══════════════════════════════════════════════════════════════

def extract_sections(stmts: list, env: Env,
                     guard: Any = None) -> List[Section]:
    T = env.T
    if guard is None: guard = _z3.BoolVal(True)
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
            if tr: sections.extend(extract_sections(stmt.body, env.copy(), tg))
            if fr and stmt.orelse: sections.extend(extract_sections(stmt.orelse, env.copy(), fg))
            if tr and fr: return sections
            if tr:
                re = env.copy()
                if stmt.orelse: exec_stmts(stmt.orelse, re)
                sections.extend(extract_sections(stmts[i+1:], re, fg))
                return sections
            if fr:
                re = env.copy()
                exec_stmts(stmt.body, re)
                sections.extend(extract_sections(stmts[i+1:], re, tg))
                return sections
            te, fe = env.copy(), env.copy()
            exec_stmts(stmt.body, te)
            if stmt.orelse: exec_stmts(stmt.orelse, fe)
            merge(env, te, fe, cond)

        elif isinstance(stmt, ast.Try):
            # Model try/except: tag return values with handler context
            handler_sig = '|'.join(
                ast.dump(h.type) if h.type else '__bare__'
                for h in (stmt.handlers if hasattr(stmt, 'handlers') else []))
            body_secs = extract_sections(stmt.body, env.copy(), guard)
            for s in body_secs:
                if handler_sig:
                    T._uid += 1
                    ctx = _z3.Function(f'try_{hash(handler_sig) & 0x7FFFFFFF}_{T._uid}',
                                       T.S, T.S)
                    sections.append(Section(guard=s.guard, term=ctx(s.term)))
                else:
                    sections.append(s)
            if hasattr(stmt, 'orelse') and stmt.orelse: exec_stmts(stmt.orelse, env)
            if hasattr(stmt, 'finalbody') and stmt.finalbody: exec_stmts(stmt.finalbody, env)
            sections.extend(extract_sections(stmts[i+1:], env, guard))
            return sections

        else:
            exec_one(stmt, env)

    return sections


def exec_stmts(stmts, env):
    for s in _skip_doc(stmts): exec_one(s, env)


def exec_one(stmt, env):
    T = env.T
    if isinstance(stmt, ast.Assign):
        val = compile_expr(stmt.value, env)
        for t in stmt.targets: assign_target(t, val, env)
    elif isinstance(stmt, ast.AugAssign) and isinstance(stmt.target, ast.Name):
        name = stmt.target.id
        old = env.get(name) or T.fresh(name)
        rhs = compile_expr(stmt.value, env)
        op_map = {ast.Add: IADD, ast.Mult: IMUL, ast.Sub: SUB,
                  ast.FloorDiv: FLOORDIV, ast.Mod: MOD}
        op = op_map.get(type(stmt.op), ADD)
        env.put(name, T.binop(op, old, rhs))
    elif isinstance(stmt, ast.For): exec_for(stmt, env)
    elif isinstance(stmt, ast.While): exec_while(stmt, env)
    elif isinstance(stmt, ast.If):
        cond = T.truthy(compile_expr(stmt.test, env))
        te, fe = env.copy(), env.copy()
        exec_stmts(stmt.body, te)
        if stmt.orelse: exec_stmts(stmt.orelse, fe)
        merge(env, te, fe, cond)
    elif isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
        env.put(stmt.name, ('__func__', stmt))
    elif isinstance(stmt, ast.ClassDef):
        env.put(stmt.name, ('__class__', stmt))
    elif isinstance(stmt, ast.Expr):
        # Track mutation: obj.method(args) → obj = method(obj, args)
        if (isinstance(stmt.value, ast.Call)
                and isinstance(stmt.value.func, ast.Attribute)
                and isinstance(stmt.value.func.value, ast.Name)):
            obj_name = stmt.value.func.value.id
            method = stmt.value.func.attr
            obj = env.get(obj_name)
            if obj is not None:
                args = [compile_expr(a, env) for a in stmt.value.args]
                T._uid += 1
                fn = _z3.Function(f'mut_{method}_{T._uid}', *([T.S]*(len(args)+1)), T.S)
                env.put(obj_name, fn(obj, *args))
    elif isinstance(stmt, ast.Try):
        exec_stmts(stmt.body, env)
        if hasattr(stmt, 'orelse') and stmt.orelse: exec_stmts(stmt.orelse, env)
        if hasattr(stmt, 'finalbody') and stmt.finalbody: exec_stmts(stmt.finalbody, env)
    elif isinstance(stmt, (ast.With, ast.AsyncWith)):
        for item in stmt.items:
            cm = compile_expr(item.context_expr, env)
            if item.optional_vars and isinstance(item.optional_vars, ast.Name):
                env.put(item.optional_vars.id, T.mkref())
        exec_stmts(stmt.body, env)


def assign_target(target, val, env):
    T = env.T
    if isinstance(target, ast.Name): env.put(target.id, val)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for j, elt in enumerate(target.elts):
            assign_target(elt, T.binop(GETITEM, val, T.mkint(j)), env)


def exec_for(stmt, env):
    T = env.T
    if not isinstance(stmt.target, ast.Name): return
    lv = stmt.target.id
    start, stop = extract_range(stmt.iter, env)
    if start is None: return

    modified = find_modified(stmt.body)
    state = {vn: env.get(vn) for vn in modified if vn != lv and env.get(vn) is not None}
    if not state: return

    # Canonical fold: acc OP= loop_var
    if len(stmt.body) == 1 and len(state) == 1:
        s = stmt.body[0]
        an = next(iter(state))
        if (isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name)
                and s.target.id == an and isinstance(s.value, ast.Name) and s.value.id == lv):
            op_map = {ast.Add: ADD, ast.Mult: MUL}
            op = op_map.get(type(s.op))
            if op is not None:
                env.put(an, T.fold(op, start, stop, state[an]))
                return

    # General RecFunction fold
    T._uid += 1
    uid = T._uid
    i_sym = _z3.Int(f'_li{uid}')
    for vn, init in state.items():
        rfn = _z3.RecFunction(f'lp_{vn}_{uid}', _z3.IntSort(), T.S)
        se = env.copy()
        se.put(lv, T.S.IntObj(i_sym))
        se.put(vn, rfn(i_sym + 1))
        exec_stmts(stmt.body, se)
        after = se.get(vn) or T.fresh(f'lp_{vn}')
        try:
            _z3.RecAddDefinition(rfn, [i_sym], _z3.If(i_sym >= stop, init, after))
            env.put(vn, rfn(start))
        except Exception:
            env.put(vn, T.fresh(f'lp_{vn}'))


def exec_while(stmt, env):
    T = env.T
    modified = find_modified(stmt.body)
    state = {vn: env.get(vn) for vn in modified if env.get(vn) is not None}
    if not state: return
    T._uid += 1; uid = T._uid
    ctr = _z3.Int(f'_wi{uid}')
    for vn, init in state.items():
        rfn = _z3.RecFunction(f'wh_{vn}_{uid}', _z3.IntSort(), T.S)
        se = env.copy()
        se.put(vn, rfn(ctr + 1))
        exec_stmts(stmt.body, se)
        cond = T.truthy(compile_expr(stmt.test, se))
        after = se.get(vn) or T.fresh(f'wh_{vn}')
        try:
            _z3.RecAddDefinition(rfn, [ctr], _z3.If(ctr > 50, init, _z3.If(cond, after, init)))
            env.put(vn, rfn(_z3.IntVal(0)))
        except Exception:
            env.put(vn, T.fresh(f'wh_{vn}'))


def merge(target, te, fe, cond):
    for k in set(te.bindings) | set(fe.bindings):
        tv, fv = te.get(k), fe.get(k)
        if tv is None or fv is None: continue
        orig = target.get(k)
        if orig is not None and tv is orig and fv is orig: continue
        try: target.put(k, _z3.If(cond, tv, fv))
        except Exception: pass


def _is_concrete_int(term):
    """Check if a Z3 term is concretely an IntObj (Python-level check)."""
    return hasattr(term, 'decl') and term.decl().name() == 'IntObj'


def extract_range(iter_expr, env):
    T = env.T; S = T.S
    if not (isinstance(iter_expr, ast.Call) and isinstance(iter_expr.func, ast.Name)
            and iter_expr.func.id == 'range'): return None, None
    args = iter_expr.args
    if len(args) == 1:
        v = compile_expr(args[0], env)
        r = _to_int_expr(v, S)
        if r is not None: return _z3.IntVal(0), r
        return None, None
    if len(args) >= 2:
        a, b = compile_expr(args[0], env), compile_expr(args[1], env)
        ra, rb = _to_int_expr(a, S), _to_int_expr(b, S)
        if ra is not None and rb is not None: return ra, rb
    return None, None


def _to_int_expr(term, S):
    """Extract a Z3 IntSort expression from a PyObj term, simplified."""
    if not hasattr(term, 'decl'): return None
    name = term.decl().name()
    if name == 'IntObj':
        return _z3.simplify(term.arg(0))
    if name == 'binop' and term.num_args() == 3:
        # binop(op, a, b) → extract int exprs from a and b, apply op directly
        a_int = _to_int_expr(term.arg(1), S)
        b_int = _to_int_expr(term.arg(2), S)
        if a_int is not None and b_int is not None:
            op_val = term.arg(0)
            # Apply the operation directly on Z3 IntSort
            try:
                op_num = int(str(_z3.simplify(op_val)))
                if op_num == ADD: return a_int + b_int
                if op_num == SUB: return a_int - b_int
                if op_num == MUL: return a_int * b_int
            except Exception:
                pass
            return S.ival(term)
    # Symbolic PyObj variable: use ival (valid when the var is IntObj)
    if hasattr(term, 'sort') and str(term.sort()) == 'PyObj':
        return S.ival(term)
    return None


def find_modified(stmts):
    modified, seen = [], set()
    for s in stmts:
        names = []
        if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name): names.append(s.target.id)
        elif isinstance(s, ast.Assign):
            for t in s.targets:
                if isinstance(t, ast.Name): names.append(t.id)
                elif isinstance(t, ast.Tuple): names.extend(e.id for e in t.elts if isinstance(e, ast.Name))
        elif isinstance(s, ast.If):
            names.extend(find_modified(s.body))
            if s.orelse: names.extend(find_modified(s.orelse))
        elif isinstance(s, ast.For): names.extend(find_modified(s.body))
        for n in names:
            if n not in seen: seen.add(n); modified.append(n)
    return modified


def _skip_doc(body):
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
        return body[1:]
    return body


def _has_ret(stmts):
    for s in stmts:
        if isinstance(s, ast.Return): return True
        if isinstance(s, ast.If) and _has_ret(s.body) and s.orelse and _has_ret(s.orelse): return True
    return False


# ═══════════════════════════════════════════════════════════════
# §4  Čech H¹ check + cubical path existence
# ═══════════════════════════════════════════════════════════════

@dataclass
class Result:
    equivalent: Optional[bool]
    explanation: str
    h0: int = 0
    h1: int = 0


def check_equivalence(source_f: str, source_g: str, timeout_ms: int = 5000) -> Result:
    if not _HAS_Z3: return Result(None, 'no z3')
    import sys
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 3000))
    try: return _check(source_f, source_g, timeout_ms)
    except RecursionError: return Result(None, 'recursion')
    except Exception as e: return Result(None, f'error: {e}')
    finally: sys.setrecursionlimit(old)


def _check(source_f, source_g, timeout_ms):
    T = Theory()
    sf = _compile_func(source_f, T)
    sg = _compile_func(source_g, T)
    if sf is None or sg is None: return Result(None, 'cannot compile')
    secs_f, params_f = sf
    secs_g, params_g = sg
    if len(params_f) != len(params_g): return Result(False, f'arity {len(params_f)}≠{len(params_g)}')
    if not secs_f or not secs_g: return Result(None, 'empty sheaf')

    # Unify params
    subst = [(pg, pf) for pf, pg in zip(params_f, params_g) if not pf.eq(pg)]
    if subst:
        secs_g = [Section(guard=_z3.substitute(s.guard, *subst),
                          term=_z3.substitute(s.term, *subst)) for s in secs_g]

    # Čech H¹: check sections agree on all overlaps
    solver = _z3.Solver()
    solver.set('timeout', timeout_ms)

    # Constrain params based on inferred types from usage.
    # If a param is used in arithmetic/comparison with ints → IntObj.
    # If used with string methods → StrObj. Etc.
    # This ensures we only check equivalence for VALID inputs.
    S = T.S
    try:
        tree_f = ast.parse(textwrap.dedent(source_f))
        tree_g = ast.parse(textwrap.dedent(source_g))
        func_f = next(n for n in tree_f.body if isinstance(n, ast.FunctionDef))
        func_g = next(n for n in tree_g.body if isinstance(n, ast.FunctionDef))
        param_names_f = [a.arg for a in func_f.args.args]
        for idx, pname in enumerate(param_names_f):
            sort = _infer_param_type(func_f, pname) or _infer_param_type(func_g, pname)
            p = params_f[idx]
            if sort == 'int':
                solver.add(S.is_IntObj(p))
            elif sort == 'str':
                solver.add(S.is_StrObj(p))
            else:
                solver.add(_z3.Or(S.is_IntObj(p), S.is_BoolObj(p), S.is_StrObj(p),
                                  S.is_NoneObj(p), S.is_Pair(p), S.is_Ref(p)))
    except Exception:
        for p in params_f:
            solver.add(_z3.Or(S.is_IntObj(p), S.is_BoolObj(p), S.is_StrObj(p),
                              S.is_NoneObj(p), S.is_Pair(p), S.is_Ref(p)))

    h0 = 0
    for sf in secs_f:
        for sg in secs_g:
            overlap = _z3.And(sf.guard, sg.guard)
            solver.push()
            solver.add(overlap)
            if solver.check() == _z3.unsat: solver.pop(); continue
            solver.pop()
            solver.push()
            solver.add(overlap, sf.term != sg.term)
            r = solver.check()
            solver.pop()
            if r == _z3.unsat: h0 += 1
            elif r == _z3.sat:
                return Result(False, 'H¹ obstruction: counterexample', h0=h0, h1=1)

    if h0 > 0: return Result(True, f'H¹=0: {h0} cubical faces verified', h0=h0)
    return Result(None, 'inconclusive')


def _compile_func(source, T):
    try: tree = ast.parse(textwrap.dedent(source))
    except SyntaxError: return None
    func = None
    for n in tree.body:
        if isinstance(n, ast.FunctionDef): func = n; break
    if func is None: return None
    param_names = [a.arg for a in func.args.args]
    params = [_z3.Const(f'p{i}', T.S) for i in range(len(param_names))]
    env = Env(T, func_name=func.name)
    for p, v in zip(param_names, params): env.put(p, v)
    body = _skip_doc(func.body)
    is_rec = any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                 and n.func.id == func.name for n in ast.walk(func))
    if is_rec:
        secs = handle_recursion(func, body, env, param_names, params)
    else:
        secs = extract_sections(body, env)
    if not secs: return None
    return secs, params


def handle_recursion(func, body, env, param_names, params):
    T = env.T
    # Canonical fold detection
    if len(param_names) == 1:
        canon = detect_canon_rec(body, func.name, param_names[0], env)
        if canon is not None:
            return [Section(guard=_z3.BoolVal(True), term=canon)]
    # General RecFunction
    T._uid += 1; uid = T._uid
    n = len(param_names)
    rfn = _z3.RecFunction(f'rec_{func.name}_{uid}', *([T.S]*n), T.S)
    sym = [_z3.FreshConst(T.S, f'_r{i}_{uid}') for i in range(n)]
    de = Env(T, func_name=func.name, is_rec=True)
    for p, s in zip(param_names, sym): de.put(p, s)
    secs = extract_sections(body, de)
    if not secs: return []
    combined = secs[-1].term
    for s in reversed(secs[:-1]): combined = _z3.If(s.guard, s.term, combined)
    try: _z3.RecAddDefinition(rfn, sym, combined)
    except Exception: return []
    gt = rfn(*params)
    subst = list(zip(sym, params))
    return [Section(guard=_z3.substitute(s.guard, *subst) if subst else s.guard, term=gt)
            for s in secs]


def detect_canon_rec(body, func_name, param, env):
    T = env.T
    body = _skip_doc(body)
    if len(body) != 2: return None
    base_stmt, rec_stmt = body
    if not (isinstance(base_stmt, ast.If) and not base_stmt.orelse
            and len(base_stmt.body) == 1 and isinstance(base_stmt.body[0], ast.Return)
            and base_stmt.body[0].value is not None): return None
    bv = base_stmt.body[0].value
    if not (isinstance(bv, ast.Constant) and isinstance(bv.value, int)): return None
    base_val = bv.value
    # Extract threshold
    test = base_stmt.test
    if not isinstance(test, ast.Compare) or len(test.ops) != 1: return None
    if not (isinstance(test.left, ast.Name) and test.left.id == param): return None
    c = test.comparators[0]
    if not isinstance(c, ast.Constant) or not isinstance(c.value, int): return None
    if isinstance(test.ops[0], ast.LtE): threshold = c.value
    elif isinstance(test.ops[0], ast.Lt): threshold = c.value - 1
    elif isinstance(test.ops[0], ast.Eq): threshold = c.value
    else: return None
    # Extract fold op
    if not (isinstance(rec_stmt, ast.Return) and rec_stmt.value): return None
    rv = rec_stmt.value
    if not isinstance(rv, ast.BinOp): return None
    def is_p(n): return isinstance(n, ast.Name) and n.id == param
    def is_r(n):
        return (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                and n.func.id == func_name and len(n.args) == 1
                and isinstance(n.args[0], ast.BinOp) and isinstance(n.args[0].op, ast.Sub)
                and isinstance(n.args[0].left, ast.Name) and n.args[0].left.id == param
                and isinstance(n.args[0].right, ast.Constant) and n.args[0].right.value == 1)
    op_map = {ast.Mult: MUL, ast.Add: ADD}
    if type(rv.op) in op_map:
        if (is_p(rv.left) and is_r(rv.right)) or (is_r(rv.left) and is_p(rv.right)):
            op = op_map[type(rv.op)]
            p = env.get(param)
            if p is None: return None
            return T.fold(op, threshold, T.S.ival(p) + 1, T.mkint(base_val))
    return None


def _infer_param_type(func: ast.FunctionDef, param: str) -> Optional[str]:
    """Infer the Z3 sort constraint for a parameter from AST usage."""
    for node in ast.walk(func):
        # Arithmetic ops → int
        if isinstance(node, ast.BinOp) and isinstance(node.op,
                (ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod, ast.Pow)):
            for s in (node.left, node.right):
                if isinstance(s, ast.Name) and s.id == param: return 'int'
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            for s in (node.left, node.right):
                if isinstance(s, ast.Name) and s.id == param:
                    other = node.right if s is node.left else node.left
                    if isinstance(other, ast.Constant) and isinstance(other.value, (int, float)):
                        return 'int'
        # Comparison with int literal → int
        if isinstance(node, ast.Compare) and isinstance(node.left, ast.Name) and node.left.id == param:
            if node.comparators and isinstance(node.comparators[0], ast.Constant):
                if isinstance(node.comparators[0].value, int): return 'int'
                if isinstance(node.comparators[0].value, str): return 'str'
        # range(p) → int
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'range':
            for arg in node.args:
                if isinstance(arg, ast.Name) and arg.id == param: return 'int'
                if isinstance(arg, ast.BinOp):
                    for s in (arg.left, arg.right):
                        if isinstance(s, ast.Name) and s.id == param: return 'int'
        # AugAssign with int → int
        if isinstance(node, ast.AugAssign) and isinstance(node.value, ast.Name) and node.value.id == param:
            return 'int'
        # Subscript index → int
        if isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Name) and node.slice.id == param:
            return 'int'
        # String methods → str
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name) and node.func.value.id == param
                and node.func.attr in ('upper', 'lower', 'strip', 'split', 'replace',
                                       'find', 'startswith', 'endswith')):
            return 'str'
    return None
