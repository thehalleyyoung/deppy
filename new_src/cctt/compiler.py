"""§2: AST Compiler — Python Source → Z3 PyObj Terms.

Compiles Python AST to presheaf sections (guard, term) pairs
over the control flow site.  Each return statement produces one
section; branches produce guarded sections.

Compilation rules:
  E1-E12: Expression compilation (literals, variables, binop, unop,
          compare, boolop, ifexp, calls, subscript, tuple/list,
          comprehension, attribute)
  S1-S9:  Statement execution (assign, augassign, return, if, for,
          while, funcdef, expr-stmt/mutation, try/except)
"""
from __future__ import annotations
import ast
import textwrap
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set

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
})


@dataclass
class Env:
    """Compilation environment: variable name → Z3 PyObj term."""
    T: Theory
    bindings: Dict[str, Any] = field(default_factory=dict)
    func_name: str = ''
    is_rec: bool = False

    def get(self, name: str) -> Optional[Any]:
        return self.bindings.get(name)

    def put(self, name: str, val: Any):
        self.bindings[name] = val

    def copy(self) -> 'Env':
        return Env(self.T, dict(self.bindings), self.func_name, self.is_rec)


@dataclass(frozen=True)
class Section:
    """A presheaf section: (guard, term) pair.

    guard: Z3 BoolRef — the path condition (which branch we're on)
    term:  Z3 PyObj   — the return value along this path
    """
    guard: Any
    term: Any


# ═══════════════════════════════════════════════════════════
# Expression Compilation (E1-E12)
# ═══════════════════════════════════════════════════════════

def compile_expr(node: ast.expr, env: Env) -> Any:
    """Compile a Python expression AST node to a Z3 PyObj term."""
    T = env.T; S = T.S

    # E1: Literals
    if isinstance(node, ast.Constant):
        v = node.value
        if isinstance(v, bool): return T.mkbool(v)
        if isinstance(v, int): return T.mkint(v)
        if isinstance(v, str): return T.mkstr(v)
        if v is None: return T.mknone()
        return T.fresh('const')

    # E2: Variables
    if isinstance(node, ast.Name):
        v = env.get(node.id)
        return v if v is not None else T.fresh(f'undef_{node.id}')

    # E3: Binary operations
    if isinstance(node, ast.BinOp):
        l, r = compile_expr(node.left, env), compile_expr(node.right, env)
        op_map = {
            ast.Add: ADD, ast.Sub: SUB, ast.Mult: MUL,
            ast.FloorDiv: FLOORDIV, ast.Mod: MOD,
            ast.LShift: LSHIFT, ast.RShift: RSHIFT,
            ast.BitOr: BITOR, ast.BitAnd: BITAND, ast.BitXor: BITXOR,
        }
        op = op_map.get(type(node.op))
        if op is not None: return T.binop(op, l, r)
        return T.fresh('binop')

    # E4: Unary operations
    if isinstance(node, ast.UnaryOp):
        a = compile_expr(node.operand, env)
        op_map = {ast.USub: NEG, ast.Not: NOT}
        op = op_map.get(type(node.op))
        if op is not None: return T.unop(op, a)
        if isinstance(node.op, ast.UAdd): return a
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
            else:
                parts.append(T.fresh('cmp'))
            left = right
        if len(parts) == 1: return parts[0]
        result = parts[-1]
        for p in reversed(parts[:-1]):
            result = _z3.If(T.truthy(p), result, T.mkbool(False))
        return result

    # E6: Boolean operations (short-circuit, return values)
    if isinstance(node, ast.BoolOp):
        vals = [compile_expr(v, env) for v in node.values]
        if isinstance(node.op, ast.And):
            r = vals[-1]
            for v in reversed(vals[:-1]): r = _z3.If(T.truthy(v), r, v)
            return r
        r = vals[-1]
        for v in reversed(vals[:-1]): r = _z3.If(T.truthy(v), v, r)
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
        if isinstance(node.slice, ast.Slice): return T.fresh('slice')
        idx = compile_expr(node.slice, env)
        return T.binop(GETITEM, base, idx)

    # E10: Tuple/List display
    if isinstance(node, (ast.Tuple, ast.List)):
        elts = [compile_expr(e, env) for e in node.elts]
        return T.mklist(*elts)

    # E11: Comprehension
    if isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
        if not node.generators: return T.fresh('comp')
        gen = node.generators[0]
        it = compile_expr(gen.iter, env)
        elt_node = node.elt if hasattr(node, 'elt') else node
        key = hash(ast.dump(elt_node)) & 0x7FFFFFFF
        fn = T.shared_fn(f'comp_{key}', 1)
        return fn(it)

    # E12: Attribute access
    if isinstance(node, ast.Attribute):
        obj = compile_expr(node.value, env)
        fn = T.shared_fn(f'attr_{node.attr}', 1)
        return fn(obj)

    # Dict/Set literals
    if isinstance(node, ast.Dict): return T.mkref()
    if isinstance(node, ast.Set): return T.mkref()

    # Lambda
    if isinstance(node, ast.Lambda): return T.mkref()

    return T.fresh(type(node).__name__)


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
        fv = env.get(node.func.id)
        if isinstance(fv, tuple) and fv[0] == '__func__':
            r = inline_call(fv[1], node.args, env)
            if r is not None: return r

    # Named calls
    if isinstance(node.func, ast.Name):
        name = node.func.id
        args = [compile_expr(a, env) for a in node.args]
        n = len(args)

        # Builtins with native Z3 semantics
        if name == 'abs' and n == 1: return T.unop(ABS_, args[0])
        if name == 'int' and n == 1: return T.unop(INT_, args[0])
        if name == 'bool' and n == 1: return T.unop(BOOL_, args[0])
        if name == 'len' and n == 1: return T.unop(LEN_, args[0])
        if name == 'max' and n == 2: return T.binop(MAX, args[0], args[1])
        if name == 'min' and n == 2: return T.binop(MIN, args[0], args[1])
        if name == 'range': return T.fresh('range')

        # isinstance → fiber projection
        if name == 'isinstance' and n == 2:
            obj = args[0]
            type_arg = node.args[1]
            tag = _resolve_isinstance_tag(type_arg, T)
            if tag is not None:
                return S.BoolObj(tag)

        # Shared builtins (univalence)
        if name in SHARED_BUILTINS and n > 0:
            fn = T.shared_fn(name, n)
            return fn(*args)

        # Class instantiation
        cv = env.get(name)
        if isinstance(cv, tuple) and cv[0] == '__class__':
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
        fn = T.shared_fn(f'meth_{method}', len(args) + 1)
        return fn(obj, *args)

    return T.fresh('dyncall')


def _resolve_isinstance_tag(type_arg, T):
    """Resolve isinstance type argument to a Z3 tag constraint."""
    tag_map = {
        'int': T.TInt, 'float': T.TInt, 'bool': T.TBool_,
        'str': T.TStr_, 'list': T.TPair_, 'tuple': T.TPair_,
        'dict': T.TRef_, 'set': T.TRef_,
    }
    if isinstance(type_arg, ast.Name):
        tag = tag_map.get(type_arg.id)
        if tag is not None:
            # We need the actual object being tested — caller handles this
            return None  # handled at call site
    return None


def inline_call(func_node, call_args, env):
    """Inline a nested function call (D2 defunctionalization)."""
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


# ═══════════════════════════════════════════════════════════
# Section Extraction (presheaf over control flow)
# ═══════════════════════════════════════════════════════════

def extract_sections(stmts: list, env: Env,
                     guard: Any = None) -> List[Section]:
    """Extract presheaf sections from a statement list."""
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
            if fr and stmt.orelse:
                sections.extend(extract_sections(stmt.orelse, env.copy(), fg))
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
            _merge_envs(env, te, fe, cond)

        elif isinstance(stmt, ast.Try):
            body_secs = extract_sections(stmt.body, env.copy(), guard)
            handler_sig = '|'.join(
                ast.dump(h.type) if h.type else '__bare__'
                for h in (stmt.handlers if hasattr(stmt, 'handlers') else []))
            for s in body_secs:
                if handler_sig:
                    T._uid += 1
                    ctx = _z3.Function(
                        f'try_{hash(handler_sig) & 0x7FFFFFFF}_{T._uid}', T.S, T.S)
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


# ═══════════════════════════════════════════════════════════
# Statement Execution (S1-S9)
# ═══════════════════════════════════════════════════════════

def exec_stmts(stmts, env):
    for s in _skip_doc(stmts): exec_one(s, env)


def exec_one(stmt, env):
    T = env.T

    # S1: Assignment
    if isinstance(stmt, ast.Assign):
        val = compile_expr(stmt.value, env)
        for t in stmt.targets: _assign_target(t, val, env)

    # S2: Augmented assignment
    elif isinstance(stmt, ast.AugAssign) and isinstance(stmt.target, ast.Name):
        name = stmt.target.id
        old = env.get(name) if env.get(name) is not None else T.fresh(name)
        rhs = compile_expr(stmt.value, env)
        op_map = {ast.Add: IADD, ast.Mult: IMUL, ast.Sub: SUB,
                  ast.FloorDiv: FLOORDIV, ast.Mod: MOD}
        op = op_map.get(type(stmt.op), ADD)
        env.put(name, T.binop(op, old, rhs))

    # S5: For loop
    elif isinstance(stmt, ast.For): _exec_for(stmt, env)

    # S6: While loop
    elif isinstance(stmt, ast.While): _exec_while(stmt, env)

    # S4: If (non-returning)
    elif isinstance(stmt, ast.If):
        cond = T.truthy(compile_expr(stmt.test, env))
        te, fe = env.copy(), env.copy()
        exec_stmts(stmt.body, te)
        if stmt.orelse: exec_stmts(stmt.orelse, fe)
        _merge_envs(env, te, fe, cond)

    # S7: Function definition
    elif isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
        env.put(stmt.name, ('__func__', stmt))

    # S7b: Class definition
    elif isinstance(stmt, ast.ClassDef):
        env.put(stmt.name, ('__class__', stmt))

    # S8: Expression statement (mutation tracking)
    elif isinstance(stmt, ast.Expr):
        if (isinstance(stmt.value, ast.Call)
                and isinstance(stmt.value.func, ast.Attribute)
                and isinstance(stmt.value.func.value, ast.Name)):
            obj_name = stmt.value.func.value.id
            method = stmt.value.func.attr
            obj = env.get(obj_name)
            if obj is not None:
                args = [compile_expr(a, env) for a in stmt.value.args]
                fn = T.shared_fn(f'mut_{method}', len(args) + 1)
                env.put(obj_name, fn(obj, *args))

    # S9: Try/except (exec mode)
    elif isinstance(stmt, ast.Try):
        exec_stmts(stmt.body, env)
        if hasattr(stmt, 'orelse') and stmt.orelse: exec_stmts(stmt.orelse, env)
        if hasattr(stmt, 'finalbody') and stmt.finalbody: exec_stmts(stmt.finalbody, env)

    # With statement
    elif isinstance(stmt, (ast.With, ast.AsyncWith)):
        for item in stmt.items:
            cm = compile_expr(item.context_expr, env)
            if item.optional_vars and isinstance(item.optional_vars, ast.Name):
                env.put(item.optional_vars.id, T.mkref())
        exec_stmts(stmt.body, env)


def _assign_target(target, val, env):
    T = env.T
    if isinstance(target, ast.Name): env.put(target.id, val)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for j, elt in enumerate(target.elts):
            _assign_target(elt, T.binop(GETITEM, val, T.mkint(j)), env)


def _exec_for(stmt, env):
    T = env.T
    if not isinstance(stmt.target, ast.Name): return
    lv = stmt.target.id
    start, stop = _extract_range(stmt.iter, env)
    if start is None: return

    modified = _find_modified(stmt.body)
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


def _exec_while(stmt, env):
    T = env.T
    modified = _find_modified(stmt.body)
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
        after = se.get(vn) if se.get(vn) is not None else T.fresh(f'wh_{vn}')
        try:
            _z3.RecAddDefinition(rfn, [ctr], _z3.If(ctr > 50, init, _z3.If(cond, after, init)))
            env.put(vn, rfn(_z3.IntVal(0)))
        except Exception:
            env.put(vn, T.fresh(f'wh_{vn}'))


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

def _merge_envs(target, te, fe, cond):
    for k in set(te.bindings) | set(fe.bindings):
        tv, fv = te.get(k), fe.get(k)
        if tv is None or fv is None: continue
        orig = target.get(k)
        if orig is not None and tv is orig and fv is orig: continue
        try: target.put(k, _z3.If(cond, tv, fv))
        except Exception: pass


def _extract_range(iter_expr, env):
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
    if not hasattr(term, 'decl'): return None
    name = term.decl().name()
    if name == 'IntObj': return _z3.simplify(term.arg(0))
    if name == 'binop' and term.num_args() == 3:
        a_int = _to_int_expr(term.arg(1), S)
        b_int = _to_int_expr(term.arg(2), S)
        if a_int is not None and b_int is not None:
            try:
                op_num = int(str(_z3.simplify(term.arg(0))))
                if op_num == ADD: return a_int + b_int
                if op_num == SUB: return a_int - b_int
                if op_num == MUL: return a_int * b_int
            except Exception: pass
            return S.ival(term)
    if hasattr(term, 'sort') and str(term.sort()) == 'PyObj':
        return S.ival(term)
    return None


def _find_modified(stmts):
    modified, seen = [], set()
    for s in stmts:
        names = []
        if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name):
            names.append(s.target.id)
        elif isinstance(s, ast.Assign):
            for t in s.targets:
                if isinstance(t, ast.Name): names.append(t.id)
                elif isinstance(t, ast.Tuple):
                    names.extend(e.id for e in t.elts if isinstance(e, ast.Name))
        elif isinstance(s, ast.If):
            names.extend(_find_modified(s.body))
            if s.orelse: names.extend(_find_modified(s.orelse))
        elif isinstance(s, ast.For): names.extend(_find_modified(s.body))
        for n in names:
            if n not in seen: seen.add(n); modified.append(n)
    return modified


def _skip_doc(body):
    if (body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        return body[1:]
    return body


def _has_ret(stmts):
    for s in stmts:
        if isinstance(s, ast.Return): return True
        if isinstance(s, ast.If) and _has_ret(s.body) and s.orelse and _has_ret(s.orelse): return True
    return False


# ═══════════════════════════════════════════════════════════
# Nat-Eliminator Extraction
# ═══════════════════════════════════════════════════════════

def detect_canon_rec(body, func_name, param, env):
    """Extract the Nat-eliminator (catamorphism) from a recursive function.

    Detects: if n OP threshold: return base_val; return BINOP(n, f(n-1))
    and produces the canonical fold RecFunction.
    """
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

    test = base_stmt.test
    if not isinstance(test, ast.Compare) or len(test.ops) != 1: return None
    if not (isinstance(test.left, ast.Name) and test.left.id == param): return None
    c = test.comparators[0]
    if not isinstance(c, ast.Constant) or not isinstance(c.value, int): return None
    if isinstance(test.ops[0], ast.LtE): threshold = c.value
    elif isinstance(test.ops[0], ast.Lt): threshold = c.value - 1
    elif isinstance(test.ops[0], ast.Eq): threshold = c.value
    else: return None

    if not (isinstance(rec_stmt, ast.Return) and rec_stmt.value): return None
    rv = rec_stmt.value
    if not isinstance(rv, ast.BinOp): return None

    def is_param(n): return isinstance(n, ast.Name) and n.id == param
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
    if op is None: return None
    if (is_param(rv.left) and is_rec(rv.right)) or (is_rec(rv.left) and is_param(rv.right)):
        p = env.get(param)
        if p is None: return None
        return T.fold(op, threshold, T.S.ival(p) + 1, T.mkint(base_val))
    return None


# ═══════════════════════════════════════════════════════════
# Top-Level Compilation
# ═══════════════════════════════════════════════════════════

def compile_func(source: str, T: Theory):
    """Compile a Python function source to (sections, params)."""
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
        secs = _handle_recursion(func, body, env, param_names, params)
    else:
        secs = extract_sections(body, env)
    if not secs: return None
    return secs, params


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
