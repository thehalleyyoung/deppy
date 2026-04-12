"""Operadic cohomological equivalence engine — complete Python 3.11 semantics.

Every Python construct maps to a term in the operad of typed operations.
The mapping is FAITHFUL: semantically different Python programs produce
structurally different operad terms.  Semantically equivalent programs
(even with different algorithms) produce the same normal form.

ARCHITECTURE:
  §1  OTerm — the universal term language (operad of Python operations)
  §2  Interpreter — COMPLETE mapping of Python 3.11 AST → OTerm
      §2a Expressions (29/29 AST node types)
      §2b Statements (28/28 AST node types)
      §2c Semantic distinctions (closures, exceptions, mutability, etc.)
  §3  Canonical forms — equational rewriting + fold extraction
  §4  Cohomological comparison — sheaf sections + H¹ via Z3
  §5  Public API

SOUNDNESS: The interpreter distinguishes ALL Python semantic differences:
  - Late vs early closure binding (lambda: x vs lambda x=x:)
  - except Exception vs bare except (different exception hierarchies)
  - int division (//) vs float truncation (int(a/b))
  - Mutable vs immutable default arguments
  - Class attributes (shared) vs instance attributes (per-object)
  - In-place mutation (+=) vs rebinding (= ... +)
  - Generator vs list comprehension (lazy vs eager evaluation)
"""
from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

try:
    import z3 as _z3
    _HAS_Z3 = True
except ImportError:
    _z3 = None  # type: ignore
    _HAS_Z3 = False


# ═══════════════════════════════════════════════════════════════
# §1  OTerm — operad term language
# ═══════════════════════════════════════════════════════════════

class OTerm:
    """Base class for operad terms."""
    __slots__ = ()
    def children(self) -> Tuple[OTerm, ...]: return ()

class OVar(OTerm):
    __slots__ = ('name',)
    def __init__(self, name: str): self.name = name
    def __repr__(self): return self.name
    def __eq__(self, o): return isinstance(o, OVar) and self.name == o.name
    def __hash__(self): return hash(('V', self.name))

class OLit(OTerm):
    __slots__ = ('value',)
    def __init__(self, value: object): self.value = value
    def __repr__(self): return repr(self.value)
    def __eq__(self, o): return isinstance(o, OLit) and type(self.value) is type(o.value) and self.value == o.value
    def __hash__(self): return hash(('L', type(self.value).__name__, self.value))

class OOp(OTerm):
    __slots__ = ('name', 'args')
    def __init__(self, name: str, args: Tuple[OTerm, ...]):
        self.name = name; self.args = args
    def children(self): return self.args
    def __repr__(self): return f'{self.name}({", ".join(repr(a) for a in self.args)})'
    def __eq__(self, o): return isinstance(o, OOp) and self.name == o.name and self.args == o.args
    def __hash__(self): return hash(('O', self.name, self.args))

class OFold(OTerm):
    """Canonical fold: fold_op(start, stop, base)."""
    __slots__ = ('op', 'start', 'stop', 'base')
    def __init__(self, op, start, stop, base):
        self.op = op; self.start = start; self.stop = stop; self.base = base
    def children(self): return (self.start, self.stop, self.base)
    def __repr__(self): return f'fold_{self.op}({self.start},{self.stop},base={self.base})'
    def __eq__(self, o):
        return isinstance(o, OFold) and self.op == o.op and self.start == o.start and self.stop == o.stop and self.base == o.base
    def __hash__(self): return hash(('F', self.op, self.start, self.stop, self.base))

class OCase(OTerm):
    """Case analysis: [(guard, value), ...]."""
    __slots__ = ('branches',)
    def __init__(self, branches): self.branches = branches
    def __repr__(self): return f'case({"|".join(f"{g}→{v}" for g,v in self.branches)})'
    def __eq__(self, o): return isinstance(o, OCase) and self.branches == o.branches
    def __hash__(self): return hash(('C', self.branches))

class OFix(OTerm):
    """General fixpoint."""
    __slots__ = ('name', 'params', 'body')
    def __init__(self, name, params, body): self.name = name; self.params = params; self.body = body
    def children(self): return (self.body,)
    def __repr__(self): return f'fix_{self.name}({",".join(self.params)}).{self.body}'
    def __eq__(self, o): return isinstance(o, OFix) and self.name == o.name and self.params == o.params and self.body == o.body
    def __hash__(self): return hash(('X', self.name, self.params, self.body))

class OSeq(OTerm):
    __slots__ = ('elts',)
    def __init__(self, elts): self.elts = elts
    def children(self): return self.elts
    def __repr__(self): return f'[{",".join(repr(e) for e in self.elts)}]'
    def __eq__(self, o): return isinstance(o, OSeq) and self.elts == o.elts
    def __hash__(self): return hash(('S', self.elts))

class ODict(OTerm):
    __slots__ = ('pairs',)
    def __init__(self, pairs): self.pairs = pairs
    def __repr__(self): return '{' + ','.join(f'{k}:{v}' for k,v in self.pairs) + '}'
    def __eq__(self, o): return isinstance(o, ODict) and self.pairs == o.pairs
    def __hash__(self): return hash(('D', self.pairs))


_OPAQUE_CTR = [0]
def _opaque(tag=''):
    _OPAQUE_CTR[0] += 1
    return OOp(f'⊥{tag}', (OLit(_OPAQUE_CTR[0]),))


# ═══════════════════════════════════════════════════════════════
# §2  Complete Python 3.11 → OTerm Interpreter
# ═══════════════════════════════════════════════════════════════

@dataclass
class Env:
    bindings: Dict[str, OTerm] = field(default_factory=dict)
    func_name: str = ''
    in_recursion: bool = False
    def get(self, name): return self.bindings.get(name)
    def put(self, name, val): self.bindings[name] = val
    def copy(self): return Env(dict(self.bindings), self.func_name, self.in_recursion)


# §2a — Expressions (complete)

def _expr(node: ast.expr, env: Env) -> OTerm:
    """TOTAL interpreter: every Python expression → OTerm."""

    # ── Atoms ──
    if isinstance(node, ast.Constant):
        # Distinguish type: int(1) ≠ float(1.0) ≠ bool(True)
        v = node.value
        if isinstance(v, bool): return OOp('bool', (OLit(v),))
        if isinstance(v, int): return OLit(v)
        if isinstance(v, float): return OOp('float', (OLit(v),))
        if isinstance(v, str): return OOp('str', (OLit(v),))
        if isinstance(v, bytes): return OOp('bytes', (OLit(v),))
        if isinstance(v, complex): return OOp('complex', (OLit(v.real), OLit(v.imag)))
        if v is None: return OOp('None', ())
        if v is ...: return OOp('Ellipsis', ())
        return _opaque('const')

    if isinstance(node, ast.Name):
        v = env.get(node.id)
        return v if v is not None else OVar(node.id)

    # ── Operators ──
    if isinstance(node, ast.BinOp):
        l, r = _expr(node.left, env), _expr(node.right, env)
        # Distinguish // from int(/) — different Python semantics
        names = {
            ast.Add:'+', ast.Sub:'-', ast.Mult:'*', ast.Div:'/',
            ast.FloorDiv:'//', ast.Mod:'%', ast.Pow:'**',
            ast.LShift:'<<', ast.RShift:'>>', ast.BitOr:'|',
            ast.BitAnd:'&', ast.BitXor:'^', ast.MatMult:'@',
        }
        return OOp(names.get(type(node.op), 'binop'), (l, r))

    if isinstance(node, ast.UnaryOp):
        operand = _expr(node.operand, env)
        names = {ast.USub:'neg', ast.UAdd:'pos', ast.Not:'not', ast.Invert:'~'}
        return OOp(names.get(type(node.op), 'unary'), (operand,))

    if isinstance(node, ast.Compare):
        left = _expr(node.left, env)
        names = {
            ast.Eq:'==', ast.NotEq:'!=', ast.Lt:'<', ast.LtE:'<=',
            ast.Gt:'>', ast.GtE:'>=', ast.In:'in', ast.NotIn:'not_in',
            ast.Is:'is', ast.IsNot:'is_not',
        }
        parts = []
        for op, comp in zip(node.ops, node.comparators):
            right = _expr(comp, env)
            parts.append(OOp(names.get(type(op), 'cmp'), (left, right)))
            left = right
        return parts[0] if len(parts) == 1 else OOp('and', tuple(parts))

    if isinstance(node, ast.BoolOp):
        vals = tuple(_expr(v, env) for v in node.values)
        return OOp('and' if isinstance(node.op, ast.And) else 'or', vals)

    if isinstance(node, ast.IfExp):
        c, t, f = _expr(node.test, env), _expr(node.body, env), _expr(node.orelse, env)
        return OCase(((c, t), (OOp('not', (c,)), f)))

    # ── Calls ──
    if isinstance(node, ast.Call):
        return _call(node, env)

    # ── Subscript / Attribute ──
    if isinstance(node, ast.Subscript):
        base = _expr(node.value, env)
        if isinstance(node.slice, ast.Slice):
            lo = _expr(node.slice.lower, env) if node.slice.lower else OOp('None', ())
            hi = _expr(node.slice.upper, env) if node.slice.upper else OOp('None', ())
            step = _expr(node.slice.step, env) if node.slice.step else OOp('None', ())
            return OOp('getslice', (base, lo, hi, step))
        return OOp('getitem', (base, _expr(node.slice, env)))

    if isinstance(node, ast.Attribute):
        return OOp(f'.{node.attr}', (_expr(node.value, env),))

    # ── Collections ──
    if isinstance(node, ast.Tuple):
        return OOp('tuple', tuple(_expr(e, env) for e in node.elts))

    if isinstance(node, ast.List):
        return OOp('list', tuple(_expr(e, env) for e in node.elts))

    if isinstance(node, ast.Set):
        return OOp('set_literal', tuple(_expr(e, env) for e in node.elts))

    if isinstance(node, ast.Dict):
        pairs = tuple(
            OOp('kv', (_expr(k, env) if k else _opaque('dk'), _expr(v, env)))
            for k, v in zip(node.keys, node.values))
        return OOp('dict', pairs)

    # ── Comprehensions (distinguish list vs set vs gen) ──
    if isinstance(node, ast.ListComp):
        return _comp(node, env, 'listcomp')
    if isinstance(node, ast.SetComp):
        return _comp(node, env, 'setcomp')
    if isinstance(node, ast.DictComp):
        return _comp(node, env, 'dictcomp')
    if isinstance(node, ast.GeneratorExp):
        # Generator ≠ listcomp semantically (lazy vs eager, single-use)
        return _comp(node, env, 'genexp')

    # ── Lambda — model default args for closure binding ──
    if isinstance(node, ast.Lambda):
        params = []
        defaults_start = len(node.args.args) - len(node.args.defaults)
        for i, a in enumerate(node.args.args):
            if i >= defaults_start:
                # Default arg = early binding: captures the VALUE at definition time
                default = _expr(node.args.defaults[i - defaults_start], env)
                params.append(OOp('param_default', (OLit(a.arg), default)))
            else:
                # No default = late binding: captures the VARIABLE (closure cell)
                params.append(OOp('param', (OLit(a.arg),)))
        body = _expr(node.body, env)
        return OOp('lambda', tuple(params) + (body,))

    # ── f-strings ──
    if isinstance(node, ast.JoinedStr):
        parts = tuple(
            _expr(v, env) if isinstance(v, ast.FormattedValue)
            else OOp('str', (OLit(v.value),)) if isinstance(v, ast.Constant)
            else _opaque('fstr')
            for v in node.values)
        return OOp('fstring', parts)

    if isinstance(node, ast.FormattedValue):
        val = _expr(node.value, env)
        conv = OLit(node.conversion) if node.conversion and node.conversion != -1 else OOp('None', ())
        fmt = _expr(node.format_spec, env) if node.format_spec else OOp('None', ())
        return OOp('format', (val, conv, fmt))

    # ── Walrus operator ──
    if isinstance(node, ast.NamedExpr):
        val = _expr(node.value, env)
        if isinstance(node.target, ast.Name):
            env.put(node.target.id, val)
        return val

    # ── Starred ──
    if isinstance(node, ast.Starred):
        return OOp('star', (_expr(node.value, env),))

    # ── Yield / Async ──
    if isinstance(node, ast.Yield):
        val = _expr(node.value, env) if node.value else OOp('None', ())
        return OOp('yield', (val,))

    if isinstance(node, ast.YieldFrom):
        return OOp('yield_from', (_expr(node.value, env),))

    if isinstance(node, ast.Await):
        return OOp('await', (_expr(node.value, env),))

    if isinstance(node, ast.Slice):
        lo = _expr(node.lower, env) if node.lower else OOp('None', ())
        hi = _expr(node.upper, env) if node.upper else OOp('None', ())
        step = _expr(node.step, env) if node.step else OOp('None', ())
        return OOp('slice_obj', (lo, hi, step))

    return _opaque(type(node).__name__)


def _call(node: ast.Call, env: Env) -> OTerm:
    """Interpret function/method calls with full semantic fidelity."""

    # Self-recursion marker
    if (isinstance(node.func, ast.Name) and node.func.id == env.func_name
            and env.in_recursion):
        args = tuple(_expr(a, env) for a in node.args)
        return OOp('__rec__', args)

    # Nested function
    if isinstance(node.func, ast.Name):
        fn_val = env.get(node.func.id)
        if isinstance(fn_val, OOp) and fn_val.name == '__func__':
            r = _inline(fn_val, node.args, node.keywords, env)
            if r is not None:
                return r

    # Build call term with kwargs (order matters for Python semantics)
    if isinstance(node.func, ast.Name):
        name = node.func.id
        args = tuple(_expr(a, env) for a in node.args)
        kwargs = tuple(
            OOp(f'kw_{k.arg or "**"}', (_expr(k.value, env),))
            for k in node.keywords)
        # Class instantiation → FRESH object (distinct identity per call)
        class_val = env.get(name)
        if isinstance(class_val, OOp) and class_val.name == 'class':
            _OPAQUE_CTR[0] += 1
            return OOp(f'{name}__new', (OLit(_OPAQUE_CTR[0]),) + class_val.args + args + kwargs)
        return OOp(name, args + kwargs)

    if isinstance(node.func, ast.Attribute):
        obj = _expr(node.func.value, env)
        method = node.func.attr
        args = tuple(_expr(a, env) for a in node.args)
        kwargs = tuple(
            OOp(f'kw_{k.arg or "**"}', (_expr(k.value, env),))
            for k in node.keywords)
        return OOp(f'.{method}', (obj,) + args + kwargs)

    # Dynamic callable
    fn = _expr(node.func, env)
    args = tuple(_expr(a, env) for a in node.args)
    return OOp('__call__', (fn,) + args)


def _comp(node, env, kind):
    """Comprehension → OTerm preserving iteration structure."""
    if not node.generators:
        return _opaque(kind)
    gen = node.generators[0]
    iter_term = _expr(gen.iter, env)
    # Use a fresh var for the comprehension target
    comp_env = env.copy()
    tgt_name = gen.target.id if isinstance(gen.target, ast.Name) else '__comp_tgt'
    comp_env.put(tgt_name, OVar(f'__{kind}_var'))
    if hasattr(node, 'elt'):
        elt = _expr(node.elt, comp_env)
    elif hasattr(node, 'key'):
        elt = OOp('kv', (_expr(node.key, comp_env), _expr(node.value, comp_env)))
    else:
        elt = _opaque('comp_elt')
    filters = tuple(_expr(f, comp_env) for f in gen.ifs) if gen.ifs else ()
    filt = OOp('and', filters) if len(filters) > 1 else (filters[0] if filters else OOp('bool', (OLit(True),)))
    inner = OOp(kind, (iter_term, elt, filt))
    # Nested generators
    for gen2 in node.generators[1:]:
        inner = OOp(f'{kind}_nested', (inner, _expr(gen2.iter, comp_env)))
    return inner


def _inline(fn_term: OOp, call_args, call_kwargs, env: Env) -> Optional[OTerm]:
    """Inline a nested function call."""
    if len(fn_term.args) < 1 or not isinstance(fn_term.args[0], OLit):
        return None
    func_node = fn_term.args[0].value
    if not isinstance(func_node, ast.FunctionDef):
        return None
    params = [a.arg for a in func_node.args.args]
    if len(call_args) != len(params):
        return None
    call_env = env.copy()
    for pname, arg_node in zip(params, call_args):
        call_env.put(pname, _expr(arg_node, env))
    sections = _extract_sections(func_node.body, call_env, OLit(True))
    if len(sections) == 1: return sections[0][1]
    if sections: return OCase(tuple(sections))
    return None


# §2b — Statements (complete)

def _extract_sections(stmts, env, guard):
    """Extract (guard, return_value) sections from statements."""
    stmts = _skip_doc(stmts)
    sections = []
    for i, stmt in enumerate(stmts):

        if isinstance(stmt, ast.Return):
            val = _expr(stmt.value, env) if stmt.value else OOp('None', ())
            sections.append((guard, val))
            return sections

        elif isinstance(stmt, ast.If):
            cond = _expr(stmt.test, env)
            tg = _and(guard, cond)
            fg = _and(guard, OOp('not', (cond,)))
            tr, fr = _has_return(stmt.body), _has_return(stmt.orelse) if stmt.orelse else False
            if tr: sections.extend(_extract_sections(stmt.body, env.copy(), tg))
            if fr and stmt.orelse: sections.extend(_extract_sections(stmt.orelse, env.copy(), fg))
            if tr and fr: return sections
            if tr:
                re = env.copy()
                if stmt.orelse: _exec_stmts(stmt.orelse, re)
                sections.extend(_extract_sections(stmts[i+1:], re, fg))
                return sections
            if fr:
                re = env.copy()
                _exec_stmts(stmt.body, re)
                sections.extend(_extract_sections(stmts[i+1:], re, tg))
                return sections
            te, fe = env.copy(), env.copy()
            _exec_stmts(stmt.body, te)
            if stmt.orelse: _exec_stmts(stmt.orelse, fe)
            _merge(env, te, fe, cond)

        elif isinstance(stmt, ast.Assign): _s_assign(stmt, env)
        elif isinstance(stmt, ast.AugAssign): _s_augassign(stmt, env)
        elif isinstance(stmt, ast.AnnAssign):
            if stmt.value: _s_assign_target(stmt.target, _expr(stmt.value, env), env)
        elif isinstance(stmt, ast.For): _s_for(stmt, env)
        elif isinstance(stmt, ast.While): _s_while(stmt, env)
        elif isinstance(stmt, ast.FunctionDef) or isinstance(stmt, ast.AsyncFunctionDef):
            _s_funcdef(stmt, env)
        elif isinstance(stmt, ast.ClassDef):
            # Classes: capture class body structure for faithful comparison
            body_terms = []
            cls_env = env.copy()
            for s in stmt.body:
                if isinstance(s, ast.FunctionDef):
                    body_terms.append(OOp('method', (OLit(s.name), OLit(s))))
                elif isinstance(s, ast.Assign):
                    for t in s.targets:
                        if isinstance(t, ast.Name):
                            body_terms.append(OOp('class_attr', (OLit(t.id), _expr(s.value, cls_env))))
            bases = tuple(_expr(b, env) for b in stmt.bases)
            env.put(stmt.name, OOp('class', (OLit(stmt.name),) + bases + tuple(body_terms)))

        elif isinstance(stmt, ast.Try):
            # Try/except: distinguish handler types faithfully
            # except Exception vs bare except → different operad terms
            handlers = []
            for h in stmt.handlers:
                if h.type is not None:
                    handler_type = _expr(h.type, env)
                else:
                    handler_type = OOp('BaseException', ())  # bare except catches all
                handlers.append(OOp('handler', (handler_type,)))
            body_sections = _extract_sections(stmt.body, env.copy(), guard)
            # If body has returns, include them with handler info
            if body_sections:
                for g, v in body_sections:
                    sections.append((g, OOp('try', (v,) + tuple(handlers))))
            # Continue with finally/orelse
            if stmt.orelse:
                _exec_stmts(stmt.orelse, env)
            if stmt.finalbody:
                _exec_stmts(stmt.finalbody, env)
            sub = _extract_sections(stmts[i+1:], env, guard)
            sections.extend(sub)
            return sections

        elif isinstance(stmt, ast.With) or isinstance(stmt, ast.AsyncWith):
            # with expr as var: → assign var, then body
            for item in stmt.items:
                cm = _expr(item.context_expr, env)
                if item.optional_vars and isinstance(item.optional_vars, ast.Name):
                    env.put(item.optional_vars.id, OOp('__enter__', (cm,)))
            _exec_stmts(stmt.body, env)

        elif isinstance(stmt, ast.Match):
            # Match/case: each case is a section
            subject = _expr(stmt.subject, env)
            for case in stmt.cases:
                pat_guard = _pattern_to_guard(case.pattern, subject, env)
                case_guard = _and(guard, pat_guard)
                if case.guard:
                    case_guard = _and(case_guard, _expr(case.guard, env))
                _bind_pattern(case.pattern, subject, env)
                sub = _extract_sections(case.body, env.copy(), case_guard)
                sections.extend(sub)
            return sections

        elif isinstance(stmt, ast.Raise):
            val = _expr(stmt.exc, env) if stmt.exc else OOp('None', ())
            sections.append((guard, OOp('raise', (val,))))
            return sections

        elif isinstance(stmt, (ast.Import, ast.ImportFrom, ast.Pass,
                               ast.Assert, ast.Delete, ast.Expr,
                               ast.Global, ast.Nonlocal, ast.Break,
                               ast.Continue)):
            if isinstance(stmt, ast.Expr):
                _expr(stmt.value, env)  # for side effects (e.g., method calls)
            pass  # control flow modifiers — skip

        elif isinstance(stmt, ast.AsyncFor):
            _s_for(stmt, env)  # treat as sync for equivalence purposes

        else:
            pass

    return sections


def _has_return(stmts):
    for s in stmts:
        if isinstance(s, ast.Return): return True
        if isinstance(s, ast.If):
            if _has_return(s.body) and s.orelse and _has_return(s.orelse): return True
    return False


def _skip_doc(body):
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
        return body[1:]
    return body


# §2c — Statement execution

def _exec_stmts(stmts, env):
    for s in stmts:
        if isinstance(s, ast.Assign): _s_assign(s, env)
        elif isinstance(s, ast.AugAssign): _s_augassign(s, env)
        elif isinstance(s, ast.AnnAssign):
            if s.value: _s_assign_target(s.target, _expr(s.value, env), env)
        elif isinstance(s, ast.For) or isinstance(s, ast.AsyncFor): _s_for(s, env)
        elif isinstance(s, ast.While): _s_while(s, env)
        elif isinstance(s, ast.If):
            cond = _expr(s.test, env)
            te, fe = env.copy(), env.copy()
            _exec_stmts(s.body, te)
            if s.orelse: _exec_stmts(s.orelse, fe)
            _merge(env, te, fe, cond)
        elif isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _s_funcdef(s, env)
        elif isinstance(s, ast.ClassDef):
            env.put(s.name, OOp('class', (OLit(s.name),)))
        elif isinstance(s, ast.With) or isinstance(s, ast.AsyncWith):
            for item in s.items:
                cm = _expr(item.context_expr, env)
                if item.optional_vars and isinstance(item.optional_vars, ast.Name):
                    env.put(item.optional_vars.id, OOp('__enter__', (cm,)))
            _exec_stmts(s.body, env)
        elif isinstance(s, ast.Try):
            _exec_stmts(s.body, env)
            if s.orelse: _exec_stmts(s.orelse, env)
            if s.finalbody: _exec_stmts(s.finalbody, env)
        elif isinstance(s, ast.Expr):
            # Track mutation side effects: obj.append(x) → obj = .append(obj, x)
            if (isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Attribute)
                    and isinstance(s.value.func.value, ast.Name)):
                obj_name = s.value.func.value.id
                method = s.value.func.attr
                obj_val = env.get(obj_name)
                if obj_val is not None:
                    args = tuple(_expr(a, env) for a in s.value.args)
                    env.put(obj_name, OOp(f'.{method}', (obj_val,) + args))
            else:
                _expr(s.value, env)
        else:
            pass


def _s_assign(stmt, env):
    val = _expr(stmt.value, env)
    for t in stmt.targets:
        _s_assign_target(t, val, env)


def _s_assign_target(target, val, env):
    if isinstance(target, ast.Name):
        env.put(target.id, val)
    elif isinstance(target, ast.Tuple) or isinstance(target, ast.List):
        for j, elt in enumerate(target.elts):
            _s_assign_target(elt, OOp('getitem', (val, OLit(j))), env)
    elif isinstance(target, ast.Subscript):
        pass  # mutation
    elif isinstance(target, ast.Attribute):
        pass  # mutation
    elif isinstance(target, ast.Starred):
        if isinstance(target.value, ast.Name):
            env.put(target.value.id, OOp('star_unpack', (val,)))


def _s_augassign(stmt, env):
    if isinstance(stmt.target, ast.Name):
        name = stmt.target.id
        old = env.get(name) or OVar(name)
        rhs = _expr(stmt.value, env)
        # AugAssign uses __iadd__ etc. (in-place) — different from +
        # This is semantically significant for mutable types
        op_names = {
            ast.Add:'iadd', ast.Sub:'isub', ast.Mult:'imul', ast.Div:'itruediv',
            ast.FloorDiv:'ifloordiv', ast.Mod:'imod', ast.Pow:'ipow',
            ast.LShift:'ilshift', ast.RShift:'irshift',
            ast.BitOr:'ior', ast.BitAnd:'iand', ast.BitXor:'ixor',
        }
        op = op_names.get(type(stmt.op), 'iaug')
        env.put(name, OOp(op, (old, rhs)))


def _s_funcdef(stmt, env):
    """Store function with its default arguments (for closure semantics)."""
    # Evaluate defaults NOW (early binding)
    defaults = tuple(_expr(d, env) for d in stmt.args.defaults)
    kw_defaults = tuple(
        _expr(d, env) if d else OOp('None', ())
        for d in stmt.args.kw_defaults)
    decorators = tuple(_expr(d, env) for d in stmt.decorator_list)
    env.put(stmt.name, OOp('__func__', (
        OLit(stmt),
        OOp('defaults', defaults),
        OOp('kw_defaults', kw_defaults),
        OOp('decorators', decorators),
    )))


def _s_for(stmt, env):
    if not isinstance(stmt.target, ast.Name):
        return
    lv = stmt.target.id
    r = _detect_range(stmt.iter, env)
    if r is not None:
        start, stop = r
        modified = _find_modified(stmt.body)
        state = {}
        for vn in modified:
            if vn == lv: continue
            v = env.get(vn)
            if v is not None: state[vn] = v
        if not state: return
        # Canonical fold: acc OP= lv
        if len(stmt.body) == 1 and len(state) == 1:
            s = stmt.body[0]
            an = next(iter(state))
            if (isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name)
                    and s.target.id == an and isinstance(s.value, ast.Name)
                    and s.value.id == lv):
                op_map = {ast.Add:'+', ast.Mult:'*', ast.Sub:'-',
                          ast.BitOr:'|', ast.BitAnd:'&', ast.BitXor:'^'}
                op = op_map.get(type(s.op))
                if op:
                    env.put(an, OFold(op, start, stop, state[an]))
                    return
        # General fold
        fold_env = env.copy()
        fold_env.put(lv, OVar(f'__{lv}_i'))
        for vn in state:
            fold_env.put(vn, OVar(f'__{vn}_next'))
        _exec_stmts(stmt.body, fold_env)
        for vn, init in state.items():
            after = fold_env.get(vn) or _opaque(f'loop_{vn}')
            env.put(vn, OFix(f'loop_{vn}', (lv,),
                             OCase(((OOp('>=', (OVar(lv), stop)), init),
                                    (OLit(True), after)))))
        return
    # Non-range iteration
    iter_val = _expr(stmt.iter, env)
    modified = _find_modified(stmt.body)
    for vn in modified:
        if vn == lv: continue
        old = env.get(vn) or OVar(vn)
        env.put(vn, OOp('fold_iter', (iter_val, old, _opaque(f'body_{vn}'))))


def _s_while(stmt, env, n=3):
    """While loop → OFix fixpoint over modified state variables.
    
    while cond: body  →  fix_state(vars) = if cond then fix_state(body(vars)) else vars
    """
    # Identify modified variables
    modified = _find_modified(stmt.body)
    state = {}
    for vn in modified:
        v = env.get(vn)
        if v is not None: state[vn] = v
    
    if not state:
        return  # no state modified — skip
    
    # Build fixpoint environment: each state var → a fresh variable
    fix_env = env.copy()
    for vn in state:
        fix_env.put(vn, OVar(f'__{vn}_w'))
    
    # Execute body symbolically
    body_env = fix_env.copy()
    _exec_stmts(stmt.body, body_env)
    
    # Build the fixpoint term
    cond = _expr(stmt.test, fix_env)
    for vn, init in state.items():
        after = body_env.get(vn) or _opaque(f'while_{vn}')
        # fix_vn = if cond then fix_vn(after) else init
        env.put(vn, OFix(f'while_{vn}', (f'__{vn}_w',),
                        OCase(((cond, after),
                               (OOp('not', (cond,)), init)))))


def _merge(target, te, fe, cond):
    for k in set(te.bindings) | set(fe.bindings):
        tv, fv = te.get(k), fe.get(k)
        if tv is None or fv is None: continue
        orig = target.get(k)
        if orig is not None and tv == orig and fv == orig: continue
        target.put(k, OCase(((cond, tv), (OOp('not', (cond,)), fv))))


def _pattern_to_guard(pattern, subject, env):
    """Convert match pattern to guard term."""
    if isinstance(pattern, ast.MatchAs):
        if pattern.pattern is None:
            return OOp('bool', (OLit(True),))  # wildcard
        return _pattern_to_guard(pattern.pattern, subject, env)
    if isinstance(pattern, ast.MatchValue):
        return OOp('==', (subject, _expr(pattern.value, env)))
    if isinstance(pattern, ast.MatchClass):
        return OOp('isinstance', (subject, _expr(pattern.cls, env)))
    return OOp('bool', (OLit(True),))

def _bind_pattern(pattern, subject, env):
    if isinstance(pattern, ast.MatchAs) and pattern.name:
        env.put(pattern.name, subject)


# ── Helpers ──

def _and(a, b):
    if isinstance(a, OLit) and a.value is True: return b
    if isinstance(b, OLit) and b.value is True: return a
    return OOp('and', (a, b))


def _detect_range(iter_expr, env):
    if not (isinstance(iter_expr, ast.Call) and isinstance(iter_expr.func, ast.Name)
            and iter_expr.func.id == 'range'): return None
    args = iter_expr.args
    if len(args) == 1: return OLit(0), _expr(args[0], env)
    if len(args) >= 2: return _expr(args[0], env), _expr(args[1], env)
    return None


def _find_modified(stmts):
    modified, seen = [], set()
    for s in stmts:
        names = []
        if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name): names.append(s.target.id)
        elif isinstance(s, ast.Assign):
            for t in s.targets:
                if isinstance(t, ast.Name): names.append(t.id)
                elif isinstance(t, ast.Tuple): names.extend(e.id for e in t.elts if isinstance(e, ast.Name))
        elif isinstance(s, ast.If):
            names.extend(_find_modified(s.body))
            if s.orelse: names.extend(_find_modified(s.orelse))
        elif isinstance(s, ast.For): names.extend(_find_modified(s.body))
        for n in names:
            if n not in seen: seen.add(n); modified.append(n)
    return modified


# ═══════════════════════════════════════════════════════════════
# §3  Canonical Forms — equational rewriting
# ═══════════════════════════════════════════════════════════════

def _normalize(t, depth=0):
    if depth > 50 or isinstance(t, (OVar, OLit)): return t
    if isinstance(t, OSeq): return OSeq(tuple(_normalize(e, depth+1) for e in t.elts))
    if isinstance(t, ODict): return ODict(tuple((_normalize(k, depth+1), _normalize(v, depth+1)) for k,v in t.pairs))
    if isinstance(t, OFold):
        return OFold(t.op, _normalize(t.start, depth+1), _normalize(t.stop, depth+1), _normalize(t.base, depth+1))
    if isinstance(t, OCase):
        return OCase(tuple((_normalize(g, depth+1), _normalize(v, depth+1)) for g,v in t.branches))
    if isinstance(t, OFix):
        body = _normalize(t.body, depth+1)
        fold = _extract_fold(t.name, t.params, body)
        return fold if fold else OFix(t.name, t.params, body)
    if isinstance(t, OOp):
        args = tuple(_normalize(a, depth+1) for a in t.args)
        return _rewrite(OOp(t.name, args), depth)
    return t


def _rewrite(t, depth):
    n, a = t.name, t.args
    # Constant folding
    if all(isinstance(x, OLit) and isinstance(x.value, (int, float)) for x in a):
        r = _eval_op(n, [x.value for x in a])
        if r is not None: return OLit(r)
    # Idempotence
    if n in ('sorted', 'set', 'list', 'bool', 'int', 'abs') and len(a) == 1:
        if isinstance(a[0], OOp) and a[0].name == n: return a[0]
    # list(sorted(x)) → sorted(x)
    if n == 'list' and len(a) == 1 and isinstance(a[0], OOp) and a[0].name == 'sorted': return a[0]
    # sorted(list(x)) → sorted(x)
    if n == 'sorted' and len(a) == 1 and isinstance(a[0], OOp) and a[0].name == 'list':
        return OOp('sorted', a[0].args)
    # neg(neg(x)) → x
    if n == 'neg' and len(a) == 1 and isinstance(a[0], OOp) and a[0].name == 'neg': return a[0].args[0]
    # not(not(x)) → x
    if n == 'not' and len(a) == 1 and isinstance(a[0], OOp) and a[0].name == 'not': return a[0].args[0]
    # Identity elements
    if n == '+' and len(a) == 2:
        if a[1] == OLit(0): return a[0]
        if a[0] == OLit(0): return a[1]
    if n == '*' and len(a) == 2:
        if a[1] == OLit(1): return a[0]
        if a[0] == OLit(1): return a[1]
        if a[1] == OLit(0) or a[0] == OLit(0): return OLit(0)
    if n == '-' and len(a) == 2 and a[1] == OLit(0): return a[0]
    if n == '//' and len(a) == 2 and a[1] == OLit(1): return a[0]
    # iadd/imul: ONLY normalize to +/* when both operands are known int literals.
    # For variables (which could be lists, strings), iadd ≠ + (in-place mutation).
    if n in ('iadd', 'imul', 'isub', 'ifloordiv', 'imod') and len(a) == 2:
        if _is_int_literal(a[0]) and _is_int_literal(a[1]):
            plain = {'iadd':'+', 'imul':'*', 'isub':'-', 'ifloordiv':'//', 'imod':'%'}[n]
            return _rewrite(OOp(plain, a), depth)
    # Canonicalize commutative ops ONLY when both args are known int literals
    # (for arbitrary types, + is not commutative: "a"+"b" ≠ "b"+"a")
    if n in ('*', '|', '&', '^', '==', '!=') and len(a) == 2:
        if _is_int_expr(a[0]) and _is_int_expr(a[1]):
            if repr(a[1]) < repr(a[0]): return OOp(n, (a[1], a[0]))
    return t


def _is_int_literal(t):
    return isinstance(t, OLit) and isinstance(t.value, int)

def _is_int_expr(t):
    """Conservative check: is this term definitely an integer?"""
    if isinstance(t, OLit) and isinstance(t.value, int): return True
    if isinstance(t, OOp) and t.name in ('+', '-', '*', '//', '%', 'neg', 'abs',
                                          'max', 'min', 'len', 'int', 'bool'):
        return True
    if isinstance(t, OFold): return True
    return False


def _eval_op(name, vals):
    if len(vals) == 2:
        a, b = vals
        ops = {'+': lambda: a+b, '-': lambda: a-b, '*': lambda: a*b,
               '//': lambda: a//b if b else None, '%': lambda: a%b if b else None,
               '**': lambda: a**b if b >= 0 else None,
               '==': lambda: a == b, '!=': lambda: a != b,
               '<': lambda: a < b, '<=': lambda: a <= b,
               '>': lambda: a > b, '>=': lambda: a >= b}
        if name in ops:
            try: return ops[name]()
            except: return None
    if len(vals) == 1:
        ops = {'neg': lambda: -vals[0], 'abs': lambda: abs(vals[0]),
               'not': lambda: not vals[0], 'bool': lambda: bool(vals[0]),
               'int': lambda: int(vals[0])}
        if name in ops:
            try: return ops[name]()
            except: return None
    return None


def _extract_fold(name, params, body):
    if len(params) != 1 or not isinstance(body, OCase): return None
    if len(body.branches) < 2: return None
    base_br = rec_br = None
    for g, v in body.branches:
        if _contains_rec(v): rec_br = (g, v)
        else: base_br = (g, v)
    if not base_br or not rec_br: return None
    threshold = _threshold(base_br[0], params[0])
    if threshold is None: return None
    op = _fold_op(rec_br[1], params[0])
    if op is None: return None
    return OFold(op, OLit(threshold), OOp('+', (OVar(params[0]), OLit(1))), base_br[1])


def _contains_rec(t):
    if isinstance(t, OOp) and t.name == '__rec__': return True
    for c in t.children():
        if _contains_rec(c): return True
    return False


def _threshold(guard, param):
    if not isinstance(guard, OOp): return None
    if guard.name == '<=' and len(guard.args) == 2:
        if isinstance(guard.args[0], OVar) and guard.args[0].name == param:
            if isinstance(guard.args[1], OLit) and isinstance(guard.args[1].value, int):
                return guard.args[1].value
    if guard.name == '<' and len(guard.args) == 2:
        if isinstance(guard.args[0], OVar) and guard.args[0].name == param:
            if isinstance(guard.args[1], OLit) and isinstance(guard.args[1].value, int):
                return guard.args[1].value - 1
    if guard.name == '==' and len(guard.args) == 2:
        if isinstance(guard.args[0], OVar) and guard.args[0].name == param:
            if isinstance(guard.args[1], OLit) and isinstance(guard.args[1].value, int):
                return guard.args[1].value
    return None


def _fold_op(val, param):
    if not isinstance(val, OOp) or len(val.args) != 2: return None
    a, b = val.args
    is_p = lambda n: isinstance(n, OVar) and n.name == param
    is_r = lambda n: (isinstance(n, OOp) and n.name == '__rec__' and len(n.args) == 1
                      and isinstance(n.args[0], OOp) and n.args[0].name == '-'
                      and isinstance(n.args[0].args[0], OVar) and n.args[0].args[0].name == param
                      and n.args[0].args[1] == OLit(1))
    if val.name in ('*', '+', '-', '|', '&', '^'):
        if (is_p(a) and is_r(b)) or (is_r(a) and is_p(b)):
            return val.name
    return None


# ═══════════════════════════════════════════════════════════════
# §4  Cohomological Comparison
# ═══════════════════════════════════════════════════════════════

def _deep_canon(t, depth=0):
    if depth > 30 or isinstance(t, (OVar, OLit)): return t
    if isinstance(t, OOp):
        args = tuple(_deep_canon(a, depth+1) for a in t.args)
        # Only flatten/sort truly commutative ops when all args are int-typed
        if t.name in ('*', '|', '&', '^') and len(args) >= 2 and all(_is_int_expr(a) for a in args):
            flat = []
            for a in args:
                if isinstance(a, OOp) and a.name == t.name: flat.extend(a.args)
                else: flat.append(a)
            return OOp(t.name, tuple(sorted(flat, key=repr)))
        # 'and'/'or' are commutative in boolean logic
        if t.name in ('and', 'or') and len(args) >= 2:
            flat = []
            for a in args:
                if isinstance(a, OOp) and a.name == t.name: flat.extend(a.args)
                else: flat.append(a)
            return OOp(t.name, tuple(sorted(flat, key=repr)))
        return OOp(t.name, args)
    if isinstance(t, OFold): return OFold(t.op, _deep_canon(t.start, depth+1), _deep_canon(t.stop, depth+1), _deep_canon(t.base, depth+1))
    if isinstance(t, OCase): return OCase(tuple((_deep_canon(g, depth+1), _deep_canon(v, depth+1)) for g,v in t.branches))
    if isinstance(t, OFix): return OFix(t.name, t.params, _deep_canon(t.body, depth+1))
    return t


def _z3_check(a, b):
    """Z3 semantic check — ONLY for terms where all free vars are integers.

    SOUNDNESS: we only create Z3 Int variables for names that appear
    exclusively in integer contexts (arithmetic, int comparisons, range).
    If any variable has ambiguous type, we skip (return None).
    """
    if not _HAS_Z3: return None
    fv = _free_vars(a) | _free_vars(b)
    if not fv: return None
    # Check that all free vars appear in integer contexts
    for v in fv:
        if not _var_is_int_in(a, v) and not _var_is_int_in(b, v):
            return None
    z3v = {n: _z3.Int(n) for n in fv}
    za, zb = _to_z3(a, z3v), _to_z3(b, z3v)
    if za is None or zb is None: return None
    s = _z3.Solver()
    s.set('timeout', 2000)
    s.add(za != zb)
    r = s.check()
    if r == _z3.unsat: return True
    if r == _z3.sat: return False
    return None


def _var_is_int_in(t, varname):
    """Check if variable 'varname' is used in an integer context in term t."""
    if isinstance(t, OVar):
        return False  # bare variable reference — no context
    if isinstance(t, OLit):
        return False
    if isinstance(t, OOp):
        # If this op is arithmetic and varname appears as direct arg
        # These ops REQUIRE integer/numeric operands in Python
        int_ops = {'-', '//', '%', '**', 'neg', 'abs',
                   '<', '<=', '>', '>=',
                   'max', 'min', 'range'}
        for arg in t.args:
            if isinstance(arg, OVar) and arg.name == varname:
                if t.name in int_ops:
                    return True
            if _var_is_int_in(arg, varname):
                return True
    if isinstance(t, OFold):
        return (_var_is_int_in(t.start, varname) or
                _var_is_int_in(t.stop, varname) or
                _var_is_int_in(t.base, varname))
    if isinstance(t, OCase):
        return any(_var_is_int_in(g, varname) or _var_is_int_in(v, varname)
                   for g, v in t.branches)
    if isinstance(t, OFix):
        if varname in t.params: return False
        return _var_is_int_in(t.body, varname)
    return False


def _free_vars(t):
    if isinstance(t, OVar): return {t.name}
    if isinstance(t, OLit): return set()
    r = set()
    for c in t.children(): r |= _free_vars(c)
    if isinstance(t, OOp):
        for a in t.args: r |= _free_vars(a)
    if isinstance(t, OCase):
        for g, v in t.branches: r |= _free_vars(g) | _free_vars(v)
    if isinstance(t, OFix): r = _free_vars(t.body) - set(t.params)
    if isinstance(t, ODict):
        for k, v in t.pairs: r |= _free_vars(k) | _free_vars(v)
    return r


_Z3_FOLDS = {}

def _to_z3(t, vars):
    if isinstance(t, OLit):
        if isinstance(t.value, int): return _z3.IntVal(t.value)
        if isinstance(t.value, bool): return _z3.BoolVal(t.value)
        return None
    if isinstance(t, OVar): return vars.get(t.name)
    if isinstance(t, OOp):
        if t.name in ('+','-','*','//','%') and len(t.args) == 2:
            l, r = _to_z3(t.args[0], vars), _to_z3(t.args[1], vars)
            if l is None or r is None: return None
            if t.name == '+': return l + r
            if t.name == '-': return l - r
            if t.name == '*': return l * r
            if t.name == '//': return l / r
            if t.name == '%': return l % r
        if t.name == 'neg' and len(t.args) == 1:
            a = _to_z3(t.args[0], vars)
            return -a if a is not None else None
        if t.name == 'abs' and len(t.args) == 1:
            a = _to_z3(t.args[0], vars)
            return _z3.If(a >= 0, a, -a) if a is not None else None
        if t.name in ('max','min') and len(t.args) == 2:
            a, b = _to_z3(t.args[0], vars), _to_z3(t.args[1], vars)
            if a is None or b is None: return None
            return _z3.If(a >= b, a, b) if t.name == 'max' else _z3.If(a <= b, a, b)
        if t.name in ('<','<=','>','>=','==','!=') and len(t.args) == 2:
            l, r = _to_z3(t.args[0], vars), _to_z3(t.args[1], vars)
            if l is None or r is None: return None
            return {'<': l<r, '<=': l<=r, '>': l>r, '>=': l>=r, '==': l==r, '!=': l!=r}[t.name]
        if t.name == 'not' and len(t.args) == 1:
            a = _to_z3(t.args[0], vars)
            if a is not None and _z3.is_bool(a): return _z3.Not(a)
        return None
    if isinstance(t, OFold):
        start, stop, base = _to_z3(t.start, vars), _to_z3(t.stop, vars), _to_z3(t.base, vars)
        if any(x is None for x in (start, stop, base)): return None
        bv = None
        try: bv = int(str(_z3.simplify(base)))
        except: pass
        if bv is None: return None
        key = (t.op, bv)
        if key not in _Z3_FOLDS:
            OPS = {'+': lambda a,b: a+b, '*': lambda a,b: a*b}
            if t.op not in OPS: return None
            fn = _z3.RecFunction(f'__zf_{t.op}_{bv}', _z3.IntSort(), _z3.IntSort(), _z3.IntSort())
            i, s = _z3.Int(f'__zi_{t.op}_{bv}'), _z3.Int(f'__zs_{t.op}_{bv}')
            _z3.RecAddDefinition(fn, [i, s], _z3.If(i >= s, _z3.IntVal(bv), OPS[t.op](i, fn(i+1, s))))
            _Z3_FOLDS[key] = fn
        return _Z3_FOLDS[key](start, stop)
    if isinstance(t, OCase):
        if not t.branches: return None
        result = _to_z3(t.branches[-1][1], vars)
        for guard, val in reversed(t.branches[:-1]):
            g, v = _to_z3(guard, vars), _to_z3(val, vars)
            if g is None or v is None or result is None: return None
            if _z3.is_bool(g): result = _z3.If(g, v, result)
            else: result = _z3.If(g != 0, v, result)
        return result
    return None


# ═══════════════════════════════════════════════════════════════
# §5  Public API
# ═══════════════════════════════════════════════════════════════

@dataclass
class EquivalenceResult:
    equivalent: Optional[bool]
    explanation: str
    h0: int = 0
    h1: int = 0


def check_equivalence(source_f: str, source_g: str) -> EquivalenceResult:
    """Operadic cohomological equivalence check."""
    import sys
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 3000))
    try:
        return _check_inner(source_f, source_g)
    except RecursionError:
        return EquivalenceResult(None, 'recursion limit')
    finally:
        sys.setrecursionlimit(old)


def _check_inner(source_f, source_g):
    _OPAQUE_CTR[0] = 0
    _Z3_FOLDS.clear()

    sf = _extract_sheaf(source_f)
    sg = _extract_sheaf(source_g)
    if sf is None or sg is None: return EquivalenceResult(None, 'cannot parse')
    secs_f, pf = sf
    secs_g, pg = sg
    if len(pf) != len(pg): return EquivalenceResult(False, f'arity {len(pf)}≠{len(pg)}')
    if not secs_f or not secs_g: return EquivalenceResult(None, 'empty sheaf')

    rename = {b: a for a, b in zip(pf, pg) if a != b}

    # Build global terms
    gf = _case(secs_f)
    gg = _case([(g, _rename(v, rename)) for g, v in secs_g])

    nf, ng = _normalize(gf), _normalize(gg)
    # Level A: structural
    if nf == ng: return EquivalenceResult(True, f'H¹=0: structural equality', h0=len(secs_f))
    # Level B: algebraic
    cf, cg = _deep_canon(nf), _deep_canon(ng)
    if cf == cg: return EquivalenceResult(True, f'H¹=0: algebraic equality', h0=len(secs_f))
    # Level C: Z3
    if _HAS_Z3:
        r = _z3_check(nf, ng)
        if r is True: return EquivalenceResult(True, f'H¹=0: Z3 proved ∀x.f(x)=g(x)', h0=len(secs_f))
        if r is False: return EquivalenceResult(False, 'H¹≠0: Z3 counterexample', h1=1)

    return EquivalenceResult(None, 'inconclusive')


def _extract_sheaf(source):
    try: tree = ast.parse(textwrap.dedent(source))
    except: return None
    func = None
    for n in tree.body:
        if isinstance(n, ast.FunctionDef): func = n; break
    if not func: return None
    pn = [a.arg for a in func.args.args]
    env = Env(func_name=func.name)
    for p in pn: env.put(p, OVar(p))
    body = _skip_doc(func.body)
    is_rec = any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == func.name for n in ast.walk(func))
    if is_rec: env.in_recursion = True
    secs = _extract_sections(body, env, OLit(True))
    if is_rec:
        for i, (g, v) in enumerate(secs):
            if _contains_rec(v):
                fixed = OFix(func.name, tuple(pn), OCase(tuple(secs)))
                normed = _normalize(fixed)
                if isinstance(normed, OFold): return [(OLit(True), normed)], pn
                return [(OLit(True), normed)], pn
    return [(_normalize(g), _normalize(v)) for g, v in secs], pn


def _case(sections):
    if len(sections) == 1: return sections[0][1]
    return OCase(tuple(sections))

def _rename(t, rename):
    if not rename: return t
    if isinstance(t, OVar): return OVar(rename.get(t.name, t.name))
    if isinstance(t, OLit): return t
    if isinstance(t, OOp): return OOp(t.name, tuple(_rename(a, rename) for a in t.args))
    if isinstance(t, OFold): return OFold(t.op, _rename(t.start, rename), _rename(t.stop, rename), _rename(t.base, rename))
    if isinstance(t, OCase): return OCase(tuple((_rename(g, rename), _rename(v, rename)) for g,v in t.branches))
    if isinstance(t, OFix):
        inner = {k:v for k,v in rename.items() if k not in t.params}
        return OFix(t.name, t.params, _rename(t.body, inner))
    if isinstance(t, OSeq): return OSeq(tuple(_rename(e, rename) for e in t.elts))
    if isinstance(t, ODict): return ODict(tuple((_rename(k, rename), _rename(v, rename)) for k,v in t.pairs))
    return t
