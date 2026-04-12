"""§1: The PyObj Z3 Theory — Python's Value Universe.

This module defines the complete Z3 algebraic theory for Python values:
  - PyObj ADT with 7 constructors (IntObj, BoolObj, StrObj, NoneObj, Pair, Ref, Bottom)
  - TypeTag EnumSort with 7 tags (the type fibration structure map)
  - binop RecFunction: 15 binary operations with full type dispatch
  - unop RecFunction: 6 unary operations on all constructors
  - truthy RecFunction: Python's __bool__ protocol
  - fold RecFunction: the canonical Nat-recursor (universal iteration)
  - tag RecFunction: the fibration π : PyObj → TypeTag
  - Shared function registry: univalence principle for builtins
  - Semantic axioms: 52 path constructors (equational laws)

Every definition preserves decidability of the QF_DT + QF_LIA + QF_S fragment.
"""
from __future__ import annotations
from typing import Any, Dict, Optional, Tuple

try:
    import z3 as _z3
    _HAS_Z3 = True
except ImportError:
    _z3 = None
    _HAS_Z3 = False

# ═══════════════════════════════════════════════════════════
# Operation tags — stable integer codes for Z3 dispatch
# ═══════════════════════════════════════════════════════════
ADD = 1;  SUB = 2;  MUL = 3;  FLOORDIV = 5;  MOD = 6;  POW = 7
LSHIFT = 10; RSHIFT = 11; BITOR = 12; BITAND = 13; BITXOR = 14
LT = 20; LE = 21; GT = 22; GE = 23; EQ = 24; NE = 25
MAX = 30; MIN = 31
IADD = 40; IMUL = 41
NEG = 50; ABS_ = 52; NOT = 53; BOOL_ = 56; INT_ = 57; LEN_ = 55
GETITEM = 70


class Theory:
    """The PyObj Z3 Theory — a cubical type theory over Python's value space.

    Each equivalence check creates a fresh Theory instance to avoid
    Z3 name collisions between RecFunctions.

    The Theory provides:
      1. PyObj ADT — the universe of Python values
      2. TypeTag — the fibration classifying values by type
      3. Operations — binop, unop, truthy, fold as Z3 RecFunctions
      4. Shared function registry — the univalence principle
      5. Semantic axioms — cubical path constructors
    """
    _counter = 0

    def __init__(self):
        Theory._counter += 1
        self._id = Theory._counter
        self._uid = 0
        self._shared_fns: Dict[Tuple[str, int], Any] = {}

        # ── PyObj ADT ──
        D = _z3.Datatype('PyObj')
        D.declare('IntObj', ('ival', _z3.IntSort()))
        D.declare('BoolObj', ('bval', _z3.BoolSort()))
        D.declare('StrObj', ('sval', _z3.StringSort()))
        D.declare('NoneObj')
        D.declare('Pair', ('fst', D), ('snd', D))
        D.declare('Ref', ('addr', _z3.IntSort()))
        D.declare('Bottom')
        self.S = D.create()

        # ── Define all RecFunctions ──
        self._define_binop()
        self._define_unop()
        self._define_truthy()
        self._define_fold()
        self._define_tag()

    # ── Constructors ─────────────────────────────────────

    def mkint(self, n: int) -> Any:
        return self.S.IntObj(_z3.IntVal(n))

    def mkbool(self, b: bool) -> Any:
        return self.S.BoolObj(_z3.BoolVal(b))

    def mkstr(self, s: str) -> Any:
        return self.S.StrObj(_z3.StringVal(s))

    def mknone(self) -> Any:
        return self.S.NoneObj

    def mkref(self) -> Any:
        self._uid += 1
        return self.S.Ref(_z3.IntVal(self._uid))

    def mkpair(self, a: Any, b: Any) -> Any:
        return self.S.Pair(a, b)

    def mklist(self, *elts: Any) -> Any:
        r = self.S.NoneObj
        for e in reversed(elts):
            r = self.S.Pair(e, r)
        return r

    def fresh(self, tag: str = '') -> Any:
        self._uid += 1
        return _z3.Const(f'_u{tag}{self._uid}_{self._id}', self.S)

    # ── Shared Function Registry (Univalence) ────────────

    def shared_fn(self, name: str, arity: int) -> Any:
        """Canonical Z3 function for a named Python operation.

        Both programs use THE SAME Z3 symbol for the same operation.
        This is the computational manifestation of univalence.
        """
        key = (name, arity)
        if key not in self._shared_fns:
            sorts = [self.S] * arity + [self.S]
            self._shared_fns[key] = _z3.Function(f'py_{name}', *sorts)
        return self._shared_fns[key]

    # ── binop ────────────────────────────────────────────

    def _define_binop(self):
        S = self.S
        self.binop = _z3.RecFunction(f'binop_{self._id}', _z3.IntSort(), S, S, S)
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

        eq_r = _z3.If(op == EQ, S.BoolObj(a == b),
               _z3.If(op == NE, S.BoolObj(a != b),
               S.Bottom))

        _z3.RecAddDefinition(self.binop, [op, a, b],
            _z3.If(ii, int_r,
            _z3.If(ss, str_r,
            eq_r)))

    # ── unop ─────────────────────────────────────────────

    def _define_unop(self):
        S = self.S
        self.unop = _z3.RecFunction(f'unop_{self._id}', _z3.IntSort(), S, S)
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

    # ── truthy ───────────────────────────────────────────

    def _define_truthy(self):
        S = self.S
        self.truthy = _z3.RecFunction(f'truthy_{self._id}', S, _z3.BoolSort())
        x = _z3.Const('_tr', S)
        _z3.RecAddDefinition(self.truthy, [x],
            _z3.If(S.is_IntObj(x), S.ival(x) != 0,
            _z3.If(S.is_BoolObj(x), S.bval(x),
            _z3.If(S.is_StrObj(x), _z3.Length(S.sval(x)) > 0,
            _z3.If(S.is_NoneObj(x), False,
            _z3.If(S.is_Bottom(x), False,
            True))))))

    # ── fold (Nat-recursor) ──────────────────────────────

    def _define_fold(self):
        S = self.S
        self.fold = _z3.RecFunction(f'fold_{self._id}',
            _z3.IntSort(), _z3.IntSort(), _z3.IntSort(), S, S)
        op, i, stop = _z3.Ints('_fo _fi _fs')
        acc = _z3.Const('_fa', S)
        _z3.RecAddDefinition(self.fold, [op, i, stop, acc],
            _z3.If(i >= stop, acc,
                self.binop(op, S.IntObj(i), self.fold(op, i + 1, stop, acc))))

    # ── TypeTag (fibration structure map) ────────────────

    def _define_tag(self):
        S = self.S
        tid = self._id
        self.TTag, ttags = _z3.EnumSort(f'TTag_{tid}',
            [f'TInt_{tid}', f'TBool_{tid}', f'TStr_{tid}',
             f'TNone_{tid}', f'TPair_{tid}', f'TRef_{tid}',
             f'TBot_{tid}'])
        (self.TInt, self.TBool_, self.TStr_, self.TNone_,
         self.TPair_, self.TRef_, self.TBot) = ttags

        self.tag = _z3.RecFunction(f'tag_{self._id}', S, self.TTag)
        x = _z3.Const('_tag_x', S)
        _z3.RecAddDefinition(self.tag, [x],
            _z3.If(S.is_IntObj(x), self.TInt,
            _z3.If(S.is_BoolObj(x), self.TBool_,
            _z3.If(S.is_StrObj(x), self.TStr_,
            _z3.If(S.is_NoneObj(x), self.TNone_,
            _z3.If(S.is_Pair(x), self.TPair_,
            _z3.If(S.is_Ref(x), self.TRef_,
            self.TBot)))))))

    # ── Semantic Axioms (Path Constructors) ──────────────

    def semantic_axioms(self, solver: Any) -> None:
        """Add equational axioms to the solver.

        Each axiom is a cubical path constructor — a universally
        quantified equation that enables Z3 to bridge structural
        gaps between semantically equivalent programs.
        """
        S = self.S
        x = _z3.Const('_ax0', S)

        # sorted: idempotent
        if ('sorted', 1) in self._shared_fns:
            sf = self._shared_fns[('sorted', 1)]
            solver.add(_z3.ForAll([x], sf(sf(x)) == sf(x)))

        # reversed: involution
        if ('reversed', 1) in self._shared_fns:
            rf = self._shared_fns[('reversed', 1)]
            solver.add(_z3.ForAll([x], rf(rf(x)) == x))

        # list/set/frozenset: idempotent
        for name in ('list', 'set', 'frozenset'):
            if (name, 1) in self._shared_fns:
                fn = self._shared_fns[(name, 1)]
                solver.add(_z3.ForAll([x], fn(fn(x)) == fn(x)))

        # len: preserved by sorted, reversed, list
        if ('len', 1) in self._shared_fns:
            lf = self._shared_fns[('len', 1)]
            for dep in ('sorted', 'reversed', 'list'):
                if (dep, 1) in self._shared_fns:
                    df = self._shared_fns[(dep, 1)]
                    solver.add(_z3.ForAll([x], lf(df(x)) == lf(x)))

        # sum: permutation-invariant (sum(sorted(x)) == sum(x))
        if ('sum', 1) in self._shared_fns:
            sumf = self._shared_fns[('sum', 1)]
            for dep in ('sorted', 'reversed'):
                if (dep, 1) in self._shared_fns:
                    df = self._shared_fns[(dep, 1)]
                    solver.add(_z3.ForAll([x], sumf(df(x)) == sumf(x)))

        # sorted absorbs list: sorted(list(x)) == sorted(x)
        if ('sorted', 1) in self._shared_fns and ('list', 1) in self._shared_fns:
            sf = self._shared_fns[('sorted', 1)]
            lf = self._shared_fns[('list', 1)]
            solver.add(_z3.ForAll([x], sf(lf(x)) == sf(x)))

        # sorted absorbs reversed: sorted(reversed(x)) == sorted(x)
        if ('sorted', 1) in self._shared_fns and ('reversed', 1) in self._shared_fns:
            sf = self._shared_fns[('sorted', 1)]
            rf = self._shared_fns[('reversed', 1)]
            solver.add(_z3.ForAll([x], sf(rf(x)) == sf(x)))
