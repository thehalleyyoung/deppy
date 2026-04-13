"""P47 Axiom: Dunder Method Equivalences.

Establishes equivalences between Python built-in functions and their
corresponding dunder (double-underscore) method calls: len(x) ↔ x.__len__(),
str(x) ↔ x.__str__(), repr(x) ↔ x.__repr__(), x[k] ↔ x.__getitem__(k),
x in y ↔ y.__contains__(x), iter(x) ↔ x.__iter__(), next(x) ↔ x.__next__(),
hash(x) ↔ x.__hash__(), bool(x) ↔ x.__bool__(), and arithmetic/comparison
operator forms.

Mathematical basis: Python's data model defines a functor from the category
of built-in operations to method dispatch.  Each built-in function f is a
natural transformation η: F ⇒ G where F maps objects to their protocol
interface and G maps objects to concrete method resolution order (MRO)
dispatch.  The dunder protocol is the universal property: for every type T
implementing __len__, the diagram commutes:

  len(x)           ≡  x.__len__()         (length protocol)
  str(x)           ≡  x.__str__()         (string protocol)
  repr(x)          ≡  x.__repr__()        (repr protocol)
  x[k]             ≡  x.__getitem__(k)    (subscript protocol)
  x in y           ≡  y.__contains__(x)   (membership protocol)
  iter(x)          ≡  x.__iter__()        (iteration protocol)
  next(x)          ≡  x.__next__()        (iterator protocol)
  hash(x)          ≡  x.__hash__()        (hash protocol)
  bool(x)          ≡  x.__bool__()        (truth protocol)
  x[k] = v         ≡  x.__setitem__(k, v) (setitem protocol)
  del x[k]         ≡  x.__delitem__(k)    (delitem protocol)
  x == y           ≡  x.__eq__(y)         (equality protocol)
  x < y            ≡  x.__lt__(y)         (ordering protocol)
  x + y            ≡  x.__add__(y)        (addition protocol)
  x(...)           ≡  x.__call__(...)     (callable protocol)
  abs(x)           ≡  x.__abs__()         (absolute value protocol)
  int(x)           ≡  x.__int__()         (int conversion protocol)
  float(x)         ≡  x.__float__()       (float conversion protocol)

Key rewrites:
  • len_fn(x) ↔ dunder_len(x)
  • str_fn(x) ↔ dunder_str(x)
  • repr_fn(x) ↔ dunder_repr(x)
  • getitem(x, k) ↔ dunder_getitem(x, k)
  • contains(y, x) ↔ dunder_contains(y, x)
  • iter_fn(x) ↔ dunder_iter(x)
  • next_fn(x) ↔ dunder_next(x)
  • hash_fn(x) ↔ dunder_hash(x)
  • bool_fn(x) ↔ dunder_bool(x)
  • setitem(x, k, v) ↔ dunder_setitem(x, k, v)
  • delitem(x, k) ↔ dunder_delitem(x, k)
  • eq_op(x, y) ↔ dunder_eq(x, y)
  • lt_op(x, y) ↔ dunder_lt(x, y)
  • add_op(x, y) ↔ dunder_add(x, y)
  • call_fn(x, args) ↔ dunder_call(x, args)
  • abs_fn(x) ↔ dunder_abs(x)
  • int_fn(x) ↔ dunder_int(x)
  • float_fn(x) ↔ dunder_float(x)

(§P47, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P47_dunder"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P02_builtins", "P11_functional", "P46_operator"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P47 Dunder Method Equivalences).

1. len_fn(x) ≡ dunder_len(x)
   len(x) ≡ x.__len__().
   Both return the number of items in x.  CPython implements len()
   by calling type(x).__len__(x).

2. str_fn(x) ≡ dunder_str(x)
   str(x) ≡ x.__str__().
   Both return the informal string representation.

3. repr_fn(x) ≡ dunder_repr(x)
   repr(x) ≡ x.__repr__().
   Both return the official string representation.

4. getitem(x, k) ≡ dunder_getitem(x, k)
   x[k] ≡ x.__getitem__(k).
   Both retrieve the item at index/key k.

5. contains(y, x) ≡ dunder_contains(y, x)
   x in y ≡ y.__contains__(x).
   Both test membership.

6. iter_fn(x) ≡ dunder_iter(x)
   iter(x) ≡ x.__iter__().
   Both return an iterator over x.

7. next_fn(x) ≡ dunder_next(x)
   next(x) ≡ x.__next__().
   Both advance the iterator and return the next item.

8. hash_fn(x) ≡ dunder_hash(x)
   hash(x) ≡ x.__hash__().
   Both return the hash value.

9. bool_fn(x) ≡ dunder_bool(x)
   bool(x) ≡ x.__bool__().
   Both return the truth value.

10. setitem(x, k, v) ≡ dunder_setitem(x, k, v)
    x[k] = v ≡ x.__setitem__(k, v).
    Both assign value v at index/key k.

11. delitem(x, k) ≡ dunder_delitem(x, k)
    del x[k] ≡ x.__delitem__(k).
    Both delete the item at index/key k.

12. eq_op(x, y) ≡ dunder_eq(x, y)
    x == y ≡ x.__eq__(y).
    Both test equality.

13. lt_op(x, y) ≡ dunder_lt(x, y)
    x < y ≡ x.__lt__(y).
    Both test strict less-than ordering.

14. add_op(x, y) ≡ dunder_add(x, y)
    x + y ≡ x.__add__(y).
    Both compute addition / concatenation.

15. call_fn(x, args) ≡ dunder_call(x, args)
    x(...) ≡ x.__call__(...).
    Both invoke the callable.

16. abs_fn(x) ≡ dunder_abs(x)
    abs(x) ≡ x.__abs__().
    Both compute the absolute value.

17. int_fn(x) ≡ dunder_int(x)
    int(x) ≡ x.__int__().
    Both convert to integer.

18. float_fn(x) ≡ dunder_float(x)
    float(x) ≡ x.__float__().
    Both convert to float.
"""

EXAMPLES = [
    ("len_fn($x)", "dunder_len($x)",
     "P47_len_to_dunder"),
    ("str_fn($x)", "dunder_str($x)",
     "P47_str_to_dunder"),
    ("getitem($x, $k)", "dunder_getitem($x, $k)",
     "P47_getitem_to_dunder"),
    ("contains($y, $x)", "dunder_contains($y, $x)",
     "P47_contains_to_dunder"),
    ("eq_op($x, $y)", "dunder_eq($x, $y)",
     "P47_eq_to_dunder"),
]

# All operator names handled by this axiom.
_DUNDER_OPS = frozenset({
    'len_fn', 'dunder_len', 'str_fn', 'dunder_str',
    'repr_fn', 'dunder_repr', 'getitem', 'dunder_getitem',
    'contains', 'dunder_contains', 'iter_fn', 'dunder_iter',
    'next_fn', 'dunder_next', 'hash_fn', 'dunder_hash',
    'bool_fn', 'dunder_bool', 'setitem', 'dunder_setitem',
    'delitem', 'dunder_delitem', 'eq_op', 'dunder_eq',
    'lt_op', 'dunder_lt', 'add_op', 'dunder_add',
    'call_fn', 'dunder_call', 'abs_fn', 'dunder_abs',
    'int_fn', 'dunder_int', 'float_fn', 'dunder_float',
})

# Mapping from builtin form to (dunder form, arity, forward label, inverse label).
_PAIRS: Tuple[Tuple[str, str, int, str, str], ...] = (
    ('len_fn',    'dunder_len',      1, 'P47_len_to_dunder',      'P47_dunder_to_len'),
    ('str_fn',    'dunder_str',      1, 'P47_str_to_dunder',      'P47_dunder_to_str'),
    ('repr_fn',   'dunder_repr',     1, 'P47_repr_to_dunder',     'P47_dunder_to_repr'),
    ('getitem',   'dunder_getitem',  2, 'P47_getitem_to_dunder',  'P47_dunder_to_getitem'),
    ('contains',  'dunder_contains', 2, 'P47_contains_to_dunder', 'P47_dunder_to_contains'),
    ('iter_fn',   'dunder_iter',     1, 'P47_iter_to_dunder',     'P47_dunder_to_iter'),
    ('next_fn',   'dunder_next',     1, 'P47_next_to_dunder',     'P47_dunder_to_next'),
    ('hash_fn',   'dunder_hash',     1, 'P47_hash_to_dunder',     'P47_dunder_to_hash'),
    ('bool_fn',   'dunder_bool',     1, 'P47_bool_to_dunder',     'P47_dunder_to_bool'),
    ('setitem',   'dunder_setitem',  3, 'P47_setitem_to_dunder',  'P47_dunder_to_setitem'),
    ('delitem',   'dunder_delitem',  2, 'P47_delitem_to_dunder',  'P47_dunder_to_delitem'),
    ('eq_op',     'dunder_eq',       2, 'P47_eq_to_dunder',       'P47_dunder_to_eq'),
    ('lt_op',     'dunder_lt',       2, 'P47_lt_to_dunder',       'P47_dunder_to_lt'),
    ('add_op',    'dunder_add',      2, 'P47_add_to_dunder',      'P47_dunder_to_add'),
    ('call_fn',   'dunder_call',     2, 'P47_call_to_dunder',     'P47_dunder_to_call'),
    ('abs_fn',    'dunder_abs',      1, 'P47_abs_to_dunder',      'P47_dunder_to_abs'),
    ('int_fn',    'dunder_int',      1, 'P47_int_to_dunder',      'P47_dunder_to_int'),
    ('float_fn',  'dunder_float',    1, 'P47_float_to_dunder',    'P47_dunder_to_float'),
)

# Precomputed lookup tables.
_BUILTIN_TO_DUNDER = {b: (d, ar, fwd) for b, d, ar, fwd, _ in _PAIRS}
_DUNDER_TO_BUILTIN = {d: (b, ar, inv) for b, d, ar, _, inv in _PAIRS}

# Labels that belong to the inverse direction.
_INVERSE_LABELS = frozenset(inv for _, _, _, _, inv in _PAIRS)


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P47: Dunder method equivalence rewrites (forward and reverse)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── Builtin → dunder direction ──
    if term.name in _BUILTIN_TO_DUNDER:
        dunder_name, arity, label = _BUILTIN_TO_DUNDER[term.name]
        if len(term.args) >= arity:
            results.append((
                OOp(dunder_name, term.args),
                label,
            ))

    # ── Dunder → builtin direction ──
    if term.name in _DUNDER_TO_BUILTIN:
        builtin_name, arity, label = _DUNDER_TO_BUILTIN[term.name]
        if len(term.args) >= arity:
            results.append((
                OOp(builtin_name, term.args),
                label,
            ))

    # ── Structural expansions ──

    # len_fn(x) → OLam(('x',), OOp('dunder_len', (OVar('x'),)))
    if term.name == 'len_fn' and len(term.args) == 1:
        x = term.args[0]
        results.append((
            OLam(('x',), OOp('dunder_len', (OVar('x'),))),
            'P47_len_to_olam',
        ))

    # getitem(x, k) → OLam structural
    if term.name == 'getitem' and len(term.args) == 2:
        x, k = term.args
        results.append((
            OLam(('x',), OOp('dunder_getitem', (OVar('x'), k))),
            'P47_getitem_to_olam',
        ))

    # contains(y, x) → OCase(dunder_contains(y, x), true, false) — expand to conditional
    if term.name == 'contains' and len(term.args) == 2:
        y, x = term.args
        results.append((
            OCase(OOp('dunder_contains', (y, x)), OLit(True), OLit(False)),
            'P47_contains_to_case',
        ))

    # eq_op(x, y) → OCase structural
    if term.name == 'eq_op' and len(term.args) == 2:
        x, y = term.args
        results.append((
            OCase(OOp('dunder_eq', (x, y)), OLit(True), OLit(False)),
            'P47_eq_to_case',
        ))

    # bool_fn(x) → OCase(dunder_bool(x), True, False)
    if term.name == 'bool_fn' and len(term.args) == 1:
        x = term.args[0]
        results.append((
            OCase(OOp('dunder_bool', (x,)), OLit(True), OLit(False)),
            'P47_bool_to_case',
        ))

    # add_op(x, y) → OOp('add', (x, y)) low-level arithmetic
    if term.name == 'add_op' and len(term.args) == 2:
        results.append((
            OOp('add', term.args),
            'P47_add_op_to_add',
        ))

    # lt_op(x, y) → OOp('lt', (x, y)) low-level comparison
    if term.name == 'lt_op' and len(term.args) == 2:
        results.append((
            OOp('lt', term.args),
            'P47_lt_op_to_lt',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (dunder → builtin form)."""
    return [(t, l) for t, l in apply(term, ctx) if l in _INVERSE_LABELS]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a dunder-related op."""
    if isinstance(term, OOp) and term.name in _DUNDER_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for builtin_name, dunder_name, _, _, _ in _PAIRS:
        if builtin_name in sc and dunder_name in tc:
            return 0.9
        if dunder_name in sc and builtin_name in tc:
            return 0.9
    for kw in _DUNDER_OPS:
        if kw in sc and kw in tc:
            return 0.85
    if any(k in sc for k in _DUNDER_OPS):
        return 0.3
    return 0.05


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    _pass = 0
    _fail = 0

    def _assert(cond: bool, msg: str) -> None:
        global _pass, _fail
        if cond:
            _pass += 1
        else:
            _fail += 1
            print(f"  FAIL: {msg}")

    # 1. len_fn → dunder_len
    t1 = OOp('len_fn', (OVar('xs'),))
    r1 = apply(t1)
    _assert(any(l == 'P47_len_to_dunder' for _, l in r1),
            "len_fn → dunder_len")

    # 2. dunder_len → len_fn
    t2 = OOp('dunder_len', (OVar('xs'),))
    r2 = apply(t2)
    _assert(any(l == 'P47_dunder_to_len' for _, l in r2),
            "dunder_len → len_fn")

    # 3. str_fn → dunder_str
    t3 = OOp('str_fn', (OVar('x'),))
    r3 = apply(t3)
    _assert(any(l == 'P47_str_to_dunder' for _, l in r3),
            "str_fn → dunder_str")

    # 4. dunder_str → str_fn
    t4 = OOp('dunder_str', (OVar('x'),))
    r4 = apply(t4)
    _assert(any(l == 'P47_dunder_to_str' for _, l in r4),
            "dunder_str → str_fn")

    # 5. repr_fn → dunder_repr
    t5 = OOp('repr_fn', (OVar('x'),))
    r5 = apply(t5)
    _assert(any(l == 'P47_repr_to_dunder' for _, l in r5),
            "repr_fn → dunder_repr")

    # 6. getitem → dunder_getitem
    t6 = OOp('getitem', (OVar('xs'), OLit(0)))
    r6 = apply(t6)
    _assert(any(l == 'P47_getitem_to_dunder' for _, l in r6),
            "getitem → dunder_getitem")

    # 7. dunder_getitem → getitem
    t7 = OOp('dunder_getitem', (OVar('xs'), OLit(0)))
    r7 = apply(t7)
    _assert(any(l == 'P47_dunder_to_getitem' for _, l in r7),
            "dunder_getitem → getitem")

    # 8. contains → dunder_contains
    t8 = OOp('contains', (OVar('ys'), OVar('x')))
    r8 = apply(t8)
    _assert(any(l == 'P47_contains_to_dunder' for _, l in r8),
            "contains → dunder_contains")

    # 9. iter_fn → dunder_iter
    t9 = OOp('iter_fn', (OVar('xs'),))
    r9 = apply(t9)
    _assert(any(l == 'P47_iter_to_dunder' for _, l in r9),
            "iter_fn → dunder_iter")

    # 10. next_fn → dunder_next
    t10 = OOp('next_fn', (OVar('it'),))
    r10 = apply(t10)
    _assert(any(l == 'P47_next_to_dunder' for _, l in r10),
            "next_fn → dunder_next")

    # 11. hash_fn → dunder_hash
    t11 = OOp('hash_fn', (OVar('x'),))
    r11 = apply(t11)
    _assert(any(l == 'P47_hash_to_dunder' for _, l in r11),
            "hash_fn → dunder_hash")

    # 12. bool_fn → dunder_bool
    t12 = OOp('bool_fn', (OVar('x'),))
    r12 = apply(t12)
    _assert(any(l == 'P47_bool_to_dunder' for _, l in r12),
            "bool_fn → dunder_bool")

    # 13. setitem → dunder_setitem
    t13 = OOp('setitem', (OVar('xs'), OLit(0), OLit(99)))
    r13 = apply(t13)
    _assert(any(l == 'P47_setitem_to_dunder' for _, l in r13),
            "setitem → dunder_setitem")

    # 14. delitem → dunder_delitem
    t14 = OOp('delitem', (OVar('xs'), OLit(0)))
    r14 = apply(t14)
    _assert(any(l == 'P47_delitem_to_dunder' for _, l in r14),
            "delitem → dunder_delitem")

    # 15. eq_op → dunder_eq
    t15 = OOp('eq_op', (OVar('a'), OVar('b')))
    r15 = apply(t15)
    _assert(any(l == 'P47_eq_to_dunder' for _, l in r15),
            "eq_op → dunder_eq")

    # 16. dunder_eq → eq_op
    t16 = OOp('dunder_eq', (OVar('a'), OVar('b')))
    r16 = apply(t16)
    _assert(any(l == 'P47_dunder_to_eq' for _, l in r16),
            "dunder_eq → eq_op")

    # 17. lt_op → dunder_lt
    t17 = OOp('lt_op', (OVar('a'), OVar('b')))
    r17 = apply(t17)
    _assert(any(l == 'P47_lt_to_dunder' for _, l in r17),
            "lt_op → dunder_lt")

    # 18. add_op → dunder_add
    t18 = OOp('add_op', (OVar('a'), OVar('b')))
    r18 = apply(t18)
    _assert(any(l == 'P47_add_to_dunder' for _, l in r18),
            "add_op → dunder_add")

    # 19. call_fn → dunder_call
    t19 = OOp('call_fn', (OVar('f'), OVar('args')))
    r19 = apply(t19)
    _assert(any(l == 'P47_call_to_dunder' for _, l in r19),
            "call_fn → dunder_call")

    # 20. abs_fn → dunder_abs
    t20 = OOp('abs_fn', (OVar('x'),))
    r20 = apply(t20)
    _assert(any(l == 'P47_abs_to_dunder' for _, l in r20),
            "abs_fn → dunder_abs")

    # 21. int_fn → dunder_int
    t21 = OOp('int_fn', (OVar('x'),))
    r21 = apply(t21)
    _assert(any(l == 'P47_int_to_dunder' for _, l in r21),
            "int_fn → dunder_int")

    # 22. float_fn → dunder_float
    t22 = OOp('float_fn', (OVar('x'),))
    r22 = apply(t22)
    _assert(any(l == 'P47_float_to_dunder' for _, l in r22),
            "float_fn → dunder_float")

    # 23. len_fn → OLam structural
    _assert(any(l == 'P47_len_to_olam' for _, l in r1),
            "len_fn → OLam")
    lam_r = [(t, l) for t, l in r1 if l == 'P47_len_to_olam']
    if lam_r:
        _assert(isinstance(lam_r[0][0], OLam),
                "len_fn produces OLam")
    else:
        _assert(False, "len_fn produces OLam")

    # 24. getitem → OLam structural
    _assert(any(l == 'P47_getitem_to_olam' for _, l in r6),
            "getitem → OLam")
    gi_lam = [(t, l) for t, l in r6 if l == 'P47_getitem_to_olam']
    if gi_lam:
        _assert(isinstance(gi_lam[0][0], OLam),
                "getitem produces OLam")
    else:
        _assert(False, "getitem produces OLam")

    # 25. contains → OCase structural
    _assert(any(l == 'P47_contains_to_case' for _, l in r8),
            "contains → OCase")
    c_case = [(t, l) for t, l in r8 if l == 'P47_contains_to_case']
    if c_case:
        _assert(isinstance(c_case[0][0], OCase),
                "contains produces OCase")
    else:
        _assert(False, "contains produces OCase")

    # 26. eq_op → OCase structural
    _assert(any(l == 'P47_eq_to_case' for _, l in r15),
            "eq_op → OCase")

    # 27. bool_fn → OCase structural
    _assert(any(l == 'P47_bool_to_case' for _, l in r12),
            "bool_fn → OCase")

    # 28. add_op → OOp('add', ...) structural
    _assert(any(l == 'P47_add_op_to_add' for _, l in r18),
            "add_op → add structural")

    # 29. lt_op → OOp('lt', ...) structural
    _assert(any(l == 'P47_lt_op_to_lt' for _, l in r17),
            "lt_op → lt structural")

    # 30. inverse: dunder_len → len_fn
    r30_inv = apply_inverse(OOp('dunder_len', (OVar('xs'),)))
    _assert(any(l == 'P47_dunder_to_len' for _, l in r30_inv),
            "inv: dunder_len → len_fn")

    # 31. inverse: dunder_getitem → getitem
    r31_inv = apply_inverse(OOp('dunder_getitem', (OVar('xs'), OLit(0))))
    _assert(any(l == 'P47_dunder_to_getitem' for _, l in r31_inv),
            "inv: dunder_getitem → getitem")

    # 32. inverse: dunder_eq → eq_op
    r32_inv = apply_inverse(OOp('dunder_eq', (OVar('a'), OVar('b'))))
    _assert(any(l == 'P47_dunder_to_eq' for _, l in r32_inv),
            "inv: dunder_eq → eq_op")

    # 33. inverse: dunder_abs → abs_fn
    r33_inv = apply_inverse(OOp('dunder_abs', (OVar('x'),)))
    _assert(any(l == 'P47_dunder_to_abs' for _, l in r33_inv),
            "inv: dunder_abs → abs_fn")

    # 34. recognizes dunder ops
    _assert(recognizes(OOp('len_fn', (OVar('x'),))),
            "recognizes len_fn")
    _assert(recognizes(OOp('dunder_len', (OVar('x'),))),
            "recognizes dunder_len")
    _assert(recognizes(OOp('eq_op', (OVar('a'), OVar('b')))),
            "recognizes eq_op")
    _assert(recognizes(OOp('dunder_call', (OVar('f'), OVar('args')))),
            "recognizes dunder_call")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 35. relevance: len_fn ↔ dunder_len high
    _assert(relevance_score(
        OOp('len_fn', (OVar('x'),)),
        OOp('dunder_len', (OVar('x'),)),
    ) > 0.7, "len/dunder relevance high")

    # 36. relevance: getitem ↔ dunder_getitem high
    _assert(relevance_score(
        OOp('getitem', (OVar('xs'), OLit(0))),
        OOp('dunder_getitem', (OVar('xs'), OLit(0))),
    ) > 0.7, "getitem/dunder relevance high")

    # 37. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    # 38. no rewrites for non-OOp
    _assert(apply(OVar('x')) == [], "no rewrites for OVar")
    _assert(apply(OLit(42)) == [], "no rewrites for OLit")

    # 39. dunder_setitem → setitem
    r39 = apply(OOp('dunder_setitem', (OVar('xs'), OLit(0), OLit(99))))
    _assert(any(l == 'P47_dunder_to_setitem' for _, l in r39),
            "dunder_setitem → setitem")

    # 40. dunder_float → float_fn
    r40 = apply(OOp('dunder_float', (OVar('x'),)))
    _assert(any(l == 'P47_dunder_to_float' for _, l in r40),
            "dunder_float → float_fn")

    print(f"P47 dunder: {_pass} passed, {_fail} failed")
