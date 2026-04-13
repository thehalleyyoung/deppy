"""P46 Axiom: Operator Module Equivalences.

Establishes equivalences between Python's operator module functions
and their lambda equivalents: operator.itemgetter(k) vs lambda x: x[k],
operator.attrgetter('a') vs lambda x: x.a, operator.methodcaller('m')
vs lambda x: x.m(), operator.add vs lambda a, b: a + b, and sorted()
with operator.itemgetter key vs lambda key.

Mathematical basis: the operator module provides named morphisms in
the category of Python types.  operator.itemgetter(k) is the
projection morphism π_k for product types (tuples/lists),
operator.attrgetter('a') is the field projection for record types,
and operator.add is the addition morphism in the additive monoid.

  itemgetter(k)      ≡ λx. π_k(x)          (projection)
  attrgetter('a')    ≡ λx. x.a              (field access)
  methodcaller('m')  ≡ λx. x.m()            (method dispatch)
  operator.add       ≡ λa,b. a + b          (addition)
  operator.mul       ≡ λa,b. a * b          (multiplication)

Key rewrites:
  • operator.itemgetter(k) ↔ lambda x: x[k]
  • operator.attrgetter('a') ↔ lambda x: x.a
  • operator.methodcaller('m') ↔ lambda x: x.m()
  • operator.add ↔ lambda a, b: a + b
  • operator.mul ↔ lambda a, b: a * b
  • operator.sub ↔ lambda a, b: a - b
  • operator.neg ↔ lambda x: -x
  • operator.not_ ↔ lambda x: not x
  • operator.eq ↔ lambda a, b: a == b
  • operator.lt ↔ lambda a, b: a < b
  • sorted(xs, key=itemgetter(k)) ↔ sorted(xs, key=lambda x: x[k])

(§P46, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P46_operator"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P11_functional", "P05_sort_variants", "P35_map_filter_reduce"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P46 Operator Module Equivalences).

1. itemgetter(k) ≡ lambda_getitem(k)
   operator.itemgetter(k) ≡ lambda x: x[k].
   Both extract element at index/key k.

2. attrgetter(attr) ≡ lambda_getattr(attr)
   operator.attrgetter('a') ≡ lambda x: x.a.
   Both access attribute 'a'.

3. methodcaller(m) ≡ lambda_method_call(m)
   operator.methodcaller('m') ≡ lambda x: x.m().
   Both call method 'm' with no arguments.

4. operator_add ≡ lambda_add
   operator.add ≡ lambda a, b: a + b.
   Both compute the sum.

5. operator_mul ≡ lambda_mul
   operator.mul ≡ lambda a, b: a * b.
   Both compute the product.

6. operator_sub ≡ lambda_sub
   operator.sub ≡ lambda a, b: a - b.
   Both compute the difference.

7. operator_neg ≡ lambda_neg
   operator.neg ≡ lambda x: -x.
   Both compute the additive inverse.

8. operator_not ≡ lambda_not
   operator.not_ ≡ lambda x: not x.
   Both compute logical negation.

9. operator_eq ≡ lambda_eq
   operator.eq ≡ lambda a, b: a == b.
   Both test equality.

10. operator_lt ≡ lambda_lt
    operator.lt ≡ lambda a, b: a < b.
    Both test strict less-than.

11. sorted_itemgetter(xs, k) ≡ sorted_lambda_key(xs, k)
    sorted(xs, key=itemgetter(k)) ≡ sorted(xs, key=lambda x: x[k]).
    Both sort by the k-th element.

12. itemgetter with tuple index → multi-projection.
"""

EXAMPLES = [
    ("itemgetter($k)", "lambda_getitem($k)",
     "P46_itemgetter_to_lambda"),
    ("attrgetter($attr)", "lambda_getattr($attr)",
     "P46_attrgetter_to_lambda"),
    ("methodcaller($m)", "lambda_method_call($m)",
     "P46_methodcaller_to_lambda"),
    ("operator_add()", "lambda_add()",
     "P46_add_to_lambda"),
    ("sorted_itemgetter($xs, $k)", "sorted_lambda_key($xs, $k)",
     "P46_sorted_itemgetter_to_lambda"),
]

_OPERATOR_OPS = frozenset({
    'itemgetter', 'lambda_getitem', 'attrgetter', 'lambda_getattr',
    'methodcaller', 'lambda_method_call', 'operator_add', 'lambda_add',
    'operator_mul', 'lambda_mul', 'operator_sub', 'lambda_sub',
    'operator_neg', 'lambda_neg', 'operator_not', 'lambda_not',
    'operator_eq', 'lambda_eq', 'operator_lt', 'lambda_lt',
    'sorted_itemgetter', 'sorted_lambda_key',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P46: Operator module equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. itemgetter(k) ↔ lambda_getitem(k) ──
    if term.name == 'itemgetter' and len(term.args) >= 1:
        results.append((
            OOp('lambda_getitem', term.args),
            'P46_itemgetter_to_lambda',
        ))

    if term.name == 'lambda_getitem' and len(term.args) >= 1:
        results.append((
            OOp('itemgetter', term.args),
            'P46_lambda_to_itemgetter',
        ))

    # ── 2. attrgetter(attr) ↔ lambda_getattr(attr) ──
    if term.name == 'attrgetter' and len(term.args) >= 1:
        results.append((
            OOp('lambda_getattr', term.args),
            'P46_attrgetter_to_lambda',
        ))

    if term.name == 'lambda_getattr' and len(term.args) >= 1:
        results.append((
            OOp('attrgetter', term.args),
            'P46_lambda_to_attrgetter',
        ))

    # ── 3. methodcaller(m) ↔ lambda_method_call(m) ──
    if term.name == 'methodcaller' and len(term.args) >= 1:
        results.append((
            OOp('lambda_method_call', term.args),
            'P46_methodcaller_to_lambda',
        ))

    if term.name == 'lambda_method_call' and len(term.args) >= 1:
        results.append((
            OOp('methodcaller', term.args),
            'P46_lambda_to_methodcaller',
        ))

    # ── 4. operator_add ↔ lambda_add ──
    if term.name == 'operator_add' and len(term.args) == 2:
        results.append((
            OOp('lambda_add', term.args),
            'P46_add_to_lambda',
        ))

    if term.name == 'lambda_add' and len(term.args) == 2:
        results.append((
            OOp('operator_add', term.args),
            'P46_lambda_to_add',
        ))

    # ── 5. operator_mul ↔ lambda_mul ──
    if term.name == 'operator_mul' and len(term.args) == 2:
        results.append((
            OOp('lambda_mul', term.args),
            'P46_mul_to_lambda',
        ))

    if term.name == 'lambda_mul' and len(term.args) == 2:
        results.append((
            OOp('operator_mul', term.args),
            'P46_lambda_to_mul',
        ))

    # ── 6. operator_sub ↔ lambda_sub ──
    if term.name == 'operator_sub' and len(term.args) == 2:
        results.append((
            OOp('lambda_sub', term.args),
            'P46_sub_to_lambda',
        ))

    if term.name == 'lambda_sub' and len(term.args) == 2:
        results.append((
            OOp('operator_sub', term.args),
            'P46_lambda_to_sub',
        ))

    # ── 7. operator_neg ↔ lambda_neg ──
    if term.name == 'operator_neg' and len(term.args) == 1:
        results.append((
            OOp('lambda_neg', term.args),
            'P46_neg_to_lambda',
        ))

    if term.name == 'lambda_neg' and len(term.args) == 1:
        results.append((
            OOp('operator_neg', term.args),
            'P46_lambda_to_neg',
        ))

    # ── 8. operator_not ↔ lambda_not ──
    if term.name == 'operator_not' and len(term.args) == 1:
        results.append((
            OOp('lambda_not', term.args),
            'P46_not_to_lambda',
        ))

    if term.name == 'lambda_not' and len(term.args) == 1:
        results.append((
            OOp('operator_not', term.args),
            'P46_lambda_to_not',
        ))

    # ── 9. operator_eq ↔ lambda_eq ──
    if term.name == 'operator_eq' and len(term.args) == 2:
        results.append((
            OOp('lambda_eq', term.args),
            'P46_eq_to_lambda',
        ))

    if term.name == 'lambda_eq' and len(term.args) == 2:
        results.append((
            OOp('operator_eq', term.args),
            'P46_lambda_to_eq',
        ))

    # ── 10. operator_lt ↔ lambda_lt ──
    if term.name == 'operator_lt' and len(term.args) == 2:
        results.append((
            OOp('lambda_lt', term.args),
            'P46_lt_to_lambda',
        ))

    if term.name == 'lambda_lt' and len(term.args) == 2:
        results.append((
            OOp('operator_lt', term.args),
            'P46_lambda_to_lt',
        ))

    # ── 11. sorted_itemgetter(xs, k) ↔ sorted_lambda_key(xs, k) ──
    if term.name == 'sorted_itemgetter' and len(term.args) == 2:
        results.append((
            OOp('sorted_lambda_key', term.args),
            'P46_sorted_itemgetter_to_lambda',
        ))

    if term.name == 'sorted_lambda_key' and len(term.args) == 2:
        results.append((
            OOp('sorted_itemgetter', term.args),
            'P46_sorted_lambda_to_itemgetter',
        ))

    # ── 12. itemgetter(k) → OLam structural form ──
    if term.name == 'itemgetter' and len(term.args) == 1:
        k = term.args[0]
        results.append((
            OLam(('x',), OOp('getitem', (OVar('x'), k))),
            'P46_itemgetter_to_olam',
        ))

    # ── 13. attrgetter(attr) → OLam structural form ──
    if term.name == 'attrgetter' and len(term.args) == 1:
        attr = term.args[0]
        results.append((
            OLam(('x',), OOp('getattr', (OVar('x'), attr))),
            'P46_attrgetter_to_olam',
        ))

    # ── 14. methodcaller(m) → OLam structural form ──
    if term.name == 'methodcaller' and len(term.args) == 1:
        m = term.args[0]
        results.append((
            OLam(('x',), OOp('method_call', (OVar('x'), m))),
            'P46_methodcaller_to_olam',
        ))

    # ── 15. operator_add → OLam structural form ──
    if term.name == 'operator_add' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OOp('add', (a, b)),
            'P46_operator_add_to_add',
        ))

    # ── 16. operator_mul → OLam structural form ──
    if term.name == 'operator_mul' and len(term.args) == 2:
        a, b = term.args
        results.append((
            OOp('mul', (a, b)),
            'P46_operator_mul_to_mul',
        ))

    # ── 17. sorted_itemgetter → OMap structural form ──
    if term.name == 'sorted_itemgetter' and len(term.args) == 2:
        xs, k = term.args
        results.append((
            OOp('sorted', (xs, OLam(('x',), OOp('getitem', (OVar('x'), k))))),
            'P46_sorted_itemgetter_expand',
        ))

    # ── 18. operator_neg → OOp('neg', ...) structural ──
    if term.name == 'operator_neg' and len(term.args) == 1:
        results.append((
            OOp('neg', term.args),
            'P46_operator_neg_to_neg',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (lambda → operator module form)."""
    inverse_labels = {
        'P46_lambda_to_itemgetter', 'P46_lambda_to_attrgetter',
        'P46_lambda_to_methodcaller', 'P46_lambda_to_add',
        'P46_lambda_to_mul', 'P46_lambda_to_sub',
        'P46_lambda_to_neg', 'P46_lambda_to_not',
        'P46_lambda_to_eq', 'P46_lambda_to_lt',
        'P46_sorted_lambda_to_itemgetter',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is an operator-module op."""
    if isinstance(term, OOp) and term.name in _OPERATOR_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('itemgetter', 'lambda_getitem', 'attrgetter',
               'lambda_getattr', 'methodcaller', 'lambda_method_call',
               'operator_add', 'lambda_add', 'operator_mul', 'lambda_mul',
               'operator_sub', 'lambda_sub', 'operator_neg', 'lambda_neg',
               'operator_not', 'lambda_not', 'operator_eq', 'lambda_eq',
               'operator_lt', 'lambda_lt', 'sorted_itemgetter',
               'sorted_lambda_key'):
        if kw in sc and kw in tc:
            return 0.9
    if ('itemgetter' in sc and 'lambda_getitem' in tc) or \
       ('lambda_getitem' in sc and 'itemgetter' in tc):
        return 0.85
    if ('attrgetter' in sc and 'lambda_getattr' in tc) or \
       ('lambda_getattr' in sc and 'attrgetter' in tc):
        return 0.85
    if ('methodcaller' in sc and 'lambda_method' in tc) or \
       ('lambda_method' in sc and 'methodcaller' in tc):
        return 0.85
    if ('operator_add' in sc and 'lambda_add' in tc) or \
       ('lambda_add' in sc and 'operator_add' in tc):
        return 0.85
    if ('sorted_itemgetter' in sc and 'sorted_lambda' in tc) or \
       ('sorted_lambda' in sc and 'sorted_itemgetter' in tc):
        return 0.8
    if any(k in sc for k in ('itemgetter', 'attrgetter', 'methodcaller',
                             'operator_add', 'operator_mul', 'operator_sub',
                             'operator_neg', 'operator_not', 'operator_eq',
                             'operator_lt', 'sorted_itemgetter')):
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

    # 1. itemgetter → lambda_getitem
    t = OOp('itemgetter', (OLit(1),))
    r = apply(t)
    _assert(any(l == 'P46_itemgetter_to_lambda' for _, l in r),
            "itemgetter → lambda")

    # 2. lambda_getitem → itemgetter
    t2 = OOp('lambda_getitem', (OLit(1),))
    r2 = apply(t2)
    _assert(any(l == 'P46_lambda_to_itemgetter' for _, l in r2),
            "lambda → itemgetter")

    # 3. attrgetter → lambda_getattr
    t3 = OOp('attrgetter', (OLit('name'),))
    r3 = apply(t3)
    _assert(any(l == 'P46_attrgetter_to_lambda' for _, l in r3),
            "attrgetter → lambda")

    # 4. lambda_getattr → attrgetter
    t4 = OOp('lambda_getattr', (OLit('name'),))
    r4 = apply(t4)
    _assert(any(l == 'P46_lambda_to_attrgetter' for _, l in r4),
            "lambda → attrgetter")

    # 5. methodcaller → lambda_method_call
    t5 = OOp('methodcaller', (OLit('strip'),))
    r5 = apply(t5)
    _assert(any(l == 'P46_methodcaller_to_lambda' for _, l in r5),
            "methodcaller → lambda")

    # 6. lambda_method_call → methodcaller
    t6 = OOp('lambda_method_call', (OLit('strip'),))
    r6 = apply(t6)
    _assert(any(l == 'P46_lambda_to_methodcaller' for _, l in r6),
            "lambda → methodcaller")

    # 7. operator_add → lambda_add
    t7 = OOp('operator_add', (OVar('a'), OVar('b')))
    r7 = apply(t7)
    _assert(any(l == 'P46_add_to_lambda' for _, l in r7),
            "add → lambda")

    # 8. lambda_add → operator_add
    t8 = OOp('lambda_add', (OVar('a'), OVar('b')))
    r8 = apply(t8)
    _assert(any(l == 'P46_lambda_to_add' for _, l in r8),
            "lambda → add")

    # 9. operator_mul → lambda_mul
    t9 = OOp('operator_mul', (OVar('a'), OVar('b')))
    r9 = apply(t9)
    _assert(any(l == 'P46_mul_to_lambda' for _, l in r9),
            "mul → lambda")

    # 10. lambda_mul → operator_mul
    t10 = OOp('lambda_mul', (OVar('a'), OVar('b')))
    r10 = apply(t10)
    _assert(any(l == 'P46_lambda_to_mul' for _, l in r10),
            "lambda → mul")

    # 11. operator_sub → lambda_sub
    t11 = OOp('operator_sub', (OVar('a'), OVar('b')))
    r11 = apply(t11)
    _assert(any(l == 'P46_sub_to_lambda' for _, l in r11),
            "sub → lambda")

    # 12. lambda_sub → operator_sub
    t12 = OOp('lambda_sub', (OVar('a'), OVar('b')))
    r12 = apply(t12)
    _assert(any(l == 'P46_lambda_to_sub' for _, l in r12),
            "lambda → sub")

    # 13. operator_neg → lambda_neg
    t13 = OOp('operator_neg', (OVar('x'),))
    r13 = apply(t13)
    _assert(any(l == 'P46_neg_to_lambda' for _, l in r13),
            "neg → lambda")

    # 14. lambda_neg → operator_neg
    t14 = OOp('lambda_neg', (OVar('x'),))
    r14 = apply(t14)
    _assert(any(l == 'P46_lambda_to_neg' for _, l in r14),
            "lambda → neg")

    # 15. operator_not → lambda_not
    t15 = OOp('operator_not', (OVar('x'),))
    r15 = apply(t15)
    _assert(any(l == 'P46_not_to_lambda' for _, l in r15),
            "not → lambda")

    # 16. lambda_not → operator_not
    t16 = OOp('lambda_not', (OVar('x'),))
    r16 = apply(t16)
    _assert(any(l == 'P46_lambda_to_not' for _, l in r16),
            "lambda → not")

    # 17. operator_eq → lambda_eq
    t17 = OOp('operator_eq', (OVar('a'), OVar('b')))
    r17 = apply(t17)
    _assert(any(l == 'P46_eq_to_lambda' for _, l in r17),
            "eq → lambda")

    # 18. lambda_eq → operator_eq
    t18 = OOp('lambda_eq', (OVar('a'), OVar('b')))
    r18 = apply(t18)
    _assert(any(l == 'P46_lambda_to_eq' for _, l in r18),
            "lambda → eq")

    # 19. operator_lt → lambda_lt
    t19 = OOp('operator_lt', (OVar('a'), OVar('b')))
    r19 = apply(t19)
    _assert(any(l == 'P46_lt_to_lambda' for _, l in r19),
            "lt → lambda")

    # 20. lambda_lt → operator_lt
    t20 = OOp('lambda_lt', (OVar('a'), OVar('b')))
    r20 = apply(t20)
    _assert(any(l == 'P46_lambda_to_lt' for _, l in r20),
            "lambda → lt")

    # 21. sorted_itemgetter → sorted_lambda_key
    t21 = OOp('sorted_itemgetter', (OVar('xs'), OLit(1)))
    r21 = apply(t21)
    _assert(any(l == 'P46_sorted_itemgetter_to_lambda' for _, l in r21),
            "sorted_itemgetter → lambda")

    # 22. sorted_lambda_key → sorted_itemgetter
    t22 = OOp('sorted_lambda_key', (OVar('xs'), OLit(1)))
    r22 = apply(t22)
    _assert(any(l == 'P46_sorted_lambda_to_itemgetter' for _, l in r22),
            "sorted_lambda → itemgetter")

    # 23. itemgetter → OLam structural
    _assert(any(l == 'P46_itemgetter_to_olam' for _, l in r),
            "itemgetter → OLam")
    lam_results = [(t, l) for t, l in r if l == 'P46_itemgetter_to_olam']
    if lam_results:
        _assert(isinstance(lam_results[0][0], OLam),
                "itemgetter produces OLam")
    else:
        _assert(False, "itemgetter produces OLam")

    # 24. attrgetter → OLam structural
    _assert(any(l == 'P46_attrgetter_to_olam' for _, l in r3),
            "attrgetter → OLam")
    attr_lam = [(t, l) for t, l in r3 if l == 'P46_attrgetter_to_olam']
    if attr_lam:
        _assert(isinstance(attr_lam[0][0], OLam),
                "attrgetter produces OLam")
    else:
        _assert(False, "attrgetter produces OLam")

    # 25. methodcaller → OLam structural
    _assert(any(l == 'P46_methodcaller_to_olam' for _, l in r5),
            "methodcaller → OLam")
    mc_lam = [(t, l) for t, l in r5 if l == 'P46_methodcaller_to_olam']
    if mc_lam:
        _assert(isinstance(mc_lam[0][0], OLam),
                "methodcaller produces OLam")
    else:
        _assert(False, "methodcaller produces OLam")

    # 26. operator_add → add structural
    _assert(any(l == 'P46_operator_add_to_add' for _, l in r7),
            "operator_add → add")

    # 27. operator_mul → mul structural
    _assert(any(l == 'P46_operator_mul_to_mul' for _, l in r9),
            "operator_mul → mul")

    # 28. sorted_itemgetter expand structural
    _assert(any(l == 'P46_sorted_itemgetter_expand' for _, l in r21),
            "sorted_itemgetter expand")

    # 29. operator_neg → neg structural
    _assert(any(l == 'P46_operator_neg_to_neg' for _, l in r13),
            "operator_neg → neg")

    # 30. inverse: lambda_getitem → itemgetter
    r30_inv = apply_inverse(OOp('lambda_getitem', (OLit(0),)))
    _assert(any(l == 'P46_lambda_to_itemgetter' for _, l in r30_inv),
            "inv: lambda → itemgetter")

    # 31. inverse: lambda_getattr → attrgetter
    r31_inv = apply_inverse(OOp('lambda_getattr', (OLit('x'),)))
    _assert(any(l == 'P46_lambda_to_attrgetter' for _, l in r31_inv),
            "inv: lambda → attrgetter")

    # 32. inverse: lambda_add → operator_add
    r32_inv = apply_inverse(OOp('lambda_add', (OVar('a'), OVar('b'))))
    _assert(any(l == 'P46_lambda_to_add' for _, l in r32_inv),
            "inv: lambda → add")

    # 33. recognizes operator ops
    _assert(recognizes(OOp('itemgetter', (OLit(0),))),
            "recognizes itemgetter")
    _assert(recognizes(OOp('operator_add', (OVar('a'), OVar('b')))),
            "recognizes operator_add")
    _assert(recognizes(OOp('sorted_itemgetter', (OVar('xs'), OLit(1)))),
            "recognizes sorted_itemgetter")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 34. relevance: itemgetter ↔ lambda_getitem high
    _assert(relevance_score(
        OOp('itemgetter', (OLit(0),)),
        OOp('lambda_getitem', (OLit(0),)),
    ) > 0.7, "itemgetter/lambda relevance high")

    # 35. relevance: sorted_itemgetter ↔ sorted_lambda high
    _assert(relevance_score(
        OOp('sorted_itemgetter', (OVar('xs'), OLit(1))),
        OOp('sorted_lambda_key', (OVar('xs'), OLit(1))),
    ) > 0.7, "sorted_itemgetter/lambda relevance high")

    # 36. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    # 37. no rewrites for non-OOp
    _assert(apply(OVar('x')) == [], "no rewrites for OVar")
    _assert(apply(OLit(42)) == [], "no rewrites for OLit")

    print(f"P46 operator: {_pass} passed, {_fail} failed")
