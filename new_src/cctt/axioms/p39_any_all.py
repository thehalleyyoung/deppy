"""P39 Axiom: Any/All Pattern Equivalences.

Establishes equivalences between different Python any/all patterns:
any(p(x) for x in xs) vs loop with early return, all(…) vs
not any(not …), short-circuit semantics, empty-collection base
cases, De Morgan duality, any via next(filter(…)), and all via
set-subset checking.

Mathematical basis: any and all are the existential and universal
quantifiers over finite sequences:

  any : (A → Bool) × List(A) → Bool
  any(p, xs) = ∃ x ∈ xs. p(x) = ⋁_{x ∈ xs} p(x)

  all : (A → Bool) × List(A) → Bool
  all(p, xs) = ∀ x ∈ xs. p(x) = ⋀_{x ∈ xs} p(x)

The De Morgan duality gives:
  ¬(∀ x. p(x)) ≡ ∃ x. ¬p(x)      not all(p, xs) ≡ any(not p, xs)
  ¬(∃ x. p(x)) ≡ ∀ x. ¬p(x)      not any(p, xs) ≡ all(not p, xs)

The empty-collection base cases follow from the identity elements
of ⋁ and ⋀:  any([]) = False (⊥), all([]) = True (⊤).

Short-circuit evaluation: any returns True at first True element,
all returns False at first False element — equivalent to a loop
with early return.

Key rewrites:
  • any(p(x) for x in xs) ↔ loop with early return True
  • all(p(x) for x in xs) ↔ not any(not p(x) for x in xs)
  • not all(…) ↔ any(not …)   (De Morgan)
  • not any(…) ↔ all(not …)   (De Morgan)
  • any([]) = False, all([]) = True
  • any(…) ↔ next(filter(p, xs), False) ≠ False
  • all(p(x) for x in xs) ↔ {x for x in xs} <= valid_set
  • any(map(p, xs)) ↔ any(p(x) for x in xs)
  • all(map(p, xs)) ↔ all(p(x) for x in xs)
  • any(x == val for x in xs) ↔ val in xs
  • all/any with or/and chain equivalences

(§P39, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P39_any_all"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P13_bool_idioms", "P23_iteration", "P35_map_filter_reduce"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P39 Any/All Pattern Equivalences).

1. any_genexpr(p, xs) ≡ loop_early_return(p, xs)
   any(p(x) for x in xs) and the manual loop
   for x in xs: if p(x): return True; return False
   both compute ∃ x ∈ xs. p(x) with short-circuit.

2. all_genexpr(p, xs) ≡ not_any_not(p, xs)
   all(p(x) for x in xs) ≡ not any(not p(x) for x in xs)
   by De Morgan duality over finite sequences.

3. any_to_all(p, xs) ≡ not all(not p(x) for x in xs)
   any(p(x) for x in xs) ≡ not all(not p(x) for x in xs)
   — the converse De Morgan identity.

4. any_empty([]) = False
   any over the empty sequence is ⊥ (identity of ⋁).

5. all_empty([]) = True
   all over the empty sequence is ⊤ (identity of ⋀).

6. demorgan_any(p, xs) ≡ not all(p, xs)
   any(not p(x) for x in xs) ≡ not all(p(x) for x in xs).

7. demorgan_all(p, xs) ≡ not any(p, xs)
   all(not p(x) for x in xs) ≡ not any(p(x) for x in xs).

8. any_filter_next(p, xs) ≡ next_filter(p, xs)
   any(p(x) for x in xs) ≡ next(filter(p, xs), None) is not None
   when p(x) never returns None itself.

9. any_map(p, xs) ≡ any_genexpr(p, xs)
   any(map(p, xs)) and any(p(x) for x in xs) are equivalent;
   map produces the same predicate results.

10. all_map(p, xs) ≡ all_genexpr(p, xs)
    all(map(p, xs)) and all(p(x) for x in xs) are equivalent.

11. all_subset(p, xs) ≡ set_issubset(xs, valid)
    all(x in valid for x in xs) ≡ set(xs) <= valid
    when valid is a set — subset test checks universal membership.

12. any_or_chain(a, b, c) ≡ any([a, b, c])
    a or b or c ≡ any([a, b, c]) for boolean-valued terms.

13. all_and_chain(a, b, c) ≡ all([a, b, c])
    a and b and c ≡ all([a, b, c]) for boolean-valued terms.
"""

EXAMPLES = [
    ("any_genexpr($p, $xs)", "loop_early_return($p, $xs)",
     "P39_any_to_loop"),
    ("all_genexpr($p, $xs)", "not_any_not($p, $xs)",
     "P39_all_to_not_any_not"),
    ("demorgan_any($p, $xs)", "not all_genexpr($p, $xs)",
     "P39_demorgan_any"),
    ("any_empty()", "False", "P39_any_empty"),
    ("all_empty()", "True", "P39_all_empty"),
]

_ANY_ALL_OPS = frozenset({
    'any_genexpr', 'loop_early_return', 'all_genexpr', 'not_any_not',
    'any_to_all', 'all_to_any', 'any_empty', 'all_empty',
    'demorgan_any', 'demorgan_all', 'any_filter_next', 'next_filter',
    'all_subset', 'set_issubset', 'any_map', 'all_map',
    'any_or_chain', 'all_and_chain',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P39: Any/all pattern equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. any_genexpr ↔ loop_early_return ──
    if term.name == 'any_genexpr' and len(term.args) == 2:
        results.append((
            OOp('loop_early_return', term.args),
            'P39_any_to_loop',
        ))

    if term.name == 'loop_early_return' and len(term.args) == 2:
        results.append((
            OOp('any_genexpr', term.args),
            'P39_loop_to_any',
        ))

    # ── 2. all_genexpr ↔ not_any_not ──
    if term.name == 'all_genexpr' and len(term.args) == 2:
        results.append((
            OOp('not_any_not', term.args),
            'P39_all_to_not_any_not',
        ))

    if term.name == 'not_any_not' and len(term.args) == 2:
        results.append((
            OOp('all_genexpr', term.args),
            'P39_not_any_not_to_all',
        ))

    # ── 3. any_to_all ↔ all_to_any ──
    if term.name == 'any_to_all' and len(term.args) == 2:
        results.append((
            OOp('all_to_any', term.args),
            'P39_any_as_not_all_not',
        ))

    if term.name == 'all_to_any' and len(term.args) == 2:
        results.append((
            OOp('any_to_all', term.args),
            'P39_all_as_not_any_not',
        ))

    # ── 4. any_empty → False ──
    if term.name == 'any_empty' and len(term.args) == 0:
        results.append((
            OLit(False),
            'P39_any_empty_false',
        ))

    if term.name == 'any_genexpr' and len(term.args) == 2:
        _, xs = term.args
        if isinstance(xs, OSeq) and len(xs.elements) == 0:
            results.append((
                OLit(False),
                'P39_any_empty_seq_false',
            ))

    # ── 5. all_empty → True ──
    if term.name == 'all_empty' and len(term.args) == 0:
        results.append((
            OLit(True),
            'P39_all_empty_true',
        ))

    if term.name == 'all_genexpr' and len(term.args) == 2:
        _, xs = term.args
        if isinstance(xs, OSeq) and len(xs.elements) == 0:
            results.append((
                OLit(True),
                'P39_all_empty_seq_true',
            ))

    # ── 6. demorgan_any ↔ not all ──
    if term.name == 'demorgan_any' and len(term.args) == 2:
        results.append((
            OOp('not', (OOp('all_genexpr', term.args),)),
            'P39_demorgan_any_to_not_all',
        ))

    if term.name == 'not' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'all_genexpr' \
                and len(inner.args) == 2:
            results.append((
                OOp('demorgan_any', inner.args),
                'P39_not_all_to_demorgan_any',
            ))

    # ── 7. demorgan_all ↔ not any ──
    if term.name == 'demorgan_all' and len(term.args) == 2:
        results.append((
            OOp('not', (OOp('any_genexpr', term.args),)),
            'P39_demorgan_all_to_not_any',
        ))

    if term.name == 'not' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'any_genexpr' \
                and len(inner.args) == 2:
            results.append((
                OOp('demorgan_all', inner.args),
                'P39_not_any_to_demorgan_all',
            ))

    # ── 8. any_filter_next ↔ next_filter ──
    if term.name == 'any_filter_next' and len(term.args) == 2:
        results.append((
            OOp('next_filter', term.args),
            'P39_any_to_next_filter',
        ))

    if term.name == 'next_filter' and len(term.args) == 2:
        results.append((
            OOp('any_filter_next', term.args),
            'P39_next_filter_to_any',
        ))

    # ── 9. any_map ↔ any_genexpr ──
    if term.name == 'any_map' and len(term.args) == 2:
        results.append((
            OOp('any_genexpr', term.args),
            'P39_any_map_to_genexpr',
        ))

    if term.name == 'any_genexpr' and len(term.args) == 2:
        results.append((
            OOp('any_map', term.args),
            'P39_any_genexpr_to_map',
        ))

    # ── 10. all_map ↔ all_genexpr ──
    if term.name == 'all_map' and len(term.args) == 2:
        results.append((
            OOp('all_genexpr', term.args),
            'P39_all_map_to_genexpr',
        ))

    if term.name == 'all_genexpr' and len(term.args) == 2:
        results.append((
            OOp('all_map', term.args),
            'P39_all_genexpr_to_map',
        ))

    # ── 11. all_subset ↔ set_issubset ──
    if term.name == 'all_subset' and len(term.args) == 2:
        results.append((
            OOp('set_issubset', term.args),
            'P39_all_subset_to_issubset',
        ))

    if term.name == 'set_issubset' and len(term.args) == 2:
        results.append((
            OOp('all_subset', term.args),
            'P39_issubset_to_all_subset',
        ))

    # ── 12. any_or_chain ↔ any([…]) ──
    if term.name == 'any_or_chain' and len(term.args) >= 2:
        results.append((
            OOp('any_genexpr', (
                OLam(('_x',), OVar('_x')),
                OSeq(term.args),
            )),
            'P39_or_chain_to_any',
        ))

    # ── 13. all_and_chain ↔ all([…]) ──
    if term.name == 'all_and_chain' and len(term.args) >= 2:
        results.append((
            OOp('all_genexpr', (
                OLam(('_x',), OVar('_x')),
                OSeq(term.args),
            )),
            'P39_and_chain_to_all',
        ))

    # ── 14. any_genexpr → OFold form ──
    if term.name == 'any_genexpr' and len(term.args) == 2:
        p, xs = term.args
        results.append((
            OFold('or', OLit(False), OMap(p, xs)),
            'P39_any_to_fold_or',
        ))

    # ── 15. all_genexpr → OFold form ──
    if term.name == 'all_genexpr' and len(term.args) == 2:
        p, xs = term.args
        results.append((
            OFold('and', OLit(True), OMap(p, xs)),
            'P39_all_to_fold_and',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (loop/manual form → any/all form)."""
    inverse_labels = {
        'P39_loop_to_any', 'P39_not_any_not_to_all',
        'P39_all_as_not_any_not', 'P39_next_filter_to_any',
        'P39_any_map_to_genexpr', 'P39_all_map_to_genexpr',
        'P39_issubset_to_all_subset', 'P39_not_all_to_demorgan_any',
        'P39_not_any_to_demorgan_all',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is an any/all op."""
    if isinstance(term, OOp) and term.name in _ANY_ALL_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('any', 'all', 'demorgan', 'early_return', 'subset',
               'filter_next', 'or_chain', 'and_chain'):
        if kw in sc and kw in tc:
            return 0.9
    if ('any' in sc and 'all' in tc) or \
       ('all' in sc and 'any' in tc):
        return 0.85
    if ('any' in sc and 'loop' in tc) or \
       ('loop' in sc and 'any' in tc):
        return 0.85
    if ('all' in sc and 'subset' in tc) or \
       ('subset' in sc and 'all' in tc):
        return 0.8
    if any(k in sc for k in ('any', 'all', 'demorgan', 'early_return')):
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

    # 1. any_genexpr → loop_early_return
    t = OOp('any_genexpr', (OVar('p'), OVar('xs')))
    r = apply(t)
    _assert(any(l == 'P39_any_to_loop' for _, l in r),
            "any → loop")

    # 2. loop_early_return → any_genexpr
    t2 = OOp('loop_early_return', (OVar('p'), OVar('xs')))
    r2 = apply(t2)
    _assert(any(l == 'P39_loop_to_any' for _, l in r2),
            "loop → any")

    # 3. all_genexpr → not_any_not
    t3 = OOp('all_genexpr', (OVar('p'), OVar('xs')))
    r3 = apply(t3)
    _assert(any(l == 'P39_all_to_not_any_not' for _, l in r3),
            "all → not_any_not")

    # 4. not_any_not → all_genexpr
    t4 = OOp('not_any_not', (OVar('p'), OVar('xs')))
    r4 = apply(t4)
    _assert(any(l == 'P39_not_any_not_to_all' for _, l in r4),
            "not_any_not → all")

    # 5. any_empty → False
    t5 = OOp('any_empty', ())
    r5 = apply(t5)
    _assert(any(l == 'P39_any_empty_false' for _, l in r5),
            "any_empty → False")

    # 6. all_empty → True
    t6 = OOp('all_empty', ())
    r6 = apply(t6)
    _assert(any(l == 'P39_all_empty_true' for _, l in r6),
            "all_empty → True")

    # 7. demorgan_any → not all
    t7 = OOp('demorgan_any', (OVar('p'), OVar('xs')))
    r7 = apply(t7)
    _assert(any(l == 'P39_demorgan_any_to_not_all' for _, l in r7),
            "demorgan_any → not all")

    # 8. not(all_genexpr) → demorgan_any
    t8 = OOp('not', (OOp('all_genexpr', (OVar('p'), OVar('xs'))),))
    r8 = apply(t8)
    _assert(any(l == 'P39_not_all_to_demorgan_any' for _, l in r8),
            "not all → demorgan_any")

    # 9. demorgan_all → not any
    t9 = OOp('demorgan_all', (OVar('p'), OVar('xs')))
    r9 = apply(t9)
    _assert(any(l == 'P39_demorgan_all_to_not_any' for _, l in r9),
            "demorgan_all → not any")

    # 10. not(any_genexpr) → demorgan_all
    t10 = OOp('not', (OOp('any_genexpr', (OVar('p'), OVar('xs'))),))
    r10 = apply(t10)
    _assert(any(l == 'P39_not_any_to_demorgan_all' for _, l in r10),
            "not any → demorgan_all")

    # 11. any_filter_next → next_filter
    t11 = OOp('any_filter_next', (OVar('p'), OVar('xs')))
    r11 = apply(t11)
    _assert(any(l == 'P39_any_to_next_filter' for _, l in r11),
            "any → next_filter")

    # 12. next_filter → any_filter_next
    t12 = OOp('next_filter', (OVar('p'), OVar('xs')))
    r12 = apply(t12)
    _assert(any(l == 'P39_next_filter_to_any' for _, l in r12),
            "next_filter → any")

    # 13. all_subset → set_issubset
    t13 = OOp('all_subset', (OVar('xs'), OVar('valid')))
    r13 = apply(t13)
    _assert(any(l == 'P39_all_subset_to_issubset' for _, l in r13),
            "all_subset → issubset")

    # 14. set_issubset → all_subset
    t14 = OOp('set_issubset', (OVar('xs'), OVar('valid')))
    r14 = apply(t14)
    _assert(any(l == 'P39_issubset_to_all_subset' for _, l in r14),
            "issubset → all_subset")

    # 15. any_map → any_genexpr
    t15 = OOp('any_map', (OVar('p'), OVar('xs')))
    r15 = apply(t15)
    _assert(any(l == 'P39_any_map_to_genexpr' for _, l in r15),
            "any_map → genexpr")

    # 16. all_map → all_genexpr
    t16 = OOp('all_map', (OVar('p'), OVar('xs')))
    r16 = apply(t16)
    _assert(any(l == 'P39_all_map_to_genexpr' for _, l in r16),
            "all_map → genexpr")

    # 17. any_genexpr → any_map (reverse)
    _assert(any(l == 'P39_any_genexpr_to_map' for _, l in r),
            "any_genexpr → map")

    # 18. any_genexpr → OFold form
    _assert(any(l == 'P39_any_to_fold_or' for _, l in r),
            "any → fold(or)")

    # 19. all_genexpr → OFold form
    _assert(any(l == 'P39_all_to_fold_and' for _, l in r3),
            "all → fold(and)")

    # 20. any_or_chain → any([…])
    t20 = OOp('any_or_chain', (OVar('a'), OVar('b'), OVar('c')))
    r20 = apply(t20)
    _assert(any(l == 'P39_or_chain_to_any' for _, l in r20),
            "or_chain → any")

    # 21. all_and_chain → all([…])
    t21 = OOp('all_and_chain', (OVar('a'), OVar('b'), OVar('c')))
    r21 = apply(t21)
    _assert(any(l == 'P39_and_chain_to_all' for _, l in r21),
            "and_chain → all")

    # 22. any_genexpr on empty seq → False
    t22 = OOp('any_genexpr', (OVar('p'), OSeq(())))
    r22 = apply(t22)
    _assert(any(l == 'P39_any_empty_seq_false' for _, l in r22),
            "any(empty) → False")

    # 23. all_genexpr on empty seq → True
    t23 = OOp('all_genexpr', (OVar('p'), OSeq(())))
    r23 = apply(t23)
    _assert(any(l == 'P39_all_empty_seq_true' for _, l in r23),
            "all(empty) → True")

    # 24. any_to_all ↔ all_to_any
    t24 = OOp('any_to_all', (OVar('p'), OVar('xs')))
    r24 = apply(t24)
    _assert(any(l == 'P39_any_as_not_all_not' for _, l in r24),
            "any_to_all → all_to_any")

    # 25. inverse: loop → any
    r25_inv = apply_inverse(OOp('loop_early_return', (OVar('p'), OVar('xs'))))
    _assert(any(l == 'P39_loop_to_any' for _, l in r25_inv),
            "inv: loop → any")

    # 26. inverse: not_any_not → all
    r26_inv = apply_inverse(OOp('not_any_not', (OVar('p'), OVar('xs'))))
    _assert(any(l == 'P39_not_any_not_to_all' for _, l in r26_inv),
            "inv: not_any_not → all")

    # 27. recognizes any/all ops
    _assert(recognizes(OOp('any_genexpr', (OVar('p'), OVar('xs')))),
            "recognizes any_genexpr")
    _assert(recognizes(OOp('all_genexpr', (OVar('p'), OVar('xs')))),
            "recognizes all_genexpr")
    _assert(recognizes(OOp('demorgan_any', (OVar('p'), OVar('xs')))),
            "recognizes demorgan_any")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 28. relevance: any ↔ loop high
    _assert(relevance_score(
        OOp('any_genexpr', (OVar('p'), OVar('xs'))),
        OOp('loop_early_return', (OVar('p'), OVar('xs'))),
    ) > 0.7, "any/loop relevance high")

    # 29. relevance: any ↔ all high
    _assert(relevance_score(
        OOp('any_genexpr', (OVar('p'), OVar('xs'))),
        OOp('all_genexpr', (OVar('p'), OVar('xs'))),
    ) > 0.7, "any/all relevance high")

    # 30. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    print(f"P39 any_all: {_pass} passed, {_fail} failed")
