"""P37 Axiom: Range / Enumerate Equivalences.

Establishes equivalences between different Python iteration-index
patterns: range(len(xs)) vs enumerate(xs), reversed range idioms,
enumerate with start offset, range-based arithmetic, and range
membership testing.

Mathematical basis: range(n) denotes the finite ordinal
  [n] = {0, 1, …, n−1}
and enumerate(xs) is the indexed coproduct (dependent sum)
  Σ_{i ∈ [|xs|]} {i} × {xs[i]}

The equivalence range(len(xs)) ↔ enumerate(xs) is the canonical
isomorphism between iterating over indices and iterating over
index-value pairs — the projection π₁ : Σ_i {i}×{xs[i]} → [|xs|]
is the forgetful functor, and the section i ↦ (i, xs[i]) is its
inverse.

range(n-1, -1, -1) and reversed(range(n)) both enumerate [n] in
reverse order.  They are related by the anti-isomorphism
  i ↦ n − 1 − i  on [n].

range(a, b) and slice(a, b) both denote the interval [a, b) ⊂ ℤ;
range produces an iterator while slice produces an index object.

Key rewrites:
  • range(len(xs)) with xs[i] ↔ enumerate(xs)
  • range(a, b) ↔ slice(a, b)
  • range(n-1, -1, -1) ↔ reversed(range(n))
  • enumerate(xs, start=1) ↔ zip(range(1, ...), xs)
  • range arithmetic: sum(range(n)) ↔ n*(n-1)//2
  • range membership O(1) vs list scan O(n)
  • enumerate index access ↔ manual index loop

(§P37, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P37_range_enumerate"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P23_iteration", "P14_slicing", "P06_itertools"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P37 Range / Enumerate Equivalences).

1. range_len(xs) ≡ enumerate_xs(xs)
   for i in range(len(xs)): ... xs[i] ... is equivalent to
   for i, x in enumerate(xs): ... x ...  Both iterate the
   indexed elements of xs.

2. range_ab(a, b) ≡ slice_ab(a, b)
   range(a, b) and slice(a, b) both denote [a, b) ⊂ ℤ.
   range yields an iterator; slice is an indexing object.

3. range_reversed(n) ≡ reversed_range(n)
   range(n-1, -1, -1) and reversed(range(n)) both iterate
   [n] in descending order: n-1, n-2, …, 0.

4. enumerate_start(xs, k) ≡ zip_range(k, xs)
   enumerate(xs, start=k) and zip(range(k, k+len(xs)), xs)
   both produce (k, xs[0]), (k+1, xs[1]), …

5. range_step(a, b, s) ≡ range_list(a, b, s)
   range(a, b, s) and list(range(a, b, s)) produce the same
   elements; the latter eagerly materialises them.

6. range_membership(x, r) ≡ list_membership(x, r)
   x in range(a, b) is O(1) arithmetic; x in list(range(a, b))
   is O(n) scan.  They have the same truth value.

7. enumerate_index(xs) ≡ index_loop(xs)
   for i, x in enumerate(xs) and the manual pattern
   i = 0; for x in xs: ...; i += 1 are equivalent.

8. range_sum(n) ≡ arithmetic_sum(n)
   sum(range(n)) = n*(n-1)//2 by Gauss's formula.

9. range_ab → OSeq literal when a, b are small known integers.

10. enumerate_start(xs, 0) simplifies to enumerate_xs(xs).
"""

EXAMPLES = [
    ("range_len($xs)", "enumerate_xs($xs)", "P37_range_len_to_enum"),
    ("range_ab($a, $b)", "slice_ab($a, $b)", "P37_range_to_slice"),
    ("range_reversed($n)", "reversed_range($n)", "P37_rev_range"),
    ("enumerate_start($xs, $k)", "zip_range($k, $xs)",
     "P37_enum_start_to_zip"),
    ("range_sum($n)", "arithmetic_sum($n)", "P37_range_sum"),
]

_RANGE_ENUMERATE_OPS = frozenset({
    'range_len', 'enumerate_xs', 'range_ab', 'slice_ab',
    'range_reversed', 'reversed_range', 'enumerate_start',
    'zip_range', 'range_step', 'range_list', 'range_membership',
    'list_membership', 'enumerate_index', 'index_loop',
    'range_sum', 'arithmetic_sum',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P37: Range/enumerate equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. range_len ↔ enumerate_xs ──
    if term.name == 'range_len' and len(term.args) >= 1:
        results.append((
            OOp('enumerate_xs', term.args),
            'P37_range_len_to_enum',
        ))

    if term.name == 'enumerate_xs' and len(term.args) >= 1:
        results.append((
            OOp('range_len', term.args),
            'P37_enum_to_range_len',
        ))

    # ── 2. range_ab ↔ slice_ab ──
    if term.name == 'range_ab' and len(term.args) == 2:
        results.append((
            OOp('slice_ab', term.args),
            'P37_range_to_slice',
        ))

    if term.name == 'slice_ab' and len(term.args) == 2:
        results.append((
            OOp('range_ab', term.args),
            'P37_slice_to_range',
        ))

    # ── 3. range_reversed ↔ reversed_range ──
    if term.name == 'range_reversed' and len(term.args) >= 1:
        results.append((
            OOp('reversed_range', term.args),
            'P37_range_rev_to_reversed',
        ))

    if term.name == 'reversed_range' and len(term.args) >= 1:
        results.append((
            OOp('range_reversed', term.args),
            'P37_reversed_to_range_rev',
        ))

    # ── 4. enumerate_start ↔ zip_range ──
    if term.name == 'enumerate_start' and len(term.args) == 2:
        xs, k = term.args
        results.append((
            OOp('zip_range', (k, xs)),
            'P37_enum_start_to_zip',
        ))

    if term.name == 'zip_range' and len(term.args) == 2:
        k, xs = term.args
        results.append((
            OOp('enumerate_start', (xs, k)),
            'P37_zip_to_enum_start',
        ))

    # ── 5. range_step ↔ range_list ──
    if term.name == 'range_step' and len(term.args) >= 2:
        results.append((
            OOp('range_list', term.args),
            'P37_range_step_to_list',
        ))

    if term.name == 'range_list' and len(term.args) >= 2:
        results.append((
            OOp('range_step', term.args),
            'P37_list_to_range_step',
        ))

    # ── 6. range_membership ↔ list_membership ──
    if term.name == 'range_membership' and len(term.args) == 2:
        results.append((
            OOp('list_membership', term.args),
            'P37_range_mem_to_list_mem',
        ))

    if term.name == 'list_membership' and len(term.args) == 2:
        results.append((
            OOp('range_membership', term.args),
            'P37_list_mem_to_range_mem',
        ))

    # ── 7. enumerate_index ↔ index_loop ──
    if term.name == 'enumerate_index' and len(term.args) >= 1:
        results.append((
            OOp('index_loop', term.args),
            'P37_enum_index_to_loop',
        ))

    if term.name == 'index_loop' and len(term.args) >= 1:
        results.append((
            OOp('enumerate_index', term.args),
            'P37_loop_to_enum_index',
        ))

    # ── 8. range_sum ↔ arithmetic_sum ──
    if term.name == 'range_sum' and len(term.args) == 1:
        n = term.args[0]
        results.append((
            OOp('arithmetic_sum', (n,)),
            'P37_range_sum_to_arith',
        ))
        # Also emit the closed-form expression
        results.append((
            OOp('int_div', (OOp('mul', (n, OOp('sub', (n, OLit(1))))),
                            OLit(2))),
            'P37_range_sum_closed_form',
        ))

    if term.name == 'arithmetic_sum' and len(term.args) == 1:
        results.append((
            OOp('range_sum', term.args),
            'P37_arith_to_range_sum',
        ))

    # ── 9. range_ab with literal bounds → OSeq ──
    if term.name == 'range_ab' and len(term.args) == 2:
        a_term, b_term = term.args
        if isinstance(a_term, OLit) and isinstance(b_term, OLit):
            a_val, b_val = a_term.value, b_term.value
            if isinstance(a_val, int) and isinstance(b_val, int) and \
                    0 <= b_val - a_val <= 10:
                elems = tuple(OLit(i) for i in range(a_val, b_val))
                results.append((
                    OSeq(elems),
                    'P37_range_literal_to_seq',
                ))

    # ── 10. enumerate_start(xs, 0) → enumerate_xs(xs) ──
    if term.name == 'enumerate_start' and len(term.args) == 2:
        xs, k = term.args
        if isinstance(k, OLit) and k.value == 0:
            results.append((
                OOp('enumerate_xs', (xs,)),
                'P37_enum_start0_simplify',
            ))

    # ── 11. range_len → enumerate_index (alternative) ──
    if term.name == 'range_len' and len(term.args) >= 1:
        results.append((
            OOp('enumerate_index', term.args),
            'P37_range_len_to_enum_index',
        ))

    # ── 12. reversed_range → range_step (explicit) ──
    if term.name == 'reversed_range' and len(term.args) == 1:
        n = term.args[0]
        results.append((
            OOp('range_step', (OOp('sub', (n, OLit(1))),
                               OLit(-1), OLit(-1))),
            'P37_reversed_to_explicit_step',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (idiomatic → manual index form)."""
    inverse_labels = {
        'P37_enum_to_range_len', 'P37_slice_to_range',
        'P37_reversed_to_range_rev', 'P37_zip_to_enum_start',
        'P37_list_to_range_step', 'P37_list_mem_to_range_mem',
        'P37_loop_to_enum_index', 'P37_arith_to_range_sum',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a range/enumerate op."""
    if isinstance(term, OOp) and term.name in _RANGE_ENUMERATE_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('range', 'enumerate', 'slice', 'reversed', 'index',
               'membership', 'arithmetic', 'sum'):
        if kw in sc and kw in tc:
            return 0.9
    if ('range' in sc and 'enumerate' in tc) or \
       ('enumerate' in sc and 'range' in tc):
        return 0.85
    if ('range' in sc and 'slice' in tc) or \
       ('slice' in sc and 'range' in tc):
        return 0.85
    if ('reversed' in sc and 'range' in tc) or \
       ('range' in sc and 'reversed' in tc):
        return 0.8
    if any(k in sc for k in ('range', 'enumerate', 'slice', 'index')):
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

    # 1. range_len → enumerate_xs
    t = OOp('range_len', (OVar('xs'),))
    r = apply(t)
    _assert(any(l == 'P37_range_len_to_enum' for _, l in r),
            "range_len → enumerate")

    # 2. enumerate_xs → range_len
    t2 = OOp('enumerate_xs', (OVar('xs'),))
    r2 = apply(t2)
    _assert(any(l == 'P37_enum_to_range_len' for _, l in r2),
            "enumerate → range_len")

    # 3. range_ab → slice_ab
    t3 = OOp('range_ab', (OLit(1), OLit(5)))
    r3 = apply(t3)
    _assert(any(l == 'P37_range_to_slice' for _, l in r3),
            "range → slice")

    # 4. slice_ab → range_ab
    t4 = OOp('slice_ab', (OLit(1), OLit(5)))
    r4 = apply(t4)
    _assert(any(l == 'P37_slice_to_range' for _, l in r4),
            "slice → range")

    # 5. range_reversed → reversed_range
    t5 = OOp('range_reversed', (OVar('n'),))
    r5 = apply(t5)
    _assert(any(l == 'P37_range_rev_to_reversed' for _, l in r5),
            "range_rev → reversed")

    # 6. reversed_range → range_reversed
    t6 = OOp('reversed_range', (OVar('n'),))
    r6 = apply(t6)
    _assert(any(l == 'P37_reversed_to_range_rev' for _, l in r6),
            "reversed → range_rev")

    # 7. enumerate_start → zip_range
    t7 = OOp('enumerate_start', (OVar('xs'), OLit(1)))
    r7 = apply(t7)
    _assert(any(l == 'P37_enum_start_to_zip' for _, l in r7),
            "enum_start → zip")

    # 8. zip_range → enumerate_start
    t8 = OOp('zip_range', (OLit(1), OVar('xs')))
    r8 = apply(t8)
    _assert(any(l == 'P37_zip_to_enum_start' for _, l in r8),
            "zip → enum_start")

    # 9. range_step → range_list
    t9 = OOp('range_step', (OLit(0), OLit(10), OLit(2)))
    r9 = apply(t9)
    _assert(any(l == 'P37_range_step_to_list' for _, l in r9),
            "range_step → list")

    # 10. range_membership → list_membership
    t10 = OOp('range_membership', (OVar('x'), OVar('r')))
    r10 = apply(t10)
    _assert(any(l == 'P37_range_mem_to_list_mem' for _, l in r10),
            "range_mem → list_mem")

    # 11. list_membership → range_membership
    t11 = OOp('list_membership', (OVar('x'), OVar('r')))
    r11 = apply(t11)
    _assert(any(l == 'P37_list_mem_to_range_mem' for _, l in r11),
            "list_mem → range_mem")

    # 12. enumerate_index → index_loop
    t12 = OOp('enumerate_index', (OVar('xs'),))
    r12 = apply(t12)
    _assert(any(l == 'P37_enum_index_to_loop' for _, l in r12),
            "enum_index → loop")

    # 13. index_loop → enumerate_index
    t13 = OOp('index_loop', (OVar('xs'),))
    r13 = apply(t13)
    _assert(any(l == 'P37_loop_to_enum_index' for _, l in r13),
            "loop → enum_index")

    # 14. range_sum → arithmetic_sum
    t14 = OOp('range_sum', (OVar('n'),))
    r14 = apply(t14)
    _assert(any(l == 'P37_range_sum_to_arith' for _, l in r14),
            "range_sum → arith")

    # 15. range_sum → closed form
    _assert(any(l == 'P37_range_sum_closed_form' for _, l in r14),
            "range_sum → closed form")

    # 16. arithmetic_sum → range_sum
    t16 = OOp('arithmetic_sum', (OVar('n'),))
    r16 = apply(t16)
    _assert(any(l == 'P37_arith_to_range_sum' for _, l in r16),
            "arith → range_sum")

    # 17. range_ab(0, 5) → OSeq literal
    t17 = OOp('range_ab', (OLit(0), OLit(5)))
    r17 = apply(t17)
    _assert(any(l == 'P37_range_literal_to_seq' for _, l in r17),
            "range(0,5) → seq")
    # check it produces 5 elements
    seq_results = [(t, l) for t, l in r17 if l == 'P37_range_literal_to_seq']
    if seq_results:
        seq_term = seq_results[0][0]
        _assert(isinstance(seq_term, OSeq) and len(seq_term.elements) == 5,
                "range(0,5) produces 5-element seq")
    else:
        _assert(False, "range(0,5) produces 5-element seq")

    # 18. enumerate_start(xs, 0) → enumerate_xs simplification
    t18 = OOp('enumerate_start', (OVar('xs'), OLit(0)))
    r18 = apply(t18)
    _assert(any(l == 'P37_enum_start0_simplify' for _, l in r18),
            "enum_start(xs, 0) → enum_xs")

    # 19. range_len → enumerate_index (alternative)
    _assert(any(l == 'P37_range_len_to_enum_index' for _, l in r),
            "range_len → enum_index")

    # 20. reversed_range → explicit step
    _assert(any(l == 'P37_reversed_to_explicit_step' for _, l in r6),
            "reversed → explicit step")

    # 21. inverse: enumerate_xs → range_len
    r21_inv = apply_inverse(OOp('enumerate_xs', (OVar('xs'),)))
    _assert(any(l == 'P37_enum_to_range_len' for _, l in r21_inv),
            "inv: enum → range_len")

    # 22. inverse: index_loop → enumerate_index
    r22_inv = apply_inverse(OOp('index_loop', (OVar('xs'),)))
    _assert(any(l == 'P37_loop_to_enum_index' for _, l in r22_inv),
            "inv: loop → enum_index")

    # 23. recognizes range/enumerate ops
    _assert(recognizes(OOp('range_len', (OVar('xs'),))),
            "recognizes range_len")
    _assert(recognizes(OOp('enumerate_xs', (OVar('xs'),))),
            "recognizes enumerate_xs")
    _assert(recognizes(OOp('range_sum', (OVar('n'),))),
            "recognizes range_sum")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 24. relevance: range ↔ enumerate high
    _assert(relevance_score(
        OOp('range_len', (OVar('xs'),)),
        OOp('enumerate_xs', (OVar('xs'),)),
    ) > 0.7, "range/enumerate relevance high")

    # 25. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    print(f"P37 range_enumerate: {_pass} passed, {_fail} failed")
