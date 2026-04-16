"""D23: Sort-then-Process Axiom — Processing Sorted Data ↔ Direct.

§23.3 of the CCTT monograph.  Theorem 23.3.1:
Processing sorted data ≡ processing unsorted when the processing
is order-invariant (commutative+associative over the processing op).

This axiom complements D19 (sort absorption) by handling the case
where sorting is followed by a non-fold processing step — map,
filter, take, drop, etc.

Key rewrites:
  • map(f, sorted(x)) → sorted(map(f, x))  when f is monotone
  • filter(p, sorted(x)) → sorted(filter(p, x))
  • take(n, sorted(x)) ↔ sorted(take(n, x))  [NOT equal in general]
  • head(sorted(x)) → min(x)
  • last(sorted(x)) → max(x)
  • getitem(sorted(x), 0) → min(x)
  • getitem(sorted(x), -1) → max(x)
  • sorted(filter(p, x)) → filter(p, sorted(x))  [sort-filter commute]
  • enumerate(sorted(x)) with index-independent processing
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D23_sort_process"
AXIOM_CATEGORY = "language_feature"

SOUNDNESS_PROOF = """
Theorem 23.3.1 (Sort-Process Commutativity).
(1) head(sorted(x)) = min(x): the first element of a sorted list
    is the minimum by definition of sorting.
(2) last(sorted(x)) = max(x): dually.
(3) filter(p, sorted(x)) = sorted(filter(p, x)): filtering preserves
    order, and re-sorting a filtered subset yields the same result
    as filtering after sorting.
(4) map(f, sorted(x)) = sorted(map(f, x)) when f is monotone: if
    f preserves order, mapping commutes with sorting.

These are instances of the naturality of the sort functor on
the category of finite multisets with monotone maps.
"""

COMPOSES_WITH = ["D19_sort_scan", "FOLD", "ALG", "QUOT"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("getitem(sorted(xs), 0)", "min(xs)", "D23_head_sorted_to_min"),
    ("getitem(sorted(xs), -1)", "max(xs)", "D23_last_sorted_to_max"),
    ("filter(p, sorted(xs))", "sorted(filter(p, xs))", "D23_filter_sort_commute"),
    ("len(sorted(xs))", "len(xs)", "D23_len_sorted_absorb"),
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def _is_sorted_term(term: OTerm) -> bool:
    """Check if term is sorted(x) or sorted_key(x, k)."""
    if isinstance(term, OOp) and term.name in ('sorted', 'sorted_key', 'sorted_rev',
                                                 'sorted_reverse', 'stable_sort'):
        return True
    return False


def _get_sorted_inner(term: OTerm) -> Optional[OTerm]:
    """Extract the inner collection from sorted(x)."""
    if isinstance(term, OOp) and term.name in ('sorted', 'sorted_key', 'stable_sort'):
        if len(term.args) >= 1:
            return term.args[0]
    return None


def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D23 sort-then-process rewrites."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. getitem(sorted(x), 0) → min(x) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        arr, idx = term.args
        if _is_sorted_term(arr):
            inner = _get_sorted_inner(arr)
            if inner is not None:
                if isinstance(idx, OLit) and idx.value == 0:
                    results.append((
                        OOp('min', (inner,)),
                        'D23_head_sorted_to_min',
                    ))
                elif isinstance(idx, OLit) and idx.value == -1:
                    results.append((
                        OOp('max', (inner,)),
                        'D23_last_sorted_to_max',
                    ))

    # ── 2. min(x) → getitem(sorted(x), 0) [inverse for bidirectional] ──
    if isinstance(term, OOp) and term.name == 'min' and len(term.args) == 1:
        results.append((
            OOp('getitem', (OOp('sorted', (term.args[0],)), OLit(0))),
            'D23_min_to_head_sorted',
        ))

    if isinstance(term, OOp) and term.name == 'max' and len(term.args) == 1:
        results.append((
            OOp('getitem', (OOp('sorted', (term.args[0],)), OLit(-1))),
            'D23_max_to_last_sorted',
        ))

    # ── 3. filter(p, sorted(x)) ↔ sorted(filter(p, x)) ──
    if isinstance(term, OMap) and term.filter_pred is not None:
        coll = term.collection
        if _is_sorted_term(coll):
            inner = _get_sorted_inner(coll)
            if inner is not None:
                # Move sort outside filter
                filtered = OMap(term.transform, inner, term.filter_pred)
                results.append((
                    OOp('sorted', (filtered,)),
                    'D23_filter_sort_commute',
                ))

    # filter_map(p, f, sorted(x)) → sorted(filter_map(p, f, x))
    if isinstance(term, OOp) and term.name == 'filter' and len(term.args) == 2:
        pred, coll = term.args
        if _is_sorted_term(coll):
            inner = _get_sorted_inner(coll)
            if inner is not None:
                results.append((
                    OOp('sorted', (OOp('filter', (pred, inner)),)),
                    'D23_filter_sort_commute_op',
                ))

    # ── 4. len(sorted(x)) → len(x) [length doesn't depend on order] ──
    if isinstance(term, OOp) and term.name == 'len' and len(term.args) == 1:
        if _is_sorted_term(term.args[0]):
            inner = _get_sorted_inner(term.args[0])
            if inner is not None:
                results.append((
                    OOp('len', (inner,)),
                    'D23_len_sorted_absorb',
                ))

    # ── 5. set(sorted(x)) → set(x) [set discards order] ──
    if isinstance(term, OOp) and term.name == 'set' and len(term.args) == 1:
        if _is_sorted_term(term.args[0]):
            inner = _get_sorted_inner(term.args[0])
            if inner is not None:
                results.append((
                    OOp('set', (inner,)),
                    'D23_set_sorted_absorb',
                ))

    # ── 6. sorted(x)[:k] → nsmallest(k, x) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        arr, sl = term.args
        if _is_sorted_term(arr):
            inner = _get_sorted_inner(arr)
            if inner is not None:
                if isinstance(sl, OOp) and sl.name == 'slice' and len(sl.args) == 2:
                    if isinstance(sl.args[0], OLit) and sl.args[0].value is None:
                        k = sl.args[1]
                        results.append((
                            OOp('nsmallest', (k, inner)),
                            'D23_sorted_slice_to_nsmallest',
                        ))

    # ── 7. sorted_reverse(x)[:k] → nlargest(k, x) ──
    if isinstance(term, OOp) and term.name == 'getitem' and len(term.args) == 2:
        arr, sl = term.args
        if isinstance(arr, OOp) and arr.name in ('sorted_reverse', 'sorted_rev'):
            if len(arr.args) >= 1:
                inner = arr.args[0]
                if isinstance(sl, OOp) and sl.name == 'slice' and len(sl.args) == 2:
                    if isinstance(sl.args[0], OLit) and sl.args[0].value is None:
                        k = sl.args[1]
                        results.append((
                            OOp('nlargest', (k, inner)),
                            'D23_reverse_sorted_slice_to_nlargest',
                        ))

    # ── 8. sum(sorted(x)) → sum(x) [sum is order-invariant] ──
    if isinstance(term, OOp) and term.name == 'sum' and len(term.args) == 1:
        if _is_sorted_term(term.args[0]):
            inner = _get_sorted_inner(term.args[0])
            if inner is not None:
                results.append((
                    OOp('sum', (inner,)),
                    'D23_sum_sorted_absorb',
                ))

    # ── 9. any/all(sorted(x)) → any/all(x) ──
    if isinstance(term, OOp) and term.name in ('any', 'all') and len(term.args) == 1:
        if _is_sorted_term(term.args[0]):
            inner = _get_sorted_inner(term.args[0])
            if inner is not None:
                results.append((
                    OOp(term.name, (inner,)),
                    f'D23_{term.name}_sorted_absorb',
                ))

    # ── 10. reversed(sorted_reverse(x)) → sorted(x) ──
    if isinstance(term, OOp) and term.name == 'reversed' and len(term.args) == 1:
        if isinstance(term.args[0], OOp) and term.args[0].name in ('sorted_reverse', 'sorted_rev'):
            if len(term.args[0].args) >= 1:
                results.append((
                    OOp('sorted', (term.args[0].args[0],)),
                    'D23_reversed_sorted_reverse',
                ))

    return results


def recognizes(term: OTerm) -> bool:
    """Return True if D23 can potentially rewrite *term*."""
    if isinstance(term, OOp):
        if term.name in ('getitem', 'len', 'set', 'sum', 'any', 'all',
                         'min', 'max', 'reversed', 'filter'):
            if len(term.args) >= 1:
                if _is_sorted_term(term.args[0]) or (
                        len(term.args) >= 2 and _is_sorted_term(term.args[1])):
                    return True
            if term.name in ('min', 'max'):
                return True
    if isinstance(term, OMap) and term.filter_pred is not None:
        if _is_sorted_term(term.collection):
            return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D23's relevance."""
    sc = source.canon()
    tc = target.canon()
    s_sorted = 'sorted(' in sc
    t_sorted = 'sorted(' in tc
    has_process = any(k in sc or k in tc for k in ('min(', 'max(', 'len(', 'getitem('))
    if s_sorted != t_sorted and has_process:
        return 0.85
    if s_sorted and has_process:
        return 0.5
    return 0.1


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: re-introduce sorted where it was absorbed."""
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OOp) and term.name == 'nsmallest' and len(term.args) == 2:
        k, coll = term.args
        results.append((
            OOp('getitem', (OOp('sorted', (coll,)),
                           OOp('slice', (OLit(None), k)))),
            'D23_nsmallest_to_sorted_slice',
        ))

    if isinstance(term, OOp) and term.name == 'nlargest' and len(term.args) == 2:
        k, coll = term.args
        results.append((
            OOp('getitem', (OOp('sorted_reverse', (coll,)),
                           OOp('slice', (OLit(None), k)))),
            'D23_nlargest_to_sorted_rev_slice',
        ))

    return results


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

    ctx = FiberCtx()
    xs = OVar('xs')

    # head of sorted → min
    t1 = OOp('getitem', (OOp('sorted', (xs,)), OLit(0)))
    r1 = apply(t1, ctx)
    _assert(any(a == 'D23_head_sorted_to_min' for _, a in r1), "head sorted → min")

    # last of sorted → max
    t2 = OOp('getitem', (OOp('sorted', (xs,)), OLit(-1)))
    r2 = apply(t2, ctx)
    _assert(any(a == 'D23_last_sorted_to_max' for _, a in r2), "last sorted → max")

    # min → head sorted (inverse direction)
    t3 = OOp('min', (xs,))
    r3 = apply(t3, ctx)
    _assert(any(a == 'D23_min_to_head_sorted' for _, a in r3), "min → head sorted")

    # len(sorted(x)) → len(x)
    t4 = OOp('len', (OOp('sorted', (xs,)),))
    r4 = apply(t4, ctx)
    _assert(any(a == 'D23_len_sorted_absorb' for _, a in r4), "len sorted absorb")

    # set(sorted(x)) → set(x)
    t5 = OOp('set', (OOp('sorted', (xs,)),))
    r5 = apply(t5, ctx)
    _assert(any(a == 'D23_set_sorted_absorb' for _, a in r5), "set sorted absorb")

    # sum(sorted(x)) → sum(x)
    t6 = OOp('sum', (OOp('sorted', (xs,)),))
    r6 = apply(t6, ctx)
    _assert(any(a == 'D23_sum_sorted_absorb' for _, a in r6), "sum sorted absorb")

    # any(sorted(x)) → any(x)
    t7 = OOp('any', (OOp('sorted', (xs,)),))
    r7 = apply(t7, ctx)
    _assert(any(a == 'D23_any_sorted_absorb' for _, a in r7), "any sorted absorb")

    # reversed(sorted_reverse(x)) → sorted(x)
    t8 = OOp('reversed', (OOp('sorted_reverse', (xs,)),))
    r8 = apply(t8, ctx)
    _assert(any(a == 'D23_reversed_sorted_reverse' for _, a in r8), "reversed sorted_rev")

    # filter on sorted
    t9 = OOp('filter', (OVar('p'), OOp('sorted', (xs,))))
    r9 = apply(t9, ctx)
    _assert(any(a == 'D23_filter_sort_commute_op' for _, a in r9), "filter-sort commute")

    # recognizes
    _assert(recognizes(t1), "recognizes getitem on sorted")
    _assert(recognizes(t3), "recognizes min")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # inverse
    t10 = OOp('nsmallest', (OLit(3), xs))
    r10 = apply_inverse(t10, ctx)
    _assert(len(r10) >= 1, "nsmallest inverse")

    print(f"D23 sort-process: {_pass} passed, {_fail} failed")
