"""D44: Two-Pointer ↔ Brute Force Equivalences (Theorem 29.2.1).

Two-pointer techniques are equivalent to brute-force search WHEN
the input satisfies structural preconditions (e.g., sorted order).

Mathematical foundation:
  The two-pointer technique exploits monotonicity of a predicate
  over a sorted sequence to reduce O(n²) search to O(n).

  Given sorted xs and predicate P(xs[i], xs[j]), if P is monotone
  in j for fixed i (or vice versa), then the two-pointer scan
  visits exactly the pairs that the brute-force nested loop does,
  but in amortized O(n) time.

  Formally, two-pointer correctness requires:
    ∀i. {j | P(xs[i], xs[j])} is a contiguous range in [0..n)
  which follows from sortedness + monotonicity of P.

  IMPORTANT: These equivalences hold ONLY under preconditions.
  Without sorted input, two-pointer may miss valid pairs.

Covers:
  • Sorted two-sum: nested loop O(n²) ↔ two-pointer O(n)
  • Merge two sorted lists: index-based ↔ pointer-based
  • Remove duplicates from sorted: comparison ↔ set-based
  • Partition: filter-based ↔ swap-based
  • Dutch national flag: three-way partition variants
  • Container with most water: brute force ↔ two-pointer
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)


# ═══════════════════════════════════════════════════════════
# Axiom metadata
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = 'D44_two_pointer'
AXIOM_CATEGORY = 'algorithmic_patterns'  # §29

SOUNDNESS_PROOF = """
Theorem 29.2.1 (Two-Pointer ↔ Brute Force under Sorted Order):
  Let xs be a sorted sequence of length n.  For the two-sum problem:
    ∃(i,j). xs[i] + xs[j] = target
  the nested loop:
    for i in range(n):
      for j in range(i+1, n):
        if xs[i] + xs[j] == target: return (i, j)
  is equivalent to the two-pointer scan:
    lo, hi = 0, n-1
    while lo < hi:
      s = xs[lo] + xs[hi]
      if s == target: return (lo, hi)
      elif s < target: lo += 1
      else: hi -= 1

Proof:
  By the sorted order invariant, xs[lo] ≤ xs[lo+1] and
  xs[hi-1] ≤ xs[hi].  If xs[lo]+xs[hi] < target, then
  xs[lo]+xs[j] < target for all j ≤ hi, so lo must increase.
  Symmetrically for the hi pointer.  The two-pointer scan
  therefore visits the same solution set.  ∎

Theorem 29.2.2 (Merge Sorted Lists):
  Merging two sorted lists by index comparison produces the
  same result as pointer-based merge:
    merge_index(a, b) = merge_pointer(a, b)

Proof:
  Both select min(a[i], b[j]) at each step, advancing the
  pointer of the smaller element.  By induction on total
  elements remaining.  ∎

Theorem 29.2.3 (Remove Duplicates from Sorted):
  For sorted xs: dedup_comparison(xs) = list(set(xs)) (as sorted list)

Proof:
  In sorted order, duplicates are adjacent.  The comparison-based
  approach keeps xs[i] when xs[i] ≠ xs[i-1].  The set removes all
  duplicates.  Sorting the set result recovers the same order.  ∎

Theorem 29.2.4 (Partition Equivalence):
  filter(p, xs) + filter(not p, xs) = swap_partition(p, xs)
  (up to ordering within each partition group).

Proof:
  Both produce a permutation of xs where elements satisfying p
  precede those not satisfying p.  The filter concatenation is
  stable; swap-based may reorder within groups.  Under quotient
  by within-group permutation, they are equal.  ∎
"""

COMPOSES_WITH = ['D43_sliding_window', 'D19_sort_scan', 'D05_fold_universal']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Two-sum: nested loop to two-pointer',
        'before': "nested_loop_two_sum(xs, target)",
        'after': "two_pointer_two_sum(xs, target)",
        'axiom': 'D44_nested_to_two_ptr',
        'precondition': 'xs is sorted',
    },
    {
        'name': 'Two-pointer to nested loop',
        'before': "two_pointer_two_sum(xs, target)",
        'after': "nested_loop_two_sum(xs, target)",
        'axiom': 'D44_two_ptr_to_nested',
    },
    {
        'name': 'Merge sorted: index to pointer',
        'before': "merge_index(a, b)",
        'after': "merge_pointer(a, b)",
        'axiom': 'D44_merge_index_to_ptr',
    },
    {
        'name': 'Dedup sorted: comparison to set',
        'before': "dedup_comparison(xs)",
        'after': "sorted(set(xs))",
        'axiom': 'D44_dedup_cmp_to_set',
        'precondition': 'xs is sorted',
    },
    {
        'name': 'Partition: filter to swap',
        'before': "filter_partition(p, xs)",
        'after': "swap_partition(p, xs)",
        'axiom': 'D44_filter_to_swap',
    },
    {
        'name': 'Dutch national flag: two-pass to three-pointer',
        'before': "two_pass_dnf(xs)",
        'after': "three_pointer_dnf(xs)",
        'axiom': 'D44_dnf_two_pass_to_three_ptr',
    },
]

# ── Known two-pointer operation names ──
TWO_POINTER_OPS: FrozenSet[str] = frozenset({
    'two_pointer', 'two_ptr', 'two_pointer_two_sum',
    'two_pointer_search', 'two_pointer_scan',
    'merge_pointer', 'merge_sorted', 'merge_index',
    'dedup_comparison', 'dedup_sorted', 'remove_duplicates',
    'swap_partition', 'filter_partition', 'partition',
    'dutch_national_flag', 'three_way_partition', 'dnf',
    'two_pass_dnf', 'three_pointer_dnf',
    'container_water', 'container_most_water',
})

# ── Brute-force counterparts ──
BRUTE_FORCE_OPS: FrozenSet[str] = frozenset({
    'nested_loop', 'nested_loop_two_sum', 'brute_force',
    'brute_force_two_sum', 'n_squared_search',
    'filter_concat', 'filter_partition',
})

# ── Preconditions required for equivalence ──
REQUIRES_SORTED: FrozenSet[str] = frozenset({
    'two_pointer_two_sum', 'two_ptr', 'two_pointer_search',
    'dedup_comparison', 'dedup_sorted',
    'merge_sorted', 'merge_pointer', 'merge_index',
})


# ═══════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberCtx:
    """Lightweight fiber context for standalone axiom evaluation."""
    param_duck_types: Dict[str, str] = field(default_factory=dict)


def _extract_free_vars(term: OTerm) -> Set[str]:
    """Extract all free variable names."""
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, OLit) or isinstance(term, OUnknown):
        return set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_free_vars(a)
        return r
    if isinstance(term, OFold):
        return _extract_free_vars(term.init) | _extract_free_vars(term.collection)
    if isinstance(term, OCase):
        return (
            _extract_free_vars(term.test)
            | _extract_free_vars(term.true_branch)
            | _extract_free_vars(term.false_branch)
        )
    if isinstance(term, OFix):
        return _extract_free_vars(term.body)
    if isinstance(term, OLam):
        return _extract_free_vars(term.body) - set(term.params)
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e)
        return r2
    if isinstance(term, OMap):
        r3 = _extract_free_vars(term.transform) | _extract_free_vars(term.collection)
        if term.filter_pred:
            r3 |= _extract_free_vars(term.filter_pred)
        return r3
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner)
    if isinstance(term, ODict):
        r4: Set[str] = set()
        for k, v in term.pairs:
            r4 |= _extract_free_vars(k) | _extract_free_vars(v)
        return r4
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body) | _extract_free_vars(term.default)
    if isinstance(term, OAbstract):
        r5: Set[str] = set()
        for a in term.inputs:
            r5 |= _extract_free_vars(a)
        return r5
    return set()


# ═══════════════════════════════════════════════════════════
# Pattern detection
# ═══════════════════════════════════════════════════════════

def _is_nested_loop_search(term: OTerm) -> bool:
    """Detect nested loop / brute-force search pattern."""
    if isinstance(term, OOp) and term.name in BRUTE_FORCE_OPS:
        return True
    # Nested OFold → nested loop
    if isinstance(term, OFold):
        if isinstance(term.collection, OFold):
            return True
    # Nested OMap → nested comprehension
    if isinstance(term, OMap):
        if isinstance(term.collection, OMap):
            return True
    return False


def _is_two_pointer_op(term: OTerm) -> bool:
    """Detect two-pointer algorithm operations."""
    if isinstance(term, OOp) and term.name in TWO_POINTER_OPS:
        return True
    return False


def _is_merge_pattern(term: OTerm) -> bool:
    """Detect merge of two sorted lists."""
    if isinstance(term, OOp) and term.name in (
        'merge_sorted', 'merge_pointer', 'merge_index', 'merge',
    ):
        return True
    return False


def _is_partition_pattern(term: OTerm) -> bool:
    """Detect partition operations (filter/swap/DNF)."""
    if isinstance(term, OOp) and term.name in (
        'partition', 'swap_partition', 'filter_partition',
        'dutch_national_flag', 'three_way_partition', 'dnf',
        'two_pass_dnf', 'three_pointer_dnf',
    ):
        return True
    return False


def _has_sorted_precondition(term: OTerm) -> bool:
    """Check if term involves operations that require sorted input."""
    if isinstance(term, OOp):
        return term.name in REQUIRES_SORTED
    canon = term.canon()
    return 'sorted' in canon


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D44 two-pointer ↔ brute force equivalences to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Nested loop → two-pointer (requires sorted) ──
    if isinstance(term, OOp) and term.name in (
        'nested_loop_two_sum', 'brute_force_two_sum', 'n_squared_search',
    ):
        results.append((
            OOp('two_pointer_two_sum', term.args),
            'D44_nested_to_two_ptr',
        ))

    # ── Two-pointer → nested loop ──
    if isinstance(term, OOp) and term.name in (
        'two_pointer_two_sum', 'two_ptr', 'two_pointer_search',
    ):
        results.append((
            OOp('nested_loop_two_sum', term.args),
            'D44_two_ptr_to_nested',
        ))

    # ── Merge index ↔ merge pointer ──
    if isinstance(term, OOp) and term.name == 'merge_index':
        results.append((
            OOp('merge_pointer', term.args),
            'D44_merge_index_to_ptr',
        ))
    if isinstance(term, OOp) and term.name == 'merge_pointer':
        results.append((
            OOp('merge_index', term.args),
            'D44_merge_ptr_to_index',
        ))
    # Both → abstract merge_sorted spec
    if isinstance(term, OOp) and term.name in ('merge_index', 'merge_pointer'):
        results.append((
            OAbstract('merge_sorted', term.args),
            'D44_merge_to_spec',
        ))

    # ── Dedup: comparison ↔ set ──
    if isinstance(term, OOp) and term.name in ('dedup_comparison', 'dedup_sorted'):
        results.append((
            OOp('sorted_set', term.args),
            'D44_dedup_cmp_to_set',
        ))
    if isinstance(term, OOp) and term.name == 'sorted_set':
        results.append((
            OOp('dedup_comparison', term.args),
            'D44_dedup_set_to_cmp',
        ))
    if isinstance(term, OOp) and term.name == 'remove_duplicates':
        results.append((
            OOp('dedup_comparison', term.args),
            'D44_remove_dup_to_cmp',
        ))
        results.append((
            OOp('sorted_set', term.args),
            'D44_remove_dup_to_set',
        ))

    # ── Partition: filter ↔ swap ──
    if isinstance(term, OOp) and term.name == 'filter_partition':
        results.append((
            OOp('swap_partition', term.args),
            'D44_filter_to_swap',
        ))
    if isinstance(term, OOp) and term.name == 'swap_partition':
        results.append((
            OOp('filter_partition', term.args),
            'D44_swap_to_filter',
        ))

    # ── Dutch national flag variants ──
    if isinstance(term, OOp) and term.name in ('two_pass_dnf', 'dutch_national_flag'):
        results.append((
            OOp('three_pointer_dnf', term.args),
            'D44_dnf_two_pass_to_three_ptr',
        ))
    if isinstance(term, OOp) and term.name == 'three_pointer_dnf':
        results.append((
            OOp('two_pass_dnf', term.args),
            'D44_dnf_three_ptr_to_two_pass',
        ))

    # ── Nested fold → two-pointer (structural detection) ──
    if isinstance(term, OFold) and isinstance(term.collection, OFold):
        free = sorted(_extract_free_vars(term))
        inputs = tuple(OVar(v) for v in free) if free else (OVar('xs'),)
        results.append((
            OOp('two_pointer_scan', inputs),
            'D44_nested_fold_to_two_ptr',
        ))

    # ── Abstract specs ──
    if isinstance(term, OAbstract):
        if 'two_sum' in term.spec:
            results.append((
                OOp('two_pointer_two_sum', term.inputs),
                'D44_spec_to_two_ptr',
            ))
            results.append((
                OOp('nested_loop_two_sum', term.inputs),
                'D44_spec_to_nested',
            ))
        if 'merge' in term.spec and 'sorted' in term.spec:
            results.append((
                OOp('merge_pointer', term.inputs),
                'D44_spec_to_merge_ptr',
            ))
        if 'partition' in term.spec:
            results.append((
                OOp('swap_partition', term.inputs),
                'D44_spec_to_swap_partition',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D44 in reverse: optimised → brute force."""
    results = apply(term, ctx)
    inverse_labels = {
        'D44_two_ptr_to_nested',
        'D44_merge_ptr_to_index',
        'D44_swap_to_filter',
        'D44_dnf_three_ptr_to_two_pass',
        'D44_dedup_set_to_cmp',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D44 is potentially applicable."""
    if isinstance(term, OOp):
        if term.name in TWO_POINTER_OPS | BRUTE_FORCE_OPS:
            return True
        if term.name in ('sorted_set',):
            return True
    if _is_nested_loop_search(term):
        return True
    if _is_merge_pattern(term):
        return True
    if _is_partition_pattern(term):
        return True
    if isinstance(term, OAbstract):
        return any(kw in term.spec for kw in ('two_sum', 'merge_sorted', 'partition'))
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D44 relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    two_ptr_kw = ['two_pointer', 'two_ptr', 'merge_pointer', 'swap_partition',
                  'three_pointer', 'dnf']
    brute_kw = ['nested_loop', 'brute_force', 'n_squared', 'filter_partition',
                'merge_index', 'dedup']

    has_ptr_s = any(kw in sc for kw in two_ptr_kw)
    has_ptr_t = any(kw in tc for kw in two_ptr_kw)
    has_brute_s = any(kw in sc for kw in brute_kw)
    has_brute_t = any(kw in tc for kw in brute_kw)

    # One brute, one two-pointer → high relevance
    if (has_brute_s and has_ptr_t) or (has_ptr_s and has_brute_t):
        return 0.95
    # Both two-pointer related
    if has_ptr_s and has_ptr_t:
        return 0.70
    if has_brute_s and has_brute_t:
        return 0.50
    # One side has relevant keyword
    if has_ptr_s or has_ptr_t or has_brute_s or has_brute_t:
        return 0.35
    return 0.05


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    passed = 0
    failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global passed, failed
        if cond:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {msg}")

    ctx = FiberCtx()
    xs = OVar('xs')
    target = OVar('target')
    a = OVar('a')
    b = OVar('b')
    p = OVar('p')

    # ── Nested loop → two-pointer ──
    print("D44: nested loop → two-pointer ...")
    nested = OOp('nested_loop_two_sum', (xs, target))
    r_nested = apply(nested, ctx)
    _assert(any(lbl == 'D44_nested_to_two_ptr' for _, lbl in r_nested),
            "nested→two_ptr")

    # ── Two-pointer → nested loop ──
    print("D44: two-pointer → nested loop ...")
    two_ptr = OOp('two_pointer_two_sum', (xs, target))
    r_ptr = apply(two_ptr, ctx)
    _assert(any(lbl == 'D44_two_ptr_to_nested' for _, lbl in r_ptr),
            "two_ptr→nested")

    # ── Merge index ↔ pointer ──
    print("D44: merge index ↔ pointer ...")
    m_idx = OOp('merge_index', (a, b))
    r_mi = apply(m_idx, ctx)
    _assert(any(lbl == 'D44_merge_index_to_ptr' for _, lbl in r_mi),
            "merge_index→ptr")

    m_ptr = OOp('merge_pointer', (a, b))
    r_mp = apply(m_ptr, ctx)
    _assert(any(lbl == 'D44_merge_ptr_to_index' for _, lbl in r_mp),
            "merge_ptr→index")

    # ── Dedup: comparison ↔ set ──
    print("D44: dedup comparison ↔ set ...")
    dedup = OOp('dedup_comparison', (xs,))
    r_dd = apply(dedup, ctx)
    _assert(any(lbl == 'D44_dedup_cmp_to_set' for _, lbl in r_dd),
            "dedup_cmp→set")

    sset = OOp('sorted_set', (xs,))
    r_ss = apply(sset, ctx)
    _assert(any(lbl == 'D44_dedup_set_to_cmp' for _, lbl in r_ss),
            "dedup_set→cmp")

    # ── Remove duplicates ──
    print("D44: remove_duplicates ...")
    rd = OOp('remove_duplicates', (xs,))
    r_rd = apply(rd, ctx)
    _assert(any(lbl == 'D44_remove_dup_to_cmp' for _, lbl in r_rd),
            "remove_dup→cmp")
    _assert(any(lbl == 'D44_remove_dup_to_set' for _, lbl in r_rd),
            "remove_dup→set")

    # ── Partition: filter ↔ swap ──
    print("D44: partition filter ↔ swap ...")
    fp = OOp('filter_partition', (p, xs))
    r_fp = apply(fp, ctx)
    _assert(any(lbl == 'D44_filter_to_swap' for _, lbl in r_fp),
            "filter→swap")

    sp = OOp('swap_partition', (p, xs))
    r_sp = apply(sp, ctx)
    _assert(any(lbl == 'D44_swap_to_filter' for _, lbl in r_sp),
            "swap→filter")

    # ── Dutch national flag ──
    print("D44: DNF two-pass ↔ three-pointer ...")
    dnf2 = OOp('two_pass_dnf', (xs,))
    r_dnf2 = apply(dnf2, ctx)
    _assert(any(lbl == 'D44_dnf_two_pass_to_three_ptr' for _, lbl in r_dnf2),
            "dnf_two_pass→three_ptr")

    dnf3 = OOp('three_pointer_dnf', (xs,))
    r_dnf3 = apply(dnf3, ctx)
    _assert(any(lbl == 'D44_dnf_three_ptr_to_two_pass' for _, lbl in r_dnf3),
            "dnf_three_ptr→two_pass")

    # ── Nested fold → two-pointer ──
    print("D44: nested fold → two-pointer ...")
    nested_fold = OFold('add', OLit(0), OFold('max', OLit(0), xs))
    r_nf = apply(nested_fold, ctx)
    _assert(any(lbl == 'D44_nested_fold_to_two_ptr' for _, lbl in r_nf),
            "nested_fold→two_ptr")

    # ── Abstract spec ──
    print("D44: abstract spec ...")
    spec_ts = OAbstract('two_sum_sorted', (xs, target))
    r_ts = apply(spec_ts, ctx)
    _assert(any(lbl == 'D44_spec_to_two_ptr' for _, lbl in r_ts),
            "spec→two_ptr")
    _assert(any(lbl == 'D44_spec_to_nested' for _, lbl in r_ts),
            "spec→nested")

    # ── recognizes ──
    print("D44: recognizes ...")
    _assert(recognizes(nested), "recognizes nested loop")
    _assert(recognizes(two_ptr), "recognizes two-pointer")
    _assert(recognizes(m_idx), "recognizes merge index")
    _assert(recognizes(fp), "recognizes filter partition")
    _assert(recognizes(dnf2), "recognizes DNF")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D44: relevance_score ...")
    score = relevance_score(
        OOp('nested_loop_two_sum', (xs,)),
        OOp('two_pointer_two_sum', (xs,)),
    )
    _assert(score > 0.9, f"nested↔ptr score={score:.2f} > 0.9")

    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D44: apply_inverse ...")
    inv = apply_inverse(two_ptr, ctx)
    _assert(len(inv) >= 1, "inverse two_ptr→nested")

    inv_sp = apply_inverse(sp, ctx)
    _assert(len(inv_sp) >= 1, "inverse swap→filter")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D44 two_pointer: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
