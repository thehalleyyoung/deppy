"""D43: Sliding Window Equivalences (Theorem 29.1.1).

Fixed-size window over a sequence: various equivalent implementations.

Mathematical foundation:
  A sliding window of size k over sequence xs of length n produces
  the family of subsequences {xs[i:i+k] | 0 ≤ i ≤ n-k}.

  All windowed computations factor through the same subsequence
  access pattern.  Different implementations (slice-based, deque,
  incremental update, monotonic deque, segment tree) compute the
  same function over each window — they differ only in how they
  maintain state across window shifts.

  The key algebraic insight: if f is decomposable as
    f(xs[i:i+k]) = g(f(xs[i-1:i+k-1]), xs[i-1], xs[i+k-1])
  then incremental update is equivalent to recomputation.

  For max/min windows, the monotonic deque maintains a subset of
  window elements that are candidates for the extremum.  This is
  equivalent to a segment tree range query over the same window.

Covers:
  • Slice-based window ↔ deque-based sliding window
  • max(window) via slice ↔ monotonic deque ↔ segment tree query
  • Running average: full recompute ↔ incremental update
  • Two-sum on sorted: nested loop ↔ two-pointer ↔ hash set
  • Sliding window maximum / minimum
  • Window-based aggregation (sum, product, count)
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

AXIOM_NAME = 'D43_sliding_window'
AXIOM_CATEGORY = 'algorithmic_patterns'  # §29

SOUNDNESS_PROOF = """
Theorem 29.1.1 (Sliding Window Equivalence):
  Let xs be a sequence of length n, k the window size, and f an
  aggregation function.  Then:

    [f(xs[i:i+k]) for i in range(n-k+1)]
      = deque_window(xs, k, f)
      = incremental_window(xs, k, f, update, remove)

  when f admits an incremental decomposition:
    f(xs[i:i+k]) = update(remove(f(xs[i-1:i+k-1]), xs[i-1]), xs[i+k-1])

Proof:
  By induction on i.  Base case: i=0, all three compute f(xs[0:k]).
  Inductive step: the incremental form updates f(window_{i-1}) to
  f(window_i) by removing xs[i-1] and adding xs[i+k-1], which by
  the decomposition assumption equals f(xs[i:i+k]).  ∎

Theorem 29.1.2 (Monotonic Deque ↔ Segment Tree for Window Extrema):
  For f = max (or min), the monotonic deque and segment tree both
  compute range-max queries over each window.

Proof:
  The monotonic deque maintains elements in decreasing order,
  discarding elements that can never be the maximum.  The segment
  tree answers range-max in O(log n) per query.  Both produce
  max(xs[i:i+k]) for each window position i.  ∎

Theorem 29.1.3 (Running Average Incremental Update):
  sum(xs[i:i+k])/k = (prev_sum - xs[i-1] + xs[i+k-1])/k

Proof:
  prev_sum = sum(xs[i-1:i+k-1]) = xs[i-1] + sum(xs[i:i+k-1]).
  sum(xs[i:i+k]) = sum(xs[i:i+k-1]) + xs[i+k-1]
                  = prev_sum - xs[i-1] + xs[i+k-1].
  Dividing both sides by k yields the result.  ∎
"""

COMPOSES_WITH = ['D04_comp_fusion', 'D05_fold_universal', 'D44_two_pointer']
REQUIRES: List[str] = []

EXAMPLES = [
    {
        'name': 'Slice to deque window',
        'before': "[xs[i:i+k] for i in range(n-k+1)]",
        'after': "deque_window(xs, k)",
        'axiom': 'D43_slice_to_deque',
    },
    {
        'name': 'Window max: slice to monotonic deque',
        'before': "[max(xs[i:i+k]) for i in range(n-k+1)]",
        'after': "monotonic_deque_max(xs, k)",
        'axiom': 'D43_window_max_to_mono_deque',
    },
    {
        'name': 'Window max: monotonic deque to segment tree',
        'before': "monotonic_deque_max(xs, k)",
        'after': "segment_tree_range_max(xs, k)",
        'axiom': 'D43_mono_deque_to_segtree',
    },
    {
        'name': 'Running average: recompute to incremental',
        'before': "[sum(xs[i:i+k])/k for i in range(n-k+1)]",
        'after': "incremental_running_avg(xs, k)",
        'axiom': 'D43_avg_recompute_to_incr',
    },
    {
        'name': 'Window sum: recompute to incremental',
        'before': "[sum(xs[i:i+k]) for i in range(n-k+1)]",
        'after': "incremental_window_sum(xs, k)",
        'axiom': 'D43_sum_recompute_to_incr',
    },
]

# ── Known sliding window operation names ──
WINDOW_OPS: FrozenSet[str] = frozenset({
    'sliding_window', 'window', 'deque_window',
    'monotonic_deque', 'monotonic_deque_max', 'monotonic_deque_min',
    'segment_tree_range_max', 'segment_tree_range_min',
    'window_max', 'window_min', 'window_sum', 'window_avg',
    'incremental_window', 'incremental_window_sum',
    'incremental_running_avg', 'running_avg', 'running_average',
})

# ── Aggregation functions that admit incremental update ──
INCREMENTAL_AGGREGATES: FrozenSet[str] = frozenset({
    'sum', 'add', 'mult', 'product',
    'max', 'min', 'count', 'mean', 'avg',
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

def _is_window_slice_pattern(term: OTerm) -> bool:
    """Detect xs[i:i+k] slice-based window comprehension.

    Only matches when slice appears inside a map/fold over a range
    (the actual sliding window pattern). Bare slice operations are
    NOT sliding windows — they're just general Python slicing.
    """
    if isinstance(term, OMap):
        canon = term.canon()
        return 'slice' in canon and ('range' in canon or 'len' in canon)
    # Bare OOp('slice', ...) is NOT a sliding window — it's just s[a:b].
    # Only the map-over-range-of-slices pattern is a genuine window.
    return False


def _is_window_aggregation(term: OTerm) -> Optional[str]:
    """Detect aggregation over a window: max(window), sum(window), etc.

    Returns the aggregation name or None.
    """
    if isinstance(term, OOp):
        if term.name in INCREMENTAL_AGGREGATES:
            for arg in term.args:
                if _is_window_slice_pattern(arg):
                    return term.name
                if isinstance(arg, OOp) and arg.name == 'slice':
                    return term.name
    if isinstance(term, OMap):
        if isinstance(term.transform, OLam):
            body = term.transform.body
            if isinstance(body, OOp) and body.name in INCREMENTAL_AGGREGATES:
                return body.name
    return None


def _is_monotonic_deque(term: OTerm) -> bool:
    """Detect monotonic deque operations."""
    if isinstance(term, OOp):
        return term.name in ('monotonic_deque', 'monotonic_deque_max',
                             'monotonic_deque_min')
    return False


def _is_segment_tree_query(term: OTerm) -> bool:
    """Detect segment tree range query."""
    if isinstance(term, OOp):
        return term.name in ('segment_tree_range_max', 'segment_tree_range_min',
                             'segment_tree_query', 'range_max', 'range_min')
    return False


# ═══════════════════════════════════════════════════════════
# Core axiom: apply()
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D43 sliding window equivalences to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── Slice-based window → deque window ──
    if _is_window_slice_pattern(term):
        free = sorted(_extract_free_vars(term))
        inputs = tuple(OVar(v) for v in free) if free else (OVar('xs'), OVar('k'))
        results.append((
            OOp('deque_window', inputs),
            'D43_slice_to_deque',
        ))

    # ── Deque window → slice-based window ──
    if isinstance(term, OOp) and term.name == 'deque_window':
        results.append((
            OOp('slice_window', term.args),
            'D43_deque_to_slice',
        ))

    # ── Window max/min aggregation → monotonic deque ──
    agg = _is_window_aggregation(term)
    if agg in ('max', 'min'):
        free = sorted(_extract_free_vars(term))
        inputs = tuple(OVar(v) for v in free) if free else (OVar('xs'), OVar('k'))
        results.append((
            OOp(f'monotonic_deque_{agg}', inputs),
            f'D43_window_{agg}_to_mono_deque',
        ))

    # ── Monotonic deque ↔ segment tree ──
    if _is_monotonic_deque(term):
        suffix = 'max' if 'max' in term.name else 'min'
        results.append((
            OOp(f'segment_tree_range_{suffix}', term.args),
            'D43_mono_deque_to_segtree',
        ))
    if _is_segment_tree_query(term):
        suffix = 'max' if 'max' in term.name else 'min'
        results.append((
            OOp(f'monotonic_deque_{suffix}', term.args),
            'D43_segtree_to_mono_deque',
        ))

    # ── Window sum/avg recompute → incremental ──
    if agg in ('sum', 'add'):
        free = sorted(_extract_free_vars(term))
        inputs = tuple(OVar(v) for v in free) if free else (OVar('xs'), OVar('k'))
        results.append((
            OOp('incremental_window_sum', inputs),
            'D43_sum_recompute_to_incr',
        ))
    if agg in ('avg', 'mean'):
        free = sorted(_extract_free_vars(term))
        inputs = tuple(OVar(v) for v in free) if free else (OVar('xs'), OVar('k'))
        results.append((
            OOp('incremental_running_avg', inputs),
            'D43_avg_recompute_to_incr',
        ))

    # ── Incremental → recompute (inverse direction) ──
    if isinstance(term, OOp) and term.name == 'incremental_window_sum':
        results.append((
            OOp('window_sum', term.args),
            'D43_incr_to_sum_recompute',
        ))
    if isinstance(term, OOp) and term.name in ('incremental_running_avg', 'running_avg'):
        results.append((
            OOp('window_avg', term.args),
            'D43_incr_to_avg_recompute',
        ))

    # ── Abstract spec: sliding_window variants ──
    if isinstance(term, OAbstract):
        if 'window' in term.spec or 'sliding' in term.spec:
            results.append((
                OOp('deque_window', term.inputs),
                'D43_spec_to_deque',
            ))
            results.append((
                OOp('slice_window', term.inputs),
                'D43_spec_to_slice',
            ))

    # ── Fold over range with slice access → incremental window ──
    if isinstance(term, OFold):
        canon = term.canon()
        if 'slice' in canon and term.op_name in INCREMENTAL_AGGREGATES:
            results.append((
                OOp(f'incremental_window_{term.op_name}', (term.collection,)),
                'D43_fold_slice_to_incr',
            ))

    # ── Named window operations → spec ──
    if isinstance(term, OOp) and term.name in WINDOW_OPS:
        results.append((
            OAbstract(f'window_{term.name}', term.args),
            'D43_window_op_to_spec',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Optional[FiberCtx] = None) -> List[Tuple[OTerm, str]]:
    """Apply D43 in reverse: optimised → naive."""
    results = apply(term, ctx)
    inverse_labels = {
        'D43_deque_to_slice',
        'D43_segtree_to_mono_deque',
        'D43_incr_to_sum_recompute',
        'D43_incr_to_avg_recompute',
    }
    return [(t, lbl) for t, lbl in results if lbl in inverse_labels]


# ═══════════════════════════════════════════════════════════
# Recognition
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Return True if D43 is potentially applicable."""
    if isinstance(term, OOp):
        if term.name in WINDOW_OPS:
            return True
        if term.name in ('slice', 'range_max', 'range_min'):
            return True
    if _is_window_slice_pattern(term):
        return True
    if _is_window_aggregation(term) is not None:
        return True
    if _is_monotonic_deque(term):
        return True
    if _is_segment_tree_query(term):
        return True
    if isinstance(term, OAbstract):
        return 'window' in term.spec or 'sliding' in term.spec
    if isinstance(term, OFold):
        canon = term.canon()
        if 'slice' in canon and term.op_name in INCREMENTAL_AGGREGATES:
            return True
    return False


# ═══════════════════════════════════════════════════════════
# Relevance scoring
# ═══════════════════════════════════════════════════════════

def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D43 relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()

    window_kw = ['window', 'sliding', 'deque', 'slice']
    opt_kw = ['monotonic', 'segment_tree', 'incremental', 'running']

    has_window_s = any(kw in sc for kw in window_kw)
    has_window_t = any(kw in tc for kw in window_kw)
    has_opt_s = any(kw in sc for kw in opt_kw)
    has_opt_t = any(kw in tc for kw in opt_kw)

    # One naive window, one optimised → high relevance
    if (has_window_s and has_opt_t) or (has_opt_s and has_window_t):
        return 0.95
    # Both window-related
    if has_window_s and has_window_t:
        return 0.80
    # Both optimised forms
    if has_opt_s and has_opt_t:
        return 0.70
    # One side has window keyword
    if has_window_s or has_window_t:
        return 0.35
    if has_opt_s or has_opt_t:
        return 0.25
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
    k = OVar('k')
    n = OVar('n')

    # ── Slice window → deque ──
    print("D43: slice window → deque ...")
    slice_term = OOp('slice', (xs,))
    _assert(_is_window_slice_pattern(slice_term), "slice pattern detected")
    r_slice = apply(slice_term, ctx)
    _assert(any(lbl == 'D43_slice_to_deque' for _, lbl in r_slice), "slice→deque")

    # ── Deque → slice ──
    print("D43: deque → slice ...")
    deque_term = OOp('deque_window', (xs, k))
    r_deque = apply(deque_term, ctx)
    _assert(any(lbl == 'D43_deque_to_slice' for _, lbl in r_deque), "deque→slice")

    # ── Monotonic deque → segment tree ──
    print("D43: monotonic deque → segment tree ...")
    mono_term = OOp('monotonic_deque_max', (xs, k))
    r_mono = apply(mono_term, ctx)
    _assert(any(lbl == 'D43_mono_deque_to_segtree' for _, lbl in r_mono),
            "mono_deque→segtree")

    # ── Segment tree → monotonic deque ──
    print("D43: segment tree → monotonic deque ...")
    seg_term = OOp('segment_tree_range_max', (xs, k))
    r_seg = apply(seg_term, ctx)
    _assert(any(lbl == 'D43_segtree_to_mono_deque' for _, lbl in r_seg),
            "segtree→mono_deque")

    # ── Incremental sum → recompute ──
    print("D43: incremental sum → recompute ...")
    incr_sum = OOp('incremental_window_sum', (xs, k))
    r_incr = apply(incr_sum, ctx)
    _assert(any(lbl == 'D43_incr_to_sum_recompute' for _, lbl in r_incr),
            "incr→sum_recompute")

    # ── Incremental avg → recompute ──
    print("D43: incremental avg → recompute ...")
    incr_avg = OOp('incremental_running_avg', (xs, k))
    r_avg = apply(incr_avg, ctx)
    _assert(any(lbl == 'D43_incr_to_avg_recompute' for _, lbl in r_avg),
            "incr→avg_recompute")

    # ── Abstract spec: window → deque/slice ──
    print("D43: abstract window spec ...")
    win_spec = OAbstract('sliding_window_max', (xs, k))
    r_spec = apply(win_spec, ctx)
    _assert(any(lbl == 'D43_spec_to_deque' for _, lbl in r_spec), "spec→deque")
    _assert(any(lbl == 'D43_spec_to_slice' for _, lbl in r_spec), "spec→slice")

    # ── Fold over slices → incremental ──
    print("D43: fold slice → incremental ...")
    fold_slice = OFold('sum', OLit(0), OOp('slice', (xs,)))
    r_fold = apply(fold_slice, ctx)
    _assert(any(lbl == 'D43_fold_slice_to_incr' for _, lbl in r_fold),
            "fold_slice→incremental")

    # ── Named window op → spec ──
    print("D43: named window op → spec ...")
    win_op = OOp('window_sum', (xs, k))
    r_wop = apply(win_op, ctx)
    _assert(any(lbl == 'D43_window_op_to_spec' for _, lbl in r_wop),
            "window_op→spec")

    # ── recognizes ──
    print("D43: recognizes ...")
    _assert(recognizes(mono_term), "recognizes monotonic deque")
    _assert(recognizes(seg_term), "recognizes segment tree")
    _assert(recognizes(deque_term), "recognizes deque window")
    _assert(recognizes(win_spec), "recognizes window spec")
    _assert(recognizes(fold_slice), "recognizes fold slice")
    _assert(not recognizes(OOp('sorted', (xs,))), "does not recognise sorted")

    # ── relevance_score ──
    print("D43: relevance_score ...")
    score = relevance_score(
        OOp('slice_window', (xs, k)),
        OOp('monotonic_deque_max', (xs, k)),
    )
    _assert(score > 0.9, f"window↔mono score={score:.2f} > 0.9")

    low = relevance_score(OOp('sorted', (xs,)), OLit(42))
    _assert(low < 0.2, f"unrelated score={low:.2f} < 0.2")

    # ── apply_inverse ──
    print("D43: apply_inverse ...")
    inv = apply_inverse(seg_term, ctx)
    _assert(len(inv) >= 1, "inverse segtree→mono_deque")

    inv_incr = apply_inverse(incr_sum, ctx)
    _assert(len(inv_incr) >= 1, "inverse incr→recompute")

    # ── Summary ──
    print(f"\n{'='*50}")
    print(f"  D43 sliding_window: {passed} passed, {failed} failed")
    print(f"{'='*50}")
    if failed > 0:
        raise SystemExit(1)
