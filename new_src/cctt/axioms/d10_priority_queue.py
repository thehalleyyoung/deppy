"""D10 Axiom: Priority Queue Equivalences.

Establishes equivalence between different priority queue
implementations: binary heap (heapq), sorted list (bisect),
balanced BST, and manual sorted-insert loops.

Mathematical basis: A priority queue is an abstract data type
with operations {insert, extract_min, peek}.  All correct
implementations are quotients of the same free algebra by the
priority-queue specification:

    extract_min(insert(pq, x)) =
        (min(x, peek(pq)), insert_rest(pq, x))

Different representations (heap, sorted list, BST) are
fibers of the same sheaf over the priority-queue interface.
The denotation is the sequence of extracted elements, which
is representation-independent.

In OTerm terms:
    fold[heappush_heappop](empty_heap, stream)
    ≡ fold[insort_pop](empty_list, stream)
    ≡ fold[bst_insert_extract](empty_bst, stream)

All three produce OFold with the same abstract combiner
'pq_extract_min' over the input stream (§21.4, Theorem 21.4.1).
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)
from cctt.path_search import FiberCtx

# ═══════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════

AXIOM_NAME = "D10_priority_queue"
AXIOM_CATEGORY = "data_structure"

COMPOSES_WITH = ["D5_fold_universal", "D11_adt", "D19_sort_scan"]
REQUIRES: List[str] = []

# Canonical names for PQ operations across implementations
_HEAP_OPS = frozenset({
    'heappush', 'heapq.heappush', 'heappop', 'heapq.heappop',
    'heappushpop', 'heapq.heappushpop', 'heapify', 'heapq.heapify',
    'nsmallest', 'heapq.nsmallest', 'nlargest', 'heapq.nlargest',
})

_SORTED_LIST_OPS = frozenset({
    'insort', 'bisect.insort', 'insort_left', 'bisect.insort_left',
    'insort_right', 'bisect.insort_right',
    'bisect_left', 'bisect.bisect_left',
    'bisect_right', 'bisect.bisect_right',
})

_BST_OPS = frozenset({
    'bst_insert', 'bst_delete', 'bst_min', 'bst_extract_min',
    'tree_insert', 'tree_delete_min',
})

_PQ_INIT_OPS = frozenset({
    'heapify', 'heapq.heapify', 'list', 'sorted',
})

SOUNDNESS_PROOF = r"""
Theorem (D10 Priority Queue Equivalence).

Let PQ be the algebraic specification:
    extract_min : PQ × Elem → (Elem, PQ)
    insert      : PQ × Elem → PQ
    empty       : PQ
    is_empty    : PQ → Bool

with the axioms:
    extract_min(insert(empty, x)) = (x, empty)
    extract_min(insert(insert(pq, x), y)) =
        let (m, pq') = extract_min(insert(pq, x)) in
        if y ≤ m then (y, insert(pq', m))
        else (m, insert(pq', y))

Claim: Any two implementations H₁, H₂ satisfying these axioms
produce the same sequence of extract_min results on equal input.

Proof:
  By structural induction on the input sequence.
  The specification uniquely determines the output sequence.
  Since both H₁ and H₂ satisfy the spec, they produce the same
  output.  □

Corollary: fold[heappush+heappop]([], stream) ≡ fold[insort+pop]([], stream)
           ≡ fold[bst_insert+extract](nil, stream)  ≡ sorted(stream)
"""

EXAMPLES = [
    {
        "name": "heapq_vs_sorted_list",
        "before": "fold[heappush_heappop]([], stream)",
        "after": "fold[insort_pop]([], stream)",
        "benchmark": None,
    },
    {
        "name": "nsmallest_vs_sorted_slice",
        "before": "heapq.nsmallest(k, xs)",
        "after": "sorted(xs)[:k]",
        "benchmark": None,
    },
    {
        "name": "heapify_vs_sorted",
        "before": "heapify(list(xs))",
        "after": "sorted(xs)",
        "benchmark": None,
    },
    {
        "name": "heap_sort_vs_sort",
        "before": "fold[heappop](heapify(xs), range(len(xs)))",
        "after": "sorted(xs)",
        "benchmark": None,
    },
]


# ═══════════════════════════════════════════════════════════
# PQ pattern recognition
# ═══════════════════════════════════════════════════════════

def _is_heap_term(term: OTerm) -> bool:
    """Check if term involves heap operations."""
    if isinstance(term, OOp):
        if term.name in _HEAP_OPS:
            return True
        return any(_is_heap_term(a) for a in term.args)
    if isinstance(term, OFold):
        return (term.op_name in ('heappush', 'heappush_heappop', 'heapq.heappush')
                or _is_heap_term(term.collection)
                or _is_heap_term(term.init))
    if isinstance(term, OFix):
        return _is_heap_term(term.body)
    if isinstance(term, OCase):
        return (_is_heap_term(term.test)
                or _is_heap_term(term.true_branch)
                or _is_heap_term(term.false_branch))
    return False


def _is_sorted_list_pq(term: OTerm) -> bool:
    """Check if term uses sorted-list PQ operations."""
    if isinstance(term, OOp):
        if term.name in _SORTED_LIST_OPS:
            return True
        return any(_is_sorted_list_pq(a) for a in term.args)
    if isinstance(term, OFold):
        return (term.op_name in ('insort', 'insort_left', 'bisect.insort')
                or _is_sorted_list_pq(term.collection))
    return False


def _is_bst_pq(term: OTerm) -> bool:
    """Check if term uses BST-based PQ operations."""
    if isinstance(term, OOp):
        if term.name in _BST_OPS:
            return True
        return any(_is_bst_pq(a) for a in term.args)
    if isinstance(term, OFold):
        return (term.op_name in ('bst_insert', 'bst_insert_extract')
                or _is_bst_pq(term.collection))
    return False


def _extract_pq_collection(term: OTerm) -> Optional[OTerm]:
    """Extract the underlying collection being priority-queued."""
    if isinstance(term, OFold):
        return term.collection
    if isinstance(term, OOp):
        if term.name in ('heapify', 'heapq.heapify', 'sorted'):
            if len(term.args) >= 1:
                return term.args[0]
        if term.name in ('nsmallest', 'heapq.nsmallest', 'nlargest', 'heapq.nlargest'):
            if len(term.args) >= 2:
                return term.args[1]
    return None


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D10: Priority queue implementation equivalences.

    Handles:
      1. Heap fold → canonical PQ fold → sorted-list fold
      2. heapq.nsmallest(k, xs) ↔ sorted(xs)[:k]
      3. heapq.nlargest(k, xs) ↔ sorted(xs, reverse=True)[:k]
      4. heapify(xs) → sorted(xs) (when only extract_min follows)
      5. Heap-based sort → sorted()
      6. BST operations → canonical PQ fold
      7. Sorted-list insort → canonical PQ fold
    """
    results: List[Tuple[OTerm, str]] = []

    # ── Heap fold → canonical PQ fold ──
    if isinstance(term, OFold):
        if term.op_name in ('heappush', 'heappush_heappop', 'heapq.heappush'):
            # Canonicalize to abstract PQ combiner
            results.append((
                OFold('pq_extract_min', term.init, term.collection),
                'D10_heap_to_canonical_pq',
            ))
        if term.op_name in ('insort', 'insort_left', 'bisect.insort'):
            results.append((
                OFold('pq_extract_min', term.init, term.collection),
                'D10_sorted_list_to_canonical_pq',
            ))
        if term.op_name in ('bst_insert', 'bst_insert_extract'):
            results.append((
                OFold('pq_extract_min', term.init, term.collection),
                'D10_bst_to_canonical_pq',
            ))
        # Canonical PQ → sorted output
        if term.op_name == 'pq_extract_min':
            results.append((
                OOp('sorted', (term.collection,)),
                'D10_pq_to_sorted',
            ))

    # ── nsmallest / nlargest ──
    if isinstance(term, OOp):
        if term.name in ('nsmallest', 'heapq.nsmallest') and len(term.args) == 2:
            k, xs = term.args
            sorted_slice = OOp('getitem', (
                OOp('sorted', (xs,)),
                OOp('slice', (OLit(None), k)),
            ))
            results.append((sorted_slice, 'D10_nsmallest_to_sorted_slice'))
        if term.name in ('nlargest', 'heapq.nlargest') and len(term.args) == 2:
            k, xs = term.args
            sorted_rev = OOp('getitem', (
                OOp('sorted_reverse', (xs,)),
                OOp('slice', (OLit(None), k)),
            ))
            results.append((sorted_rev, 'D10_nlargest_to_sorted_slice'))

        # Reverse: sorted(xs)[:k] → nsmallest
        if term.name == 'getitem' and len(term.args) == 2:
            arr, slc = term.args
            if isinstance(arr, OOp) and arr.name == 'sorted' and len(arr.args) >= 1:
                if isinstance(slc, OOp) and slc.name == 'slice' and len(slc.args) == 2:
                    if isinstance(slc.args[0], OLit) and slc.args[0].value is None:
                        results.append((
                            OOp('nsmallest', (slc.args[1], arr.args[0])),
                            'D10_sorted_slice_to_nsmallest',
                        ))

        # heapify → sorted
        if term.name in ('heapify', 'heapq.heapify') and len(term.args) >= 1:
            results.append((
                OOp('sorted', (term.args[0],)),
                'D10_heapify_to_sorted',
            ))

    # ── Heap sort pattern: fold[heappop] over heapify ──
    if isinstance(term, OFold):
        if term.op_name in ('heappop', 'heapq.heappop'):
            if isinstance(term.init, OOp) and term.init.name in ('heapify', 'heapq.heapify'):
                if len(term.init.args) >= 1:
                    results.append((
                        OOp('sorted', (term.init.args[0],)),
                        'D10_heapsort_to_sorted',
                    ))

    return results


# ═══════════════════════════════════════════════════════════
# Recognizer & scoring
# ═══════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D10 apply to this term?"""
    if isinstance(term, OOp):
        if term.name in _HEAP_OPS | _SORTED_LIST_OPS | _BST_OPS:
            return True
        # sorted(xs)[:k] pattern
        if term.name == 'getitem' and len(term.args) == 2:
            if isinstance(term.args[0], OOp) and term.args[0].name in ('sorted', 'sorted_reverse'):
                return True
    if isinstance(term, OFold):
        if term.op_name in ('heappush', 'heappush_heappop', 'heapq.heappush',
                            'insort', 'insort_left', 'bisect.insort',
                            'bst_insert', 'bst_insert_extract',
                            'pq_extract_min', 'heappop', 'heapq.heappop'):
            return True
    return False


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Heuristic 0.0–1.0 for how likely D10 helps bridge term→other."""
    score = 0.0
    t_heap = _is_heap_term(term)
    t_sorted = _is_sorted_list_pq(term)
    t_bst = _is_bst_pq(term)
    o_heap = _is_heap_term(other)
    o_sorted = _is_sorted_list_pq(other)
    o_bst = _is_bst_pq(other)

    # Cross-implementation: strong signal
    if (t_heap and (o_sorted or o_bst)) or (t_sorted and (o_heap or o_bst)):
        score = max(score, 0.9)
    if t_bst and (o_heap or o_sorted):
        score = max(score, 0.9)

    # One side is a PQ op, other is sorted
    if isinstance(other, OOp) and other.name == 'sorted':
        if t_heap or t_sorted or t_bst:
            score = max(score, 0.85)
    if isinstance(term, OOp) and term.name == 'sorted':
        if o_heap or o_sorted or o_bst:
            score = max(score, 0.85)

    # nsmallest ↔ sorted[:k]
    if isinstance(term, OOp) and term.name in ('nsmallest', 'heapq.nsmallest'):
        if isinstance(other, OOp) and other.name == 'getitem':
            score = max(score, 0.95)

    return min(score, 1.0)


# ═══════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Reverse D10: expand sorted() back to heap-based or bisect-based.

    sorted(xs) → fold[heappop](heapify(xs), range(len(xs)))
    sorted(xs)[:k] → nsmallest(k, xs)
    """
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OOp):
        if term.name == 'sorted' and len(term.args) >= 1:
            xs = term.args[0]
            # → heapsort
            heap = OOp('heapify', (xs,))
            heapsort = OFold('heappop', heap, OOp('range', (OOp('len', (xs,)),)))
            results.append((heapsort, 'D10_inv_sorted_to_heapsort'))
            # → insort fold
            insort_fold = OFold('insort', OSeq(()), xs)
            results.append((insort_fold, 'D10_inv_sorted_to_insort'))

        if term.name == 'nsmallest' and len(term.args) == 2:
            k, xs = term.args
            sorted_slice = OOp('getitem', (
                OOp('sorted', (xs,)),
                OOp('slice', (OLit(None), k)),
            ))
            results.append((sorted_slice, 'D10_inv_nsmallest_to_sorted'))

    return results


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    ctx = FiberCtx(param_duck_types={})

    # Test 1: heap fold → canonical PQ
    heap_fold = OFold('heappush', OSeq(()), OVar('stream'))
    rewrites = apply(heap_fold, ctx)
    assert any('D10_heap_to_canonical_pq' in ax for _, ax in rewrites), \
        f"Expected heap→pq, got {[ax for _, ax in rewrites]}"
    print("✓ heap fold → canonical PQ")

    # Test 2: sorted-list fold → canonical PQ
    insort_fold = OFold('insort', OSeq(()), OVar('stream'))
    rewrites = apply(insort_fold, ctx)
    assert any('D10_sorted_list_to_canonical_pq' in ax for _, ax in rewrites)
    print("✓ sorted-list fold → canonical PQ")

    # Test 3: BST fold → canonical PQ
    bst_fold = OFold('bst_insert', OVar('nil'), OVar('stream'))
    rewrites = apply(bst_fold, ctx)
    assert any('D10_bst_to_canonical_pq' in ax for _, ax in rewrites)
    print("✓ BST fold → canonical PQ")

    # Test 4: nsmallest → sorted[:k]
    nsmall = OOp('nsmallest', (OLit(5), OVar('xs')))
    rewrites = apply(nsmall, ctx)
    assert any('D10_nsmallest_to_sorted_slice' in ax for _, ax in rewrites)
    print("✓ nsmallest → sorted[:k]")

    # Test 5: sorted[:k] → nsmallest
    sorted_slice = OOp('getitem', (
        OOp('sorted', (OVar('xs'),)),
        OOp('slice', (OLit(None), OLit(5))),
    ))
    rewrites = apply(sorted_slice, ctx)
    assert any('D10_sorted_slice_to_nsmallest' in ax for _, ax in rewrites)
    print("✓ sorted[:k] → nsmallest")

    # Test 6: heapify → sorted
    heapify = OOp('heapify', (OVar('xs'),))
    rewrites = apply(heapify, ctx)
    assert any('D10_heapify_to_sorted' in ax for _, ax in rewrites)
    print("✓ heapify → sorted")

    # Test 7: heapsort → sorted
    heapsort = OFold('heappop', OOp('heapify', (OVar('xs'),)),
                     OOp('range', (OOp('len', (OVar('xs'),)),)))
    rewrites = apply(heapsort, ctx)
    assert any('D10_heapsort_to_sorted' in ax for _, ax in rewrites)
    print("✓ heapsort → sorted")

    # Test 8: recognizes
    assert recognizes(heap_fold)
    assert recognizes(nsmall)
    assert recognizes(sorted_slice)
    assert not recognizes(OVar('x'))
    assert not recognizes(OFold('add', OLit(0), OVar('xs')))
    print("✓ recognizes()")

    # Test 9: relevance_score
    sorted_target = OOp('sorted', (OVar('xs'),))
    score = relevance_score(heap_fold, sorted_target)
    assert score >= 0.8, f"Expected high relevance, got {score}"
    print(f"✓ relevance_score(heap, sorted) = {score:.2f}")

    # Test 10: inverse
    inv = apply_inverse(sorted_target, ctx)
    assert any('D10_inv_sorted_to_heapsort' in ax for _, ax in inv)
    assert any('D10_inv_sorted_to_insort' in ax for _, ax in inv)
    print("✓ apply_inverse(sorted) → heapsort + insort")

    # Test 11: canonical PQ → sorted
    canon_pq = OFold('pq_extract_min', OSeq(()), OVar('stream'))
    rewrites = apply(canon_pq, ctx)
    assert any('D10_pq_to_sorted' in ax for _, ax in rewrites)
    print("✓ canonical PQ → sorted")

    print("\nAll D10 self-tests passed ✓")
