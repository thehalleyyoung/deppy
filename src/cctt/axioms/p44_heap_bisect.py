"""P44 Axiom: Heap/Bisect Equivalences.

Establishes equivalences between Python's heapq/bisect module
operations and their naive sorting-based equivalents:
heapq.nsmallest(k, xs) ↔ sorted(xs)[:k],
heapq.nlargest(k, xs) ↔ sorted(xs, reverse=True)[:k],
bisect.insort ↔ append-then-sort,
heapq.merge ↔ sorted(chain(...)),
heapq.push/pop patterns, and bisect_left ↔ binary search loop.

Mathematical basis: a min-heap is the free join-semilattice on a
totally ordered set.  The priority queue operations correspond to
algebraic operations on this semilattice:

  heapq.nsmallest(k, xs) ≡ take(k, sort(xs))
  heapq.nlargest(k, xs)  ≡ take(k, sort_desc(xs))
  bisect.insort(xs, x)   ≡ sort(append(xs, x))
  heapq.merge(*iters)    ≡ sort(chain(*iters))

The heap invariant xs[k] ≤ xs[2k+1], xs[k] ≤ xs[2k+2] ensures
O(n log k) extraction, while sorted()[:k] is O(n log n).

Key rewrites:
  • heapq.nsmallest(k, xs) ↔ sorted(xs)[:k]
  • heapq.nlargest(k, xs)  ↔ sorted(xs, reverse=True)[:k]
  • bisect.insort(xs, x)   ↔ xs.append(x); xs.sort()
  • heapq.merge(*seqs)     ↔ sorted(chain(*seqs))
  • heapq.heappush(h, v)   ↔ append + re-sort
  • heapq.heappop(h)       ↔ sorted; pop first
  • bisect_left(xs, x)     ↔ binary search loop
  • heapq.heappushpop(h,v) ↔ push then pop
  • heapq.heapreplace(h,v) ↔ pop then push
  • priority_queue pattern  ↔ heapq operations

(§P44, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P44_heap_bisect"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P05_sort_variants", "P06_itertools", "P23_iteration"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P44 Heap/Bisect Equivalences).

1. heapq_nsmallest(k, xs) ≡ sorted_slice_k(xs, k)
   heapq.nsmallest(k, xs) ≡ sorted(xs)[:k].
   Both return the k smallest elements in sorted order.

2. heapq_nlargest(k, xs) ≡ sorted_rev_slice_k(xs, k)
   heapq.nlargest(k, xs) ≡ sorted(xs, reverse=True)[:k].
   Both return the k largest elements in descending order.

3. bisect_insort(xs, x) ≡ append_sort(xs, x)
   bisect.insort(xs, x) ≡ xs.append(x); xs.sort().
   Both insert x maintaining sorted order.

4. heapq_merge(seqs) ≡ sorted_chain(seqs)
   heapq.merge(*seqs) ≡ sorted(chain(*seqs)).
   Both produce a sorted iterator from sorted inputs.

5. heapq_push(h, v) ≡ list_append_sort(h, v)
   heapq.heappush(h, v) ≡ h.append(v); h.sort().
   Both add v maintaining the heap/sorted invariant.

6. heapq_pop(h) ≡ sorted_pop_first(h)
   heapq.heappop(h) ≡ h.sort(); h.pop(0).
   Both remove and return the smallest element.

7. bisect_left(xs, x) ≡ binary_search(xs, x)
   bisect.bisect_left(xs, x) is equivalent to a manual
   binary search loop finding the leftmost insertion point.

8. heapq_pushpop(h, v) ≡ push_then_pop(h, v)
   heapq.heappushpop(h, v) ≡ heappush(h, v); heappop(h).
   Push then pop in one optimised step.

9. heapq_replace(h, v) ≡ pop_then_push(h, v)
   heapq.heapreplace(h, v) ≡ old = heappop(h); heappush(h, v); old.
   Pop then push in one optimised step.

10. priority_queue(ops) ≡ heapq_operations(ops)
    queue.PriorityQueue wraps heapq with thread safety.
"""

EXAMPLES = [
    ("heapq_nsmallest($k, $xs)", "sorted_slice_k($xs, $k)",
     "P44_nsmallest_to_sorted_slice"),
    ("heapq_nlargest($k, $xs)", "sorted_rev_slice_k($xs, $k)",
     "P44_nlargest_to_sorted_rev_slice"),
    ("bisect_insort($xs, $x)", "append_sort($xs, $x)",
     "P44_insort_to_append_sort"),
    ("heapq_merge($seqs)", "sorted_chain($seqs)",
     "P44_merge_to_sorted_chain"),
    ("bisect_left($xs, $x)", "binary_search($xs, $x)",
     "P44_bisect_to_binary_search"),
]

_HEAP_BISECT_OPS = frozenset({
    'heapq_nsmallest', 'sorted_slice_k', 'heapq_nlargest',
    'sorted_rev_slice_k', 'bisect_insort', 'append_sort',
    'heapq_merge', 'sorted_chain', 'heapq_push', 'list_append_sort',
    'heapq_pop', 'sorted_pop_first', 'bisect_left', 'binary_search',
    'heapq_pushpop', 'push_then_pop', 'heapq_replace', 'pop_then_push',
    'priority_queue', 'heapq_operations',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P44: Heap/bisect equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. heapq_nsmallest(k, xs) ↔ sorted_slice_k(xs, k) ──
    if term.name == 'heapq_nsmallest' and len(term.args) == 2:
        k, xs = term.args
        results.append((
            OOp('sorted_slice_k', (xs, k)),
            'P44_nsmallest_to_sorted_slice',
        ))

    if term.name == 'sorted_slice_k' and len(term.args) == 2:
        xs, k = term.args
        results.append((
            OOp('heapq_nsmallest', (k, xs)),
            'P44_sorted_slice_to_nsmallest',
        ))

    # ── 2. heapq_nlargest(k, xs) ↔ sorted_rev_slice_k(xs, k) ──
    if term.name == 'heapq_nlargest' and len(term.args) == 2:
        k, xs = term.args
        results.append((
            OOp('sorted_rev_slice_k', (xs, k)),
            'P44_nlargest_to_sorted_rev_slice',
        ))

    if term.name == 'sorted_rev_slice_k' and len(term.args) == 2:
        xs, k = term.args
        results.append((
            OOp('heapq_nlargest', (k, xs)),
            'P44_sorted_rev_slice_to_nlargest',
        ))

    # ── 3. bisect_insort(xs, x) ↔ append_sort(xs, x) ──
    if term.name == 'bisect_insort' and len(term.args) == 2:
        results.append((
            OOp('append_sort', term.args),
            'P44_insort_to_append_sort',
        ))

    if term.name == 'append_sort' and len(term.args) == 2:
        results.append((
            OOp('bisect_insort', term.args),
            'P44_append_sort_to_insort',
        ))

    # ── 4. heapq_merge(seqs) ↔ sorted_chain(seqs) ──
    if term.name == 'heapq_merge' and len(term.args) >= 1:
        results.append((
            OOp('sorted_chain', term.args),
            'P44_merge_to_sorted_chain',
        ))

    if term.name == 'sorted_chain' and len(term.args) >= 1:
        results.append((
            OOp('heapq_merge', term.args),
            'P44_sorted_chain_to_merge',
        ))

    # ── 5. heapq_push(h, v) ↔ list_append_sort(h, v) ──
    if term.name == 'heapq_push' and len(term.args) == 2:
        results.append((
            OOp('list_append_sort', term.args),
            'P44_push_to_append_sort',
        ))

    if term.name == 'list_append_sort' and len(term.args) == 2:
        results.append((
            OOp('heapq_push', term.args),
            'P44_append_sort_to_push',
        ))

    # ── 6. heapq_pop(h) ↔ sorted_pop_first(h) ──
    if term.name == 'heapq_pop' and len(term.args) == 1:
        results.append((
            OOp('sorted_pop_first', term.args),
            'P44_pop_to_sorted_pop_first',
        ))

    if term.name == 'sorted_pop_first' and len(term.args) == 1:
        results.append((
            OOp('heapq_pop', term.args),
            'P44_sorted_pop_first_to_pop',
        ))

    # ── 7. bisect_left(xs, x) ↔ binary_search(xs, x) ──
    if term.name == 'bisect_left' and len(term.args) == 2:
        results.append((
            OOp('binary_search', term.args),
            'P44_bisect_to_binary_search',
        ))

    if term.name == 'binary_search' and len(term.args) == 2:
        results.append((
            OOp('bisect_left', term.args),
            'P44_binary_search_to_bisect',
        ))

    # ── 8. heapq_pushpop(h, v) ↔ push_then_pop(h, v) ──
    if term.name == 'heapq_pushpop' and len(term.args) == 2:
        results.append((
            OOp('push_then_pop', term.args),
            'P44_pushpop_to_push_then_pop',
        ))

    if term.name == 'push_then_pop' and len(term.args) == 2:
        results.append((
            OOp('heapq_pushpop', term.args),
            'P44_push_then_pop_to_pushpop',
        ))

    # ── 9. heapq_replace(h, v) ↔ pop_then_push(h, v) ──
    if term.name == 'heapq_replace' and len(term.args) == 2:
        results.append((
            OOp('pop_then_push', term.args),
            'P44_replace_to_pop_then_push',
        ))

    if term.name == 'pop_then_push' and len(term.args) == 2:
        results.append((
            OOp('heapq_replace', term.args),
            'P44_pop_then_push_to_replace',
        ))

    # ── 10. priority_queue(ops) ↔ heapq_operations(ops) ──
    if term.name == 'priority_queue' and len(term.args) >= 1:
        results.append((
            OOp('heapq_operations', term.args),
            'P44_pq_to_heapq_operations',
        ))

    if term.name == 'heapq_operations' and len(term.args) >= 1:
        results.append((
            OOp('priority_queue', term.args),
            'P44_heapq_operations_to_pq',
        ))

    # ── 11. heapq_nsmallest(1, xs) → OOp('min_fn', (xs,)) ──
    if term.name == 'heapq_nsmallest' and len(term.args) == 2:
        k, xs = term.args
        if isinstance(k, OLit) and k.value == 1:
            results.append((
                OOp('min_fn', (xs,)),
                'P44_nsmallest_1_to_min',
            ))

    # ── 12. heapq_nlargest(1, xs) → OOp('max_fn', (xs,)) ──
    if term.name == 'heapq_nlargest' and len(term.args) == 2:
        k, xs = term.args
        if isinstance(k, OLit) and k.value == 1:
            results.append((
                OOp('max_fn', (xs,)),
                'P44_nlargest_1_to_max',
            ))

    # ── 13. bisect_left → OFix (binary search loop) structural ──
    if term.name == 'bisect_left' and len(term.args) == 2:
        xs, x = term.args
        results.append((
            OFix('bs', OCase(
                OOp('lt', (OVar('lo'), OVar('hi'))),
                OCase(
                    OOp('lt', (OOp('getitem', (xs, OVar('mid'))), x)),
                    OOp('bs', (OOp('add', (OVar('mid'), OLit(1))), OVar('hi'))),
                    OOp('bs', (OVar('lo'), OVar('mid'))),
                ),
                OVar('lo'),
            )),
            'P44_bisect_to_loop',
        ))

    # ── 14. heapq_pushpop → OCase optimisation ──
    if term.name == 'heapq_pushpop' and len(term.args) == 2:
        h, v = term.args
        results.append((
            OCase(
                OOp('and', (OOp('len', (h,)), OOp('lt', (OOp('getitem', (h, OLit(0))), v)))),
                OOp('heapq_replace', (h, v)),
                v,
            ),
            'P44_pushpop_to_case',
        ))

    # ── 15. heapq_merge → OFold structural form ──
    if term.name == 'heapq_merge' and len(term.args) >= 1:
        results.append((
            OFold('merge_sorted', OSeq(()), OSeq(term.args)),
            'P44_merge_to_fold',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (naive sort → heapq/bisect form)."""
    inverse_labels = {
        'P44_sorted_slice_to_nsmallest', 'P44_sorted_rev_slice_to_nlargest',
        'P44_append_sort_to_insort', 'P44_sorted_chain_to_merge',
        'P44_append_sort_to_push', 'P44_sorted_pop_first_to_pop',
        'P44_binary_search_to_bisect', 'P44_push_then_pop_to_pushpop',
        'P44_pop_then_push_to_replace', 'P44_heapq_operations_to_pq',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a heap/bisect op."""
    if isinstance(term, OOp) and term.name in _HEAP_BISECT_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('heapq_nsmallest', 'sorted_slice_k', 'heapq_nlargest',
               'sorted_rev_slice_k', 'bisect_insort', 'append_sort',
               'heapq_merge', 'sorted_chain', 'heapq_push',
               'list_append_sort', 'heapq_pop', 'sorted_pop_first',
               'bisect_left', 'binary_search', 'heapq_pushpop',
               'push_then_pop', 'heapq_replace', 'pop_then_push',
               'priority_queue', 'heapq_operations'):
        if kw in sc and kw in tc:
            return 0.9
    if ('heapq_nsmallest' in sc and 'sorted_slice' in tc) or \
       ('sorted_slice' in sc and 'heapq_nsmallest' in tc):
        return 0.85
    if ('heapq_nlargest' in sc and 'sorted_rev' in tc) or \
       ('sorted_rev' in sc and 'heapq_nlargest' in tc):
        return 0.85
    if ('bisect_insort' in sc and 'append_sort' in tc) or \
       ('append_sort' in sc and 'bisect_insort' in tc):
        return 0.85
    if ('heapq_merge' in sc and 'sorted_chain' in tc) or \
       ('sorted_chain' in sc and 'heapq_merge' in tc):
        return 0.85
    if ('bisect_left' in sc and 'binary_search' in tc) or \
       ('binary_search' in sc and 'bisect_left' in tc):
        return 0.8
    if any(k in sc for k in ('heapq', 'bisect', 'sorted_slice',
                             'sorted_rev', 'binary_search',
                             'priority_queue')):
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

    # 1. heapq_nsmallest → sorted_slice_k
    t = OOp('heapq_nsmallest', (OLit(3), OVar('xs')))
    r = apply(t)
    _assert(any(l == 'P44_nsmallest_to_sorted_slice' for _, l in r),
            "nsmallest → sorted_slice")

    # 2. sorted_slice_k → heapq_nsmallest
    t2 = OOp('sorted_slice_k', (OVar('xs'), OLit(3)))
    r2 = apply(t2)
    _assert(any(l == 'P44_sorted_slice_to_nsmallest' for _, l in r2),
            "sorted_slice → nsmallest")

    # 3. heapq_nlargest → sorted_rev_slice_k
    t3 = OOp('heapq_nlargest', (OLit(5), OVar('xs')))
    r3 = apply(t3)
    _assert(any(l == 'P44_nlargest_to_sorted_rev_slice' for _, l in r3),
            "nlargest → sorted_rev_slice")

    # 4. sorted_rev_slice_k → heapq_nlargest
    t4 = OOp('sorted_rev_slice_k', (OVar('xs'), OLit(5)))
    r4 = apply(t4)
    _assert(any(l == 'P44_sorted_rev_slice_to_nlargest' for _, l in r4),
            "sorted_rev_slice → nlargest")

    # 5. bisect_insort → append_sort
    t5 = OOp('bisect_insort', (OVar('xs'), OVar('x')))
    r5 = apply(t5)
    _assert(any(l == 'P44_insort_to_append_sort' for _, l in r5),
            "insort → append_sort")

    # 6. append_sort → bisect_insort
    t6 = OOp('append_sort', (OVar('xs'), OVar('x')))
    r6 = apply(t6)
    _assert(any(l == 'P44_append_sort_to_insort' for _, l in r6),
            "append_sort → insort")

    # 7. heapq_merge → sorted_chain
    t7 = OOp('heapq_merge', (OVar('a'), OVar('b')))
    r7 = apply(t7)
    _assert(any(l == 'P44_merge_to_sorted_chain' for _, l in r7),
            "merge → sorted_chain")

    # 8. sorted_chain → heapq_merge
    t8 = OOp('sorted_chain', (OVar('a'), OVar('b')))
    r8 = apply(t8)
    _assert(any(l == 'P44_sorted_chain_to_merge' for _, l in r8),
            "sorted_chain → merge")

    # 9. heapq_push → list_append_sort
    t9 = OOp('heapq_push', (OVar('h'), OVar('v')))
    r9 = apply(t9)
    _assert(any(l == 'P44_push_to_append_sort' for _, l in r9),
            "push → append_sort")

    # 10. list_append_sort → heapq_push
    t10 = OOp('list_append_sort', (OVar('h'), OVar('v')))
    r10 = apply(t10)
    _assert(any(l == 'P44_append_sort_to_push' for _, l in r10),
            "append_sort → push")

    # 11. heapq_pop → sorted_pop_first
    t11 = OOp('heapq_pop', (OVar('h'),))
    r11 = apply(t11)
    _assert(any(l == 'P44_pop_to_sorted_pop_first' for _, l in r11),
            "pop → sorted_pop_first")

    # 12. sorted_pop_first → heapq_pop
    t12 = OOp('sorted_pop_first', (OVar('h'),))
    r12 = apply(t12)
    _assert(any(l == 'P44_sorted_pop_first_to_pop' for _, l in r12),
            "sorted_pop_first → pop")

    # 13. bisect_left → binary_search
    t13 = OOp('bisect_left', (OVar('xs'), OVar('x')))
    r13 = apply(t13)
    _assert(any(l == 'P44_bisect_to_binary_search' for _, l in r13),
            "bisect → binary_search")

    # 14. binary_search → bisect_left
    t14 = OOp('binary_search', (OVar('xs'), OVar('x')))
    r14 = apply(t14)
    _assert(any(l == 'P44_binary_search_to_bisect' for _, l in r14),
            "binary_search → bisect")

    # 15. heapq_pushpop → push_then_pop
    t15 = OOp('heapq_pushpop', (OVar('h'), OVar('v')))
    r15 = apply(t15)
    _assert(any(l == 'P44_pushpop_to_push_then_pop' for _, l in r15),
            "pushpop → push_then_pop")

    # 16. push_then_pop → heapq_pushpop
    t16 = OOp('push_then_pop', (OVar('h'), OVar('v')))
    r16 = apply(t16)
    _assert(any(l == 'P44_push_then_pop_to_pushpop' for _, l in r16),
            "push_then_pop → pushpop")

    # 17. heapq_replace → pop_then_push
    t17 = OOp('heapq_replace', (OVar('h'), OVar('v')))
    r17 = apply(t17)
    _assert(any(l == 'P44_replace_to_pop_then_push' for _, l in r17),
            "replace → pop_then_push")

    # 18. pop_then_push → heapq_replace
    t18 = OOp('pop_then_push', (OVar('h'), OVar('v')))
    r18 = apply(t18)
    _assert(any(l == 'P44_pop_then_push_to_replace' for _, l in r18),
            "pop_then_push → replace")

    # 19. priority_queue → heapq_operations
    t19 = OOp('priority_queue', (OVar('ops'),))
    r19 = apply(t19)
    _assert(any(l == 'P44_pq_to_heapq_operations' for _, l in r19),
            "pq → heapq_operations")

    # 20. heapq_operations → priority_queue
    t20 = OOp('heapq_operations', (OVar('ops'),))
    r20 = apply(t20)
    _assert(any(l == 'P44_heapq_operations_to_pq' for _, l in r20),
            "heapq_operations → pq")

    # 21. heapq_nsmallest(1, xs) → min_fn
    t21 = OOp('heapq_nsmallest', (OLit(1), OVar('xs')))
    r21 = apply(t21)
    _assert(any(l == 'P44_nsmallest_1_to_min' for _, l in r21),
            "nsmallest(1) → min")

    # 22. heapq_nlargest(1, xs) → max_fn
    t22 = OOp('heapq_nlargest', (OLit(1), OVar('xs')))
    r22 = apply(t22)
    _assert(any(l == 'P44_nlargest_1_to_max' for _, l in r22),
            "nlargest(1) → max")

    # 23. bisect_left → OFix structural
    _assert(any(l == 'P44_bisect_to_loop' for _, l in r13),
            "bisect → loop structural")
    loop_results = [(t, l) for t, l in r13 if l == 'P44_bisect_to_loop']
    if loop_results:
        _assert(isinstance(loop_results[0][0], OFix),
                "bisect produces OFix")
    else:
        _assert(False, "bisect produces OFix")

    # 24. heapq_pushpop → OCase structural
    _assert(any(l == 'P44_pushpop_to_case' for _, l in r15),
            "pushpop → case structural")
    case_results = [(t, l) for t, l in r15 if l == 'P44_pushpop_to_case']
    if case_results:
        _assert(isinstance(case_results[0][0], OCase),
                "pushpop produces OCase")
    else:
        _assert(False, "pushpop produces OCase")

    # 25. heapq_merge → OFold structural
    _assert(any(l == 'P44_merge_to_fold' for _, l in r7),
            "merge → fold structural")
    fold_results = [(t, l) for t, l in r7 if l == 'P44_merge_to_fold']
    if fold_results:
        _assert(isinstance(fold_results[0][0], OFold),
                "merge produces OFold")
    else:
        _assert(False, "merge produces OFold")

    # 26. inverse: sorted_slice → nsmallest
    r26_inv = apply_inverse(OOp('sorted_slice_k', (OVar('xs'), OLit(3))))
    _assert(any(l == 'P44_sorted_slice_to_nsmallest' for _, l in r26_inv),
            "inv: sorted_slice → nsmallest")

    # 27. inverse: append_sort → insort
    r27_inv = apply_inverse(OOp('append_sort', (OVar('xs'), OVar('x'))))
    _assert(any(l == 'P44_append_sort_to_insort' for _, l in r27_inv),
            "inv: append_sort → insort")

    # 28. inverse: binary_search → bisect
    r28_inv = apply_inverse(OOp('binary_search', (OVar('xs'), OVar('x'))))
    _assert(any(l == 'P44_binary_search_to_bisect' for _, l in r28_inv),
            "inv: binary_search → bisect")

    # 29. recognizes heap/bisect ops
    _assert(recognizes(OOp('heapq_nsmallest', (OLit(3), OVar('xs')))),
            "recognizes heapq_nsmallest")
    _assert(recognizes(OOp('bisect_left', (OVar('xs'), OVar('x')))),
            "recognizes bisect_left")
    _assert(recognizes(OOp('priority_queue', (OVar('ops'),))),
            "recognizes priority_queue")
    _assert(not recognizes(OLit(42)), "!recognizes literal")
    _assert(not recognizes(OVar('x')), "!recognizes var")

    # 30. relevance: nsmallest ↔ sorted_slice high
    _assert(relevance_score(
        OOp('heapq_nsmallest', (OLit(3), OVar('xs'))),
        OOp('sorted_slice_k', (OVar('xs'), OLit(3))),
    ) > 0.7, "nsmallest/sorted_slice relevance high")

    # 31. relevance: bisect ↔ binary_search high
    _assert(relevance_score(
        OOp('bisect_left', (OVar('xs'), OVar('x'))),
        OOp('binary_search', (OVar('xs'), OVar('x'))),
    ) > 0.7, "bisect/binary_search relevance high")

    # 32. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    # 33. no rewrites for non-OOp
    _assert(apply(OVar('x')) == [], "no rewrites for OVar")
    _assert(apply(OLit(42)) == [], "no rewrites for OLit")

    print(f"P44 heap_bisect: {_pass} passed, {_fail} failed")
