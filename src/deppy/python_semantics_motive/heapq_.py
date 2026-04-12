"""Interpretation of Python heapq module in the motive framework."""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

HEAPQ_OPS = {
    'heappush': ('Heap.push', (Sort.SEQ, Sort.TOP), Sort.NONE,
                 frozenset({Refinement.SORTED}), Effect.MUTATE),
    'heappop': ('Heap.pop', (Sort.SEQ,), Sort.TOP,
                frozenset({Refinement.SORTED}), Effect.MUTATE),
    'heapify': ('Heap.heapify', (Sort.SEQ,), Sort.NONE,
                frozenset({Refinement.SORTED}), Effect.MUTATE),
    'heapreplace': ('Heap.replace', (Sort.SEQ, Sort.TOP), Sort.TOP,
                    frozenset({Refinement.SORTED}), Effect.MUTATE),
    'heappushpop': ('Heap.pushpop', (Sort.SEQ, Sort.TOP), Sort.TOP,
                    frozenset({Refinement.SORTED}), Effect.MUTATE),
    'merge': ('Heap.merge', (Sort.ITER,), Sort.ITER,
              frozenset({Refinement.SORTED}), Effect.PURE),
    'nlargest': ('Heap.nlargest', (Sort.NUM, Sort.ITER), Sort.SEQ,
                 frozenset({Refinement.SORTED}), Effect.PURE),
    'nsmallest': ('Heap.nsmallest', (Sort.NUM, Sort.ITER), Sort.SEQ,
                  frozenset({Refinement.SORTED}), Effect.PURE),
}
