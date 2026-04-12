"""Interpretation of Python itertools module in the motive framework.

Every itertools function is mapped to a TypedOp with precise sorts.
"""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

ITERTOOLS_OPS = {
    # Infinite iterators
    'count': ('Iter.count', (Sort.NUM,), Sort.ITER, frozenset(), Effect.PURE),
    'cycle': ('Iter.cycle', (Sort.ITER,), Sort.ITER, frozenset(), Effect.PURE),
    'repeat': ('Iter.repeat', (Sort.TOP,), Sort.ITER, frozenset(), Effect.PURE),

    # Terminating iterators
    'accumulate': ('Iter.accumulate', (Sort.ITER,), Sort.ITER,
                   frozenset({Refinement.MAPPED}), Effect.PURE),
    'chain': ('Iter.chain', (Sort.ITER,), Sort.ITER,
              frozenset({Refinement.ASSOCIATIVE}), Effect.PURE),
    'chain_from_iterable': ('Iter.chain', (Sort.ITER,), Sort.ITER,
                            frozenset({Refinement.ASSOCIATIVE}), Effect.PURE),
    'compress': ('Iter.compress', (Sort.ITER, Sort.ITER), Sort.ITER,
                 frozenset({Refinement.FILTERED}), Effect.PURE),
    'dropwhile': ('Iter.dropwhile', (Sort.FUNC, Sort.ITER), Sort.ITER,
                  frozenset({Refinement.FILTERED}), Effect.PURE),
    'filterfalse': ('Iter.filterfalse', (Sort.FUNC, Sort.ITER), Sort.ITER,
                    frozenset({Refinement.FILTERED}), Effect.PURE),
    'groupby': ('Iter.groupby', (Sort.ITER,), Sort.ITER, frozenset(), Effect.PURE),
    'islice': ('Iter.islice', (Sort.ITER, Sort.NUM), Sort.ITER, frozenset(), Effect.PURE),
    'pairwise': ('Iter.pairwise', (Sort.ITER,), Sort.ITER, frozenset(), Effect.PURE),
    'starmap': ('Iter.starmap', (Sort.FUNC, Sort.ITER), Sort.ITER,
                frozenset({Refinement.MAPPED}), Effect.PURE),
    'takewhile': ('Iter.takewhile', (Sort.FUNC, Sort.ITER), Sort.ITER,
                  frozenset({Refinement.FILTERED}), Effect.PURE),
    'tee': ('Iter.tee', (Sort.ITER, Sort.NUM), Sort.SEQ, frozenset(), Effect.PURE),
    'zip_longest': ('Iter.zip_longest', (Sort.ITER,), Sort.ITER, frozenset(), Effect.PURE),
    'batched': ('Iter.batched', (Sort.ITER, Sort.NUM), Sort.ITER, frozenset(), Effect.PURE),

    # Combinatoric iterators
    'product': ('Iter.product', (Sort.ITER,), Sort.ITER,
                frozenset({Refinement.COMMUTATIVE}), Effect.PURE),
    'permutations': ('Iter.permutations', (Sort.ITER,), Sort.ITER, frozenset(), Effect.PURE),
    'combinations': ('Iter.combinations', (Sort.ITER, Sort.NUM), Sort.ITER,
                     frozenset({Refinement.SORTED}), Effect.PURE),
    'combinations_with_replacement': ('Iter.combinations_wr', (Sort.ITER, Sort.NUM), Sort.ITER,
                                      frozenset({Refinement.SORTED}), Effect.PURE),
}
