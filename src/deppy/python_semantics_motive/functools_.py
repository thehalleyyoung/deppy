"""Interpretation of Python functools module in the motive framework."""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

FUNCTOOLS_OPS = {
    'reduce': ('Accum.fold', (Sort.FUNC, Sort.ITER), Sort.TOP, frozenset(), Effect.PURE),
    'partial': ('Func.partial', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'partialmethod': ('Func.partial', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'lru_cache': ('Func.memoize', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'cache': ('Func.memoize', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'cached_property': ('Func.memoize', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'wraps': ('Func.wraps', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'update_wrapper': ('Func.wraps', (Sort.FUNC, Sort.FUNC), Sort.FUNC, frozenset(), Effect.MUTATE),
    'total_ordering': ('Type.total_ordering', (Sort.FUNC,), Sort.FUNC,
                       frozenset({Refinement.SORTED}), Effect.PURE),
    'cmp_to_key': ('Func.cmp_to_key', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'singledispatch': ('Func.dispatch', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'singledispatchmethod': ('Func.dispatch', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
}
