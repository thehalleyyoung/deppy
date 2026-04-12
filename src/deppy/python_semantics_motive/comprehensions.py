"""Interpretation of Python comprehensions in the motive framework.

List/dict/set/generator comprehensions are typed operations that combine
iteration, filtering, and mapping in a single construct.
"""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

# ── Comprehension operations ─────────────────────────────────────

COMPREHENSION_OPS = {
    'listcomp': ('Comprehension.collect', (Sort.ITER,), Sort.SEQ,
                 frozenset({Refinement.MAPPED}), Effect.ALLOCATE),
    'setcomp': ('Comprehension.collect_set', (Sort.ITER,), Sort.SET,
                frozenset({Refinement.MAPPED}), Effect.ALLOCATE),
    'dictcomp': ('Comprehension.collect_map', (Sort.ITER,), Sort.MAP,
                 frozenset({Refinement.MAPPED}), Effect.ALLOCATE),
    'genexpr': ('Comprehension.lazy', (Sort.ITER,), Sort.ITER,
                frozenset({Refinement.MAPPED}), Effect.PURE),

    # Sub-operations within comprehensions
    'iterate': ('Comprehension.iterate', (Sort.ITER,), Sort.TOP,
                frozenset(), Effect.ITERATE),
    'filter': ('Comprehension.filter', (Sort.BOOL,), Sort.BOOL,
               frozenset({Refinement.FILTERED}), Effect.PURE),
    'nested': ('Comprehension.nested', (Sort.ITER,), Sort.TOP,
               frozenset(), Effect.ITERATE),
    'transform': ('Comprehension.transform', (Sort.TOP,), Sort.TOP,
                  frozenset({Refinement.MAPPED}), Effect.PURE),
}
