"""Interpretation of Python bisect module in the motive framework."""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

BISECT_OPS = {
    'bisect': ('Search.bisect', (Sort.SEQ, Sort.TOP), Sort.NUM,
               frozenset({Refinement.SORTED}), Effect.PURE),
    'bisect_left': ('Search.bisect_left', (Sort.SEQ, Sort.TOP), Sort.NUM,
                    frozenset({Refinement.SORTED}), Effect.PURE),
    'bisect_right': ('Search.bisect_right', (Sort.SEQ, Sort.TOP), Sort.NUM,
                     frozenset({Refinement.SORTED}), Effect.PURE),
    'insort': ('Search.insort', (Sort.SEQ, Sort.TOP), Sort.NONE,
               frozenset({Refinement.SORTED}), Effect.MUTATE),
    'insort_left': ('Search.insort_left', (Sort.SEQ, Sort.TOP), Sort.NONE,
                    frozenset({Refinement.SORTED}), Effect.MUTATE),
    'insort_right': ('Search.insort_right', (Sort.SEQ, Sort.TOP), Sort.NONE,
                     frozenset({Refinement.SORTED}), Effect.MUTATE),
}
