"""Interpretation of Python re module in the motive framework."""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

RE_OPS = {
    # Pattern compilation
    'compile': ('Re.compile', (Sort.STR,), Sort.TOP, frozenset(), Effect.PURE),

    # Matching
    'match': ('Re.match', (Sort.STR, Sort.STR), Sort.TOP, frozenset(), Effect.PURE),
    'fullmatch': ('Re.fullmatch', (Sort.STR, Sort.STR), Sort.TOP, frozenset(), Effect.PURE),
    'search': ('Re.search', (Sort.STR, Sort.STR), Sort.TOP, frozenset(), Effect.PURE),

    # Finding
    'findall': ('Re.findall', (Sort.STR, Sort.STR), Sort.SEQ, frozenset(), Effect.PURE),
    'finditer': ('Re.finditer', (Sort.STR, Sort.STR), Sort.ITER, frozenset(), Effect.PURE),

    # Substitution
    'sub': ('Re.sub', (Sort.STR, Sort.STR, Sort.STR), Sort.STR, frozenset(), Effect.PURE),
    'subn': ('Re.subn', (Sort.STR, Sort.STR, Sort.STR), Sort.SEQ, frozenset(), Effect.PURE),

    # Splitting
    'split': ('Re.split', (Sort.STR, Sort.STR), Sort.SEQ, frozenset(), Effect.PURE),

    # Escaping
    'escape': ('Re.escape', (Sort.STR,), Sort.STR, frozenset({Refinement.IDEMPOTENT}), Effect.PURE),

    # Match object methods
    'group': ('Re.group', (Sort.TOP,), Sort.STR, frozenset(), Effect.PURE),
    'groups': ('Re.groups', (Sort.TOP,), Sort.SEQ, frozenset(), Effect.PURE),
    'groupdict': ('Re.groupdict', (Sort.TOP,), Sort.MAP, frozenset(), Effect.PURE),
    'start': ('Re.start', (Sort.TOP,), Sort.NUM, frozenset(), Effect.PURE),
    'end': ('Re.end', (Sort.TOP,), Sort.NUM, frozenset(), Effect.PURE),
    'span': ('Re.span', (Sort.TOP,), Sort.SEQ, frozenset(), Effect.PURE),
}
