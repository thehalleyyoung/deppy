"""Interpretation of Python copy module in the motive framework."""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

COPY_OPS = {
    'copy': ('Clone.shallow', (Sort.TOP,), Sort.TOP, frozenset(), Effect.ALLOCATE),
    'deepcopy': ('Clone.deep', (Sort.TOP,), Sort.TOP, frozenset(), Effect.ALLOCATE),
}

# IMPORTANT: Clone.shallow and Clone.deep are INCOMPATIBLE operations.
# Shallow copy may share internal references; deep copy never does.
# This distinction is semantically critical for equivalence checking.
