"""Interpretation of Python collections module in the motive framework.

Counter, OrderedDict, defaultdict, deque, namedtuple, ChainMap.
"""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement
from deppy.python_semantics_motive.builtin_types import DEQUE_OPS, COUNTER_OPS

# ── defaultdict operations ───────────────────────────────────────

DEFAULTDICT_OPS = {
    'default_factory': ('Map.default_factory', (), Sort.TOP, frozenset(), Effect.PURE),
    '__missing__': ('Map.missing', (Sort.TOP,), Sort.TOP, frozenset(), Effect.MUTATE),
    # Inherits all dict operations
}

# ── OrderedDict operations ───────────────────────────────────────

ORDEREDDICT_OPS = {
    'move_to_end': ('Map.move_to_end', (Sort.TOP,), Sort.NONE,
                    frozenset({Refinement.SORTED}), Effect.MUTATE),
    # Inherits all dict operations, with ordering refinement
}

# ── namedtuple operations ────────────────────────────────────────

NAMEDTUPLE_OPS = {
    '_make': ('Seq.namedtuple_make', (Sort.SEQ,), Sort.SEQ, frozenset(), Effect.ALLOCATE),
    '_asdict': ('Seq.namedtuple_asdict', (Sort.SEQ,), Sort.MAP, frozenset(), Effect.PURE),
    '_replace': ('Seq.namedtuple_replace', (Sort.SEQ,), Sort.SEQ, frozenset(), Effect.ALLOCATE),
    '_fields': ('Seq.namedtuple_fields', (Sort.SEQ,), Sort.SEQ, frozenset(), Effect.PURE),
}

# ── ChainMap operations ──────────────────────────────────────────

CHAINMAP_OPS = {
    'new_child': ('Map.chain_new_child', (Sort.MAP,), Sort.MAP, frozenset(), Effect.ALLOCATE),
    'parents': ('Map.chain_parents', (Sort.MAP,), Sort.MAP, frozenset(), Effect.PURE),
    'maps': ('Map.chain_maps', (Sort.MAP,), Sort.SEQ, frozenset(), Effect.PURE),
}

# Collect all collections operations
ALL_COLLECTIONS_OPS = {}
for table in [DEQUE_OPS, COUNTER_OPS, DEFAULTDICT_OPS, ORDEREDDICT_OPS,
              NAMEDTUPLE_OPS, CHAINMAP_OPS]:
    ALL_COLLECTIONS_OPS.update(table)
