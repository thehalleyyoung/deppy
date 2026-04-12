"""Interpretation of Python string methods in the motive framework.

Complete coverage of all str methods with precise sort signatures,
refinement predicates, and effects.
"""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

# Re-export from builtin_types for convenience
from deppy.python_semantics_motive.builtin_types import STR_OPS

# ── Extended string operations ───────────────────────────────────
# Additional string-related operations not covered in STR_OPS

EXTENDED_STR_OPS = {
    # String formatting
    'format_spec': ('Str.format_spec', (Sort.STR, Sort.TOP), Sort.STR, frozenset(), Effect.PURE),
    'percent_format': ('Str.percent_format', (Sort.STR, Sort.TOP), Sort.STR, frozenset(), Effect.PURE),

    # Regex operations on strings
    're_match': ('Str.re_match', (Sort.STR, Sort.STR), Sort.TOP, frozenset(), Effect.PURE),
    're_search': ('Str.re_search', (Sort.STR, Sort.STR), Sort.TOP, frozenset(), Effect.PURE),
    're_findall': ('Str.re_findall', (Sort.STR, Sort.STR), Sort.SEQ, frozenset(), Effect.PURE),
    're_sub': ('Str.re_sub', (Sort.STR, Sort.STR, Sort.STR), Sort.STR, frozenset(), Effect.PURE),
    're_split': ('Str.re_split', (Sort.STR, Sort.STR), Sort.SEQ, frozenset(), Effect.PURE),

    # String concatenation (+ operator on strings)
    'concat': ('Str.concat', (Sort.STR, Sort.STR), Sort.STR, frozenset({Refinement.ASSOCIATIVE}), Effect.PURE),
    'repeat': ('Str.repeat', (Sort.STR, Sort.NUM), Sort.STR, frozenset(), Effect.PURE),

    # String membership
    'contains': ('Str.contains', (Sort.STR, Sort.STR), Sort.BOOL, frozenset(), Effect.PURE),

    # String conversion
    'to_bytes': ('Str.to_bytes', (Sort.STR,), Sort.STR, frozenset(), Effect.PURE),
    'from_bytes': ('Str.from_bytes', (Sort.STR,), Sort.STR, frozenset(), Effect.PURE),
}
