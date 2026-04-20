"""
deppy.heap — Heap-related constructs for Deppy.

Re-exports heap primitives so that ``from deppy.heap import Ref`` works.
"""
from __future__ import annotations

from deppy.separation import (           # noqa: F401
    Ref, SLProp, PointsTo, pts_to, pts_to_frac,
    AttrTo, attr_to, DictEntry, dict_entry,
    ElemAt, elem_at, ArrayPtsTo, array_pts_to,
    SepConj, Wand, wand, Exists, exists,
    Emp, emp, Pure,
)
from deppy.proofs.sugar import requires, ensures  # noqa: F401
