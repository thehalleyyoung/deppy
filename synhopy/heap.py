"""
synhopy.heap — Heap-related constructs for SynHoPy.

Re-exports heap primitives so that ``from synhopy.heap import Ref`` works.
"""
from __future__ import annotations

from synhopy.separation import (           # noqa: F401
    Ref, SLProp, PointsTo, pts_to, pts_to_frac,
    AttrTo, attr_to, DictEntry, dict_entry,
    ElemAt, elem_at, ArrayPtsTo, array_pts_to,
    SepConj, Wand, wand, Exists, exists,
    Emp, emp, Pure,
)
from synhopy.proofs.sugar import requires, ensures  # noqa: F401
