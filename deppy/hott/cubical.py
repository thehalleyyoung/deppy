"""
deppy.hott.cubical — Cubical HoTT primitives.

Provides interval type, face maps, and cubical path operations for
``from deppy.hott.cubical import Interval, PathType, refl, ap``.
"""
from __future__ import annotations

from deppy.core.types import PathType    # noqa: F401
from deppy.core.kernel import (          # noqa: F401
    Refl as refl, Ap as ap, Sym as sym,
    Trans as trans, Cong as cong,
    PathComp as path_comp, FunExt as funext,
)


class Interval:
    """The abstract interval I with endpoints i0 and i1."""
    i0 = 0
    i1 = 1

    @staticmethod
    def connect(a, b):
        """Connection algebra: max/min on the interval."""
        return max(a, b)
