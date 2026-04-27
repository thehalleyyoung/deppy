"""Example: writing Python with deppy proof decorators inline.

This demonstrates the *dual* of the ``.deppy`` sidecar workflow.
When you're writing a Python module rather than retrofitting proof
metadata onto someone else's code, decorators keep proof annotations
right next to the implementation they describe.

Run via::

    python -m deppy.pipeline.run_verify --from-module \\
        examples.decorated_geometry --out decorated_geometry.lean
"""
from __future__ import annotations

from deppy.proofs.sidecar_decorators import (
    foundation, axiom, verify, spec, psdl_proof, code_type,
)


# ── Foundations: generic mathematical facts ────────────────────────

@foundation
def Real_sqrt_nonneg():
    """sqrt(x) >= 0 when x >= 0"""


@foundation(citation="Pythagoras")
def Real_sqrt_sq_nonneg():
    """sqrt(x)**2 == x when x >= 0"""


@foundation
def Real_add_comm():
    """a + b == b + a"""


@foundation
def Real_sub_sq_swap():
    """(a - b)**2 == (b - a)**2"""


@foundation
def Real_sum_of_squares_nonneg():
    """sum of nonneg terms == 0 iff each term == 0"""


# ── Axioms: claims about the live module's behaviour ──────────────

@axiom(
    target="examples.decorated_geometry.Point.distance",
    statement="Point.distance(p, q) >= 0",
    module="examples",
)
def dist_nonneg():
    """Point.distance is non-negative."""


@axiom(
    target="examples.decorated_geometry.Point.distance",
    statement="Point.distance(p, q) == Point.distance(q, p)",
    module="examples",
)
def dist_symmetric():
    """Point.distance is symmetric."""


# ── Code types — Lean signatures for symbols Z3 can't infer ──────

code_type("sqrt", "Int → Int")(None)
code_type("sum_zip_sub_sq", "Point → Point → Int")(None)


# ── The actual Python class with verify-block annotations ────────

@spec(
    guarantees=[
        "Distance is non-negative.",
        "Distance is symmetric: d(p, q) == d(q, p).",
    ],
    axioms=["dist_nonneg", "dist_symmetric"],
)
class Point:
    """Two-dimensional point with Euclidean distance."""

    def __init__(self, x: int, y: int) -> None:
        self.x = x
        self.y = y

    @verify(
        property="Point.distance(p, q) >= 0",
        via="foundation Real_sqrt_nonneg",
        binders={"p": "Point", "q": "Point"},
    )
    @psdl_proof("""
# value-fibre when ``other`` is a Point: distance reduces to
# ``sqrt(sum_zip_sub_sq(self, other))``.  Z3 dispatches the side
# condition.
if isinstance(other, Point):
    inline(Point.distance, sqrt(sum_zip_sub_sq(self, other)))
    apply(Real_sqrt_nonneg)
    assert sum_zip_sub_sq(self, other) >= 0, "z3"
else:
    raise NotImplementedError
""")
    def distance(self, other):
        # Live implementation — also what the verify block targets.
        from math import sqrt
        if isinstance(other, Point):
            return sqrt(
                (self.x - other.x) ** 2 + (self.y - other.y) ** 2
            )
        raise NotImplementedError

    @verify(
        property="Point.distance(p, q) == Point.distance(q, p)",
        via="foundation Real_sub_sq_swap",
        binders={"p": "Point", "q": "Point"},
    )
    def distance_symmetric(self, other):
        """Symmetric distance."""
        return self.distance(other)
