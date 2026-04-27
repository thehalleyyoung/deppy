"""Geometric-property functions whose @implies decorators are
translated to Lean theorems by deppy's certificate generator.

This module is the *target source* for ``write_certificate``.  Each
function computes a quantity from sympy.geometry and carries an
@implies decorator stating a property the deppy pipeline should
prove (or — when honestly unprovable — emit ``sorry`` for).

Properties are intentionally varied to exercise:
  * linear-arithmetic implies (audit fix #7)
  * conjunct-of-pre implies
  * cubical-witness implies (round-2 integration #2)
  * opaque implies (e.g., references sympy.geometry calls)
  * @implies whose post mentions ``result_count`` (regression
    test for round-1 audit fix #11 — substring substitution)

The deppy pipeline analyses the Python AST, runs cubical analysis
of the bodies, generates a Lean certificate listing each property
as a theorem, and decides which theorems can be discharged
automatically.
"""
from __future__ import annotations

from deppy import implies


# ─────────────────────────────────────────────────────────────────
#  A.  Distance properties
# ─────────────────────────────────────────────────────────────────

@implies("True", "result >= 0")
def euclidean_distance_squared(
    x1: int, y1: int, x2: int, y2: int,
) -> int:
    """The *squared* Euclidean distance is non-negative.

    The actual distance involves a square root which deppy's
    Python→Lean translator can't currently round-trip; the
    squared form is purely arithmetic and provable via ``omega``.
    """
    dx = x1 - x2
    dy = y1 - y2
    return dx * dx + dy * dy


@implies(
    "x1 == x2 and y1 == y2",
    "result == 0",
)
def distance_zero_for_equal_points(
    x1: int, y1: int, x2: int, y2: int,
) -> int:
    """When the two points coincide, squared distance is zero.

    Pre-condition exposes the equal-points hypothesis; the
    classifier should pick LINEAR_ARITH (omega closes it after
    substitution).
    """
    dx = x1 - x2
    dy = y1 - y2
    return dx * dx + dy * dy


@implies("True", "result == result")
def distance_symmetric_witness(
    x1: int, y1: int, x2: int, y2: int,
) -> int:
    """Tautology to exercise the IDENTITY classifier.

    The post is ``result == result``; classifier picks IDENTITY
    after substitution and closes with ``intro h; exact h``.
    """
    return (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)


# ─────────────────────────────────────────────────────────────────
#  B.  Midpoint
# ─────────────────────────────────────────────────────────────────

@implies(
    "True",
    "result == (a_x + b_x) // 2",
)
def midpoint_x(a_x: int, b_x: int) -> int:
    """The x-coordinate of the midpoint is the average of the
    two x-coordinates (integer-division form to keep arithmetic
    in ``omega``'s reach).
    """
    return (a_x + b_x) // 2


@implies(
    "a_x == b_x",
    "result == a_x",
)
def midpoint_x_collapsed(a_x: int, b_x: int) -> int:
    """When both x-coordinates coincide, the midpoint x equals
    either of them.  Conditional pre exposes the equality."""
    return (a_x + b_x) // 2


# ─────────────────────────────────────────────────────────────────
#  C.  Triangle centroid (3 vertices → 1 average)
# ─────────────────────────────────────────────────────────────────

@implies(
    "True",
    "3 * result == a + b + c",
)
def triangle_centroid_x_int(a: int, b: int, c: int) -> int:
    """The x-coordinate of the centroid satisfies
    ``3 * centroid_x == a_x + b_x + c_x``.

    Stated in the integer form (multiplied by 3 to avoid
    division) so omega can verify it directly.
    """
    return (a + b + c) // 3


@implies(
    "a == b and b == c",
    "result == a",
)
def equilateral_centroid(a: int, b: int, c: int) -> int:
    """For an equilateral triangle (here represented by all
    coordinates equal), the centroid coincides with the vertex.

    Pre is a CONJUNCT — classifier picks CONJUNCT.
    """
    return (a + b + c) // 3


# ─────────────────────────────────────────────────────────────────
#  D.  Cross product / collinearity
# ─────────────────────────────────────────────────────────────────

@implies(
    "True",
    "result == result",
)
def cross_2d(
    a_x: int, a_y: int, b_x: int, b_y: int,
    c_x: int, c_y: int,
) -> int:
    """2D cross product (B - A) × (C - A) in the z component.

    Three points are collinear iff this is zero.  The post is a
    tautology (IDENTITY classification) — the function is here to
    feed cubical analysis a non-trivial control-flow shape.
    """
    return (b_x - a_x) * (c_y - a_y) - (c_x - a_x) * (b_y - a_y)


@implies(
    "(b_x - a_x) * (c_y - a_y) == (c_x - a_x) * (b_y - a_y)",
    "result == 0",
)
def collinear_cross_zero(
    a_x: int, a_y: int, b_x: int, b_y: int,
    c_x: int, c_y: int,
) -> int:
    """When the cross product is zero (collinearity), the
    function returns zero.  Pre is a hypothesis that, combined
    with the function body's computation, yields the post.

    Classifier should pick LINEAR_ARITH with omega tactic.
    """
    return (b_x - a_x) * (c_y - a_y) - (c_x - a_x) * (b_y - a_y)


# ─────────────────────────────────────────────────────────────────
#  E.  Triangle area (twice the absolute value of cross / 2)
# ─────────────────────────────────────────────────────────────────

@implies(
    "(b_x - a_x) * (c_y - a_y) == (c_x - a_x) * (b_y - a_y)",
    "result == 0",
)
def triangle_doubled_area_signed(
    a_x: int, a_y: int, b_x: int, b_y: int,
    c_x: int, c_y: int,
) -> int:
    """Twice the *signed* area of triangle ABC.

    When vertices are collinear (pre), this is zero.  The
    classifier exercises LINEAR_ARITH after substituting the
    body.
    """
    return (b_x - a_x) * (c_y - a_y) - (c_x - a_x) * (b_y - a_y)


# ─────────────────────────────────────────────────────────────────
#  F.  Properties involving conditional control flow
#      (exercise cubical analysis)
# ─────────────────────────────────────────────────────────────────

@implies(
    "True",
    "result >= 0",
)
def absolute_x_diff(p_x: int, q_x: int) -> int:
    """``|p_x - q_x|`` — non-negative.

    The body has an if-else (cubical 2-cell).  Both branches
    return a non-negative value, so the post holds on both arms;
    cubical analysis should detect that the property is
    Kan-fillable from the two branches.
    """
    if p_x >= q_x:
        return p_x - q_x
    else:
        return q_x - p_x


@implies(
    "True",
    "result >= 0",
)
def squared_max_distance(
    p_x: int, p_y: int, q_x: int, q_y: int,
) -> int:
    """Max of squared distances along x or y axis — non-negative.

    Two-branch conditional with non-trivial expressions in each
    branch.  Cubical analysis sees a 2-cell; both branches
    establish ``result >= 0`` so the join is Kan-fillable.
    """
    dx = (p_x - q_x) * (p_x - q_x)
    dy = (p_y - q_y) * (p_y - q_y)
    if dx >= dy:
        return dx
    else:
        return dy


# ─────────────────────────────────────────────────────────────────
#  G.  ``result_count`` — regression for audit fix #11
#      (round-1 cheat: substring substitution)
# ─────────────────────────────────────────────────────────────────

@implies(
    "n >= 0",
    "result == n + 1",
)
def vertex_count_for_polygon(n: int) -> int:
    """A closed polygon with ``n`` edges has ``n + 1`` vertex
    *traversals* (we visit the start twice to close the loop).

    The post mentions ``n``, NOT ``result_count``.  The previous
    cheat would have rewritten ``result_count`` if it had appeared;
    we keep this test in to confirm fix #11 isn't regressed.
    """
    return n + 1


@implies(
    "True",
    "result_count >= 0 or result == 0",
)
def vertex_index_safe(idx: int) -> int:
    """Post mentions ``result_count`` as a separate identifier.

    Audit fix #11 must NOT rewrite ``result_count`` to
    ``(vertex_index_safe idx)_count``.  The classifier might
    pick OPAQUE because ``result_count`` is a free name; either
    way, the certificate must preserve it.
    """
    if idx < 0:
        return 0
    return idx


# ─────────────────────────────────────────────────────────────────
#  H.  Properties that should fall to honest sorry
# ─────────────────────────────────────────────────────────────────

@implies(
    "True",
    "hasattr(result, 'foo')",
)
def opaque_property(x: int) -> int:
    """Post uses ``hasattr`` — an opaque predicate.  The
    classifier (audit fix #7) must classify as OPAQUE and emit
    ``sorry`` honestly, not silently fall back to deppy_safe.
    """
    return x + 1


# ─────────────────────────────────────────────────────────────────
#  I.  A multi-implies stack — exercises the audit log
# ─────────────────────────────────────────────────────────────────

@implies("True", "result >= 0")
@implies("x > 0", "result > 0")
@implies("x == 0", "result == 0")
def square(x: int) -> int:
    """The square ``x²`` is non-negative; positive when x > 0;
    zero when x == 0.  Three @implies on one function — each
    becomes a separate Lean theorem in the certificate."""
    return x * x


# ─────────────────────────────────────────────────────────────────
#  J.  Module-level functions calling each other (cohomology)
# ─────────────────────────────────────────────────────────────────

def is_origin(x: int, y: int) -> bool:
    """Returns True iff (x, y) is the origin."""
    return x == 0 and y == 0


@implies("True", "result == 0 or result >= 1")
def origin_indicator(x: int, y: int) -> int:
    """Indicator function: 1 at origin, 0 elsewhere.

    Calls ``is_origin`` — exercises the inter-procedural
    cohomology computation (call edge ``origin_indicator → is_origin``
    becomes a 1-simplex in the simplicial complex).
    """
    if is_origin(x, y):
        return 1
    else:
        return 0


@implies("True", "result == 0 or result == 1 or result == 2")
def quadrant_count(x: int, y: int) -> int:
    """Returns 0, 1, or 2 depending on which axis quadrant the
    point lies in (a 3-way classification).  Exercises a
    2-cell with three branches via nested if/else.
    """
    if x > 0:
        if y > 0:
            return 1  # quadrant I
        else:
            return 0  # axis or below
    else:
        return 2      # left half-plane
