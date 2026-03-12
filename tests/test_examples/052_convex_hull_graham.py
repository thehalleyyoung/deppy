"""Graham scan for 2D convex hull.

Bug: sorts by angle using atan2(x, y) instead of atan2(y, x),
sorting by the wrong angle and producing an incorrect hull.
"""

CORRECT = r"""
import math

def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

def dist_sq(a, b):
    return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2

def graham_scan(points):
    if len(points) < 3:
        return list(points)

    # Find the lowest point (and leftmost if tie)
    pivot = min(points, key=lambda p: (p[1], p[0]))

    def angle_key(p):
        if p == pivot:
            return (-4, 0)
        # CORRECT: atan2(y, x) gives the standard angle from positive x-axis
        ang = math.atan2(p[1] - pivot[1], p[0] - pivot[0])
        return (ang, dist_sq(pivot, p))

    sorted_pts = sorted(points, key=angle_key)

    # Build the hull
    hull = []
    for pt in sorted_pts:
        while len(hull) >= 2 and cross(hull[-2], hull[-1], pt) <= 0:
            hull.pop()
        hull.append(pt)

    return hull

points = POINTS
result = graham_scan(points)
"""

BUGGY = r"""
import math

def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

def dist_sq(a, b):
    return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2

def graham_scan(points):
    if len(points) < 3:
        return list(points)

    # Find the lowest point (and leftmost if tie)
    pivot = min(points, key=lambda p: (p[1], p[0]))

    def angle_key(p):
        if p == pivot:
            return (-4, 0)
        # BUG: atan2(x, y) instead of atan2(y, x) -- sorts by wrong angle
        ang = math.atan2(p[0] - pivot[0], p[1] - pivot[1])
        return (ang, dist_sq(pivot, p))

    sorted_pts = sorted(points, key=angle_key)

    # Build the hull
    hull = []
    for pt in sorted_pts:
        while len(hull) >= 2 and cross(hull[-2], hull[-1], pt) <= 0:
            hull.pop()
        hull.append(pt)

    return hull

points = POINTS
result = graham_scan(points)
"""


def SPEC(points, result):
    if not isinstance(result, list):
        return False
    if len(points) < 3:
        return set(map(tuple, result)) == set(map(tuple, points))

    # All hull points must be from input
    pts_set = set(map(tuple, points))
    for p in result:
        if tuple(p) not in pts_set:
            return False

    if len(result) < 3:
        return False

    # Hull must be convex: all cross products same sign (CCW)
    n = len(result)
    for i in range(n):
        o = result[i]
        a = result[(i + 1) % n]
        b = result[(i + 2) % n]
        cp = (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
        if cp < 0:
            return False

    # All input points must be inside or on the hull
    def sign(o, a, p):
        return (a[0] - o[0]) * (p[1] - o[1]) - (a[1] - o[1]) * (p[0] - o[0])

    for p in points:
        inside = True
        for i in range(n):
            o = result[i]
            a = result[(i + 1) % n]
            if sign(o, a, p) < -1e-9:
                inside = False
                break
        if not inside:
            return False

    # No collinear redundant points on the hull
    for i in range(n):
        o = result[i]
        a = result[(i + 1) % n]
        b = result[(i + 2) % n]
        cp = (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
        if abs(cp) < 1e-12:
            return False

    return True


BUG_DESC = (
    "Sorts points by angle using atan2(x, y) instead of atan2(y, x). "
    "This computes the angle from the positive y-axis instead of the "
    "positive x-axis, causing the sweep to visit points in the wrong "
    "order and produce a non-convex or incomplete hull."
)


def _generate_points():
    import random
    # The bug: sorts by atan2(x, y) instead of atan2(y, x). This computes
    # angle from the +y axis instead of +x axis, reversing the sweep order.
    #
    # To trigger: need points in different angular positions around the pivot
    # where atan2(y,x) and atan2(x,y) give different orderings. This happens
    # for any non-trivial point set that isn't symmetric about y=x.
    #
    # Strategy: place points around the lowest point such that the angular
    # orderings differ. Points spread across both sides of the y=x line
    # from the pivot guarantee different orderings.
    #
    # Use small point count (6-8) to stay within max_size.

    # Start with a clear convex configuration where ordering matters
    pivot_y = -5
    points = [(0, pivot_y)]  # This will be the lowest point (pivot)

    # Place points at various angles above the pivot
    # Include points where atan2(y,x) order differs from atan2(x,y) order
    candidates = [
        (3, 0),    # angle from pivot: atan2(5,3) vs atan2(3,5)
        (5, 1),    # atan2(6,5) vs atan2(5,6)
        (1, 4),    # atan2(9,1) vs atan2(1,9)
        (-3, 2),   # atan2(7,-3) vs atan2(-3,7)
        (-4, 0),   # atan2(5,-4) vs atan2(-4,5)
        (-1, 5),   # atan2(10,-1) vs atan2(-1,10)
        (4, 4),    # atan2(9,4) vs atan2(4,9)
    ]
    # Pick 5-7 of them
    n_extra = random.randint(5, min(7, len(candidates)))
    chosen = random.sample(candidates, n_extra)
    points.extend(chosen)

    # Add 1-2 interior points
    for _ in range(random.randint(1, 2)):
        x = random.randint(-1, 2)
        y = random.randint(-2, 2)
        points.append((x, y))

    points = list(set(points))
    return points


INPUT_OVERRIDES = {
    "POINTS": _generate_points,
}
