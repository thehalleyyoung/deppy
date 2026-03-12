"""Incremental Delaunay triangulation via Bowyer-Watson algorithm.

Inserts points one at a time into a triangulation. For each new point,
finds all triangles whose circumcircle contains the point, removes them,
and re-triangulates the resulting polygonal hole.

Bug: the in-circle test flips the sign of the determinant. This means
points that should be inside a circumcircle are considered outside and
vice versa, causing the algorithm to flip edges incorrectly and produce
a non-Delaunay triangulation.
"""

CORRECT = r"""
def in_circle(ax, ay, bx, by, cx, cy, dx, dy):
    # Returns True if point (dx, dy) is inside the circumcircle of triangle (a, b, c)
    # Using the standard determinant test
    # Positive determinant means d is inside (for CCW-oriented triangle)
    adx = ax - dx
    ady = ay - dy
    bdx = bx - dx
    bdy = by - dy
    cdx = cx - dx
    cdy = cy - dy

    det = (adx * adx + ady * ady) * (bdx * cdy - cdx * bdy) \
        - (bdx * bdx + bdy * bdy) * (adx * cdy - cdx * ady) \
        + (cdx * cdx + cdy * cdy) * (adx * bdy - bdx * ady)

    return det > 0  # CORRECT: positive means inside

def orient2d(ax, ay, bx, by, cx, cy):
    # Returns positive if (a, b, c) is CCW, negative if CW, zero if collinear
    return (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)

def circumcenter(ax, ay, bx, by, cx, cy):
    D = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(D) < 1e-12:
        return None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / D
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / D
    return (ux, uy)

def delaunay_triangulate(points):
    # Bowyer-Watson incremental algorithm
    if len(points) < 3:
        return []

    # Create super-triangle that contains all points
    min_x = min(p[0] for p in points) - 1
    max_x = max(p[0] for p in points) + 1
    min_y = min(p[1] for p in points) - 1
    max_y = max(p[1] for p in points) + 1
    dx = max_x - min_x
    dy = max_y - min_y
    dmax = max(dx, dy) * 10

    # Super-triangle vertices (indices -3, -2, -1 conceptually)
    st0 = (min_x - dmax, min_y - dmax)
    st1 = (min_x + 2 * dmax, min_y - dmax)
    st2 = (min_x, min_y + 2 * dmax)

    all_points = list(points) + [st0, st1, st2]
    n = len(points)
    st_indices = {n, n + 1, n + 2}

    # Initial triangulation is just the super-triangle
    triangles = set()
    triangles.add((n, n + 1, n + 2))

    for pi in range(n):
        px, py = all_points[pi]

        # Find all triangles whose circumcircle contains the new point
        bad_triangles = set()
        for tri in triangles:
            i, j, k = tri
            ax, ay = all_points[i]
            bx, by = all_points[j]
            cx, cy = all_points[k]
            # Ensure CCW orientation for correct in_circle test
            if orient2d(ax, ay, bx, by, cx, cy) < 0:
                ax, ay, bx, by = bx, by, ax, ay
                i, j = j, i
            if in_circle(ax, ay, bx, by, cx, cy, px, py):
                bad_triangles.add(tri)

        # Find the boundary polygon of the hole
        boundary = []
        for tri in bad_triangles:
            i, j, k = tri
            edges = [(i, j), (j, k), (k, i)]
            for e in edges:
                # An edge is on the boundary if it is not shared by another bad triangle
                shared = False
                for other in bad_triangles:
                    if other == tri:
                        continue
                    oi, oj, ok = other
                    other_edges = {(oi, oj), (oj, ok), (ok, oi),
                                   (oj, oi), (ok, oj), (oi, ok)}
                    if (e[0], e[1]) in other_edges or (e[1], e[0]) in other_edges:
                        shared = True
                        break
                if not shared:
                    boundary.append(e)

        # Remove bad triangles
        for tri in bad_triangles:
            triangles.discard(tri)

        # Re-triangulate with the new point
        for e0, e1 in boundary:
            triangles.add((pi, e0, e1))

    # Remove triangles that include super-triangle vertices
    final = []
    for tri in triangles:
        i, j, k = tri
        if i in st_indices or j in st_indices or k in st_indices:
            continue
        final.append(sorted([i, j, k]))

    final.sort()
    return final

points = POINTS
result = delaunay_triangulate(points)
"""

BUGGY = r"""
def in_circle(ax, ay, bx, by, cx, cy, dx, dy):
    # Returns True if point (dx, dy) is inside the circumcircle of triangle (a, b, c)
    adx = ax - dx
    ady = ay - dy
    bdx = bx - dx
    bdy = by - dy
    cdx = cx - dx
    cdy = cy - dy

    det = (adx * adx + ady * ady) * (bdx * cdy - cdx * bdy) \
        - (bdx * bdx + bdy * bdy) * (adx * cdy - cdx * ady) \
        + (cdx * cdx + cdy * cdy) * (adx * bdy - bdx * ady)

    # BUG: flipped sign — returns True when det < 0 instead of det > 0
    # This accepts points outside the circumcircle and rejects those inside
    return det < 0

def orient2d(ax, ay, bx, by, cx, cy):
    return (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)

def circumcenter(ax, ay, bx, by, cx, cy):
    D = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(D) < 1e-12:
        return None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / D
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / D
    return (ux, uy)

def delaunay_triangulate(points):
    if len(points) < 3:
        return []

    min_x = min(p[0] for p in points) - 1
    max_x = max(p[0] for p in points) + 1
    min_y = min(p[1] for p in points) - 1
    max_y = max(p[1] for p in points) + 1
    dx = max_x - min_x
    dy = max_y - min_y
    dmax = max(dx, dy) * 10

    st0 = (min_x - dmax, min_y - dmax)
    st1 = (min_x + 2 * dmax, min_y - dmax)
    st2 = (min_x, min_y + 2 * dmax)

    all_points = list(points) + [st0, st1, st2]
    n = len(points)
    st_indices = {n, n + 1, n + 2}

    triangles = set()
    triangles.add((n, n + 1, n + 2))

    for pi in range(n):
        px, py = all_points[pi]

        bad_triangles = set()
        for tri in triangles:
            i, j, k = tri
            ax, ay = all_points[i]
            bx, by = all_points[j]
            cx, cy = all_points[k]
            if orient2d(ax, ay, bx, by, cx, cy) < 0:
                ax, ay, bx, by = bx, by, ax, ay
                i, j = j, i
            if in_circle(ax, ay, bx, by, cx, cy, px, py):
                bad_triangles.add(tri)

        boundary = []
        for tri in bad_triangles:
            i, j, k = tri
            edges = [(i, j), (j, k), (k, i)]
            for e in edges:
                shared = False
                for other in bad_triangles:
                    if other == tri:
                        continue
                    oi, oj, ok = other
                    other_edges = {(oi, oj), (oj, ok), (ok, oi),
                                   (oj, oi), (ok, oj), (oi, ok)}
                    if (e[0], e[1]) in other_edges or (e[1], e[0]) in other_edges:
                        shared = True
                        break
                if not shared:
                    boundary.append(e)

        for tri in bad_triangles:
            triangles.discard(tri)

        for e0, e1 in boundary:
            triangles.add((pi, e0, e1))

    final = []
    for tri in triangles:
        i, j, k = tri
        if i in st_indices or j in st_indices or k in st_indices:
            continue
        final.append(sorted([i, j, k]))

    final.sort()
    return final

points = POINTS
result = delaunay_triangulate(points)
"""


def SPEC(points, result):
    # Verify Delaunay triangulation properties
    if not isinstance(result, list):
        return False
    if len(points) < 3:
        return result == []

    # Check that each triangle is valid (indices in range)
    n = len(points)
    for tri in result:
        if len(tri) != 3:
            return False
        for idx in tri:
            if idx < 0 or idx >= n:
                return False
        if len(set(tri)) != 3:
            return False

    # Check Delaunay property: no point inside any triangle's circumcircle
    for tri in result:
        i, j, k = tri
        ax, ay = points[i]
        bx, by = points[j]
        cx, cy = points[k]
        D = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
        if abs(D) < 1e-10:
            continue
        ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / D
        uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / D
        r_sq = (ax - ux) ** 2 + (ay - uy) ** 2
        for m in range(n):
            if m in tri:
                continue
            px, py = points[m]
            d_sq = (px - ux) ** 2 + (py - uy) ** 2
            if d_sq < r_sq - 1e-6:
                # Point m is strictly inside circumcircle — not Delaunay
                return False

    return True


BUG_DESC = (
    "The in_circle test should return True when the determinant is positive "
    "(for a CCW-oriented triangle), meaning the query point is inside the "
    "circumcircle. The bug flips the sign, returning True when det < 0. "
    "This causes the Bowyer-Watson algorithm to remove the wrong triangles "
    "during point insertion, producing a non-Delaunay triangulation."
)


def _gen_points():
    import random
    # The bug flips the sign of the in_circle test (det < 0 instead of det > 0).
    # This makes the Bowyer-Watson algorithm identify the WRONG triangles as
    # "bad" during point insertion, producing a non-Delaunay triangulation.
    #
    # The bug is triggered whenever a new point falls inside a circumcircle
    # of an existing triangle (common case). With 5+ non-cocircular points
    # in general position, the flipped test will produce wrong results.
    #
    # Strategy: use a small set of well-spread points with no 4 cocircular
    # points and no 3 collinear points. Small integer coords in a modest
    # range work well. Use fewer points (5-7) to keep within max_size=8.
    points = [
        [0, 0],
        [4, 0],
        [0, 4],
        [4, 4],
        [2, 2],
    ]
    # Add 1-2 more random points to add variety
    extras = random.randint(1, 2)
    used = set(map(tuple, points))
    for _ in range(extras):
        for _attempt in range(20):
            x = random.randint(-1, 5)
            y = random.randint(-1, 5)
            if (x, y) not in used:
                points.append([x, y])
                used.add((x, y))
                break

    random.shuffle(points)
    return points


INPUT_OVERRIDES = {
    "POINTS": _gen_points,
}
