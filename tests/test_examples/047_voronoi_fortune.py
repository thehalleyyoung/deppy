"""Fortune's sweep-line algorithm for Voronoi diagrams (simplified).

Computes the nearest-site assignment for a grid of query points given
a set of sites. Uses a simplified sweep-line approach that processes
site events and circle events to determine Voronoi cell boundaries.

Bug: when processing circle events, the breakpoint calculation between
arcs swaps the left and right site, producing incorrect cell boundaries.
This causes some query points near cell edges to be assigned to the
wrong site.
"""

CORRECT = r"""
import math

def dist_sq(p1, p2):
    return (p1[0] - p2[0]) ** 2 + (p1[1] - p2[1]) ** 2

def nearest_site_brute(point, sites):
    # Find the index of the nearest site to a point
    best_idx = 0
    best_dist = dist_sq(point, sites[0])
    for i in range(1, len(sites)):
        d = dist_sq(point, sites[i])
        if d < best_dist:
            best_dist = d
            best_idx = i
    return best_idx

def breakpoint_x(site_a, site_b, sweep_y):
    # Compute the x-coordinate of the breakpoint between two parabolas
    # defined by site_a and site_b with directrix at sweep_y
    ax, ay = site_a
    bx, by = site_b
    if ay == by:
        return (ax + bx) / 2.0
    if ay == sweep_y:
        return float(ax)
    if by == sweep_y:
        return float(bx)
    # Solve the quadratic for intersection
    da = ay - sweep_y
    db = by - sweep_y
    # Standard breakpoint formula
    A = 1.0 / da - 1.0 / db
    B = -2.0 * ax / da + 2.0 * bx / db
    C = (ax * ax + ay * ay - sweep_y * sweep_y) / da - (bx * bx + by * by - sweep_y * sweep_y) / db
    if abs(A) < 1e-12:
        if abs(B) < 1e-12:
            return (ax + bx) / 2.0
        return -C / B
    disc = B * B - 4 * A * C
    if disc < 0:
        disc = 0
    sqrt_disc = math.sqrt(disc)
    x1 = (-B + sqrt_disc) / (2 * A)
    x2 = (-B - sqrt_disc) / (2 * A)
    # CORRECT: choose the breakpoint that is between the two sites
    if ax <= bx:
        return min(x1, x2) if ay > by else max(x1, x2)
    else:
        return max(x1, x2) if ay > by else min(x1, x2)

def circumcenter(a, b, c):
    # Compute circumcenter of triangle (a, b, c)
    ax, ay = a
    bx, by = b
    cx, cy = c
    D = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(D) < 1e-12:
        return None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / D
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / D
    return (ux, uy)

def compute_voronoi_assignment(sites, query_points):
    # Simplified Fortune's: process sites by y-coordinate, maintain beach line
    # For each query point, find the nearest site using the sweep structure

    if not sites:
        return [-1] * len(query_points)

    n = len(sites)
    if n == 1:
        return [0] * len(query_points)

    # Sort sites by y-coordinate
    indexed_sites = [(sites[i], i) for i in range(n)]
    indexed_sites.sort(key=lambda s: (s[0][1], s[0][0]))

    # Beach line: list of site indices in left-to-right order
    beach = []
    site_ptr = 0
    assignments = []

    for qx, qy in query_points:
        # Advance sweep line to just past the query y
        sweep_y = qy + 0.001

        # Add all sites above the sweep line to beach
        while site_ptr < n and indexed_sites[site_ptr][0][1] <= sweep_y:
            site_idx = indexed_sites[site_ptr][1]
            # Insert into beach at correct position
            sx = sites[site_idx][0]
            insert_pos = 0
            for j in range(len(beach)):
                bj = beach[j]
                if j + 1 < len(beach):
                    bk = beach[j + 1]
                    bp = breakpoint_x(sites[bj], sites[bk], sweep_y)
                    if sx > bp:
                        insert_pos = j + 1
                    else:
                        break
                else:
                    if len(beach) > 0 and sx > sites[bj][0]:
                        insert_pos = j + 1
            beach.insert(insert_pos, site_idx)
            site_ptr += 1

        # Find which arc the query point falls under
        if not beach:
            assignments.append(nearest_site_brute((qx, qy), sites))
            continue

        if len(beach) == 1:
            assignments.append(beach[0])
            continue

        found = False
        for j in range(len(beach) - 1):
            bp = breakpoint_x(sites[beach[j]], sites[beach[j + 1]], sweep_y)
            if qx <= bp:
                assignments.append(beach[j])
                found = True
                break
        if not found:
            assignments.append(beach[-1])

    return assignments

sites = SITES
query_points = QUERY_POINTS
result = compute_voronoi_assignment(sites, query_points)
"""

BUGGY = r"""
import math

def dist_sq(p1, p2):
    return (p1[0] - p2[0]) ** 2 + (p1[1] - p2[1]) ** 2

def nearest_site_brute(point, sites):
    best_idx = 0
    best_dist = dist_sq(point, sites[0])
    for i in range(1, len(sites)):
        d = dist_sq(point, sites[i])
        if d < best_dist:
            best_dist = d
            best_idx = i
    return best_idx

def breakpoint_x(site_a, site_b, sweep_y):
    ax, ay = site_a
    bx, by = site_b
    if ay == by:
        return (ax + bx) / 2.0
    if ay == sweep_y:
        return float(ax)
    if by == sweep_y:
        return float(bx)
    da = ay - sweep_y
    db = by - sweep_y
    A = 1.0 / da - 1.0 / db
    B = -2.0 * ax / da + 2.0 * bx / db
    C = (ax * ax + ay * ay - sweep_y * sweep_y) / da - (bx * bx + by * by - sweep_y * sweep_y) / db
    if abs(A) < 1e-12:
        if abs(B) < 1e-12:
            return (ax + bx) / 2.0
        return -C / B
    disc = B * B - 4 * A * C
    if disc < 0:
        disc = 0
    sqrt_disc = math.sqrt(disc)
    x1 = (-B + sqrt_disc) / (2 * A)
    x2 = (-B - sqrt_disc) / (2 * A)
    # BUG: swapped left/right choice — uses opposite breakpoint
    if ax <= bx:
        return max(x1, x2) if ay > by else min(x1, x2)  # BUG: swapped min/max
    else:
        return min(x1, x2) if ay > by else max(x1, x2)  # BUG: swapped min/max

def circumcenter(a, b, c):
    ax, ay = a
    bx, by = b
    cx, cy = c
    D = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(D) < 1e-12:
        return None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / D
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / D
    return (ux, uy)

def compute_voronoi_assignment(sites, query_points):
    if not sites:
        return [-1] * len(query_points)

    n = len(sites)
    if n == 1:
        return [0] * len(query_points)

    indexed_sites = [(sites[i], i) for i in range(n)]
    indexed_sites.sort(key=lambda s: (s[0][1], s[0][0]))

    beach = []
    site_ptr = 0
    assignments = []

    for qx, qy in query_points:
        sweep_y = qy + 0.001

        while site_ptr < n and indexed_sites[site_ptr][0][1] <= sweep_y:
            site_idx = indexed_sites[site_ptr][1]
            sx = sites[site_idx][0]
            insert_pos = 0
            for j in range(len(beach)):
                bj = beach[j]
                if j + 1 < len(beach):
                    bk = beach[j + 1]
                    bp = breakpoint_x(sites[bj], sites[bk], sweep_y)
                    if sx > bp:
                        insert_pos = j + 1
                    else:
                        break
                else:
                    if len(beach) > 0 and sx > sites[bj][0]:
                        insert_pos = j + 1
            beach.insert(insert_pos, site_idx)
            site_ptr += 1

        if not beach:
            assignments.append(nearest_site_brute((qx, qy), sites))
            continue

        if len(beach) == 1:
            assignments.append(beach[0])
            continue

        found = False
        for j in range(len(beach) - 1):
            bp = breakpoint_x(sites[beach[j]], sites[beach[j + 1]], sweep_y)
            if qx <= bp:
                assignments.append(beach[j])
                found = True
                break
        if not found:
            assignments.append(beach[-1])

    return assignments

sites = SITES
query_points = QUERY_POINTS
result = compute_voronoi_assignment(sites, query_points)
"""


def SPEC(sites, query_points, result):
    # Each query point should be assigned to its nearest site
    if not isinstance(result, list):
        return False
    if len(result) != len(query_points):
        return False
    for i, (qx, qy) in enumerate(query_points):
        if not isinstance(result[i], int):
            return False
        if result[i] < 0 or result[i] >= len(sites):
            return False
        # Check that the assigned site is indeed nearest
        assigned_dist = (qx - sites[result[i]][0]) ** 2 + (qy - sites[result[i]][1]) ** 2
        for j in range(len(sites)):
            d = (qx - sites[j][0]) ** 2 + (qy - sites[j][1]) ** 2
            if d < assigned_dist - 1e-6:
                return False
    return True


BUG_DESC = (
    "In the breakpoint_x function, when choosing which root of the quadratic "
    "to return, the correct version picks min for left-of-right sites and max "
    "for right-of-left. The buggy version swaps these choices, placing the "
    "breakpoint on the wrong side. This shifts Voronoi cell boundaries and "
    "causes query points near edges to be assigned to the wrong site."
)


def _gen():
    import random
    # The bug swaps min/max root choice for the breakpoint quadratic,
    # placing the breakpoint on the wrong side. This shifts Voronoi
    # boundaries and misassigns query points near cell edges.
    #
    # To trigger reliably: need sites at different y-coordinates (so
    # the quadratic has two distinct roots and the min/max choice matters),
    # and query points placed near the midpoint between pairs of sites
    # (near cell boundaries where the wrong breakpoint causes misassignment).
    #
    # Strategy: place sites with varied y-coordinates and query densely
    # near the midpoints between site pairs.

    # Use well-separated sites with different y-values
    sites = [
        [0, 0],
        [6, 3],
        [3, 7],
    ]
    # Optionally add 1-2 more sites
    extra = random.randint(0, 2)
    for _ in range(extra):
        x = random.randint(-2, 10)
        y = random.randint(-2, 10)
        if [x, y] not in sites:
            sites.append([x, y])

    # Generate query points near midpoints between sites (near Voronoi edges)
    query_points = []
    n = len(sites)
    for i in range(n):
        for j in range(i + 1, n):
            mx = (sites[i][0] + sites[j][0]) / 2.0
            my = (sites[i][1] + sites[j][1]) / 2.0
            # Place queries near the midpoint with small perturbations
            for _ in range(3):
                dx = random.uniform(-0.5, 0.5)
                dy = random.uniform(-0.5, 0.5)
                query_points.append([round(mx + dx, 2), round(my + dy, 2)])

    # Also add some random queries
    for _ in range(5):
        x = random.uniform(-1, 8)
        y = random.uniform(-1, 8)
        query_points.append([round(x, 2), round(y, 2)])

    # Sort query points by y to work with the sweep-line
    query_points.sort(key=lambda p: (p[1], p[0]))

    return {"SITES": sites, "QUERY_POINTS": query_points}

INPUT_OVERRIDES = _gen
