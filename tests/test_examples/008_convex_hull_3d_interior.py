"""3D convex hull interior point test using signed volume method.

Given a set of 3D points, compute a convex hull as triangular faces,
then check if a query point is inside by verifying consistent signed
tetrahedron volumes across all faces.

Bug: when computing the visibility test during incremental hull construction,
two vertices are swapped in the signed_volume call, reversing the face
normal for the visibility check and producing a malformed hull.
"""

CORRECT = r"""
def cross(a, b):
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )

def sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])

def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]

def signed_volume(a, b, c, d):
    # Signed volume of tetrahedron (a, b, c, d)
    ab = sub(b, a)
    ac = sub(c, a)
    ad = sub(d, a)
    return dot(cross(ab, ac), ad)

def convex_hull_faces(points):
    # Compute convex hull faces using incremental algorithm.
    # Returns list of triangles (i, j, k) as indices into points,
    # oriented so normals point outward.
    n = len(points)
    if n < 4:
        return []

    # Find initial non-degenerate tetrahedron
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                for l in range(k + 1, n):
                    vol = signed_volume(points[i], points[j],
                                        points[k], points[l])
                    if abs(vol) > 1e-10:
                        p0, p1, p2, p3 = i, j, k, l
                        # Orient so vol > 0
                        if vol < 0:
                            p1, p2 = p2, p1
                        faces = [
                            (p0, p1, p2),
                            (p0, p2, p3),
                            (p0, p3, p1),
                            (p1, p3, p2),
                        ]
                        # Add remaining points incrementally
                        for pt_idx in range(n):
                            if pt_idx in (p0, p1, p2, p3):
                                continue
                            # Find visible faces
                            visible = []
                            for fi, face in enumerate(faces):
                                a, b_idx, c_idx = face
                                # CORRECT: normal computed with proper vertex order
                                v = signed_volume(
                                    points[a], points[b_idx],
                                    points[c_idx], points[pt_idx])
                                if v < -1e-10:
                                    visible.append(fi)
                            if not visible:
                                continue
                            # Collect horizon edges
                            horizon = []
                            for fi in visible:
                                a, b_idx, c_idx = faces[fi]
                                edges = [(a, b_idx), (b_idx, c_idx), (c_idx, a)]
                                for e in edges:
                                    rev = (e[1], e[0])
                                    shared = False
                                    for fj in visible:
                                        if fj == fi:
                                            continue
                                        fa, fb, fc = faces[fj]
                                        fedges = [(fa, fb), (fb, fc), (fc, fa)]
                                        if rev in fedges:
                                            shared = True
                                            break
                                    if not shared:
                                        horizon.append(e)
                            # Remove visible faces (reverse order to preserve indices)
                            for fi in sorted(visible, reverse=True):
                                faces.pop(fi)
                            # Add new faces from horizon to new point
                            for e in horizon:
                                faces.append((e[0], e[1], pt_idx))
                        return faces
    return []

def point_inside_hull(points, query):
    # Check if query point is inside the convex hull of points.
    faces = convex_hull_faces(points)
    if len(faces) < 4:
        result = (False, len(faces))
        return result

    # Compute centroid as reference interior point
    cx = sum(p[0] for p in points) / len(points)
    cy = sum(p[1] for p in points) / len(points)
    cz = sum(p[2] for p in points) / len(points)
    centroid = (cx, cy, cz)

    # For each face, query and centroid must be on the same side
    for face in faces:
        a, b_idx, c_idx = face
        vol_centroid = signed_volume(points[a], points[b_idx],
                                     points[c_idx], centroid)
        vol_query = signed_volume(points[a], points[b_idx],
                                  points[c_idx], query)
        if abs(vol_centroid) < 1e-10:
            continue
        if vol_centroid > 0 and vol_query < -1e-10:
            result = (False, len(faces))
            return result
        if vol_centroid < 0 and vol_query > 1e-10:
            result = (False, len(faces))
            return result

    result = (True, len(faces))
    return result

points = POINTS
query = QUERY
result = point_inside_hull(points, query)
"""

BUGGY = r"""
def cross(a, b):
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )

def sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])

def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]

def signed_volume(a, b, c, d):
    # Signed volume of tetrahedron (a, b, c, d)
    ab = sub(b, a)
    ac = sub(c, a)
    ad = sub(d, a)
    return dot(cross(ab, ac), ad)

def convex_hull_faces(points):
    # Compute convex hull faces using incremental algorithm.
    n = len(points)
    if n < 4:
        return []

    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                for l in range(k + 1, n):
                    vol = signed_volume(points[i], points[j],
                                        points[k], points[l])
                    if abs(vol) > 1e-10:
                        p0, p1, p2, p3 = i, j, k, l
                        if vol < 0:
                            p1, p2 = p2, p1
                        faces = [
                            (p0, p1, p2),
                            (p0, p2, p3),
                            (p0, p3, p1),
                            (p1, p3, p2),
                        ]
                        for pt_idx in range(n):
                            if pt_idx in (p0, p1, p2, p3):
                                continue
                            visible = []
                            for fi, face in enumerate(faces):
                                a, b_idx, c_idx = face
                                # BUG: swapped b_idx and c_idx in signed_volume
                                # This reverses the normal for visibility test
                                v = signed_volume(
                                    points[a], points[c_idx],
                                    points[b_idx], points[pt_idx])
                                if v < -1e-10:
                                    visible.append(fi)
                            if not visible:
                                continue
                            horizon = []
                            for fi in visible:
                                a, b_idx, c_idx = faces[fi]
                                edges = [(a, b_idx), (b_idx, c_idx), (c_idx, a)]
                                for e in edges:
                                    rev = (e[1], e[0])
                                    shared = False
                                    for fj in visible:
                                        if fj == fi:
                                            continue
                                        fa, fb, fc = faces[fj]
                                        fedges = [(fa, fb), (fb, fc), (fc, fa)]
                                        if rev in fedges:
                                            shared = True
                                            break
                                    if not shared:
                                        horizon.append(e)
                            for fi in sorted(visible, reverse=True):
                                faces.pop(fi)
                            for e in horizon:
                                faces.append((e[0], e[1], pt_idx))
                        return faces
    return []

def point_inside_hull(points, query):
    # Check if query point is inside the convex hull of points.
    faces = convex_hull_faces(points)
    if len(faces) < 4:
        result = (False, len(faces))
        return result

    cx = sum(p[0] for p in points) / len(points)
    cy = sum(p[1] for p in points) / len(points)
    cz = sum(p[2] for p in points) / len(points)
    centroid = (cx, cy, cz)

    for face in faces:
        a, b_idx, c_idx = face
        vol_centroid = signed_volume(points[a], points[b_idx],
                                     points[c_idx], centroid)
        vol_query = signed_volume(points[a], points[b_idx],
                                  points[c_idx], query)
        if abs(vol_centroid) < 1e-10:
            continue
        if vol_centroid > 0 and vol_query < -1e-10:
            result = (False, len(faces))
            return result
        if vol_centroid < 0 and vol_query > 1e-10:
            result = (False, len(faces))
            return result

    result = (True, len(faces))
    return result

points = POINTS
query = QUERY
result = point_inside_hull(points, query)
"""


def SPEC(points, query, result):
    """Verify interior point test against brute-force reference.
    For each face of the hull (found via O(n^4) brute force), check
    that query and all other points are on the same side.
    """
    is_inside, num_faces = result

    if not isinstance(is_inside, bool):
        return False
    if not isinstance(num_faces, int):
        return False

    # Reference geometry helpers
    def ref_sub(a, b):
        return (a[0] - b[0], a[1] - b[1], a[2] - b[2])

    def ref_cross(a, b):
        return (
            a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0],
        )

    def ref_dot(a, b):
        return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]

    def ref_signed_vol(a, b, c, d):
        ab = ref_sub(b, a)
        ac = ref_sub(c, a)
        ad = ref_sub(d, a)
        return ref_dot(ref_cross(ab, ac), ad)

    n = len(points)
    if n < 4:
        if is_inside:
            return False
        return True

    # Brute-force: for each triple, check if it's a hull face
    # (all other points on one side), then check query against it
    ref_inside = True
    found_any_face = False
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                vols = []
                for l in range(n):
                    if l in (i, j, k):
                        continue
                    v = ref_signed_vol(points[i], points[j], points[k], points[l])
                    vols.append(v)
                if not vols:
                    continue
                all_pos = all(v >= -1e-10 for v in vols)
                all_neg = all(v <= 1e-10 for v in vols)
                if all_pos or all_neg:
                    found_any_face = True
                    qvol = ref_signed_vol(points[i], points[j], points[k], query)
                    if all_pos and qvol < -1e-10:
                        ref_inside = False
                    elif all_neg and qvol > 1e-10:
                        ref_inside = False

    if not found_any_face:
        # Degenerate (coplanar) point set
        return True

    if is_inside != ref_inside:
        return False

    return True


BUG_DESC = (
    "When computing the visibility test during incremental hull construction, "
    "two vertices (b_idx and c_idx) are swapped in the signed_volume call, "
    "reversing the face normal direction. This causes the wrong faces to be "
    "identified as visible when adding new points, producing an incorrect "
    "convex hull with malformed face orientations that breaks the interior "
    "point test."
)


def _gen():
    import random
    # The bug: swapped b_idx and c_idx in signed_volume during visibility test,
    # reversing the face normal. This makes the algorithm consider the WRONG
    # faces as visible when adding new points, producing a malformed hull.
    #
    # The bug manifests whenever a 5th+ point is added that is outside the
    # current tetrahedron (visibility check is wrong). With the swapped
    # vertices, visible faces become invisible and vice versa.
    #
    # Strategy: use a clear tetrahedron (4 vertices) plus additional points
    # outside it that must be incorporated. The query point should be inside
    # the true hull so the buggy hull fails the interior test.
    #
    # Use a small, well-separated point set with the query at the centroid.

    # Start with well-separated vertices forming a clear tetrahedron
    base_points = [
        (0, 0, 0),
        (6, 0, 0),
        (0, 6, 0),
        (0, 0, 6),
    ]

    # Add 2-3 more points outside the initial tetrahedron
    extra_candidates = [
        (6, 6, 0),
        (6, 0, 6),
        (0, 6, 6),
        (3, 3, 3),   # inside initial tet but tests hull update
        (-2, -2, -2),
    ]
    n_extra = random.randint(2, 3)
    extras = random.sample(extra_candidates, n_extra)
    points = base_points + extras

    random.shuffle(points)

    # Query point: centroid of all points (should be inside the hull)
    cx = sum(p[0] for p in points) / len(points)
    cy = sum(p[1] for p in points) / len(points)
    cz = sum(p[2] for p in points) / len(points)
    # Small perturbation to avoid degeneracies
    query = (
        round(cx + random.uniform(-0.1, 0.1), 2),
        round(cy + random.uniform(-0.1, 0.1), 2),
        round(cz + random.uniform(-0.1, 0.1), 2),
    )

    return {"POINTS": points, "QUERY": query}

INPUT_OVERRIDES = _gen
