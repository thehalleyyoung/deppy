"""K-d tree construction and k-nearest-neighbor query.

Bug: When deciding whether to explore the other subtree during backtracking,
the correct algorithm checks |query[dim] - node.split_value| where dim is the
node's split dimension. The bug always uses dimension 0 instead of the node's
split dimension, causing incorrect pruning and missed nearer points.
"""

CORRECT = r"""
import math

def kd_tree_knn(points, query, k):
    # Build a balanced k-d tree from 2D points
    # Each node: (point, left, right, split_dim)

    def build(pts, depth):
        if not pts:
            return None
        dim = depth % 2
        pts_sorted = sorted(pts, key=lambda p: p[dim])
        mid = len(pts_sorted) // 2
        return {
            'point': pts_sorted[mid],
            'left': build(pts_sorted[:mid], depth + 1),
            'right': build(pts_sorted[mid + 1:], depth + 1),
            'dim': dim
        }

    def dist_sq(a, b):
        return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2

    def search(node, query, k, best):
        # best is a max-heap by negative distance (list of (-dist_sq, point))
        if node is None:
            return

        d = dist_sq(node['point'], query)
        if len(best) < k:
            best.append((d, node['point']))
            best.sort(key=lambda x: -x[0])
        elif d < best[0][0]:
            best[0] = (d, node['point'])
            best.sort(key=lambda x: -x[0])

        dim = node['dim']
        diff = query[dim] - node['point'][dim]

        if diff <= 0:
            first, second = node['left'], node['right']
        else:
            first, second = node['right'], node['left']

        search(first, query, k, best)

        # CORRECT: check distance to splitting plane using node's split dimension
        worst_best = best[0][0] if len(best) == k else float('inf')
        plane_dist_sq = diff * diff  # uses dim from node['dim']
        if len(best) < k or plane_dist_sq < worst_best:
            search(second, query, k, best)

    tree = build(points, 0)
    best = []
    search(tree, query, k, best)
    best.sort(key=lambda x: (x[0], x[1]))
    result_points = [p for _, p in best]
    return result_points

points = POINTS
query = QUERY
k = K
result = kd_tree_knn(points, query, k)
"""

BUGGY = r"""
import math

def kd_tree_knn(points, query, k):
    # Build a balanced k-d tree from 2D points
    # Each node: (point, left, right, split_dim)

    def build(pts, depth):
        if not pts:
            return None
        dim = depth % 2
        pts_sorted = sorted(pts, key=lambda p: p[dim])
        mid = len(pts_sorted) // 2
        return {
            'point': pts_sorted[mid],
            'left': build(pts_sorted[:mid], depth + 1),
            'right': build(pts_sorted[mid + 1:], depth + 1),
            'dim': dim
        }

    def dist_sq(a, b):
        return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2

    def search(node, query, k, best):
        # best is a max-heap by negative distance (list of (-dist_sq, point))
        if node is None:
            return

        d = dist_sq(node['point'], query)
        if len(best) < k:
            best.append((d, node['point']))
            best.sort(key=lambda x: -x[0])
        elif d < best[0][0]:
            best[0] = (d, node['point'])
            best.sort(key=lambda x: -x[0])

        dim = node['dim']
        diff = query[dim] - node['point'][dim]

        if diff <= 0:
            first, second = node['left'], node['right']
        else:
            first, second = node['right'], node['left']

        search(first, query, k, best)

        # BUG: always uses dimension 0 instead of node's split dimension
        wrong_diff = query[0] - node['point'][0]  # should be query[dim] - node['point'][dim]
        worst_best = best[0][0] if len(best) == k else float('inf')
        plane_dist_sq = wrong_diff * wrong_diff
        if len(best) < k or plane_dist_sq < worst_best:
            search(second, query, k, best)

    tree = build(points, 0)
    best = []
    search(tree, query, k, best)
    best.sort(key=lambda x: (x[0], x[1]))
    result_points = [p for _, p in best]
    return result_points

points = POINTS
query = QUERY
k = K
result = kd_tree_knn(points, query, k)
"""


def SPEC(POINTS, QUERY, K, result):
    """Verify k-nearest neighbors by comparing to brute-force."""
    if not isinstance(result, list):
        return False
    if len(result) != min(K, len(POINTS)):
        return False

    # Brute-force: compute all distances, sort, take top k
    def dist_sq(a, b):
        return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2

    dists = [(dist_sq(p, QUERY), tuple(p)) for p in POINTS]
    dists.sort(key=lambda x: (x[0], x[1]))
    expected = [list(p) for d, p in dists[:K]]

    # Both should contain the same set of points
    # (sorted by distance then coords, so order should match)
    result_tuples = sorted([tuple(p) for p in result])
    expected_tuples = sorted([tuple(p) for p in expected])

    # If there are ties at the boundary, we need to check distances match
    if result_tuples == expected_tuples:
        return True

    # Check that result distances are all <= the kth best distance
    result_dists = sorted([dist_sq(p, QUERY) for p in result])
    expected_dists = sorted([dist_sq(p, QUERY) for p in expected])
    return result_dists == expected_dists


BUG_DESC = (
    "When checking whether to explore the other subtree during backtracking, "
    "the algorithm always computes distance to splitting plane using dimension 0 "
    "instead of the node's actual split dimension. This causes incorrect pruning: "
    "at depth-1 nodes (split dim=1), the plane distance check uses the wrong "
    "coordinate, potentially skipping subtrees that contain nearer points."
)


def _generate_points():
    import random
    n = random.randint(15, 30)
    points = []
    for _ in range(n):
        x = random.randint(-20, 20)
        y = random.randint(-20, 20)
        points.append([x, y])
    # Remove duplicates
    seen = set()
    unique = []
    for p in points:
        t = tuple(p)
        if t not in seen:
            seen.add(t)
            unique.append(p)
    return unique


def _generate_query():
    import random
    return [random.randint(-3, 3), random.randint(-3, 3)]


INPUT_OVERRIDES = {
    "POINTS": _generate_points,
    "QUERY": _generate_query,
    "K": lambda: 3,
}
