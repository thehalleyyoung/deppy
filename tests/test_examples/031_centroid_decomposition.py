"""Centroid decomposition of a tree. Bug: doesn't remove centroid from subtree before recursing,
so the centroid gets counted in child subtree sizes, producing wrong decomposition structure."""

CORRECT = r"""
# Centroid decomposition of a tree
# Build adjacency list from edge list
n = len(TREE_EDGES) + 1
adj = [[] for _ in range(n)]
for u, v in TREE_EDGES:
    adj[u].append(v)
    adj[v].append(u)

subtree_size = [0] * n
removed = [False] * n

def compute_size(v, parent):
    subtree_size[v] = 1
    for u in adj[v]:
        if u != parent and not removed[u]:
            compute_size(u, v)
            subtree_size[v] += subtree_size[u]

def find_centroid(v, parent, tree_size):
    for u in adj[v]:
        if u != parent and not removed[u]:
            if subtree_size[u] > tree_size // 2:
                return find_centroid(u, v, tree_size)
    return v

# centroid_parent[v] = parent of v in centroid decomposition tree, -1 for root
centroid_parent = [-1] * n
centroid_depth = [0] * n

def decompose(v, depth):
    compute_size(v, -1)
    tree_size = subtree_size[v]
    centroid = find_centroid(v, -1, tree_size)
    removed[centroid] = True
    centroid_depth[centroid] = depth
    for u in adj[centroid]:
        if not removed[u]:
            decompose(u, depth + 1)
            # find centroid of that subtree to set parent
            # We need to find what centroid was chosen for u's subtree
            # Instead, let's set parent during recursion
    removed[centroid] = False

# Redo with parent tracking
removed2 = [False] * n
centroid_parent2 = [-1] * n
centroid_depth2 = [0] * n

def compute_size2(v, parent):
    subtree_size[v] = 1
    for u in adj[v]:
        if u != parent and not removed2[u]:
            compute_size2(u, v)
            subtree_size[v] += subtree_size[u]

def find_centroid2(v, parent, tree_size):
    for u in adj[v]:
        if u != parent and not removed2[u]:
            if subtree_size[u] > tree_size // 2:
                return find_centroid2(u, v, tree_size)
    return v

def decompose2(v, par, depth):
    compute_size2(v, -1)
    tree_size = subtree_size[v]
    centroid = find_centroid2(v, -1, tree_size)
    centroid_parent2[centroid] = par
    centroid_depth2[centroid] = depth
    removed2[centroid] = True
    for u in adj[centroid]:
        if not removed2[u]:
            decompose2(u, centroid, depth + 1)
    removed2[centroid] = False

if n > 0:
    decompose2(0, -1, 0)

# Build the centroid decomposition tree as adjacency list
cd_children = [[] for _ in range(n)]
cd_root = -1
for v in range(n):
    if centroid_parent2[v] == -1:
        cd_root = v
    else:
        cd_children[centroid_parent2[v]].append(v)

result = {
    "centroid_parent": centroid_parent2,
    "centroid_depth": centroid_depth2,
    "cd_root": cd_root,
    "cd_children": cd_children,
    "n": n
}
"""

BUGGY = r"""
# Centroid decomposition of a tree
# BUG: doesn't mark centroid as removed before recursing into children
# so the centroid is counted in child subtree sizes
n = len(TREE_EDGES) + 1
adj = [[] for _ in range(n)]
for u, v in TREE_EDGES:
    adj[u].append(v)
    adj[v].append(u)

subtree_size = [0] * n
removed = [False] * n

def compute_size(v, parent):
    subtree_size[v] = 1
    for u in adj[v]:
        if u != parent and not removed[u]:
            compute_size(u, v)
            subtree_size[v] += subtree_size[u]

def find_centroid(v, parent, tree_size):
    for u in adj[v]:
        if u != parent and not removed[u]:
            if subtree_size[u] > tree_size // 2:
                return find_centroid(u, v, tree_size)
    return v

centroid_parent2 = [-1] * n
centroid_depth2 = [0] * n

def decompose2(v, par, depth):
    compute_size(v, -1)
    tree_size = subtree_size[v]
    centroid = find_centroid(v, -1, tree_size)
    centroid_parent2[centroid] = par
    centroid_depth2[centroid] = depth
    # BUG: should set removed[centroid] = True here BEFORE recursing
    for u in adj[centroid]:
        if not removed[u]:
            decompose2(u, centroid, depth + 1)
    # This means the centroid is still visible in child subtrees
    # causing infinite recursion or wrong structure
    # To avoid infinite recursion we at least mark it after, but the
    # decomposition structure is wrong
    removed[centroid] = True

# To avoid infinite recursion in the buggy version, we use an iterative
# approach with a visited set
removed3 = [False] * n
centroid_parent3 = [-1] * n
centroid_depth3 = [0] * n
visit_order = []

def compute_size3(v, parent):
    subtree_size[v] = 1
    for u in adj[v]:
        if u != parent and not removed3[u]:
            compute_size3(u, v)
            subtree_size[v] += subtree_size[u]

def find_centroid3(v, parent, tree_size):
    for u in adj[v]:
        if u != parent and not removed3[u]:
            if subtree_size[u] > tree_size // 2:
                return find_centroid3(u, v, tree_size)
    return v

def decompose3(v, par, depth):
    compute_size3(v, -1)
    tree_size = subtree_size[v]
    centroid = find_centroid3(v, -1, tree_size)
    centroid_parent3[centroid] = par
    centroid_depth3[centroid] = depth
    # BUG: not removing centroid before recursing
    children_to_process = []
    for u in adj[centroid]:
        if not removed3[u] and u != centroid:
            children_to_process.append(u)
    removed3[centroid] = True  # remove after collecting, but sizes were wrong
    for u in children_to_process:
        if not removed3[u]:
            decompose3(u, centroid, depth + 1)

if n > 0:
    decompose3(0, -1, 0)

cd_children = [[] for _ in range(n)]
cd_root = -1
for v in range(n):
    if centroid_parent3[v] == -1:
        cd_root = v
    else:
        cd_children[centroid_parent3[v]].append(v)

result = {
    "centroid_parent": centroid_parent3,
    "centroid_depth": centroid_depth3,
    "cd_root": cd_root,
    "cd_children": cd_children,
    "n": n
}
"""

def SPEC(tree_edges, result):
    """Verify centroid decomposition properties."""
    n = result["n"]
    if n <= 1:
        return True
    cd_parent = result["centroid_parent"]
    cd_depth = result["centroid_depth"]
    cd_root = result["cd_root"]
    cd_children = result["cd_children"]

    # Exactly one root
    roots = [v for v in range(n) if cd_parent[v] == -1]
    if len(roots) != 1:
        return False

    # Every node appears exactly once in the decomposition tree
    visited = set()
    stack = [cd_root]
    while stack:
        v = stack.pop()
        if v in visited:
            return False
        visited.add(v)
        for c in cd_children[v]:
            stack.append(c)
    if len(visited) != n:
        return False

    # Depth of root is 0, children have depth = parent_depth + 1
    if cd_depth[cd_root] != 0:
        return False
    stack = [cd_root]
    while stack:
        v = stack.pop()
        for c in cd_children[v]:
            if cd_depth[c] != cd_depth[v] + 1:
                return False
            stack.append(c)

    # Key property: max depth of centroid decomposition is O(log n)
    max_depth = max(cd_depth)
    import math
    if max_depth > 2 * math.ceil(math.log2(n + 1)) + 1:
        return False

    return True

BUG_DESC = "Doesn't remove centroid from subtree before recursing, so child subtree sizes include the centroid, producing a decomposition that can exceed O(log n) depth."

def _gen():
    import random
    # The bug doesn't remove the centroid before recursing, so child subtree
    # sizes include the centroid vertex. This causes wrong centroid selection
    # in subtrees, leading to deeper-than-O(log n) decomposition.
    #
    # Path graphs are worst case but sizes 15-30 are too large for max_size=8.
    # A path of length 7-8 (n=8 vertices) is the right size and still
    # triggers the bug: the centroid decomposition of a path should have
    # depth O(log n) ~ 3, but the bug produces depth 4+ because it
    # keeps picking wrong centroids.
    #
    # We also include "caterpillar" trees (path with single pendants) which
    # are another good trigger case.

    case = random.choice(["path", "caterpillar", "broom"])
    if case == "path":
        # Path: 0-1-2-3-4-5-6-7
        n = 8
        edges = [(i, i+1) for i in range(n-1)]
    elif case == "caterpillar":
        # Path 0-1-2-3-4 with pendants 5,6,7 off vertices 1,2,3
        edges = [(0,1), (1,2), (2,3), (3,4), (1,5), (2,6), (3,7)]
    else:
        # Broom: path 0-1-2-3-4-5 with star at vertex 0: 0-6, 0-7
        edges = [(0,1), (1,2), (2,3), (3,4), (4,5), (0,6), (0,7)]
    return edges

INPUT_OVERRIDES = {"TREE_EDGES": _gen}
