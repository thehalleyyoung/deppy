"""Rooted tree isomorphism via canonical form hashing. Bug: sorts hashes but uses unsorted children for canonical form."""

CORRECT = r"""
# Rooted Tree Isomorphism via canonical form hashing
# Two rooted trees are isomorphic iff they have the same canonical form
# Canonical form: recursively hash children, sort child hashes, combine
#
# TREES is a list of (root, edges) pairs where edges are undirected (parent, child) pairs
# We test all pairs for isomorphism

def build_adj(edges, n):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj

def compute_canonical(root, adj):
    # BFS to establish parent-child relationships
    parent = [-1] * len(adj)
    children = [[] for _ in range(len(adj))]
    visited = [False] * len(adj)
    visited[root] = True
    queue = [root]
    order = []
    while queue:
        u = queue.pop(0)
        order.append(u)
        for v in adj[u]:
            if not visited[v]:
                visited[v] = True
                parent[v] = u
                children[u].append(v)
                queue.append(v)

    # Compute canonical form bottom-up
    canonical = [""] * len(adj)
    for u in reversed(order):
        child_canonicals = []
        for c in children[u]:
            child_canonicals.append(canonical[c])
        # Sort child canonical forms for isomorphism invariance
        child_canonicals.sort()
        canonical[u] = "(" + "".join(child_canonicals) + ")"

    return canonical[root]

# Compute canonical form for each tree
canonicals = []
for root, edges, n in TREES:
    adj = build_adj(edges, n)
    canonicals.append(compute_canonical(root, adj))

# Compare all pairs
iso_matrix = []
for i in range(len(TREES)):
    row = []
    for j in range(len(TREES)):
        row.append(canonicals[i] == canonicals[j])
    iso_matrix.append(row)

result = {
    "canonicals": canonicals,
    "iso_matrix": iso_matrix,
}
"""

BUGGY = r"""
# Rooted Tree Isomorphism via canonical form hashing

def build_adj(edges, n):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj

def compute_canonical(root, adj):
    parent = [-1] * len(adj)
    children = [[] for _ in range(len(adj))]
    visited = [False] * len(adj)
    visited[root] = True
    queue = [root]
    order = []
    while queue:
        u = queue.pop(0)
        order.append(u)
        for v in adj[u]:
            if not visited[v]:
                visited[v] = True
                parent[v] = u
                children[u].append(v)
                queue.append(v)

    canonical = [""] * len(adj)
    for u in reversed(order):
        child_canonicals = []
        for c in children[u]:
            child_canonicals.append(canonical[c])
        # BUG: sorts the list (for display) but then uses original unsorted
        # children order to build the canonical form
        sorted_canonicals = sorted(child_canonicals)
        # Uses child_canonicals (insertion order) instead of sorted_canonicals
        canonical[u] = "(" + "".join(child_canonicals) + ")"

    return canonical[root]

canonicals = []
for root, edges, n in TREES:
    adj = build_adj(edges, n)
    canonicals.append(compute_canonical(root, adj))

iso_matrix = []
for i in range(len(TREES)):
    row = []
    for j in range(len(TREES)):
        row.append(canonicals[i] == canonicals[j])
    iso_matrix.append(row)

result = {
    "canonicals": canonicals,
    "iso_matrix": iso_matrix,
}
"""


def SPEC(trees, result):
    n = len(trees)
    iso = result["iso_matrix"]
    cans = result["canonicals"]

    if len(iso) != n or len(cans) != n:
        return False

    # Check iso_matrix is reflexive and symmetric
    for i in range(n):
        if not iso[i][i]:
            return False
        for j in range(n):
            if iso[i][j] != iso[j][i]:
                return False

    # Check transitivity
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if iso[i][j] and iso[j][k] and not iso[i][k]:
                    return False

    # Brute-force isomorphism check
    def get_children_map(root, edges, num_nodes):
        adj = [[] for _ in range(num_nodes)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        ch = [[] for _ in range(num_nodes)]
        visited = [False] * num_nodes
        visited[root] = True
        queue = [root]
        while queue:
            u = queue.pop(0)
            for v in adj[u]:
                if not visited[v]:
                    visited[v] = True
                    ch[u].append(v)
                    queue.append(v)
        return ch

    def true_canonical(node, ch):
        child_cans = sorted([true_canonical(c, ch) for c in ch[node]])
        return "(" + "".join(child_cans) + ")"

    true_cans = []
    for root, edges, num_nodes in trees:
        ch = get_children_map(root, edges, num_nodes)
        true_cans.append(true_canonical(root, ch))

    for i in range(n):
        for j in range(n):
            expected = (true_cans[i] == true_cans[j])
            if iso[i][j] != expected:
                return False

    return True


BUG_DESC = "Sorts child canonical forms into a separate list but uses the unsorted original list when building the canonical string, making the result dependent on child insertion order and breaking isomorphism detection."


def _gen_trees():
    # Tree A (rooted at 0):     0
    #                          / \
    #                         1   2
    #                        /
    #                       3
    tree_a = (0, [(0, 1), (0, 2), (1, 3)], 4)

    # Tree B (rooted at 0):     0       (isomorphic to A, children swapped)
    #                          / \
    #                         1   2
    #                              \
    #                               3
    tree_b = (0, [(0, 1), (0, 2), (2, 3)], 4)

    # Tree C (rooted at 0):     0       (NOT isomorphic to A)
    #                           |
    #                           1
    #                          / \
    #                         2   3
    tree_c = (0, [(0, 1), (1, 2), (1, 3)], 4)

    # Tree D: same structure as C but different numbering
    #                           0
    #                           |
    #                           1
    #                          / \
    #                         3   2
    tree_d = (0, [(0, 1), (1, 3), (1, 2)], 4)

    return [tree_a, tree_b, tree_c, tree_d]


INPUT_OVERRIDES = {
    "TREES": _gen_trees,
}
