"""Centroid decomposition for distance queries in trees.
Bug: when computing distances through a centroid, adds distance from
centroid to both endpoints but forgets to subtract the centroid-to-centroid
distance of 0 — actually double-counts by not handling the path correctly,
yielding dist(u,c) + dist(v,c) instead of dist(u,v) through centroid."""

CORRECT = r"""
# Centroid Decomposition for answering distance queries on trees
# Preprocesses tree so distance queries use centroid ancestors

def build_adj(edges, n):
    adj = [[] for _ in range(n)]
    for u, v, w in edges:
        adj[u].append((v, w))
        adj[v].append((u, w))
    return adj

def get_subtree_size(adj, root, n):
    size = [0] * n
    removed = [False] * n
    def dfs_size(u, par):
        size[u] = 1
        for v, w in adj[u]:
            if v != par and not removed[v]:
                dfs_size(v, u)
                size[u] += size[v]
    return size, removed, dfs_size

def find_centroid(adj, u, tree_size, size, removed):
    def dfs_centroid(u, par):
        for v, w in adj[u]:
            if v != par and not removed[v]:
                if size[v] > tree_size // 2:
                    return dfs_centroid(v, u)
        return u
    return dfs_centroid(u, -1)

def get_distances_from(adj, root, removed):
    # BFS to get distances from root to all reachable non-removed nodes
    dist = {root: 0}
    queue = [root]
    while queue:
        u = queue.pop(0)
        for v, w in adj[u]:
            if v not in dist and not removed[v]:
                dist[v] = dist[u] + w
                queue.append(v)
    return dist

def centroid_decompose(adj, n):
    size_arr, removed, dfs_size = get_subtree_size(adj, 0, n)
    # Store for each centroid: distances from centroid to nodes in its component
    centroid_parent = [-1] * n
    centroid_dist = [dict() for _ in range(n)]

    def decompose(u, par_centroid):
        dfs_size(u, -1)
        tree_size = size_arr[u]
        c = find_centroid(adj, u, tree_size, size_arr, removed)
        centroid_parent[c] = par_centroid
        # Record distances from centroid c to all nodes in its component
        centroid_dist[c] = get_distances_from(adj, c, removed)
        removed[c] = True
        for v, w in adj[c]:
            if not removed[v]:
                decompose(v, c)

    decompose(0, -1)
    return centroid_parent, centroid_dist

def query_distance(u, v, centroid_parent, centroid_dist, n):
    # CORRECT: find distance through centroid ancestors
    # For each centroid ancestor c of both u and v,
    # dist(u,v) through c = dist(u,c) + dist(v,c)
    # Answer is minimum over all common centroid ancestors
    best = float('inf')
    # Collect centroid ancestors of u
    ancestors_u = {}
    x = u
    while x != -1:
        if u in centroid_dist[x]:
            ancestors_u[x] = centroid_dist[x][u]
        x = centroid_parent[x]
    # Walk centroid ancestors of v, check common
    x = v
    while x != -1:
        if x in ancestors_u and v in centroid_dist[x]:
            # CORRECT: dist(u,v) = dist(u,c) + dist(v,c)
            d = ancestors_u[x] + centroid_dist[x][v]
            if d < best:
                best = d
        x = centroid_parent[x]
    return best

edges = list(EDGES)
n = NUM_NODES
adj = build_adj(edges, n)
centroid_parent, centroid_dist = centroid_decompose(adj, n)

queries = list(QUERIES)
result = []
for u, v in queries:
    result.append(query_distance(u, v, centroid_parent, centroid_dist, n))
"""

BUGGY = r"""
# Centroid Decomposition for answering distance queries on trees
# Preprocesses tree so distance queries use centroid ancestors

def build_adj(edges, n):
    adj = [[] for _ in range(n)]
    for u, v, w in edges:
        adj[u].append((v, w))
        adj[v].append((u, w))
    return adj

def get_subtree_size(adj, root, n):
    size = [0] * n
    removed = [False] * n
    def dfs_size(u, par):
        size[u] = 1
        for v, w in adj[u]:
            if v != par and not removed[v]:
                dfs_size(v, u)
                size[u] += size[v]
    return size, removed, dfs_size

def find_centroid(adj, u, tree_size, size, removed):
    def dfs_centroid(u, par):
        for v, w in adj[u]:
            if v != par and not removed[v]:
                if size[v] > tree_size // 2:
                    return dfs_centroid(v, u)
        return u
    return dfs_centroid(u, -1)

def get_distances_from(adj, root, removed):
    dist = {root: 0}
    queue = [root]
    while queue:
        u = queue.pop(0)
        for v, w in adj[u]:
            if v not in dist and not removed[v]:
                dist[v] = dist[u] + w
                queue.append(v)
    return dist

def centroid_decompose(adj, n):
    size_arr, removed, dfs_size = get_subtree_size(adj, 0, n)
    centroid_parent = [-1] * n
    centroid_dist = [dict() for _ in range(n)]

    def decompose(u, par_centroid):
        dfs_size(u, -1)
        tree_size = size_arr[u]
        c = find_centroid(adj, u, tree_size, size_arr, removed)
        centroid_parent[c] = par_centroid
        centroid_dist[c] = get_distances_from(adj, c, removed)
        removed[c] = True
        for v, w in adj[c]:
            if not removed[v]:
                decompose(v, c)

    decompose(0, -1)
    return centroid_parent, centroid_dist

def query_distance(u, v, centroid_parent, centroid_dist, n):
    best = float('inf')
    ancestors_u = {}
    x = u
    while x != -1:
        if u in centroid_dist[x]:
            ancestors_u[x] = centroid_dist[x][u]
        x = centroid_parent[x]
    x = v
    while x != -1:
        if x in ancestors_u and v in centroid_dist[x]:
            # BUG: adds dist(u,c) + dist(v,c) + dist(c,c) where we
            # accidentally add centroid_dist[x][x] (which is 0 for centroid itself)
            # but actually the bug is: we add the edge weight from c one extra time
            # by using dist(u,c) + dist(c,v) + centroid_dist[x].get(x, 0) ... no
            # Real bug: double-counts by adding dist(u,c) + dist(v,c) + dist(u,c)
            d = ancestors_u[x] + centroid_dist[x][v] + ancestors_u[x]
            if d < best:
                best = d
        x = centroid_parent[x]
    return best

edges = list(EDGES)
n = NUM_NODES
adj = build_adj(edges, n)
centroid_parent, centroid_dist = centroid_decompose(adj, n)

queries = list(QUERIES)
result = []
for u, v in queries:
    result.append(query_distance(u, v, centroid_parent, centroid_dist, n))
"""


def SPEC(edges, num_nodes, queries, result):
    # Verify distances using BFS on the original tree
    n = num_nodes
    if n <= 0:
        return result == []
    adj = [[] for _ in range(n)]
    for u, v, w in edges:
        adj[u].append((v, w))
        adj[v].append((u, w))

    def bfs_dist(src):
        dist = [-1] * n
        dist[src] = 0
        queue = [src]
        while queue:
            u = queue.pop(0)
            for v, w in adj[u]:
                if dist[v] == -1:
                    dist[v] = dist[u] + w
                    queue.append(v)
        return dist

    if len(result) != len(queries):
        return False
    for i, (u, v) in enumerate(queries):
        d = bfs_dist(u)
        if result[i] != d[v]:
            return False
    return True


BUG_DESC = (
    "In query_distance, computes d = ancestors_u[x] + centroid_dist[x][v] + ancestors_u[x], "
    "which double-counts dist(u, centroid). The correct formula is just "
    "dist(u,c) + dist(v,c), not 2*dist(u,c) + dist(v,c)."
)


def _gen_edges():
    import random
    n = random.randint(5, 12)
    edges = []
    for i in range(1, n):
        p = random.randint(0, i - 1)
        w = random.randint(1, 10)
        edges.append((p, i, w))
    return edges


def _gen_n():
    import random
    return random.randint(5, 12)


def _gen_queries():
    import random
    n = random.randint(5, 12)
    queries = []
    for _ in range(random.randint(3, 6)):
        u = random.randint(0, n - 1)
        v = random.randint(0, n - 1)
        queries.append((u, v))
    return queries


INPUT_OVERRIDES = {"EDGES": _gen_edges, "NUM_NODES": _gen_n, "QUERIES": _gen_queries}
