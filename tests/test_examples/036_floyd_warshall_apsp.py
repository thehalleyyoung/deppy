"""Floyd-Warshall all-pairs shortest paths. Bug: initializes diagonal to infinity instead
of 0, causing self-distance to be nonzero which propagates errors through path computation."""

CORRECT = r"""
# Floyd-Warshall all-pairs shortest paths
# GRAPH is a list of (u, v, weight) edges, N is number of vertices

n = NUM_VERTICES
edges = WEIGHTED_EDGES

INF = float('inf')

# Initialize distance matrix
dist = [[INF] * n for _ in range(n)]
nxt = [[-1] * n for _ in range(n)]

# Self-distance is 0
for i in range(n):
    dist[i][i] = 0
    nxt[i][i] = i

# Set direct edges
for u, v, w in edges:
    if w < dist[u][v]:
        dist[u][v] = w
        nxt[u][v] = v
    if w < dist[v][u]:
        dist[v][u] = w
        nxt[v][u] = u

# Floyd-Warshall relaxation
for k in range(n):
    for i in range(n):
        for j in range(n):
            if dist[i][k] + dist[k][j] < dist[i][j]:
                dist[i][j] = dist[i][k] + dist[k][j]
                nxt[i][j] = nxt[i][k]

# Reconstruct all paths
def reconstruct_path(src, dst):
    if dist[src][dst] == INF:
        return []
    path = [src]
    curr = src
    while curr != dst:
        curr = nxt[curr][dst]
        if curr == -1:
            return []
        path.append(curr)
    return path

# Build paths for all reachable pairs
all_paths = {}
for i in range(n):
    for j in range(n):
        if i != j and dist[i][j] < INF:
            all_paths[(i, j)] = reconstruct_path(i, j)

result = {
    "dist": dist,
    "next": nxt,
    "all_paths": all_paths,
    "n": n,
}
"""

BUGGY = r"""
# Floyd-Warshall with diagonal initialization bug
n = NUM_VERTICES
edges = WEIGHTED_EDGES

INF = float('inf')

dist = [[INF] * n for _ in range(n)]
nxt = [[-1] * n for _ in range(n)]

# BUG: Missing initialization of dist[i][i] = 0
# The diagonal stays at INF, meaning self-loops cost infinity
# This propagates: paths i->k->i->k->j won't work correctly
# and any path through a vertex gets wrong distance

# Set direct edges
for u, v, w in edges:
    if w < dist[u][v]:
        dist[u][v] = w
        nxt[u][v] = v
    if w < dist[v][u]:
        dist[v][u] = w
        nxt[v][u] = u

# Floyd-Warshall relaxation
for k in range(n):
    for i in range(n):
        for j in range(n):
            if dist[i][k] + dist[k][j] < dist[i][j]:
                dist[i][j] = dist[i][k] + dist[k][j]
                nxt[i][j] = nxt[i][k]

def reconstruct_path(src, dst):
    if dist[src][dst] == INF:
        return []
    path = [src]
    curr = src
    while curr != dst:
        curr = nxt[curr][dst]
        if curr == -1:
            return []
        path.append(curr)
    return path

all_paths = {}
for i in range(n):
    for j in range(n):
        if i != j and dist[i][j] < INF:
            all_paths[(i, j)] = reconstruct_path(i, j)

result = {
    "dist": dist,
    "next": nxt,
    "all_paths": all_paths,
    "n": n,
}
"""

def SPEC(num_vertices, weighted_edges, result):
    """Verify Floyd-Warshall APSP correctness."""
    n = result["n"]
    dist = result["dist"]
    all_paths = result["all_paths"]

    # Self-distance must be 0
    for i in range(n):
        if dist[i][i] != 0:
            return False

    # Build adjacency for verification
    from collections import defaultdict
    import heapq

    adj = defaultdict(list)
    for u, v, w in weighted_edges:
        adj[u].append((v, w))
        adj[v].append((u, w))

    # Verify distances with Dijkstra from each source
    def dijkstra(src):
        d = [float('inf')] * n
        d[src] = 0
        pq = [(0, src)]
        while pq:
            cost, u = heapq.heappop(pq)
            if cost > d[u]:
                continue
            for v, w in adj[u]:
                if d[u] + w < d[v]:
                    d[v] = d[u] + w
                    heapq.heappush(pq, (d[v], v))
        return d

    for src in range(n):
        true_dist = dijkstra(src)
        for dst in range(n):
            td = true_dist[dst]
            fd = dist[src][dst]
            if td == float('inf') and fd == float('inf'):
                continue
            if abs(td - fd) > 1e-9:
                return False

    # Verify paths are consistent with distances
    for (i, j), path in all_paths.items():
        if len(path) < 2:
            return False
        if path[0] != i or path[-1] != j:
            return False
        # Sum path weights
        total = 0
        valid = True
        for k in range(len(path) - 1):
            u, v = path[k], path[k + 1]
            # Find minimum weight edge between u and v
            min_w = float('inf')
            for nb, w in adj[u]:
                if nb == v and w < min_w:
                    min_w = w
            if min_w == float('inf'):
                valid = False
                break
            total += min_w
        if valid and abs(total - dist[i][j]) > 1e-9:
            return False

    return True

BUG_DESC = "Fails to initialize dist[i][i] = 0 on the diagonal, leaving self-distance as infinity, which prevents the Floyd-Warshall relaxation from computing correct shortest paths."

def _gen():
    import random
    # Bug: doesn't initialize dist[i][i] = 0. During FW relaxation, dist[i][i]
    # will become min round-trip distance (e.g., dist[i][j] + dist[j][i]) which
    # is > 0. SPEC checks dist[i][i] != 0 directly, catching this.
    #
    # Any connected graph triggers the bug since dist[i][i] will be set to
    # the minimum 2-hop round trip cost, not 0.
    # Keep sizes small (max_size=8).
    n = random.randint(3, 6)
    edges = []
    edge_set = set()
    # Spanning tree
    for i in range(1, n):
        parent = random.randint(0, i - 1)
        w = random.randint(1, 10)
        e = (min(i, parent), max(i, parent))
        if e not in edge_set:
            edge_set.add(e)
            edges.append((i, parent, w))
    # A couple extra edges
    for _ in range(random.randint(0, 2)):
        u = random.randint(0, n - 1)
        v = random.randint(0, n - 1)
        if u != v:
            e = (min(u, v), max(u, v))
            if e not in edge_set:
                edge_set.add(e)
                w = random.randint(1, 10)
                edges.append((u, v, w))
    return {"NUM_VERTICES": n, "WEIGHTED_EDGES": edges}

INPUT_OVERRIDES = _gen
