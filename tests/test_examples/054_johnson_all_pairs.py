"""Johnson's algorithm for all-pairs shortest paths.

Uses Bellman-Ford to compute potentials, then reweights edges and runs
Dijkstra from each source. Bug: after computing Dijkstra distances with
reweighted edges, forgets to subtract h[u] - h[v] to recover the true
shortest distances.
"""

CORRECT = r"""
import heapq

def bellman_ford(n, edges, source):
    dist = [float('inf')] * n
    dist[source] = 0
    for _ in range(n - 1):
        for u, v, w in edges:
            if dist[u] < float('inf') and dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
    # Check for negative cycles
    for u, v, w in edges:
        if dist[u] < float('inf') and dist[u] + w < dist[v]:
            return None  # negative cycle
    return dist

def dijkstra(adj, source, n):
    dist = [float('inf')] * n
    dist[source] = 0
    pq = [(0, source)]
    while pq:
        d, u = heapq.heappop(pq)
        if d > dist[u]:
            continue
        for v, w in adj[u]:
            nd = d + w
            if nd < dist[v]:
                dist[v] = nd
                heapq.heappush(pq, (nd, v))
    return dist

def johnson(n, edges):
    # Add virtual node n connected to all with weight 0
    new_edges = list(edges)
    for v in range(n):
        new_edges.append((n, v, 0))

    h = bellman_ford(n + 1, new_edges, n)
    if h is None:
        return None  # negative cycle

    # Reweight edges
    reweighted_adj = [[] for _ in range(n)]
    for u, v, w in edges:
        new_w = w + h[u] - h[v]
        reweighted_adj[u].append((v, new_w))

    # Run Dijkstra from each node
    result = []
    for u in range(n):
        d = dijkstra(reweighted_adj, u, n)
        row = []
        for v in range(n):
            if d[v] == float('inf'):
                row.append(float('inf'))
            else:
                # CORRECT: adjust back by subtracting h[u] - h[v]
                row.append(d[v] - h[u] + h[v])
        result.append(row)
    return result

n_nodes = N_NODES
edges = EDGES
result = johnson(n_nodes, edges)
"""

BUGGY = r"""
import heapq

def bellman_ford(n, edges, source):
    dist = [float('inf')] * n
    dist[source] = 0
    for _ in range(n - 1):
        for u, v, w in edges:
            if dist[u] < float('inf') and dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
    for u, v, w in edges:
        if dist[u] < float('inf') and dist[u] + w < dist[v]:
            return None
    return dist

def dijkstra(adj, source, n):
    dist = [float('inf')] * n
    dist[source] = 0
    pq = [(0, source)]
    while pq:
        d, u = heapq.heappop(pq)
        if d > dist[u]:
            continue
        for v, w in adj[u]:
            nd = d + w
            if nd < dist[v]:
                dist[v] = nd
                heapq.heappush(pq, (nd, v))
    return dist

def johnson(n, edges):
    new_edges = list(edges)
    for v in range(n):
        new_edges.append((n, v, 0))

    h = bellman_ford(n + 1, new_edges, n)
    if h is None:
        return None

    reweighted_adj = [[] for _ in range(n)]
    for u, v, w in edges:
        new_w = w + h[u] - h[v]
        reweighted_adj[u].append((v, new_w))

    result = []
    for u in range(n):
        d = dijkstra(reweighted_adj, u, n)
        row = []
        for v in range(n):
            if d[v] == float('inf'):
                row.append(float('inf'))
            else:
                # BUG: returns reweighted distance without adjustment
                row.append(d[v])
        result.append(row)
    return result

n_nodes = N_NODES
edges = EDGES
result = johnson(n_nodes, edges)
"""


def SPEC(n_nodes, edges, result):
    if result is None:
        # Could be negative cycle; verify with Bellman-Ford
        dist = [float('inf')] * n_nodes
        dist[0] = 0
        for _ in range(n_nodes - 1):
            for u, v, w in edges:
                if dist[u] < float('inf') and dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
        for u, v, w in edges:
            if dist[u] < float('inf') and dist[u] + w < dist[v]:
                return True  # correctly detected
        return False  # false negative cycle report

    if not isinstance(result, list) or len(result) != n_nodes:
        return False

    # Verify each result[u][v] is the true shortest path via Bellman-Ford
    # Build adjacency for BF
    for src in range(n_nodes):
        dist = [float('inf')] * n_nodes
        dist[src] = 0
        for _ in range(n_nodes - 1):
            for u, v, w in edges:
                if dist[u] < float('inf') and dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w

        row = result[src]
        if not isinstance(row, list) or len(row) != n_nodes:
            return False
        for v in range(n_nodes):
            expected = dist[v]
            actual = row[v]
            if expected == float('inf'):
                if actual != float('inf'):
                    return False
            else:
                if abs(actual - expected) > 1e-9:
                    return False

    return True


BUG_DESC = (
    "After running Dijkstra with reweighted edges, the algorithm reports "
    "the reweighted distances directly instead of adjusting back by "
    "subtracting h[u] - h[v]. This means all reported distances are offset "
    "by the potential difference, giving wrong shortest path values whenever "
    "potentials differ."
)


def _gen():
    import random
    # The bug: after Dijkstra on reweighted edges, the code returns
    # d[v] directly instead of d[v] - h[u] + h[v]. The error is
    # (h[u] - h[v]) for each (u,v) pair. This only matters when
    # potentials differ, which requires negative-weight edges.
    #
    # Strategy: build a small graph (3-5 nodes) with a guaranteed
    # negative edge and no negative cycle. A simple chain with one
    # negative edge suffices.
    #
    # Example: 0->1 weight 5, 1->2 weight -3, 0->2 weight 4
    # h = [0, 0, -3], reweighted: 0->1:5, 1->2:0, 0->2:7
    # Dijkstra from 0: d=[0,5,5], correct: [0,5,5-0+(-3)]=[0,5,2], buggy: [0,5,5]

    n = random.randint(3, 5)

    while True:
        edges = []
        # Forward chain with positive weights
        for i in range(n - 1):
            edges.append((i, i + 1, random.randint(3, 8)))

        # Add 1-2 negative edges (but not forming negative cycles)
        neg_count = random.randint(1, 2)
        for _ in range(neg_count):
            u = random.randint(0, n - 2)
            v = random.randint(u + 1, n - 1)
            w = random.randint(-5, -1)
            edges.append((u, v, w))

        # Verify no negative cycle
        dist = [0] * (n + 1)
        all_edges = edges + [(n, v, 0) for v in range(n)]
        for _ in range(n):
            for u, v, w in all_edges:
                if dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
        has_neg_cycle = False
        for u, v, w in all_edges:
            if dist[u] + w < dist[v]:
                has_neg_cycle = True
                break

        # Verify potentials actually differ (otherwise bug doesn't manifest)
        potentials = dist[:n]
        potentials_differ = len(set(potentials)) > 1

        if not has_neg_cycle and potentials_differ:
            return {"N_NODES": n, "EDGES": edges}

INPUT_OVERRIDES = _gen
