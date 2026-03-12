"""Ford-Fulkerson (Edmonds-Karp) max-flow with min-cut extraction."""

import random
from collections import deque

CORRECT = """
from collections import deque

def solve(n, edges, source, sink):
    # Build adjacency list with capacities
    # edges: list of (u, v, cap)
    graph = [[0] * n for _ in range(n)]
    original_cap = [[0] * n for _ in range(n)]
    for u, v, cap in edges:
        graph[u][v] += cap
        original_cap[u][v] += cap

    def bfs(source, sink, parent):
        visited = [False] * n
        visited[source] = True
        queue = deque([source])
        while queue:
            u = queue.popleft()
            for v in range(n):
                if not visited[v] and graph[u][v] > 0:
                    visited[v] = True
                    parent[v] = u
                    if v == sink:
                        return True
                    queue.append(v)
        return False

    max_flow = 0
    parent = [-1] * n

    while bfs(source, sink, parent):
        # Find min residual capacity along the path
        path_flow = float('inf')
        v = sink
        while v != source:
            u = parent[v]
            path_flow = min(path_flow, graph[u][v])
            v = u

        # Update residual capacities
        v = sink
        while v != source:
            u = parent[v]
            graph[u][v] -= path_flow
            graph[v][u] += path_flow
            v = u

        max_flow += path_flow
        parent = [-1] * n

    # Find min cut: BFS on residual graph from source
    visited = [False] * n
    visited[source] = True
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in range(n):
            if not visited[v] and graph[u][v] > 0:
                visited[v] = True
                queue.append(v)

    S = sorted([i for i in range(n) if visited[i]])
    T = sorted([i for i in range(n) if not visited[i]])

    cut_edges = []
    for u in S:
        for v in T:
            if original_cap[u][v] > 0:
                cut_edges.append((u, v, original_cap[u][v]))

    return (max_flow, S, T, cut_edges)
"""

BUGGY = """
from collections import deque

def solve(n, edges, source, sink):
    # Build adjacency list with capacities
    graph = [[0] * n for _ in range(n)]
    original_cap = [[0] * n for _ in range(n)]
    for u, v, cap in edges:
        graph[u][v] += cap
        original_cap[u][v] += cap
        # BUG: reverse edges initialized to forward capacity instead of 0
        # This inflates the residual graph before any flow is sent
        if original_cap[v][u] == 0:
            graph[v][u] = cap

    def bfs(source, sink, parent):
        visited = [False] * n
        visited[source] = True
        queue = deque([source])
        while queue:
            u = queue.popleft()
            for v in range(n):
                if not visited[v] and graph[u][v] > 0:
                    visited[v] = True
                    parent[v] = u
                    if v == sink:
                        return True
                    queue.append(v)
        return False

    max_flow = 0
    parent = [-1] * n

    while bfs(source, sink, parent):
        path_flow = float('inf')
        v = sink
        while v != source:
            u = parent[v]
            path_flow = min(path_flow, graph[u][v])
            v = u

        v = sink
        while v != source:
            u = parent[v]
            graph[u][v] -= path_flow
            graph[v][u] += path_flow
            v = u

        max_flow += path_flow
        parent = [-1] * n

    # Find min cut via BFS on residual graph
    visited = [False] * n
    visited[source] = True
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in range(n):
            if not visited[v] and graph[u][v] > 0:
                visited[v] = True
                queue.append(v)

    S = sorted([i for i in range(n) if visited[i]])
    T = sorted([i for i in range(n) if not visited[i]])

    cut_edges = []
    for u in S:
        for v in T:
            if original_cap[u][v] > 0:
                cut_edges.append((u, v, original_cap[u][v]))

    return (max_flow, S, T, cut_edges)
"""

BUG_DESC = (
    "When constructing the residual graph, reverse edges are initialized with "
    "forward capacity instead of 0. This creates phantom residual capacity on "
    "reverse edges before any flow is sent, causing the max-flow algorithm to "
    "route flow through non-existent reverse paths and producing an incorrect "
    "max-flow value and min-cut partition."
)


def SPEC(n, edges, source, sink, result):
    """Verify min-cut correctness."""
    max_flow, S, T, cut_edges = result

    # (1) S and T partition all nodes
    all_nodes = set(range(n))
    if set(S) | set(T) != all_nodes:
        return False
    if set(S) & set(T):
        return False

    # (2) source in S, sink in T
    if source not in S or sink not in T:
        return False

    # (3) Cut capacity equals max_flow
    cap_map = {}
    for u, v, cap in edges:
        cap_map[(u, v)] = cap_map.get((u, v), 0) + cap

    cut_capacity = 0
    s_set = set(S)
    t_set = set(T)
    for (u, v), cap in cap_map.items():
        if u in s_set and v in t_set:
            cut_capacity += cap

    if cut_capacity != max_flow:
        return False

    # (4) Verify max flow via reference: run clean Edmonds-Karp
    from collections import deque as dq
    g = [[0] * n for _ in range(n)]
    for u, v, cap in edges:
        g[u][v] += cap

    def ref_bfs(src, snk, par):
        vis = [False] * n
        vis[src] = True
        q = dq([src])
        while q:
            uu = q.popleft()
            for vv in range(n):
                if not vis[vv] and g[uu][vv] > 0:
                    vis[vv] = True
                    par[vv] = uu
                    if vv == snk:
                        return True
                    q.append(vv)
        return False

    ref_flow = 0
    par = [-1] * n
    while ref_bfs(source, sink, par):
        pf = float('inf')
        v = sink
        while v != source:
            u = par[v]
            pf = min(pf, g[u][v])
            v = u
        v = sink
        while v != source:
            u = par[v]
            g[u][v] -= pf
            g[v][u] += pf
            v = u
        ref_flow += pf
        par = [-1] * n

    if max_flow != ref_flow:
        return False

    return True


def _gen_input():
    n = random.randint(5, 7)
    source = 0
    sink = n - 1
    edges = []
    # Ensure path from source to sink
    for i in range(n - 1):
        edges.append((i, i + 1, random.randint(1, 10)))
    # Add random extra edges (no self-loops, directed)
    for _ in range(random.randint(3, 8)):
        u = random.randint(0, n - 2)
        v = random.randint(u + 1, n - 1)
        edges.append((u, v, random.randint(1, 10)))
    return {"n": n, "edges": edges, "source": source, "sink": sink}


INPUT_OVERRIDES = {"_gen": _gen_input}
