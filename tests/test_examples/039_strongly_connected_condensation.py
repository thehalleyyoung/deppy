"""Kosaraju's algorithm for SCC + DAG condensation. Bug: in second pass, uses original
graph instead of transposed graph, producing incorrect strongly connected components."""

CORRECT = r"""
# Kosaraju's algorithm: find SCCs and build condensation DAG
# DIGRAPH_EDGES is a list of (u, v) directed edges, DIGRAPH_N is vertex count

n = DIGRAPH_N
edges = DIGRAPH_EDGES

# Build adjacency lists for original and transposed graph
adj = [[] for _ in range(n)]
adj_t = [[] for _ in range(n)]
for u, v in edges:
    adj[u].append(v)
    adj_t[v].append(u)

# First pass: DFS on original graph, record finish order
visited = [False] * n
finish_order = []

def dfs1(v):
    stack = [(v, False)]
    while stack:
        node, processed = stack.pop()
        if processed:
            finish_order.append(node)
            continue
        if visited[node]:
            continue
        visited[node] = True
        stack.append((node, True))
        for u in adj[node]:
            if not visited[u]:
                stack.append((u, False))

for i in range(n):
    if not visited[i]:
        dfs1(i)

# Second pass: DFS on TRANSPOSED graph in reverse finish order
comp = [-1] * n
num_components = 0

def dfs2(v, c):
    stack = [v]
    while stack:
        node = stack.pop()
        if comp[node] != -1:
            continue
        comp[node] = c
        for u in adj_t[node]:
            if comp[u] == -1:
                stack.append(u)

for v in reversed(finish_order):
    if comp[v] == -1:
        dfs2(v, num_components)
        num_components += 1

# Build condensation DAG
dag_edges = set()
for u, v in edges:
    if comp[u] != comp[v]:
        dag_edges.add((comp[u], comp[v]))

# Group vertices by component
components = [[] for _ in range(num_components)]
for v in range(n):
    components[comp[v]].append(v)

result = {
    "comp": comp,
    "num_components": num_components,
    "components": components,
    "dag_edges": sorted(dag_edges),
    "n": n,
}
"""

BUGGY = r"""
# Kosaraju's algorithm with transposition bug
n = DIGRAPH_N
edges = DIGRAPH_EDGES

adj = [[] for _ in range(n)]
adj_t = [[] for _ in range(n)]
for u, v in edges:
    adj[u].append(v)
    adj_t[v].append(u)

visited = [False] * n
finish_order = []

def dfs1(v):
    stack = [(v, False)]
    while stack:
        node, processed = stack.pop()
        if processed:
            finish_order.append(node)
            continue
        if visited[node]:
            continue
        visited[node] = True
        stack.append((node, True))
        for u in adj[node]:
            if not visited[u]:
                stack.append((u, False))

for i in range(n):
    if not visited[i]:
        dfs1(i)

# Second pass: BUG - uses adj (original graph) instead of adj_t (transposed)
# This means the second DFS follows edges in the wrong direction
comp = [-1] * n
num_components = 0

def dfs2(v, c):
    stack = [v]
    while stack:
        node = stack.pop()
        if comp[node] != -1:
            continue
        comp[node] = c
        # BUG: should use adj_t[node] (transposed graph)
        for u in adj[node]:
            if comp[u] == -1:
                stack.append(u)

for v in reversed(finish_order):
    if comp[v] == -1:
        dfs2(v, num_components)
        num_components += 1

dag_edges = set()
for u, v in edges:
    if comp[u] != comp[v]:
        dag_edges.add((comp[u], comp[v]))

components = [[] for _ in range(num_components)]
for v in range(n):
    components[comp[v]].append(v)

result = {
    "comp": comp,
    "num_components": num_components,
    "components": components,
    "dag_edges": sorted(dag_edges),
    "n": n,
}
"""

def SPEC(digraph_n, digraph_edges, result):
    """Verify SCC and condensation correctness."""
    n = result["n"]
    comp = result["comp"]
    num_comp = result["num_components"]
    components = result["components"]
    dag_edges = result["dag_edges"]

    # Every vertex assigned to a component
    for v in range(n):
        if comp[v] < 0 or comp[v] >= num_comp:
            return False

    # Components partition all vertices
    all_verts = set()
    for c in components:
        for v in c:
            if v in all_verts:
                return False
            all_verts.add(v)
    if all_verts != set(range(n)):
        return False

    # Build adjacency for reachability check
    adj = [[] for _ in range(n)]
    for u, v in digraph_edges:
        adj[u].append(v)

    def can_reach(src, dst):
        visited = set()
        stack = [src]
        while stack:
            node = stack.pop()
            if node == dst:
                return True
            if node in visited:
                continue
            visited.add(node)
            for nb in adj[node]:
                stack.append(nb)
        return False

    # Within each SCC, every pair of vertices must be mutually reachable
    for c in components:
        for i in range(len(c)):
            for j in range(i + 1, len(c)):
                if not can_reach(c[i], c[j]) or not can_reach(c[j], c[i]):
                    return False

    # Vertices in different SCCs must NOT be mutually reachable
    # (at least one direction must fail)
    for ci in range(num_comp):
        for cj in range(ci + 1, num_comp):
            u = components[ci][0]
            v = components[cj][0]
            if can_reach(u, v) and can_reach(v, u):
                return False

    # Condensation DAG must be acyclic
    # Topological sort check
    in_deg = [0] * num_comp
    dag_adj = [[] for _ in range(num_comp)]
    for u, v in dag_edges:
        dag_adj[u].append(v)
        in_deg[v] += 1
    from collections import deque
    queue = deque([i for i in range(num_comp) if in_deg[i] == 0])
    topo_count = 0
    while queue:
        node = queue.popleft()
        topo_count += 1
        for nb in dag_adj[node]:
            in_deg[nb] -= 1
            if in_deg[nb] == 0:
                queue.append(nb)
    if topo_count != num_comp:
        return False

    return True

BUG_DESC = "In the second pass of Kosaraju's algorithm, uses the original graph instead of the transposed graph, causing vertices to be grouped into incorrect strongly connected components."

def _gen():
    import random
    # The bug uses adj (original) instead of adj_t (transposed) in the 2nd DFS pass.
    # To trigger: need a directed graph where traversing forward from a node in
    # reverse-finish-order reaches vertices in a different SCC, but traversing
    # backward (transpose) would not. This happens when there's a one-way bridge
    # between SCCs: e.g., SCC1 -> SCC2 but not SCC2 -> SCC1.
    #
    # With the bug, the 2nd pass DFS follows forward edges and merges separate
    # SCCs into one. We need at least 2 SCCs with a cross-edge from one to another.
    #
    # Reliable structure: two cycles connected by a single directed edge.
    # Cycle A: 0->1->2->0, Cycle B: 3->4->5->3, Bridge: 2->3
    # Correct: {0,1,2} and {3,4,5}
    # Buggy: 2nd pass follows adj, so from the last-finished node it can reach
    # across the bridge and merge them.

    # Pick small sizes for reliability
    scc1_size = random.randint(2, 4)
    scc2_size = random.randint(2, 4)
    n = scc1_size + scc2_size
    edges = []
    edge_set = set()

    # SCC 1: cycle on [0, scc1_size)
    for i in range(scc1_size):
        e = (i, (i + 1) % scc1_size)
        edges.append(e)
        edge_set.add(e)

    # SCC 2: cycle on [scc1_size, n)
    for i in range(scc2_size):
        u = scc1_size + i
        v = scc1_size + (i + 1) % scc2_size
        e = (u, v)
        edges.append(e)
        edge_set.add(e)

    # One-way bridge from SCC1 to SCC2
    bridge_src = random.randint(0, scc1_size - 1)
    bridge_dst = random.randint(scc1_size, n - 1)
    e = (bridge_src, bridge_dst)
    if e not in edge_set:
        edges.append(e)
        edge_set.add(e)

    # Optionally add a second one-way bridge (still same direction) for variety
    if random.random() < 0.5:
        src2 = random.randint(0, scc1_size - 1)
        dst2 = random.randint(scc1_size, n - 1)
        e2 = (src2, dst2)
        if e2 not in edge_set:
            edges.append(e2)
            edge_set.add(e2)

    return {"DIGRAPH_N": n, "DIGRAPH_EDGES": edges}

INPUT_OVERRIDES = _gen
