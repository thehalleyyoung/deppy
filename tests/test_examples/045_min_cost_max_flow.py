"""Min-cost max-flow via successive shortest paths (Bellman-Ford based).

Finds maximum flow of minimum cost in a directed network. Uses Bellman-Ford
to find shortest (cheapest) augmenting paths and pushes flow along them.

Bug: when augmenting flow along a path, the reverse edge cost should be set
to the negation of the forward edge cost. The bug uses the original
(positive) cost for the reverse edge, making the reverse edges expensive
instead of refund-giving. This prevents proper flow rerouting and produces
suboptimal (too expensive) solutions.
"""

CORRECT = r"""
def min_cost_max_flow(num_nodes, edges, source, sink):
    # edges: list of (u, v, capacity, cost)
    # Build adjacency list with forward and reverse edges
    # Each edge stored as [to, cap, cost, rev_index]
    graph = [[] for _ in range(num_nodes)]

    def add_edge(u, v, cap, cost):
        graph[u].append([v, cap, cost, len(graph[v])])
        graph[v].append([u, 0, -cost, len(graph[u]) - 1])  # CORRECT: -cost

    for u, v, cap, cost in edges:
        add_edge(u, v, cap, cost)

    total_flow = 0
    total_cost = 0

    while True:
        # Bellman-Ford to find shortest path from source to sink
        dist = [float("inf")] * num_nodes
        dist[source] = 0
        in_queue = [False] * num_nodes
        prev_node = [-1] * num_nodes
        prev_edge = [-1] * num_nodes

        # SPFA (Bellman-Ford with queue)
        queue = [source]
        in_queue[source] = True

        while queue:
            u = queue.pop(0)
            in_queue[u] = False
            for i, (v, cap, cost, rev) in enumerate(graph[u]):
                if cap > 0 and dist[u] + cost < dist[v]:
                    dist[v] = dist[u] + cost
                    prev_node[v] = u
                    prev_edge[v] = i
                    if not in_queue[v]:
                        queue.append(v)
                        in_queue[v] = True

        if dist[sink] == float("inf"):
            break

        # Find bottleneck capacity along the path
        bottleneck = float("inf")
        v = sink
        while v != source:
            u = prev_node[v]
            e_idx = prev_edge[v]
            bottleneck = min(bottleneck, graph[u][e_idx][1])
            v = u

        # Augment flow along the path
        v = sink
        while v != source:
            u = prev_node[v]
            e_idx = prev_edge[v]
            graph[u][e_idx][1] -= bottleneck
            rev_idx = graph[u][e_idx][3]
            graph[v][rev_idx][1] += bottleneck
            v = u

        total_flow += bottleneck
        total_cost += bottleneck * dist[sink]

    return {"flow": total_flow, "cost": total_cost}

num_nodes = NUM_NODES
edges = EDGES
source = SOURCE
sink = SINK
result = min_cost_max_flow(num_nodes, edges, source, sink)
"""

BUGGY = r"""
def min_cost_max_flow(num_nodes, edges, source, sink):
    # edges: list of (u, v, capacity, cost)
    graph = [[] for _ in range(num_nodes)]

    def add_edge(u, v, cap, cost):
        graph[u].append([v, cap, cost, len(graph[v])])
        # BUG: reverse edge cost should be -cost, but uses +cost
        # This means traversing the reverse edge costs money instead of
        # refunding it, preventing optimal flow rerouting
        graph[v].append([u, 0, cost, len(graph[u]) - 1])  # BUG: cost instead of -cost

    for u, v, cap, cost in edges:
        add_edge(u, v, cap, cost)

    total_flow = 0
    total_cost = 0

    while True:
        dist = [float("inf")] * num_nodes
        dist[source] = 0
        in_queue = [False] * num_nodes
        prev_node = [-1] * num_nodes
        prev_edge = [-1] * num_nodes

        queue = [source]
        in_queue[source] = True

        while queue:
            u = queue.pop(0)
            in_queue[u] = False
            for i, (v, cap, cost, rev) in enumerate(graph[u]):
                if cap > 0 and dist[u] + cost < dist[v]:
                    dist[v] = dist[u] + cost
                    prev_node[v] = u
                    prev_edge[v] = i
                    if not in_queue[v]:
                        queue.append(v)
                        in_queue[v] = True

        if dist[sink] == float("inf"):
            break

        bottleneck = float("inf")
        v = sink
        while v != source:
            u = prev_node[v]
            e_idx = prev_edge[v]
            bottleneck = min(bottleneck, graph[u][e_idx][1])
            v = u

        v = sink
        while v != source:
            u = prev_node[v]
            e_idx = prev_edge[v]
            graph[u][e_idx][1] -= bottleneck
            rev_idx = graph[u][e_idx][3]
            graph[v][rev_idx][1] += bottleneck
            v = u

        total_flow += bottleneck
        total_cost += bottleneck * dist[sink]

    return {"flow": total_flow, "cost": total_cost}

num_nodes = NUM_NODES
edges = EDGES
source = SOURCE
sink = SINK
result = min_cost_max_flow(num_nodes, edges, source, sink)
"""


def SPEC(num_nodes, edges, source, sink, result):
    # Verify min-cost max-flow by checking:
    # 1) Flow is valid (max flow value)
    # 2) Cost matches a brute-force computation for small instances
    if not isinstance(result, dict):
        return False
    if "flow" not in result or "cost" not in result:
        return False

    flow_val = result["flow"]
    cost_val = result["cost"]

    if not isinstance(flow_val, (int, float)) or flow_val < 0:
        return False

    # Compute max flow using simple BFS (Edmonds-Karp) for verification
    # Build capacity graph
    cap = {}
    edge_cost = {}
    adj = [[] for _ in range(num_nodes)]
    for u, v, c, w in edges:
        if (u, v) not in cap:
            cap[(u, v)] = 0
            edge_cost[(u, v)] = w
            adj[u].append(v)
            adj[v].append(u)
        cap[(u, v)] += c
        if (v, u) not in cap:
            cap[(v, u)] = 0
            edge_cost[(v, u)] = -w

    # Simple max flow check
    def bfs_path():
        from collections import deque
        visited = {source}
        queue = deque([(source, [source])])
        while queue:
            node, path = queue.popleft()
            for nxt in adj[node]:
                if nxt not in visited and cap.get((node, nxt), 0) > 0:
                    visited.add(nxt)
                    if nxt == sink:
                        return path + [nxt]
                    queue.append((nxt, path + [nxt]))
        return None

    # Compute max flow value
    cap_copy = dict(cap)
    max_flow = 0
    while True:
        # Restore cap for this check
        pass
        path = bfs_path()
        if path is None:
            break
        # Find bottleneck
        bn = float("inf")
        for i in range(len(path) - 1):
            bn = min(bn, cap[(path[i], path[i + 1])])
        for i in range(len(path) - 1):
            cap[(path[i], path[i + 1])] -= bn
            cap[(path[i + 1], path[i])] = cap.get((path[i + 1], path[i]), 0) + bn
        max_flow += bn

    # Flow value should match max flow
    if flow_val != max_flow:
        return False

    # For cost: verify using a reference implementation
    # Re-run the correct algorithm inline
    graph2 = [[] for _ in range(num_nodes)]
    def add_e(u, v, c, w):
        graph2[u].append([v, c, w, len(graph2[v])])
        graph2[v].append([u, 0, -w, len(graph2[u]) - 1])
    for u, v, c, w in edges:
        add_e(u, v, c, w)
    ref_cost = 0
    ref_flow = 0
    while True:
        dist2 = [float("inf")] * num_nodes
        dist2[source] = 0
        inq = [False] * num_nodes
        pn = [-1] * num_nodes
        pe = [-1] * num_nodes
        q = [source]
        inq[source] = True
        while q:
            u = q.pop(0)
            inq[u] = False
            for i, (v, c2, w2, r) in enumerate(graph2[u]):
                if c2 > 0 and dist2[u] + w2 < dist2[v]:
                    dist2[v] = dist2[u] + w2
                    pn[v] = u
                    pe[v] = i
                    if not inq[v]:
                        q.append(v)
                        inq[v] = True
        if dist2[sink] == float("inf"):
            break
        bn = float("inf")
        v = sink
        while v != source:
            u = pn[v]
            bn = min(bn, graph2[u][pe[v]][1])
            v = u
        v = sink
        while v != source:
            u = pn[v]
            graph2[u][pe[v]][1] -= bn
            ri = graph2[u][pe[v]][3]
            graph2[v][ri][1] += bn
            v = u
        ref_flow += bn
        ref_cost += bn * dist2[sink]

    if cost_val != ref_cost:
        return False

    return True


BUG_DESC = (
    "When creating reverse edges for the residual graph, the cost of the "
    "reverse edge should be the negation of the forward edge cost (-cost). "
    "The bug uses the original positive cost, so pushing flow back along "
    "a reverse edge incurs cost instead of providing a refund. This prevents "
    "the algorithm from rerouting flow to find the minimum cost."
)


def _gen_num_nodes():
    return 5


def _gen_edges():
    import random
    # Create a small network with multiple paths of different costs
    edges = []
    # Ensure connectivity from 0 to 4 with varied costs
    edges.append((0, 1, random.randint(2, 5), random.randint(1, 3)))
    edges.append((0, 2, random.randint(2, 5), random.randint(1, 3)))
    edges.append((1, 3, random.randint(2, 5), random.randint(1, 4)))
    edges.append((2, 3, random.randint(2, 5), random.randint(1, 4)))
    edges.append((1, 2, random.randint(1, 3), random.randint(1, 2)))
    edges.append((3, 4, random.randint(3, 7), random.randint(1, 3)))
    edges.append((2, 4, random.randint(1, 3), random.randint(2, 5)))
    return edges


def _gen_source():
    return 0


def _gen_sink():
    return 4


INPUT_OVERRIDES = {
    "NUM_NODES": _gen_num_nodes,
    "EDGES": _gen_edges,
    "SOURCE": _gen_source,
    "SINK": _gen_sink,
}
