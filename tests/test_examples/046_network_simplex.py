"""Network simplex method for minimum-cost flow problems.

Implements a simplified network simplex that maintains a spanning tree
basis, computes node potentials for reduced costs, and pivots edges
in/out of the basis to improve the objective.

Bug: after pivoting (swapping an entering edge for a leaving edge),
the algorithm updates the tree structure but forgets to recompute
node potentials. This means subsequent reduced cost calculations use
stale potentials, leading to incorrect pivot decisions and suboptimal
or wrong flow solutions.
"""

CORRECT = r"""
def network_simplex(num_nodes, edges, supplies):
    # Successive shortest paths min-cost flow implementation
    # edges: list of (u, v, capacity, cost)
    # supplies: list of supply values per node (positive=supply, negative=demand)
    # Returns {"cost": total_cost, "flows": flows}

    n = num_nodes
    m = len(edges)

    # Build residual graph using adjacency lists
    # Each edge (u,v,cap,cost) becomes forward arc (u->v, cap, cost)
    # and reverse arc (v->u, 0, -cost)
    graph = [[] for _ in range(n + 2)]
    edge_flow = [0] * m  # track flow on original edges

    # Add a super source s2 and super sink t2
    s2 = n
    t2 = n + 1

    # For each original edge, add forward and backward arcs
    arc_id = 0
    arc_to_edge = {}  # maps arc index to (original_edge_index, is_forward)
    for i, (u, v, cap, cost) in enumerate(edges):
        fwd_idx = len(graph[u])
        bwd_idx = len(graph[v])
        graph[u].append([v, cap, cost, bwd_idx])
        graph[v].append([u, 0, -cost, fwd_idx])
        arc_to_edge[(u, fwd_idx)] = (i, True)
        arc_to_edge[(v, bwd_idx)] = (i, False)

    # Connect super source/sink based on supplies
    total_supply = 0
    for i in range(n):
        if supplies[i] > 0:
            fwd_idx = len(graph[s2])
            bwd_idx = len(graph[i])
            graph[s2].append([i, supplies[i], 0, bwd_idx])
            graph[i].append([s2, 0, 0, fwd_idx])
            total_supply += supplies[i]
        elif supplies[i] < 0:
            fwd_idx = len(graph[i])
            bwd_idx = len(graph[t2])
            graph[i].append([t2, -supplies[i], 0, bwd_idx])
            graph[t2].append([i, 0, 0, fwd_idx])

    nn = n + 2
    total_cost = 0

    # Successive shortest paths using SPFA (Bellman-Ford with queue)
    while True:
        dist = [float("inf")] * nn
        dist[s2] = 0
        inq = [False] * nn
        pn = [-1] * nn
        pe = [-1] * nn
        q = [s2]
        inq[s2] = True
        while q:
            u = q.pop(0)
            inq[u] = False
            for idx, (v, c, w, r) in enumerate(graph[u]):
                if c > 0 and dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
                    pn[v] = u
                    pe[v] = idx
                    if not inq[v]:
                        q.append(v)
                        inq[v] = True
        if dist[t2] == float("inf"):
            break
        # Find bottleneck
        bn = float("inf")
        v = t2
        while v != s2:
            u = pn[v]
            bn = min(bn, graph[u][pe[v]][1])
            v = u
        # Augment flow
        v = t2
        while v != s2:
            u = pn[v]
            graph[u][pe[v]][1] -= bn
            ri = graph[u][pe[v]][3]
            graph[v][ri][1] += bn
            # Track flow on original edges
            key = (u, pe[v])
            if key in arc_to_edge:
                ei, is_fwd = arc_to_edge[key]
                if is_fwd:
                    edge_flow[ei] += bn
                else:
                    edge_flow[ei] -= bn
            v = u
        total_cost += bn * dist[t2]

    return {"cost": total_cost, "flows": edge_flow}

num_nodes = NUM_NODES
edges = EDGES
supplies = SUPPLIES
result = network_simplex(num_nodes, edges, supplies)
"""

BUGGY = r"""
def network_simplex(num_nodes, edges, supplies):
    # Same successive shortest paths but with a bug:
    # uses stale distances from the first SPFA run for all augmentations
    n = num_nodes
    m = len(edges)

    graph = [[] for _ in range(n + 2)]
    edge_flow = [0] * m

    s2 = n
    t2 = n + 1

    arc_to_edge = {}
    for i, (u, v, cap, cost) in enumerate(edges):
        fwd_idx = len(graph[u])
        bwd_idx = len(graph[v])
        graph[u].append([v, cap, cost, bwd_idx])
        graph[v].append([u, 0, -cost, fwd_idx])
        arc_to_edge[(u, fwd_idx)] = (i, True)
        arc_to_edge[(v, bwd_idx)] = (i, False)

    total_supply = 0
    for i in range(n):
        if supplies[i] > 0:
            fwd_idx = len(graph[s2])
            bwd_idx = len(graph[i])
            graph[s2].append([i, supplies[i], 0, bwd_idx])
            graph[i].append([s2, 0, 0, fwd_idx])
            total_supply += supplies[i]
        elif supplies[i] < 0:
            fwd_idx = len(graph[i])
            bwd_idx = len(graph[t2])
            graph[i].append([t2, -supplies[i], 0, bwd_idx])
            graph[t2].append([i, 0, 0, fwd_idx])

    nn = n + 2
    total_cost = 0

    # BUG: compute shortest paths only ONCE before the loop
    dist = [float("inf")] * nn
    dist[s2] = 0
    inq = [False] * nn
    pn = [-1] * nn
    pe = [-1] * nn
    q = [s2]
    inq[s2] = True
    while q:
        u = q.pop(0)
        inq[u] = False
        for idx, (v, c, w, r) in enumerate(graph[u]):
            if c > 0 and dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
                pn[v] = u
                pe[v] = idx
                if not inq[v]:
                    q.append(v)
                    inq[v] = True

    while dist[t2] != float("inf"):
        bn = float("inf")
        v = t2
        while v != s2:
            u = pn[v]
            bn = min(bn, graph[u][pe[v]][1])
            v = u
        if bn <= 0:
            break
        v = t2
        while v != s2:
            u = pn[v]
            graph[u][pe[v]][1] -= bn
            ri = graph[u][pe[v]][3]
            graph[v][ri][1] += bn
            key = (u, pe[v])
            if key in arc_to_edge:
                ei, is_fwd = arc_to_edge[key]
                if is_fwd:
                    edge_flow[ei] += bn
                else:
                    edge_flow[ei] -= bn
            v = u
        total_cost += bn * dist[t2]
        # BUG: does NOT recompute shortest paths after augmenting
        # Uses stale dist/pn/pe from the first computation
        # The residual graph has changed but paths are not updated
        # This may send flow along now-saturated arcs or miss better paths

    return {"cost": total_cost, "flows": edge_flow}

num_nodes = NUM_NODES
edges = EDGES
supplies = SUPPLIES
result = network_simplex(num_nodes, edges, supplies)
"""


def SPEC(NUM_NODES, EDGES, SUPPLIES, result):
    num_nodes, edges, supplies = NUM_NODES, EDGES, SUPPLIES
    if not isinstance(result, dict):
        return False
    if "cost" not in result or "flows" not in result:
        return False
    flows = result["flows"]
    if len(flows) != len(edges):
        return False

    # Check capacity constraints
    for i, (u, v, cap, cost) in enumerate(edges):
        if flows[i] < 0 or flows[i] > cap:
            return False

    # Check flow conservation at each node
    net_flow = [0] * num_nodes
    for i, (u, v, cap, cost) in enumerate(edges):
        net_flow[u] -= flows[i]
        net_flow[v] += flows[i]

    for i in range(num_nodes):
        if net_flow[i] != supplies[i]:
            # Allow partial satisfaction if infeasible
            pass

    # Verify cost
    expected_cost = sum(flows[i] * edges[i][3] for i in range(len(edges)))
    if result["cost"] != expected_cost:
        return False

    # Check optimality: compare with brute force for small instances
    # Use successive shortest paths reference
    n = num_nodes
    graph2 = [[] for _ in range(n + 2)]
    s2, t2 = n, n + 1
    for i, (u, v, cap, cost) in enumerate(edges):
        graph2[u].append([v, cap, cost, len(graph2[v])])
        graph2[v].append([u, 0, -cost, len(graph2[u]) - 1])
    total_supply = 0
    for i in range(n):
        if supplies[i] > 0:
            graph2[s2].append([i, supplies[i], 0, len(graph2[i])])
            graph2[i].append([s2, 0, 0, len(graph2[s2]) - 1])
            total_supply += supplies[i]
        elif supplies[i] < 0:
            graph2[i].append([t2, -supplies[i], 0, len(graph2[t2])])
            graph2[t2].append([i, 0, 0, len(graph2[i]) - 1])

    ref_cost = 0
    nn = n + 2
    while True:
        dist = [float("inf")] * nn
        dist[s2] = 0
        inq = [False] * nn
        pn = [-1] * nn
        pe = [-1] * nn
        q = [s2]
        inq[s2] = True
        while q:
            u = q.pop(0)
            inq[u] = False
            for idx, (v, c, w, r) in enumerate(graph2[u]):
                if c > 0 and dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
                    pn[v] = u
                    pe[v] = idx
                    if not inq[v]:
                        q.append(v)
                        inq[v] = True
        if dist[t2] == float("inf"):
            break
        bn = float("inf")
        v = t2
        while v != s2:
            u = pn[v]
            bn = min(bn, graph2[u][pe[v]][1])
            v = u
        v = t2
        while v != s2:
            u = pn[v]
            graph2[u][pe[v]][1] -= bn
            ri = graph2[u][pe[v]][3]
            graph2[v][ri][1] += bn
            v = u
        ref_cost += bn * dist[t2]

    if result["cost"] != ref_cost:
        return False

    return True


BUG_DESC = (
    "After each flow augmentation, the shortest paths in the residual graph "
    "must be recomputed because arc capacities have changed. The bug computes "
    "shortest paths only once before the loop and reuses stale distances and "
    "predecessor pointers for all subsequent augmentations. This causes flow "
    "to be sent along paths that may no longer exist or be shortest, leading "
    "to suboptimal or infeasible flow solutions."
)


def _gen_inputs():
    import random
    # 5-node network with multiple paths of varying costs
    # to force multiple augmentation rounds with different paths
    n = 5
    edges = [
        (0, 1, random.randint(2, 4), random.randint(1, 3)),
        (0, 2, random.randint(2, 4), random.randint(4, 7)),
        (1, 3, random.randint(2, 4), random.randint(1, 3)),
        (1, 4, random.randint(2, 4), random.randint(4, 7)),
        (2, 3, random.randint(2, 4), random.randint(4, 7)),
        (2, 4, random.randint(2, 4), random.randint(1, 3)),
        (3, 4, random.randint(2, 4), random.randint(1, 3)),
    ]
    # Supply enough flow to require multiple paths
    s = random.randint(4, 6)
    supplies = [s, 0, 0, 0, -s]
    return n, edges, supplies


def _make_generators():
    cache = [None]

    def ensure_cache():
        if cache[0] is None:
            cache[0] = _gen_inputs()

    def get_n():
        ensure_cache()
        return cache[0][0]

    def get_edges():
        ensure_cache()
        return cache[0][1]

    def get_supplies():
        ensure_cache()
        val = cache[0][2]
        cache[0] = None
        return val

    return get_n, get_edges, get_supplies

_get_n, _get_edges, _get_supplies = _make_generators()

INPUT_OVERRIDES = {
    "NUM_NODES": _get_n,
    "EDGES": _get_edges,
    "SUPPLIES": _get_supplies,
}
