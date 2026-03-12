"""Edmonds-Karp maximum flow algorithm (BFS-based Ford-Fulkerson).

Bug: when augmenting flow along the found path, the reverse edge update
in the residual graph SUBTRACTS the bottleneck instead of ADDING it.
This corrupts the residual graph, causing incorrect flow values.
"""

CORRECT = r"""
from collections import deque

def edmonds_karp(capacity, source, sink):
    # Collect all nodes
    nodes = set()
    for u in capacity:
        nodes.add(u)
        for v in capacity[u]:
            nodes.add(v)

    # Initialize residual capacities
    residual = {n: {} for n in nodes}
    for u in capacity:
        for v in capacity[u]:
            residual[u][v] = residual[u].get(v, 0) + capacity[u][v]
            if u not in residual[v]:
                residual[v][u] = 0

    # Initialize flow graph
    flow = {n: {} for n in nodes}
    for u in capacity:
        for v in capacity[u]:
            flow[u][v] = 0

    def bfs_find_path():
        parent = {source: None}
        queue = deque([source])
        while queue:
            u = queue.popleft()
            if u == sink:
                path = []
                node = sink
                while node != source:
                    prev = parent[node]
                    path.append((prev, node))
                    node = prev
                path.reverse()
                return path
            for v in residual.get(u, {}):
                if v not in parent and residual[u][v] > 0:
                    parent[v] = u
                    queue.append(v)
        return None

    max_flow = 0

    while True:
        path = bfs_find_path()
        if path is None:
            break

        # Find bottleneck
        bottleneck = float('inf')
        for u, v in path:
            if residual[u][v] < bottleneck:
                bottleneck = residual[u][v]

        # Augment along path
        for u, v in path:
            residual[u][v] -= bottleneck
            # CORRECT: add bottleneck to reverse residual edge
            if u not in residual[v]:
                residual[v][u] = 0
            residual[v][u] += bottleneck

            # Update flow tracking
            if v in capacity.get(u, {}):
                flow[u][v] += bottleneck
            elif u in capacity.get(v, {}):
                flow[v][u] -= bottleneck

        max_flow += bottleneck

    result = (max_flow, flow)
    return result

capacity = CAPACITY
source = SOURCE
sink = SINK
result = edmonds_karp(capacity, source, sink)
"""

BUGGY = r"""
from collections import deque

def edmonds_karp(capacity, source, sink):
    # Collect all nodes
    nodes = set()
    for u in capacity:
        nodes.add(u)
        for v in capacity[u]:
            nodes.add(v)

    # Initialize residual capacities
    residual = {n: {} for n in nodes}
    for u in capacity:
        for v in capacity[u]:
            residual[u][v] = residual[u].get(v, 0) + capacity[u][v]
            if u not in residual[v]:
                residual[v][u] = 0

    # Initialize flow graph
    flow = {n: {} for n in nodes}
    for u in capacity:
        for v in capacity[u]:
            flow[u][v] = 0

    def bfs_find_path():
        parent = {source: None}
        queue = deque([source])
        while queue:
            u = queue.popleft()
            if u == sink:
                path = []
                node = sink
                while node != source:
                    prev = parent[node]
                    path.append((prev, node))
                    node = prev
                path.reverse()
                return path
            for v in residual.get(u, {}):
                if v not in parent and residual[u][v] > 0:
                    parent[v] = u
                    queue.append(v)
        return None

    max_flow = 0

    while True:
        path = bfs_find_path()
        if path is None:
            break

        # Find bottleneck
        bottleneck = float('inf')
        for u, v in path:
            if residual[u][v] < bottleneck:
                bottleneck = residual[u][v]

        # Augment along path
        for u, v in path:
            residual[u][v] -= bottleneck
            # BUG: subtracts bottleneck from reverse edge instead of adding
            if u not in residual[v]:
                residual[v][u] = 0
            residual[v][u] -= bottleneck

            # Update flow tracking
            if v in capacity.get(u, {}):
                flow[u][v] += bottleneck
            elif u in capacity.get(v, {}):
                flow[v][u] -= bottleneck

        max_flow += bottleneck

    result = (max_flow, flow)
    return result

capacity = CAPACITY
source = SOURCE
sink = SINK
result = edmonds_karp(capacity, source, sink)
"""


def SPEC(capacity, source, sink, result):
    """Verify max flow correctness:
    1) Flow conservation at non-source/sink nodes.
    2) Capacity constraints: 0 <= flow[u][v] <= capacity[u][v].
    3) Flow value equals net flow out of source.
    4) Optimality: compare to reference implementation.
    """
    from collections import deque

    max_flow_val, flow = result

    nodes = set()
    for u in capacity:
        nodes.add(u)
        for v in capacity[u]:
            nodes.add(v)

    # Capacity constraints
    for u in capacity:
        for v in capacity[u]:
            f = flow.get(u, {}).get(v, 0)
            if f < -1e-9 or f > capacity[u][v] + 1e-9:
                return False

    # Flow conservation
    for node in nodes:
        if node == source or node == sink:
            continue
        total_in = sum(flow.get(u, {}).get(node, 0) for u in capacity)
        total_out = sum(flow.get(node, {}).get(v, 0) for v in capacity.get(node, {}))
        if abs(total_in - total_out) > 1e-9:
            return False

    # Flow value check
    source_out = sum(flow.get(source, {}).get(v, 0) for v in capacity.get(source, {}))
    source_in = sum(flow.get(u, {}).get(source, 0) for u in capacity)
    if abs(max_flow_val - (source_out - source_in)) > 1e-9:
        return False

    # Reference max flow for optimality
    def ref_max_flow(cap, s, t):
        ns = set()
        for uu in cap:
            ns.add(uu)
            for vv in cap[uu]:
                ns.add(vv)
        res = {nn: {} for nn in ns}
        for uu in cap:
            for vv in cap[uu]:
                res[uu][vv] = res[uu].get(vv, 0) + cap[uu][vv]
                if uu not in res[vv]:
                    res[vv][uu] = 0
        total = 0
        while True:
            par = {s: None}
            q = deque([s])
            found = False
            while q:
                uu = q.popleft()
                if uu == t:
                    found = True
                    break
                for vv in res[uu]:
                    if vv not in par and res[uu][vv] > 0:
                        par[vv] = uu
                        q.append(vv)
            if not found:
                break
            path = []
            nd = t
            while nd != s:
                pr = par[nd]
                path.append((pr, nd))
                nd = pr
            bn = min(res[a][b] for a, b in path)
            for a, b in path:
                res[a][b] -= bn
                if a not in res[b]:
                    res[b][a] = 0
                res[b][a] += bn
            total += bn
        return total

    ref = ref_max_flow(capacity, source, sink)
    if abs(max_flow_val - ref) > 1e-9:
        return False

    return True


BUG_DESC = (
    "When augmenting flow along an augmenting path, the reverse edge update "
    "in the residual graph SUBTRACTS the bottleneck instead of ADDING it "
    "(residual[v][u] -= bottleneck instead of += bottleneck). This corrupts "
    "the residual graph so future BFS rounds cannot find valid augmenting "
    "paths, yielding a suboptimal max flow value."
)


def _generate_capacity():
    """Generate a flow network that requires multiple augmenting paths.

    The bug subtracts bottleneck from reverse edges instead of adding.
    This means after the first augmenting path, reverse edges have negative
    residual capacity, so the algorithm can never reroute flow. The bug
    produces wrong max-flow whenever >1 augmenting path is needed.

    Classic diamond graph: s->a, s->b, a->t, b->t, a->b
    Max flow = cap(s->a) + cap(s->b), but the BFS might first route
    s->a->b->t, then needs reverse edge b->a to route s->a->t via residual.
    """
    import random
    # Diamond: 0=s, 1=a, 2=b, 3=t
    # Two paths: 0->1->3 and 0->2->3, plus cross edge 1->2
    # BFS will find 0->1->2->3 first (or 0->1->3), then needs residual edges
    cap = {
        0: {1: random.randint(3, 8), 2: random.randint(3, 8)},
        1: {2: random.randint(1, 3), 3: random.randint(3, 8)},
        2: {3: random.randint(3, 8)},
    }
    return cap


_cached_cap = {}


def _gen_capacity():
    import random
    cap = _generate_capacity()
    _cached_cap['sink'] = 3
    return cap


INPUT_OVERRIDES = {
    "capacity": _gen_capacity,
    "source": lambda: 0,
    "sink": lambda: _cached_cap.pop('sink', 3),
}
