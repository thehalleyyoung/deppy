"""Push-relabel algorithm for maximum flow.

Bug: in the relabel operation, sets height to min(height of admissible
neighbor) but doesn't add 1, so the node never gets high enough to push
flow and the algorithm terminates with suboptimal flow.
"""

CORRECT = r"""
def push_relabel(n, cap, source, sink):
    # cap[u][v] = capacity; n = number of nodes
    # Returns maximum flow value

    flow = [[0] * n for _ in range(n)]
    height = [0] * n
    excess = [0] * n
    height[source] = n

    # Initialize preflow: saturate all edges from source
    for v in range(n):
        if cap[source][v] > 0:
            flow[source][v] = cap[source][v]
            flow[v][source] = -cap[source][v]
            excess[v] = cap[source][v]
            excess[source] -= cap[source][v]

    # Active nodes (not source or sink, with positive excess)
    def get_active():
        active = []
        for v in range(n):
            if v != source and v != sink and excess[v] > 0:
                active.append(v)
        return active

    def push(u, v):
        d = min(excess[u], cap[u][v] - flow[u][v])
        if d > 0 and height[u] == height[v] + 1:
            flow[u][v] += d
            flow[v][u] -= d
            excess[u] -= d
            excess[v] += d
            return True
        return False

    def relabel(u):
        min_height = float('inf')
        for v in range(n):
            if cap[u][v] - flow[u][v] > 0:
                min_height = min(min_height, height[v])
        if min_height < float('inf'):
            # CORRECT: set height to min_height + 1
            height[u] = min_height + 1

    max_iter = n * n * 4  # safety bound
    iteration = 0
    while iteration < max_iter:
        active = get_active()
        if not active:
            break
        u = active[0]
        pushed = False
        for v in range(n):
            if push(u, v):
                pushed = True
                break
        if not pushed:
            relabel(u)
        iteration += 1

    return excess[sink]

n = N_NODES
cap = CAPACITY
source = SOURCE
sink = SINK
result = push_relabel(n, cap, source, sink)
"""

BUGGY = r"""
def push_relabel(n, cap, source, sink):
    flow = [[0] * n for _ in range(n)]
    height = [0] * n
    excess = [0] * n
    height[source] = n

    for v in range(n):
        if cap[source][v] > 0:
            flow[source][v] = cap[source][v]
            flow[v][source] = -cap[source][v]
            excess[v] = cap[source][v]
            excess[source] -= cap[source][v]

    def get_active():
        active = []
        for v in range(n):
            if v != source and v != sink and excess[v] > 0:
                active.append(v)
        return active

    def push(u, v):
        d = min(excess[u], cap[u][v] - flow[u][v])
        if d > 0 and height[u] == height[v] + 1:
            flow[u][v] += d
            flow[v][u] -= d
            excess[u] -= d
            excess[v] += d
            return True
        return False

    def relabel(u):
        min_height = float('inf')
        for v in range(n):
            if cap[u][v] - flow[u][v] > 0:
                min_height = min(min_height, height[v])
        if min_height < float('inf'):
            # BUG: missing +1, so height never exceeds neighbor's height
            height[u] = min_height

    max_iter = n * n * 4
    iteration = 0
    while iteration < max_iter:
        active = get_active()
        if not active:
            break
        u = active[0]
        pushed = False
        for v in range(n):
            if push(u, v):
                pushed = True
                break
        if not pushed:
            relabel(u)
        iteration += 1

    return excess[sink]

n = N_NODES
cap = CAPACITY
source = SOURCE
sink = SINK
result = push_relabel(n, cap, source, sink)
"""


def SPEC(n_nodes, capacity, source, sink, result):
    if not isinstance(result, (int, float)):
        return False

    # Compute max flow via BFS-based Ford-Fulkerson (Edmonds-Karp) for reference
    from collections import deque
    n = n_nodes
    cap = [row[:] for row in capacity]
    flow = [[0] * n for _ in range(n)]

    def bfs():
        visited = [False] * n
        visited[source] = True
        parent = [-1] * n
        queue = deque([source])
        while queue:
            u = queue.popleft()
            for v in range(n):
                if not visited[v] and cap[u][v] - flow[u][v] > 0:
                    visited[v] = True
                    parent[v] = u
                    if v == sink:
                        return parent
                    queue.append(v)
        return None

    max_flow = 0
    while True:
        parent = bfs()
        if parent is None:
            break
        # Find bottleneck
        path_flow = float('inf')
        v = sink
        while v != source:
            u = parent[v]
            path_flow = min(path_flow, cap[u][v] - flow[u][v])
            v = u
        # Update flow
        v = sink
        while v != source:
            u = parent[v]
            flow[u][v] += path_flow
            flow[v][u] -= path_flow
            v = u
        max_flow += path_flow

    return result == max_flow


BUG_DESC = (
    "In the relabel operation, the height is set to min(height of neighbors "
    "with residual capacity) without adding 1. Since push requires "
    "height[u] == height[v] + 1, the relabeled node never becomes high "
    "enough to push flow, causing the algorithm to loop until the iteration "
    "limit and return suboptimal flow."
)


def _gen():
    import random
    # The bug: relabel sets height[u] = min_height instead of min_height + 1.
    # This means after relabel, height[u] == height[v] for the lowest neighbor v,
    # but push requires height[u] == height[v] + 1. So the node can never push
    # after relabeling. The algorithm hits max_iter and returns suboptimal flow.
    #
    # To trigger: need a graph where flow MUST go through intermediate nodes
    # that require relabeling. Source connects only to intermediates (not sink),
    # intermediates connect to sink.
    #
    # After initial preflow, excess sits at intermediate nodes with height 0.
    # They need relabeling to push to sink (height 0). Correct relabel sets
    # height to 1, enabling push. Buggy sets height to 0, push never happens.
    #
    # Simple 4-node graph: 0->1 (cap 10), 0->2 (cap 10), 1->3 (cap 10), 2->3 (cap 10)
    # No direct 0->3 edge. Max flow = 20. Buggy gets 0 (nodes 1,2 can't push to 3).
    #
    # Use small graphs with NO direct source-to-sink edge.
    graphs = [
        # n=4: s=0, t=3. Two parallel paths through nodes 1 and 2.
        (4, [[0,10,10,0],[0,0,0,10],[0,0,0,10],[0,0,0,0]]),
        # n=3: s=0, t=2. Single path through node 1.
        (3, [[0,10,0],[0,0,10],[0,0,0]]),
        # n=4: s=0, t=3. Path 0->1->2->3.
        (4, [[0,5,0,0],[0,0,5,0],[0,0,0,5],[0,0,0,0]]),
        # n=5: s=0, t=4. Diamond: 0->1, 0->2, 1->3, 2->3, 3->4.
        (5, [[0,8,8,0,0],[0,0,0,8,0],[0,0,0,8,0],[0,0,0,0,16],[0,0,0,0,0]]),
        # n=4: s=0, t=3. 0->1(5), 0->2(3), 1->2(2), 1->3(3), 2->3(5)
        (4, [[0,5,3,0],[0,0,2,3],[0,0,0,5],[0,0,0,0]]),
    ]
    n, cap = random.choice(graphs)
    _gen._n = n
    _gen._cap = cap
    _gen._source = 0
    _gen._sink = n - 1
    return n


def _gen_cap():
    return _gen._cap


def _gen_source():
    return _gen._source


def _gen_sink():
    return _gen._sink


INPUT_OVERRIDES = {
    "N_NODES": _gen,
    "CAPACITY": _gen_cap,
    "SOURCE": _gen_source,
    "SINK": _gen_sink,
}
