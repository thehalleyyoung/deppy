"""Dinic's algorithm for maximum flow via blocking flows on level graphs.

Bug: When building the level graph via BFS, the condition for adding an edge
should check that the residual capacity is > 0. The bug omits this check,
adding zero-capacity edges to the level graph. This causes incorrect level
assignments, making the DFS miss valid augmenting paths and terminate early
with a suboptimal flow value.
"""

CORRECT = r"""
from collections import deque

def dinic_max_flow(capacity, source, sink):
    nodes = set()
    for u in capacity:
        nodes.add(u)
        for v in capacity[u]:
            nodes.add(v)
    nodes = sorted(nodes)

    # Initialize residual capacity matrix
    res = {}
    for u in nodes:
        res[u] = {}
        for v in nodes:
            res[u][v] = 0
    for u in capacity:
        for v in capacity[u]:
            res[u][v] = capacity[u][v]

    def bfs_level():
        level = {u: -1 for u in nodes}
        level[source] = 0
        queue = deque([source])
        while queue:
            u = queue.popleft()
            for v in nodes:
                # CORRECT: only traverse edges with positive residual capacity
                if level[v] == -1 and res[u][v] > 0:
                    level[v] = level[u] + 1
                    queue.append(v)
        if level[sink] == -1:
            return None
        return level

    def dfs_blocking(u, pushed, level, iter_ptr):
        if u == sink:
            return pushed
        while iter_ptr[u] < len(nodes):
            v = nodes[iter_ptr[u]]
            if level.get(v, -1) == level[u] + 1 and res[u][v] > 0:
                d = dfs_blocking(v, min(pushed, res[u][v]), level, iter_ptr)
                if d > 0:
                    res[u][v] -= d
                    res[v][u] += d
                    return d
            iter_ptr[u] += 1
        return 0

    total_flow = 0
    iteration_limit = 0
    while iteration_limit < 200:
        level = bfs_level()
        if level is None:
            break
        iter_ptr = {u: 0 for u in nodes}
        while True:
            f = dfs_blocking(source, float('inf'), level, iter_ptr)
            if f == 0:
                break
            total_flow += f
        iteration_limit += 1

    result = total_flow
    return result

cap = CAPACITY
src = SOURCE
snk = SINK
result = dinic_max_flow(cap, src, snk)
"""

BUGGY = r"""
from collections import deque

def dinic_max_flow(capacity, source, sink):
    nodes = set()
    for u in capacity:
        nodes.add(u)
        for v in capacity[u]:
            nodes.add(v)
    nodes = sorted(nodes)

    # Initialize residual capacity matrix
    res = {}
    for u in nodes:
        res[u] = {}
        for v in nodes:
            res[u][v] = 0
    for u in capacity:
        for v in capacity[u]:
            res[u][v] = capacity[u][v]

    def bfs_level():
        level = {u: -1 for u in nodes}
        level[source] = 0
        queue = deque([source])
        while queue:
            u = queue.popleft()
            for v in nodes:
                # BUG: omits the residual capacity check (res[u][v] > 0)
                # This traverses zero-capacity edges, causing wrong level
                # assignments where nodes appear closer than they really are
                if level[v] == -1:
                    level[v] = level[u] + 1
                    queue.append(v)
        if level[sink] == -1:
            return None
        return level

    def dfs_blocking(u, pushed, level, iter_ptr):
        if u == sink:
            return pushed
        while iter_ptr[u] < len(nodes):
            v = nodes[iter_ptr[u]]
            if level.get(v, -1) == level[u] + 1 and res[u][v] > 0:
                d = dfs_blocking(v, min(pushed, res[u][v]), level, iter_ptr)
                if d > 0:
                    res[u][v] -= d
                    res[v][u] += d
                    return d
            iter_ptr[u] += 1
        return 0

    total_flow = 0
    iteration_limit = 0
    while iteration_limit < 200:
        level = bfs_level()
        if level is None:
            break
        iter_ptr = {u: 0 for u in nodes}
        while True:
            f = dfs_blocking(source, float('inf'), level, iter_ptr)
            if f == 0:
                break
            total_flow += f
        iteration_limit += 1

    result = total_flow
    return result

cap = CAPACITY
src = SOURCE
snk = SINK
result = dinic_max_flow(cap, src, snk)
"""


def SPEC(CAPACITY, SOURCE, SINK, result):
    """Verify max flow correctness by comparing to reference Ford-Fulkerson."""
    from collections import deque

    nodes = set()
    for u in CAPACITY:
        nodes.add(u)
        for v in CAPACITY[u]:
            nodes.add(v)
    nodes = sorted(nodes)

    if SOURCE not in nodes or SINK not in nodes:
        return result == 0

    res = {}
    for u in nodes:
        res[u] = {}
        for v in nodes:
            res[u][v] = 0
    for u in CAPACITY:
        for v in CAPACITY[u]:
            res[u][v] = CAPACITY[u][v]

    ref_flow = 0
    while True:
        parent = {SOURCE: None}
        queue = deque([SOURCE])
        found = False
        while queue and not found:
            u = queue.popleft()
            for v in nodes:
                if v not in parent and res[u][v] > 0:
                    parent[v] = u
                    if v == SINK:
                        found = True
                        break
                    queue.append(v)
        if not found:
            break
        bottleneck = float('inf')
        v = SINK
        while parent[v] is not None:
            u = parent[v]
            bottleneck = min(bottleneck, res[u][v])
            v = u
        v = SINK
        while parent[v] is not None:
            u = parent[v]
            res[u][v] -= bottleneck
            res[v][u] += bottleneck
            v = u
        ref_flow += bottleneck

    if not isinstance(result, int):
        return False
    return result == ref_flow


BUG_DESC = (
    "When building the level graph via BFS, omits the residual capacity check "
    "(res[u][v] > 0), adding zero-capacity edges. This causes incorrect level "
    "assignments where nodes get shorter distances through zero-capacity edges, "
    "making the DFS miss valid augmenting paths and terminate with suboptimal flow."
)


def _generate_graph():
    import random
    n = random.randint(6, 8)
    capacity = {i: {} for i in range(n)}
    # Ensure path 0 -> ... -> n-1
    mid = list(range(1, n - 1))
    random.shuffle(mid)
    chain = [0] + mid + [n - 1]
    for i in range(len(chain) - 1):
        capacity[chain[i]][chain[i + 1]] = random.randint(1, 10)
    # Second path for richer flow structure
    mid2 = list(range(1, n - 1))
    random.shuffle(mid2)
    chain2 = [0] + mid2[:2] + [n - 1]
    for i in range(len(chain2) - 1):
        u, v = chain2[i], chain2[i + 1]
        if v not in capacity[u]:
            capacity[u][v] = random.randint(1, 10)
    # Random extra edges
    for _ in range(n):
        u = random.randint(0, n - 2)
        v = random.randint(u + 1, n - 1)
        if v not in capacity.get(u, {}):
            capacity[u][v] = random.randint(1, 10)
    capacity = {u: edges for u, edges in capacity.items() if edges}
    return capacity


INPUT_OVERRIDES = {
    "CAPACITY": _generate_graph,
    "SOURCE": lambda: 0,
    "SINK": lambda: 5,
}
