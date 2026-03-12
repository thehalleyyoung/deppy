"""Kahn's algorithm (BFS-based topological sort).

Bug: doesn't decrement in-degree of neighbors when removing a node,
causing valid successors to never reach in-degree 0.
"""

CORRECT = r"""
def kahn_toposort(graph):
    # Collect all nodes
    all_nodes = set(graph.keys())
    for targets in graph.values():
        for t in targets:
            all_nodes.add(t)

    # Compute in-degrees
    in_degree = {v: 0 for v in all_nodes}
    for u in graph:
        for v in graph[u]:
            in_degree[v] = in_degree.get(v, 0) + 1

    # Initialize queue with nodes of in-degree 0
    from collections import deque
    queue = deque()
    for v in sorted(all_nodes):
        if in_degree[v] == 0:
            queue.append(v)

    order = []
    while queue:
        u = queue.popleft()
        order.append(u)
        for v in sorted(graph.get(u, [])):
            # CORRECT: decrement in-degree of neighbor
            in_degree[v] -= 1
            if in_degree[v] == 0:
                queue.append(v)

    # If order doesn't contain all nodes, there's a cycle
    if len(order) != len(all_nodes):
        return None
    return order

graph = GRAPH
result = kahn_toposort(graph)
"""

BUGGY = r"""
def kahn_toposort(graph):
    # Collect all nodes
    all_nodes = set(graph.keys())
    for targets in graph.values():
        for t in targets:
            all_nodes.add(t)

    # Compute in-degrees
    in_degree = {v: 0 for v in all_nodes}
    for u in graph:
        for v in graph[u]:
            in_degree[v] = in_degree.get(v, 0) + 1

    # Initialize queue with nodes of in-degree 0
    from collections import deque
    queue = deque()
    for v in sorted(all_nodes):
        if in_degree[v] == 0:
            queue.append(v)

    order = []
    while queue:
        u = queue.popleft()
        order.append(u)
        for v in sorted(graph.get(u, [])):
            # BUG: doesn't decrement in-degree, so successors never enqueued
            if in_degree[v] == 0:
                queue.append(v)

    # If order doesn't contain all nodes, there's a cycle
    if len(order) != len(all_nodes):
        return None
    return order

graph = GRAPH
result = kahn_toposort(graph)
"""


def SPEC(graph, result):
    # Collect all nodes
    all_nodes = set(graph.keys())
    for targets in graph.values():
        for t in targets:
            all_nodes.add(t)

    # Check for cycles using DFS
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {v: WHITE for v in all_nodes}
    has_cycle = [False]

    def dfs(u):
        color[u] = GRAY
        for v in graph.get(u, []):
            if color[v] == GRAY:
                has_cycle[0] = True
                return
            if color[v] == WHITE:
                dfs(v)
                if has_cycle[0]:
                    return
        color[u] = BLACK

    for v in all_nodes:
        if color[v] == WHITE:
            dfs(v)
            if has_cycle[0]:
                break

    if has_cycle[0]:
        # Graph has a cycle, result should be None
        return result is None

    # Graph is a DAG, result must be a valid topological order
    if result is None:
        return False
    if not isinstance(result, list):
        return False
    if set(result) != all_nodes:
        return False
    if len(result) != len(all_nodes):
        return False

    # Check topological property: for every edge u->v, u appears before v
    pos = {v: i for i, v in enumerate(result)}
    for u in graph:
        for v in graph[u]:
            if pos[u] >= pos[v]:
                return False

    return True


BUG_DESC = (
    "When processing a node from the queue, the algorithm fails to decrement "
    "the in-degree of its neighbors. This means nodes that should eventually "
    "reach in-degree 0 never do, and the algorithm reports a false cycle "
    "(returns None) even for valid DAGs."
)


def _generate_graph():
    import random
    n = random.randint(6, 10)
    nodes = list(range(n))
    # Generate a DAG with a guaranteed chain so most nodes have in-degree > 0.
    # Without decrementing in-degree, the buggy version will only output
    # the source node(s) with initial in-degree 0.
    perm = list(range(n))
    random.shuffle(perm)
    rank = {perm[i]: i for i in range(n)}

    graph = {v: [] for v in nodes}
    # Chain in rank order ensures n-1 nodes have in-degree >= 1
    for i in range(n - 1):
        u = perm[i]
        v = perm[i + 1]
        graph[u].append(v)
    # Additional random edges
    for u in nodes:
        for v in nodes:
            if rank[u] < rank[v] and random.random() < 0.25:
                if v not in graph[u]:
                    graph[u].append(v)

    return graph


INPUT_OVERRIDES = {
    "GRAPH": _generate_graph,
}
