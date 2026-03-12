"""Parallel topological sort: assign each node the earliest possible level
(time step) respecting dependencies, then return nodes grouped by level.

Bug: When processing nodes at current level, the bug checks in_degree[v] == 0
BEFORE decrementing instead of after. This causes nodes to be assigned to
earlier levels than they should, violating dependency constraints.
"""

CORRECT = r"""
from collections import deque

def parallel_topo_sort(graph, nodes):
    # graph: dict of node -> list of successors
    # nodes: list of all node ids
    # Returns list of lists: nodes at each level

    # Compute in-degrees
    in_degree = {n: 0 for n in nodes}
    for u in nodes:
        for v in graph.get(u, []):
            in_degree[v] = in_degree.get(v, 0) + 1

    # Find all nodes with in-degree 0 for the first level
    current_level = []
    for n in nodes:
        if in_degree[n] == 0:
            current_level.append(n)
    current_level.sort()

    result = []
    processed = set()

    while current_level:
        result.append(list(current_level))
        next_level = []
        for u in current_level:
            processed.add(u)
            for v in graph.get(u, []):
                in_degree[v] -= 1
                # CORRECT: check after decrement
                if in_degree[v] == 0:
                    next_level.append(v)
        next_level.sort()
        current_level = next_level

    # Check all nodes processed
    if len(processed) != len(nodes):
        return None  # cycle detected

    return result

graph = GRAPH
nodes = NODES
result = parallel_topo_sort(graph, nodes)
"""

BUGGY = r"""
from collections import deque

def parallel_topo_sort(graph, nodes):
    # graph: dict of node -> list of successors
    # nodes: list of all node ids
    # Returns list of lists: nodes at each level

    # Compute in-degrees
    in_degree = {n: 0 for n in nodes}
    for u in nodes:
        for v in graph.get(u, []):
            in_degree[v] = in_degree.get(v, 0) + 1

    # Find all nodes with in-degree 0 for the first level
    current_level = []
    for n in nodes:
        if in_degree[n] == 0:
            current_level.append(n)
    current_level.sort()

    result = []
    processed = set()

    while current_level:
        result.append(list(current_level))
        next_level = []
        for u in current_level:
            processed.add(u)
            for v in graph.get(u, []):
                # BUG: check BEFORE decrement instead of after
                if in_degree[v] == 0:
                    next_level.append(v)
                in_degree[v] -= 1
        next_level.sort()
        current_level = next_level

    # Check all nodes processed
    if len(processed) != len(nodes):
        return None  # cycle detected

    return result

graph = GRAPH
nodes = NODES
result = parallel_topo_sort(graph, nodes)
"""


def SPEC(GRAPH, NODES, result):
    """Verify parallel topological sort:
    1) All nodes appear exactly once
    2) For every edge u->v, level(u) < level(v)
    3) Optimality: each node is at the earliest possible level
       (level(v) = 0 if no predecessors, else max(level(pred)+1) for all predecessors)
    """
    if result is None:
        return False
    if not isinstance(result, list):
        return False

    # Check all nodes appear exactly once
    seen = set()
    node_level = {}
    for level_idx, level_nodes in enumerate(result):
        if not isinstance(level_nodes, list):
            return False
        for n in level_nodes:
            if n in seen:
                return False
            seen.add(n)
            node_level[n] = level_idx

    if seen != set(NODES):
        return False

    # Build predecessors map
    predecessors = {n: [] for n in NODES}
    for u in NODES:
        for v in GRAPH.get(u, []):
            predecessors[v].append(u)

    # Check dependency constraint: for every edge u->v, level(u) < level(v)
    for u in NODES:
        for v in GRAPH.get(u, []):
            if node_level[u] >= node_level[v]:
                return False

    # Check optimality: level(v) should be exactly max(level(pred)+1) over all preds
    # or 0 if no predecessors
    for n in NODES:
        preds = predecessors[n]
        if not preds:
            expected_level = 0
        else:
            expected_level = max(node_level[p] + 1 for p in preds)
        if node_level[n] != expected_level:
            return False

    return True


BUG_DESC = (
    "When processing nodes at the current level and decrementing successor "
    "in-degrees, the bug checks in_degree[v] == 0 BEFORE the decrement instead "
    "of after. This means nodes whose in-degree is about to become 0 are never "
    "added to the next level (they had in_degree=1 at check time), while nodes "
    "that already had in_degree=0 (which shouldn't exist) could be spuriously added. "
    "The result is that some nodes are never processed, returning None (cycle detected)."
)


def _generate_dag():
    import random
    n = random.randint(6, 10)
    nodes = list(range(n))
    graph = {i: [] for i in nodes}

    # Create a DAG: only add edges from lower to higher node ids
    # to guarantee acyclicity
    for i in nodes:
        for j in nodes:
            if i < j and random.random() < 0.35:
                graph[i].append(j)

    # Ensure some depth: add a chain
    chain = random.sample(nodes, min(4, n))
    chain.sort()
    for idx in range(len(chain) - 1):
        u, v = chain[idx], chain[idx + 1]
        if v not in graph[u]:
            graph[u].append(v)

    # Ensure at least one node has multiple predecessors (for interesting levels)
    if n >= 4:
        target = nodes[-1]
        sources = random.sample(nodes[:-1], min(2, n - 1))
        for s in sources:
            if target not in graph[s]:
                graph[s].append(target)

    return graph


def _generate_nodes():
    # Will be called after GRAPH is generated, but we generate independently
    # and reconcile in the graph generator
    import random
    n = random.randint(6, 10)
    return list(range(n))


def _generate_graph_and_nodes():
    import random
    n = random.randint(6, 10)
    nodes = list(range(n))
    graph = {i: [] for i in nodes}

    for i in nodes:
        for j in nodes:
            if i < j and random.random() < 0.35:
                graph[i].append(j)

    # Add a chain for depth
    chain = random.sample(nodes, min(4, n))
    chain.sort()
    for idx in range(len(chain) - 1):
        u, v = chain[idx], chain[idx + 1]
        if v not in graph[u]:
            graph[u].append(v)

    return graph, nodes


_cached = [None]

def _get_cached():
    import random
    if _cached[0] is None:
        _cached[0] = _generate_graph_and_nodes()
    return _cached[0]

def _gen_graph():
    _cached[0] = None
    g, n = _generate_graph_and_nodes()
    _cached[0] = (g, n)
    return g

def _gen_nodes():
    if _cached[0] is None:
        _gen_graph()
    return _cached[0][1]


INPUT_OVERRIDES = {
    "GRAPH": _gen_graph,
    "NODES": _gen_nodes,
}
