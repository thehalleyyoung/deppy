"""Tarjan's algorithm for strongly connected components.

Bug: After the recursive DFS call to child w, the correct algorithm updates
lowlink[v] = min(lowlink[v], lowlink[w]). The buggy version omits this
update entirely, so the parent node never learns about back-edges found
deeper in the DFS tree. This causes the algorithm to split SCCs that should
be merged, producing too many (smaller) components.
"""

CORRECT = r"""
def tarjan_scc(graph):
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = {}
    result = []

    all_nodes = set(graph.keys())
    for targets in graph.values():
        for t in targets:
            all_nodes.add(t)

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True

        for w in graph.get(v, []):
            if w not in index:
                strongconnect(w)
                # CORRECT: propagate lowlink from child
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            component = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                component.append(w)
                if w == v:
                    break
            result.append(sorted(component))

    for v in sorted(all_nodes):
        if v not in index:
            strongconnect(v)

    result.sort(key=lambda c: c[0])
    return result

graph = GRAPH
result = tarjan_scc(graph)
"""

BUGGY = r"""
def tarjan_scc(graph):
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = {}
    result = []

    all_nodes = set(graph.keys())
    for targets in graph.values():
        for t in targets:
            all_nodes.add(t)

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True

        for w in graph.get(v, []):
            if w not in index:
                strongconnect(w)
                # BUG: missing lowlink[v] = min(lowlink[v], lowlink[w])
                # The parent never learns about back-edges found by children
                pass
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            component = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                component.append(w)
                if w == v:
                    break
            result.append(sorted(component))

    for v in sorted(all_nodes):
        if v not in index:
            strongconnect(v)

    result.sort(key=lambda c: c[0])
    return result

graph = GRAPH
result = tarjan_scc(graph)
"""


def SPEC(graph, result):
    """Verify SCC correctness:
    1) Every node appears in exactly one SCC.
    2) Union of all SCCs equals all nodes.
    3) Within each SCC, every pair of nodes is mutually reachable.
    4) No two different SCCs can be merged (maximality).
    """
    from collections import deque

    all_nodes = set(graph.keys())
    for targets in graph.values():
        for t in targets:
            all_nodes.add(t)

    if not isinstance(result, list):
        return False

    seen = set()
    for comp in result:
        if not isinstance(comp, list):
            return False
        for node in comp:
            if node in seen:
                return False
            seen.add(node)

    if seen != all_nodes:
        return False

    def reachable(src, target):
        visited = set()
        queue = deque([src])
        visited.add(src)
        while queue:
            u = queue.popleft()
            if u == target:
                return True
            for w in graph.get(u, []):
                if w not in visited:
                    visited.add(w)
                    queue.append(w)
        return False

    for comp in result:
        for i in range(len(comp)):
            for j in range(i + 1, len(comp)):
                if not reachable(comp[i], comp[j]):
                    return False
                if not reachable(comp[j], comp[i]):
                    return False

    node_to_scc = {}
    for idx, comp in enumerate(result):
        for node in comp:
            node_to_scc[node] = idx

    for comp in result:
        for node in comp:
            for other_node in all_nodes:
                if node_to_scc[other_node] != node_to_scc[node]:
                    if reachable(node, other_node) and reachable(other_node, node):
                        return False

    for comp in result:
        if comp != sorted(comp):
            return False
    for i in range(len(result) - 1):
        if result[i][0] > result[i + 1][0]:
            return False

    return True


BUG_DESC = (
    "After the recursive DFS call to an unvisited child w, the buggy version "
    "omits the update lowlink[v] = min(lowlink[v], lowlink[w]). Without this, "
    "the parent node v never learns that its subtree can reach an ancestor, "
    "so it incorrectly thinks it is the root of an SCC. This splits genuine "
    "SCCs into smaller fragments."
)


def _generate_graph():
    import random
    n = random.randint(5, 10)
    nodes = list(range(n))
    graph = {i: [] for i in nodes}

    for i in nodes:
        for j in nodes:
            if i != j and random.random() < 0.3:
                graph[i].append(j)

    # Guarantee at least one non-trivial SCC: add a 3-cycle
    cycle_nodes = random.sample(nodes, 3)
    for idx in range(3):
        src = cycle_nodes[idx]
        dst = cycle_nodes[(idx + 1) % 3]
        if dst not in graph[src]:
            graph[src].append(dst)

    return graph


INPUT_OVERRIDES = {
    "GRAPH": _generate_graph,
}
