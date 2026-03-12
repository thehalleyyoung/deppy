"""Find all articulation points (cut vertices) in an undirected graph.

Bug: For the root special case, the correct algorithm counts only DFS tree
children (nodes where root is the DFS parent). The bug counts ALL neighbors
of root in the adjacency list, so a root with many edges but only one DFS
tree child is incorrectly identified as an articulation point.
"""

CORRECT = r"""
def find_articulation_points(adj, n):
    # adj: dict mapping node -> list of neighbors (undirected)
    # n: number of nodes (0..n-1)
    # Returns sorted list of articulation points

    disc = [-1] * n
    low = [0] * n
    parent = [-1] * n
    ap = [False] * n
    timer = [0]

    def dfs(u):
        children_in_tree = 0
        disc[u] = timer[0]
        low[u] = timer[0]
        timer[0] += 1

        for v in adj.get(u, []):
            if disc[v] == -1:
                # Tree edge
                children_in_tree += 1
                parent[v] = u
                dfs(v)
                low[u] = min(low[u], low[v])

                # Non-root articulation point check
                if parent[u] != -1 and low[v] >= disc[u]:
                    ap[u] = True

                # CORRECT: Root check uses DFS tree children count
                if parent[u] == -1 and children_in_tree > 1:
                    ap[u] = True

            elif v != parent[u]:
                # Back edge
                low[u] = min(low[u], disc[v])

    # Run DFS from each unvisited node (handle disconnected components)
    for i in range(n):
        if disc[i] == -1:
            dfs(i)

    result = sorted([i for i in range(n) if ap[i]])
    return result

adj = ADJ
n = NUM_NODES
result = find_articulation_points(adj, n)
"""

BUGGY = r"""
def find_articulation_points(adj, n):
    # adj: dict mapping node -> list of neighbors (undirected)
    # n: number of nodes (0..n-1)
    # Returns sorted list of articulation points

    disc = [-1] * n
    low = [0] * n
    parent = [-1] * n
    ap = [False] * n
    timer = [0]

    def dfs(u):
        children_in_tree = 0
        disc[u] = timer[0]
        low[u] = timer[0]
        timer[0] += 1

        for v in adj.get(u, []):
            if disc[v] == -1:
                # Tree edge
                children_in_tree += 1
                parent[v] = u
                dfs(v)
                low[u] = min(low[u], low[v])

                # Non-root articulation point check
                if parent[u] != -1 and low[v] >= disc[u]:
                    ap[u] = True

            elif v != parent[u]:
                # Back edge
                low[u] = min(low[u], disc[v])

        # BUG: Root check uses total neighbor count instead of DFS tree children
        if parent[u] == -1 and len(adj.get(u, [])) > 1:
            ap[u] = True

    # Run DFS from each unvisited node (handle disconnected components)
    for i in range(n):
        if disc[i] == -1:
            dfs(i)

    result = sorted([i for i in range(n) if ap[i]])
    return result

adj = ADJ
n = NUM_NODES
result = find_articulation_points(adj, n)
"""


def SPEC(ADJ, NUM_NODES, result):
    """Verify articulation points:
    For each reported AP, removing it should disconnect the graph.
    For each non-reported node, removing it should NOT disconnect the graph.
    """
    from collections import deque

    if not isinstance(result, list):
        return False
    if result != sorted(result):
        return False
    if len(set(result)) != len(result):
        return False

    def count_components(adj, n, removed):
        visited = [False] * n
        visited[removed] = True  # treat removed as visited
        components = 0
        for start in range(n):
            if visited[start]:
                continue
            if not adj.get(start, []) and start == removed:
                continue
            components += 1
            queue = deque([start])
            visited[start] = True
            while queue:
                u = queue.popleft()
                for v in adj.get(u, []):
                    if not visited[v]:
                        visited[v] = True
                        queue.append(v)
        return components

    # Count components of original graph
    def count_original_components(adj, n):
        visited = [False] * n
        components = 0
        for start in range(n):
            if visited[start]:
                continue
            components += 1
            queue = deque([start])
            visited[start] = True
            while queue:
                u = queue.popleft()
                for v in adj.get(u, []):
                    if not visited[v]:
                        visited[v] = True
                        queue.append(v)
        return components

    orig_components = count_original_components(ADJ, NUM_NODES)

    # For each reported AP, removing it should increase components
    for node in result:
        if node < 0 or node >= NUM_NODES:
            return False
        c = count_components(ADJ, NUM_NODES, node)
        # After removing a node, we should have more components
        # (accounting for the removed node itself)
        remaining_nodes = NUM_NODES - 1
        # Count components among remaining nodes
        if c <= orig_components:
            # Removing an AP should increase component count
            # (or at least the graph restricted to the AP's component splits)
            return False

    # For each non-reported node, removing should NOT increase components
    result_set = set(result)
    for node in range(NUM_NODES):
        if node in result_set:
            continue
        c = count_components(ADJ, NUM_NODES, node)
        if c > orig_components:
            return False  # missed an articulation point

    return True


BUG_DESC = (
    "For the root special case in DFS-based articulation point detection, the bug "
    "checks len(adj[root]) > 1 (total number of neighbors) instead of counting "
    "only DFS tree children. In a graph where the root has multiple edges but they "
    "all lead into the same biconnected component (only one DFS tree child), the "
    "root is incorrectly identified as an articulation point."
)


def _generate_graph():
    import random
    n = random.randint(6, 10)
    adj = {i: [] for i in range(n)}

    # Create a connected spanning tree first
    nodes = list(range(n))
    random.shuffle(nodes)
    for i in range(1, n):
        u, v = nodes[i - 1], nodes[i]
        adj[u].append(v)
        adj[v].append(u)

    # Add extra edges with some probability
    for i in range(n):
        for j in range(i + 1, n):
            if j not in adj[i] and random.random() < 0.3:
                adj[i].append(j)
                adj[j].append(i)

    # Ensure a bridge exists to guarantee at least one AP:
    # Pick a node and connect it via a single edge to the rest
    # Actually, add a pendant vertex (degree 1 connection through a specific node)
    # The node connecting to pendant is an AP if pendant is its only path
    bridge_node = random.randint(0, n - 2)
    leaf = n - 1  # reuse last node as leaf-like
    # Clear leaf's connections and reconnect via single bridge
    for neighbor in list(adj[leaf]):
        adj[neighbor].remove(leaf)
    adj[leaf] = [bridge_node]
    if leaf not in adj[bridge_node]:
        adj[bridge_node].append(leaf)

    # Ensure root (node 0) has multiple neighbors but is NOT an AP
    # by adding back-edges creating a cycle including node 0
    if n >= 4 and len(adj[0]) >= 2:
        # Connect two of node 0's neighbors to each other
        nbrs = adj[0][:2]
        if nbrs[1] not in adj[nbrs[0]]:
            adj[nbrs[0]].append(nbrs[1])
            adj[nbrs[1]].append(nbrs[0])

    return adj, n


_cached_graph = [None]

def _gen_adj():
    g, n = _generate_graph()
    _cached_graph[0] = (g, n)
    return g

def _gen_n():
    if _cached_graph[0] is None:
        _gen_adj()
    return _cached_graph[0][1]


INPUT_OVERRIDES = {
    "ADJ": _gen_adj,
    "NUM_NODES": _gen_n,
}
