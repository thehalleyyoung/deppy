"""Bridge detection in undirected graphs via DFS. Bug: uses low[v] >= disc[u] instead of
low[v] > disc[u] for bridge check, incorrectly marking non-bridge edges as bridges in
graphs with back-edges to the parent's discovery time."""

CORRECT = r"""
# Bridge finding in an undirected graph using Tarjan's algorithm
# An edge (u,v) is a bridge if removing it disconnects the graph

n_vertices = GRAPH_N
edges = GRAPH_EDGES

adj = [[] for _ in range(n_vertices)]
for u, v in edges:
    adj[u].append(v)
    adj[v].append(u)

disc = [-1] * n_vertices
low = [-1] * n_vertices
timer = [0]
bridges = []

def dfs(u, parent):
    disc[u] = low[u] = timer[0]
    timer[0] += 1

    for v in adj[u]:
        if disc[v] == -1:
            dfs(v, u)
            low[u] = min(low[u], low[v])
            # Bridge condition: no back edge from subtree of v can reach u or above
            if low[v] > disc[u]:
                bridges.append((min(u, v), max(u, v)))
        elif v != parent:
            low[u] = min(low[u], disc[v])

# Handle disconnected graph
for i in range(n_vertices):
    if disc[i] == -1:
        dfs(i, -1)

bridges.sort()

result = {
    "bridges": bridges,
    "n_vertices": n_vertices,
    "n_edges": len(edges),
    "disc": disc,
    "low": low,
}
"""

BUGGY = r"""
# Bridge finding with incorrect bridge condition
n_vertices = GRAPH_N
edges = GRAPH_EDGES

adj = [[] for _ in range(n_vertices)]
for u, v in edges:
    adj[u].append(v)
    adj[v].append(u)

disc = [-1] * n_vertices
low = [-1] * n_vertices
timer = [0]
bridges = []

def dfs(u, parent):
    disc[u] = low[u] = timer[0]
    timer[0] += 1

    for v in adj[u]:
        if disc[v] == -1:
            dfs(v, u)
            low[u] = min(low[u], low[v])
            # BUG: uses >= instead of >
            # This marks edges as bridges even when there is a back-edge
            # to exactly disc[u], which means the edge is NOT a bridge
            if low[v] >= disc[u]:
                bridges.append((min(u, v), max(u, v)))
        elif v != parent:
            low[u] = min(low[u], disc[v])

for i in range(n_vertices):
    if disc[i] == -1:
        dfs(i, -1)

bridges.sort()

result = {
    "bridges": bridges,
    "n_vertices": n_vertices,
    "n_edges": len(edges),
    "disc": disc,
    "low": low,
}
"""

def SPEC(graph_n, graph_edges, result):
    """Verify bridge detection correctness."""
    bridges = result["bridges"]
    n = result["n_vertices"]

    # Build adjacency for connectivity check
    from collections import deque

    def is_connected_without(edge_to_remove, verts, all_edges):
        # Check if the graph remains connected after removing one edge
        adj_test = [[] for _ in range(n)]
        removed_once = False
        for u, v in all_edges:
            e = (min(u, v), max(u, v))
            if e == edge_to_remove and not removed_once:
                removed_once = True
                continue
            adj_test[u].append(v)
            adj_test[v].append(u)
        # BFS from first vertex with edges
        start = -1
        has_edge = set()
        for u, v in all_edges:
            has_edge.add(u)
            has_edge.add(v)
        if not has_edge:
            return True
        start = min(has_edge)
        visited = set()
        queue = deque([start])
        visited.add(start)
        while queue:
            curr = queue.popleft()
            for nb in adj_test[curr]:
                if nb not in visited:
                    visited.add(nb)
                    queue.append(nb)
        return has_edge.issubset(visited)

    # Compute true bridges by brute force
    true_bridges = set()
    for u, v in graph_edges:
        e = (min(u, v), max(u, v))
        if not is_connected_without(e, n, graph_edges):
            true_bridges.add(e)

    reported = set(tuple(b) for b in bridges)

    if reported != true_bridges:
        return False

    return True

BUG_DESC = "Uses low[v] >= disc[u] instead of low[v] > disc[u] for bridge detection, which falsely identifies tree edges as bridges when there is a back-edge reaching exactly disc[u]."

def _gen():
    import random
    # Bug: uses low[v] >= disc[u] instead of low[v] > disc[u].
    # This falsely marks edge (u,v) as bridge when low[v] == disc[u].
    # low[v] == disc[u] means v's subtree has a back-edge reaching exactly u,
    # so (u,v) is NOT a bridge (removing it still leaves a cycle through u).
    #
    # To trigger: need a tree edge (u,v) where v's subtree has a back-edge
    # to exactly u (not above u). A simple cycle does this:
    #
    # Example: triangle 0-1-2-0
    #   DFS from 0: disc[0]=0, disc[1]=1, disc[2]=2
    #   Edge 2->0 is back-edge: low[2] = min(low[2], disc[0]) = 0
    #   low[1] = min(low[1], low[2]) = 0
    #   Check edge 0->1: low[1]=0 >= disc[0]=0? YES (bug says bridge)
    #                     low[1]=0 > disc[0]=0? NO (correct says not bridge)
    #   Triangle has NO bridges. Bug reports (0,1) as bridge.
    #
    # Use small graphs with triangles and some tree edges (actual bridges).

    cases = [
        # Triangle only: no bridges, bug reports false bridges
        {"GRAPH_N": 3, "GRAPH_EDGES": [(0,1), (1,2), (2,0)]},
        # Triangle + pendant: (3,2) is a real bridge, but bug also reports triangle edges
        {"GRAPH_N": 4, "GRAPH_EDGES": [(0,1), (1,2), (2,0), (2,3)]},
        # Two triangles connected by a bridge
        {"GRAPH_N": 6, "GRAPH_EDGES": [(0,1), (1,2), (2,0), (2,3), (3,4), (4,5), (5,3)]},
        # Square (4-cycle): back-edge reaches parent exactly
        {"GRAPH_N": 4, "GRAPH_EDGES": [(0,1), (1,2), (2,3), (3,0)]},
        # Triangle with extra vertex
        {"GRAPH_N": 5, "GRAPH_EDGES": [(0,1), (1,2), (2,0), (0,3), (3,4)]},
        # Diamond: 0-1, 0-2, 1-3, 2-3 - no bridges
        {"GRAPH_N": 4, "GRAPH_EDGES": [(0,1), (0,2), (1,3), (2,3)]},
    ]
    return random.choice(cases)

INPUT_OVERRIDES = _gen
