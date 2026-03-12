"""Hierholzer's algorithm for Eulerian path/circuit. Bug: doesn't check that all vertices
with nonzero degree are connected, so returns an invalid path for disconnected graphs
that satisfy Euler degree conditions locally."""

CORRECT = r"""
# Hierholzer's algorithm for Eulerian path or circuit
# Returns the path as a list of vertices, or empty list if none exists

from collections import defaultdict, deque

n_vertices = GRAPH_N
edges = GRAPH_EDGES

adj = defaultdict(list)
degree = [0] * n_vertices
for u, v in edges:
    adj[u].append(v)
    adj[v].append(u)
    degree[u] += 1
    degree[v] += 1

# Check degree conditions
odd_degree_vertices = [v for v in range(n_vertices) if degree[v] % 2 == 1]

can_have_euler = False
start_vertex = -1
is_circuit = False

if len(odd_degree_vertices) == 0:
    can_have_euler = True
    is_circuit = True
    # Find a vertex with nonzero degree
    for v in range(n_vertices):
        if degree[v] > 0:
            start_vertex = v
            break
elif len(odd_degree_vertices) == 2:
    can_have_euler = True
    is_circuit = False
    start_vertex = odd_degree_vertices[0]
else:
    can_have_euler = False

# Check connectivity of vertices with nonzero degree
if can_have_euler and start_vertex != -1:
    visited = set()
    stack = [start_vertex]
    visited.add(start_vertex)
    while stack:
        curr = stack.pop()
        for nb in adj[curr]:
            if nb not in visited:
                visited.add(nb)
                stack.append(nb)
    nonzero_verts = {v for v in range(n_vertices) if degree[v] > 0}
    if not nonzero_verts.issubset(visited):
        can_have_euler = False

path = []
if can_have_euler and start_vertex != -1:
    # Build adjacency with edge indices for removal
    adj2 = defaultdict(list)
    used = [False] * len(edges)
    for idx, (u, v) in enumerate(edges):
        adj2[u].append((v, idx))
        adj2[v].append((u, idx))

    # Hierholzer's algorithm
    stack = [start_vertex]
    circuit = []
    ptr = defaultdict(int)  # pointer for each vertex into its adjacency list

    while stack:
        v = stack[-1]
        found = False
        while ptr[v] < len(adj2[v]):
            nb, eidx = adj2[v][ptr[v]]
            ptr[v] += 1
            if not used[eidx]:
                used[eidx] = True
                stack.append(nb)
                found = True
                break
        if not found:
            circuit.append(stack.pop())

    path = circuit[::-1]

result = {
    "path": path,
    "n_vertices": n_vertices,
    "n_edges": len(edges),
    "is_circuit": is_circuit,
    "can_have_euler": can_have_euler,
}
"""

BUGGY = r"""
# Hierholzer's algorithm - BUG: missing connectivity check
from collections import defaultdict, deque

n_vertices = GRAPH_N
edges = GRAPH_EDGES

adj = defaultdict(list)
degree = [0] * n_vertices
for u, v in edges:
    adj[u].append(v)
    adj[v].append(u)
    degree[u] += 1
    degree[v] += 1

odd_degree_vertices = [v for v in range(n_vertices) if degree[v] % 2 == 1]

can_have_euler = False
start_vertex = -1
is_circuit = False

if len(odd_degree_vertices) == 0:
    can_have_euler = True
    is_circuit = True
    for v in range(n_vertices):
        if degree[v] > 0:
            start_vertex = v
            break
elif len(odd_degree_vertices) == 2:
    can_have_euler = True
    is_circuit = False
    start_vertex = odd_degree_vertices[0]
else:
    can_have_euler = False

# BUG: No connectivity check!
# A disconnected graph can satisfy degree conditions locally
# but have no Eulerian path/circuit

path = []
if can_have_euler and start_vertex != -1:
    adj2 = defaultdict(list)
    used = [False] * len(edges)
    for idx, (u, v) in enumerate(edges):
        adj2[u].append((v, idx))
        adj2[v].append((u, idx))

    stack = [start_vertex]
    circuit = []
    ptr = defaultdict(int)

    while stack:
        v = stack[-1]
        found = False
        while ptr[v] < len(adj2[v]):
            nb, eidx = adj2[v][ptr[v]]
            ptr[v] += 1
            if not used[eidx]:
                used[eidx] = True
                stack.append(nb)
                found = True
                break
        if not found:
            circuit.append(stack.pop())

    path = circuit[::-1]

result = {
    "path": path,
    "n_vertices": n_vertices,
    "n_edges": len(edges),
    "is_circuit": is_circuit,
    "can_have_euler": can_have_euler,
}
"""

def SPEC(graph_n, graph_edges, result):
    """Verify Eulerian path/circuit correctness."""
    path = result["path"]
    n_edges = result["n_edges"]
    can_have = result["can_have_euler"]

    if n_edges == 0:
        return True

    # First check: does an Euler path/circuit actually exist?
    # Need degree check + connectivity
    from collections import defaultdict
    degree = [0] * graph_n
    adj = defaultdict(set)
    for u, v in graph_edges:
        degree[u] += 1
        degree[v] += 1
        adj[u].add(v)
        adj[v].add(u)

    odd = [v for v in range(graph_n) if degree[v] % 2 == 1]
    nonzero = {v for v in range(graph_n) if degree[v] > 0}

    # Check connectivity
    if nonzero:
        start = min(nonzero)
        visited = set()
        stack = [start]
        visited.add(start)
        while stack:
            curr = stack.pop()
            for nb in adj[curr]:
                if nb not in visited:
                    visited.add(nb)
                    stack.append(nb)
        connected = nonzero.issubset(visited)
    else:
        connected = True

    euler_exists = connected and len(odd) in (0, 2)

    if not euler_exists:
        # No Euler path exists; algorithm should not return a valid one
        if can_have and len(path) > 0:
            # Buggy code thinks it exists - check if path is actually valid
            # The path should NOT cover all edges
            edge_count = defaultdict(int)
            for u, v in graph_edges:
                e = (min(u, v), max(u, v))
                edge_count[e] += 1
            path_edge_count = defaultdict(int)
            for i in range(len(path) - 1):
                e = (min(path[i], path[i+1]), max(path[i], path[i+1]))
                path_edge_count[e] += 1
            if path_edge_count != edge_count:
                return False
            return True  # Path covers all edges somehow
        return True

    # Euler path exists; verify the returned path
    if len(path) != n_edges + 1:
        return False

    # Check each edge in path is a valid edge and each edge used exactly once
    edge_count = defaultdict(int)
    for u, v in graph_edges:
        e = (min(u, v), max(u, v))
        edge_count[e] += 1

    path_edge_count = defaultdict(int)
    for i in range(len(path) - 1):
        e = (min(path[i], path[i+1]), max(path[i], path[i+1]))
        path_edge_count[e] += 1

    if path_edge_count != edge_count:
        return False

    return True

BUG_DESC = "Missing connectivity check: returns a partial Eulerian path for disconnected graphs that satisfy degree conditions locally, resulting in a path that doesn't cover all edges."

def _gen():
    import random
    # Bug: missing connectivity check. The buggy code will try to find an Euler
    # path/circuit in a disconnected graph that satisfies degree conditions locally.
    # It will only traverse edges reachable from the start vertex, returning a
    # partial path that doesn't cover all edges. SPEC catches this.
    #
    # Generate disconnected graphs where each component has valid Euler degree
    # conditions (all even degree for circuit, or exactly 2 odd-degree vertices
    # summed across components so the global check passes).

    cases = [
        # Two disjoint triangles (all even degree -> circuit condition met globally)
        {"GRAPH_N": 6, "GRAPH_EDGES": [(0,1), (1,2), (2,0), (3,4), (4,5), (5,3)]},
        # Two disjoint squares
        {"GRAPH_N": 8, "GRAPH_EDGES": [(0,1), (1,2), (2,3), (3,0), (4,5), (5,6), (6,7), (7,4)]},
        # Triangle + single edge (both components have all even degree... no:
        # single edge has degree 1 at both endpoints. Use two triangles + isolated edge pair)
        # Two disjoint cycles of different sizes
        {"GRAPH_N": 7, "GRAPH_EDGES": [(0,1), (1,2), (2,0), (3,4), (4,5), (5,6), (6,3)]},
        # Three disjoint triangles
        {"GRAPH_N": 9, "GRAPH_EDGES": [(0,1), (1,2), (2,0), (3,4), (4,5), (5,3), (6,7), (7,8), (8,6)]},  # noqa
        # Two components each with Euler path condition (2 odd-degree vertices each,
        # but globally 4 odd-degree -> neither code tries euler. Skip this pattern.)
        # Triangle + path that forms a cycle
        {"GRAPH_N": 7, "GRAPH_EDGES": [(0,1), (1,2), (2,0), (3,4), (4,5), (5,6), (6,3)]},
    ]
    return random.choice(cases)

INPUT_OVERRIDES = _gen
