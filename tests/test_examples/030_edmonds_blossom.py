"""Simplified Edmonds' blossom algorithm for maximum matching in general
(non-bipartite) graphs.

Bug: When contracting a blossom, all edges incident to blossom vertices should
be redirected to the blossom super-node. The bug only redirects edges from the
blossom base vertex, missing edges from other blossom members, which causes
potential augmenting paths through the blossom to be missed.
"""

CORRECT = r"""
from collections import deque

def max_matching(n, edges):
    # n: number of vertices (0..n-1)
    # edges: list of (u, v) undirected edges
    # Returns: list of matched edge tuples and matching size

    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)

    match = [-1] * n

    def find_augmenting_path(root):
        # BFS to find augmenting path with blossom contraction
        parent = [-1] * n
        visited = [False] * n
        base = list(range(n))  # base[v] = base of blossom containing v

        def find_base(u, v):
            # Find LCA in the forest
            used = [False] * n
            cu = u
            while True:
                cu = base[cu]
                used[cu] = True
                if match[cu] == -1:
                    break
                cu = parent[match[cu]]
            cv = v
            while True:
                cv = base[cv]
                if used[cv]:
                    return cv
                cv = parent[match[cv]]

        def contract_blossom(u, v, lca, queue):
            while base[u] != lca:
                parent[u] = v
                v2 = match[u]
                visited[v2] = True
                queue.append(v2)
                base[u] = lca
                base[v2] = lca
                u = parent[v2]
            # CORRECT: base is updated for all blossom vertices

        queue = deque([root])
        visited[root] = True

        while queue:
            u = queue.popleft()
            for v in adj[u]:
                if base[u] == base[v] or match[u] == v:
                    continue
                if v == root or (match[v] != -1 and parent[match[v]] != -1):
                    # Blossom found
                    lca = find_base(u, v)
                    contract_blossom(u, v, lca, queue)
                    contract_blossom(v, u, lca, queue)
                elif parent[v] == -1:
                    parent[v] = u
                    if match[v] == -1:
                        # Augmenting path found - augment
                        cur = v
                        while cur != -1:
                            prev = parent[cur]
                            pprev = match[prev]
                            match[cur] = prev
                            match[prev] = cur
                            cur = pprev
                        return True
                    else:
                        w = match[v]
                        visited[w] = True
                        queue.append(w)
        return False

    matching_size = 0
    for u in range(n):
        if match[u] == -1:
            if find_augmenting_path(u):
                matching_size += 1

    matched_edges = []
    seen = set()
    for u in range(n):
        if match[u] != -1 and u not in seen:
            v = match[u]
            matched_edges.append((min(u, v), max(u, v)))
            seen.add(u)
            seen.add(v)
    matched_edges.sort()

    return matched_edges, matching_size

num_vertices = NUM_VERTICES
edges = EDGES
result = max_matching(num_vertices, edges)
"""

BUGGY = r"""
from collections import deque

def max_matching(n, edges):
    # n: number of vertices (0..n-1)
    # edges: list of (u, v) undirected edges
    # Returns: list of matched edge tuples and matching size

    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)

    match = [-1] * n

    def find_augmenting_path(root):
        # BFS to find augmenting path with blossom contraction
        parent = [-1] * n
        visited = [False] * n
        base = list(range(n))  # base[v] = base of blossom containing v

        def find_base(u, v):
            # Find LCA in the forest
            used = [False] * n
            cu = u
            while True:
                cu = base[cu]
                used[cu] = True
                if match[cu] == -1:
                    break
                cu = parent[match[cu]]
            cv = v
            while True:
                cv = base[cv]
                if used[cv]:
                    return cv
                cv = parent[match[cv]]

        def contract_blossom(u, v, lca, queue):
            # BUG: only updates base for the first vertex, not all blossom vertices
            if base[u] != lca:
                parent[u] = v
                base[u] = lca
                v2 = match[u]
                if v2 != -1:
                    visited[v2] = True
                    queue.append(v2)
                    base[v2] = lca
                # Missing: does NOT continue the loop to update all blossom vertices
                # Should walk: u -> parent[match[u]] -> ... until reaching lca

        queue = deque([root])
        visited[root] = True

        while queue:
            u = queue.popleft()
            for v in adj[u]:
                if base[u] == base[v] or match[u] == v:
                    continue
                if v == root or (match[v] != -1 and parent[match[v]] != -1):
                    # Blossom found
                    lca = find_base(u, v)
                    contract_blossom(u, v, lca, queue)
                    contract_blossom(v, u, lca, queue)
                elif parent[v] == -1:
                    parent[v] = u
                    if match[v] == -1:
                        # Augmenting path found - augment
                        cur = v
                        while cur != -1:
                            prev = parent[cur]
                            pprev = match[prev]
                            match[cur] = prev
                            match[prev] = cur
                            cur = pprev
                        return True
                    else:
                        w = match[v]
                        visited[w] = True
                        queue.append(w)
        return False

    matching_size = 0
    for u in range(n):
        if match[u] == -1:
            if find_augmenting_path(u):
                matching_size += 1

    matched_edges = []
    seen = set()
    for u in range(n):
        if match[u] != -1 and u not in seen:
            v = match[u]
            matched_edges.append((min(u, v), max(u, v)))
            seen.add(u)
            seen.add(v)
    matched_edges.sort()

    return matched_edges, matching_size

num_vertices = NUM_VERTICES
edges = EDGES
result = max_matching(num_vertices, edges)
"""


def SPEC(NUM_VERTICES, EDGES, result):
    """Verify maximum matching:
    1) Matching is valid: no vertex in more than one matched edge
    2) All matched edges exist in original graph
    3) Matching size is optimal (brute force for small graphs)
    """
    from itertools import combinations

    if not isinstance(result, (list, tuple)) or len(result) != 2:
        return False

    matched_edges, matching_size = result

    if not isinstance(matched_edges, list):
        return False
    if not isinstance(matching_size, int):
        return False
    if len(matched_edges) != matching_size:
        return False

    edge_set = set()
    for u, v in EDGES:
        edge_set.add((min(u, v), max(u, v)))

    # (1) & (2) Validity check
    used_vertices = set()
    for edge in matched_edges:
        if not isinstance(edge, (list, tuple)) or len(edge) != 2:
            return False
        u, v = edge
        # Edge must exist in original graph
        if (min(u, v), max(u, v)) not in edge_set:
            return False
        # No vertex reuse
        if u in used_vertices or v in used_vertices:
            return False
        used_vertices.add(u)
        used_vertices.add(v)

    # (3) Optimality: brute force maximum matching for small graphs
    n = NUM_VERTICES
    edge_list = list(edge_set)

    if len(edge_list) <= 20:
        # Try all subsets of edges to find max matching
        best = matching_size  # at least as good as what we found

        def brute_force_max_matching(edges_list):
            max_size = 0

            def backtrack(idx, used, size):
                nonlocal max_size
                if size > max_size:
                    max_size = size
                # Pruning: remaining edges can't improve enough
                if size + (len(edges_list) - idx) <= max_size:
                    return
                for i in range(idx, len(edges_list)):
                    u, v = edges_list[i]
                    if u not in used and v not in used:
                        used.add(u)
                        used.add(v)
                        backtrack(i + 1, used, size + 1)
                        used.remove(u)
                        used.remove(v)

            backtrack(0, set(), 0)
            return max_size

        optimal = brute_force_max_matching(edge_list)
        if matching_size != optimal:
            return False

    return True


BUG_DESC = (
    "When contracting a blossom, the correct algorithm walks along the blossom "
    "cycle updating the base of every vertex in the blossom to the LCA. The bug "
    "only updates the base for the first vertex and its match, stopping after one "
    "step instead of traversing the entire blossom. This means vertices deeper in "
    "the blossom retain their original base, so edges incident to them are not "
    "properly redirected through the super-node, missing augmenting paths."
)


def _generate_graph():
    # The bug only updates base for the first vertex in a blossom contraction,
    # not the full cycle. To trigger this, we need a graph where:
    # 1. There's a blossom (odd cycle) of size >= 5 (a triangle blossom
    #    only has 3 vertices, and the bug updates 2 of them, which may suffice)
    # 2. An augmenting path goes through deeper blossom vertices whose base
    #    was NOT updated.
    #
    # Classic triggering case: a 5-cycle with pendant edges needing augmentation.
    # Triangle 0-1-2 with pendant vertices attached, plus a 5-cycle.
    #
    # Known hard graph for incomplete blossom contraction:
    #   Pentagon 0-1-2-3-4 (5-cycle / blossom)
    #   Pendant vertex 5 connected to 0
    #   Pendant vertex 6 connected to 2
    #
    # Maximum matching = 3 (e.g., {(0,5), (1,2), (3,4)} or {(0,5), (2,6), (3,4)})
    # The buggy code may find only 2 because it can't augment through the full blossom.

    import random
    # Use a few known hard cases that reliably trigger the bug
    cases = [
        # Case 1: Pentagon with two pendants
        (7, [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (2,6)]),
        # Case 2: Pentagon with three pendants
        (8, [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (2,6), (4,7)]),
        # Case 3: Two triangles sharing an edge with pendants
        (7, [(0,1), (1,2), (2,0), (2,3), (3,4), (4,2), (0,5), (4,6)]),
        # Case 4: 7-cycle with pendant
        (8, [(0,1), (1,2), (2,3), (3,4), (4,5), (5,6), (6,0), (0,7)]),
    ]
    return random.choice(cases)


_cached = [None]

def _gen_vertices():
    n, e = _generate_graph()
    _cached[0] = (n, e)
    return n

def _gen_edges():
    if _cached[0] is None:
        _gen_vertices()
    return _cached[0][1]


INPUT_OVERRIDES = {
    "NUM_VERTICES": _gen_vertices,
    "EDGES": _gen_edges,
}
