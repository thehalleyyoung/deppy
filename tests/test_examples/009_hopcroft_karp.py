"""Hopcroft-Karp algorithm for maximum bipartite matching.

Uses alternating BFS/DFS phases to find maximum matching in a bipartite
graph. BFS builds a layered graph of shortest augmenting paths, then DFS
finds vertex-disjoint augmenting paths within that layered structure.

Bug: in the DFS phase, when an augmenting path is found, only match_left
is updated (match_left[u] = v) but match_right is NOT updated
(match_right[v] = u is missing). This means subsequent augmenting paths
don't see the updated matching and can reuse already-matched right nodes.
"""

CORRECT = r"""
from collections import deque

def hopcroft_karp(graph):
    # Find maximum bipartite matching.
    # graph: dict mapping left nodes to list of right node neighbors.
    # Returns (matching_dict, matching_size).
    INF = float('inf')

    # Collect all left and right nodes
    left_nodes = sorted(graph.keys())
    right_nodes = set()
    for u in graph:
        for v in graph[u]:
            right_nodes.add(v)
    right_nodes = sorted(right_nodes)

    # NIL sentinel for unmatched nodes
    NIL = None

    # Initialize matchings
    match_left = {u: NIL for u in left_nodes}
    match_right = {v: NIL for v in right_nodes}

    # Distance labels for BFS layers
    dist = {}

    def bfs():
        # Build layered graph of shortest augmenting paths.
        queue = deque()
        for u in left_nodes:
            if match_left[u] is NIL:
                dist[u] = 0
                queue.append(u)
            else:
                dist[u] = INF

        found = False
        while queue:
            u = queue.popleft()
            for v in graph.get(u, []):
                # Follow matched edge from v to its left partner
                next_u = match_right[v]
                if next_u is NIL:
                    found = True
                elif dist.get(next_u, INF) == INF:
                    dist[next_u] = dist[u] + 1
                    queue.append(next_u)
        return found

    def dfs(u):
        # Find augmenting path from u via DFS on layered graph.
        for v in graph.get(u, []):
            next_u = match_right[v]
            if next_u is NIL or (dist.get(next_u, INF) == dist[u] + 1
                                  and dfs(next_u)):
                # CORRECT: update both match_left and match_right
                match_left[u] = v
                match_right[v] = u
                return True
        dist[u] = INF
        return False

    matching_size = 0

    # Alternate BFS and DFS phases until no more augmenting paths
    while bfs():
        for u in left_nodes:
            if match_left[u] is NIL:
                if dfs(u):
                    matching_size += 1

    # Build result matching dict (only matched pairs)
    matching = {}
    for u in left_nodes:
        if match_left[u] is not NIL:
            matching[u] = match_left[u]

    result = (matching, matching_size)
    return result

graph = GRAPH
result = hopcroft_karp(graph)
"""

BUGGY = r"""
from collections import deque

def hopcroft_karp(graph):
    # Find maximum bipartite matching.
    # graph: dict mapping left nodes to list of right node neighbors.
    # Returns (matching_dict, matching_size).
    INF = float('inf')

    # Collect all left and right nodes
    left_nodes = sorted(graph.keys())
    right_nodes = set()
    for u in graph:
        for v in graph[u]:
            right_nodes.add(v)
    right_nodes = sorted(right_nodes)

    # NIL sentinel for unmatched nodes
    NIL = None

    # Initialize matchings
    match_left = {u: NIL for u in left_nodes}
    match_right = {v: NIL for v in right_nodes}

    # Distance labels for BFS layers
    dist = {}

    def bfs():
        # Build layered graph of shortest augmenting paths.
        queue = deque()
        for u in left_nodes:
            if match_left[u] is NIL:
                dist[u] = 0
                queue.append(u)
            else:
                dist[u] = INF

        found = False
        while queue:
            u = queue.popleft()
            for v in graph.get(u, []):
                next_u = match_right[v]
                if next_u is NIL:
                    found = True
                elif dist.get(next_u, INF) == INF:
                    dist[next_u] = dist[u] + 1
                    queue.append(next_u)
        return found

    def dfs(u):
        # Find augmenting path from u via DFS on layered graph.
        for v in graph.get(u, []):
            next_u = match_right[v]
            if next_u is NIL or (dist.get(next_u, INF) == dist[u] + 1
                                  and dfs(next_u)):
                # BUG: only updates match_left, forgets match_right
                match_left[u] = v
                # match_right[v] = u  <-- MISSING!
                return True
        dist[u] = INF
        return False

    matching_size = 0

    # Alternate BFS and DFS phases until no more augmenting paths
    while bfs():
        for u in left_nodes:
            if match_left[u] is NIL:
                if dfs(u):
                    matching_size += 1

    # Build result matching dict (only matched pairs)
    matching = {}
    for u in left_nodes:
        if match_left[u] is not NIL:
            matching[u] = match_left[u]

    result = (matching, matching_size)
    return result

graph = GRAPH
result = hopcroft_karp(graph)
"""


def SPEC(graph, result):
    """Verify bipartite matching correctness:
    1) Matching is valid: no two left nodes matched to same right node.
    2) All matched edges exist in original graph.
    3) Matching size is optimal (compare to brute-force for small inputs).
    """
    matching, matching_size = result

    if not isinstance(matching, dict):
        return False
    if not isinstance(matching_size, int):
        return False

    # Check matching size consistency
    if len(matching) != matching_size:
        return False

    # Check all matched edges exist in graph
    for u, v in matching.items():
        if u not in graph:
            return False
        if v not in graph[u]:
            return False

    # Check no two left nodes match to the same right node
    right_used = set()
    for u, v in matching.items():
        if v in right_used:
            return False
        right_used.add(v)

    # Optimality check: brute-force maximum matching
    left_nodes = sorted(graph.keys())
    right_nodes = set()
    for u in graph:
        for v in graph[u]:
            right_nodes.add(v)
    right_nodes = sorted(right_nodes)

    # For small graphs, find maximum matching by trying all possibilities
    def max_matching_brute(left_list, assigned, depth):
        if depth == len(left_list):
            return 0
        u = left_list[depth]
        # Option 1: don't match u
        best = max_matching_brute(left_list, assigned, depth + 1)
        # Option 2: match u to some unassigned v
        for v in graph.get(u, []):
            if v not in assigned:
                assigned.add(v)
                candidate = 1 + max_matching_brute(left_list, assigned, depth + 1)
                if candidate > best:
                    best = candidate
                assigned.remove(v)
        return best

    if len(left_nodes) <= 8 and len(right_nodes) <= 8:
        optimal = max_matching_brute(left_nodes, set(), 0)
        if matching_size != optimal:
            return False

    return True


BUG_DESC = (
    "In the DFS phase, when an augmenting path is found and the matching "
    "is updated, only match_left[u] = v is set, but match_right[v] = u "
    "is omitted. This means the BFS phase in subsequent iterations still "
    "sees right node v as unmatched (match_right[v] == NIL), allowing "
    "multiple left nodes to be 'matched' to the same right node. The "
    "result is an invalid matching that may also be suboptimal."
)


def _generate_graph():
    import random
    n_left = random.randint(3, 5)
    n_right = random.randint(3, 5)
    graph = {}
    for u in range(n_left):
        # Each left node gets 2-3 random right neighbors
        num_edges = random.randint(2, min(3, n_right))
        neighbors = random.sample(range(n_right), num_edges)
        graph[u] = neighbors
    return graph


INPUT_OVERRIDES = {
    "GRAPH": _generate_graph,
}
