"""Augmenting path algorithm for maximum bipartite matching.

Bug: when DFS finds an augmenting path, only updates one end of the
matching instead of flipping the entire augmenting path.
"""

CORRECT = r"""
def max_bipartite_matching(adj, n_left, n_right):
    # adj: dict mapping left node -> list of right nodes
    # Returns dict of right_node -> left_node (the matching)
    match_right = {}  # right -> left
    match_left = {}   # left -> right

    def dfs(u, visited):
        for v in adj.get(u, []):
            if v in visited:
                continue
            visited.add(v)
            # If v is free or we can find an augmenting path from match_right[v]
            if v not in match_right or dfs(match_right[v], visited):
                # CORRECT: update both sides of the matching
                match_right[v] = u
                match_left[u] = v
                return True
        return False

    for u in range(n_left):
        visited = set()
        dfs(u, visited)

    # Return matching as list of (left, right) pairs sorted by left node
    matching = []
    for u in range(n_left):
        if u in match_left:
            matching.append((u, match_left[u]))
    matching.sort()
    return matching

adj = ADJ
n_left = N_LEFT
n_right = N_RIGHT
result = max_bipartite_matching(adj, n_left, n_right)
"""

BUGGY = r"""
def max_bipartite_matching(adj, n_left, n_right):
    # adj: dict mapping left node -> list of right nodes
    # Returns dict of right_node -> left_node (the matching)
    match_right = {}  # right -> left
    match_left = {}   # left -> right

    def dfs(u, visited):
        for v in adj.get(u, []):
            if v in visited:
                continue
            visited.add(v)
            if v not in match_right or dfs(match_right[v], visited):
                # BUG: only update match_left, not match_right
                # This means match_right never gets updated beyond initial,
                # so augmenting paths through previously matched nodes fail
                match_left[u] = v
                return True
        return False

    for u in range(n_left):
        visited = set()
        dfs(u, visited)

    # Return matching as list of (left, right) pairs sorted by left node
    matching = []
    for u in range(n_left):
        if u in match_left:
            matching.append((u, match_left[u]))
    matching.sort()
    return matching

adj = ADJ
n_left = N_LEFT
n_right = N_RIGHT
result = max_bipartite_matching(adj, n_left, n_right)
"""


def SPEC(adj, n_left, n_right, result):
    if not isinstance(result, list):
        return False

    # All entries must be valid (left, right) pairs
    left_used = set()
    right_used = set()
    for pair in result:
        if not isinstance(pair, (list, tuple)) or len(pair) != 2:
            return False
        u, v = pair
        if u < 0 or u >= n_left:
            return False
        if v not in adj.get(u, []):
            return False
        if u in left_used or v in right_used:
            return False  # not a valid matching
        left_used.add(u)
        right_used.add(v)

    # Verify maximality: no augmenting path exists
    # Build residual graph and check for augmenting paths via BFS
    match_right = {}
    match_left = {}
    for u, v in result:
        match_left[u] = v
        match_right[v] = u

    # Try to find augmenting path from any free left node
    from collections import deque
    for start in range(n_left):
        if start in match_left:
            continue
        # BFS for augmenting path
        # We alternate: free left -> right neighbors -> matched left -> ...
        visited_right = set()
        queue = deque([start])
        visited_left = {start}
        parent = {}  # right_node -> left_node that reached it
        found = False
        while queue and not found:
            u = queue.popleft()
            for v in adj.get(u, []):
                if v in visited_right:
                    continue
                visited_right.add(v)
                if v not in match_right:
                    # Found augmenting path -> matching is not maximum
                    found = True
                    break
                else:
                    next_left = match_right[v]
                    if next_left not in visited_left:
                        visited_left.add(next_left)
                        queue.append(next_left)
        if found:
            return False

    return True


BUG_DESC = (
    "When an augmenting path is found via DFS, only match_left[u] = v is "
    "updated but match_right[v] = u is not. This means future DFS calls "
    "cannot detect that v is already matched, so augmenting paths through "
    "previously matched right-side nodes are never found, resulting in a "
    "sub-optimal matching."
)


def _generate_adj():
    import random
    n_left = random.randint(4, 7)
    n_right = random.randint(4, 7)
    adj = {}
    for u in range(n_left):
        neighbors = []
        for v in range(n_right):
            if random.random() < 0.45:
                neighbors.append(v)
        if not neighbors:
            neighbors.append(random.randint(0, n_right - 1))
        adj[u] = neighbors
    return adj


def _generate_n_left():
    return _generate_n_left._val


def _generate_n_right():
    return _generate_n_right._val


def _gen():
    import random
    n_left = random.randint(4, 7)
    n_right = random.randint(4, 7)
    adj = {}
    for u in range(n_left):
        neighbors = []
        for v in range(n_right):
            if random.random() < 0.45:
                neighbors.append(v)
        if not neighbors:
            neighbors.append(random.randint(0, n_right - 1))
        adj[u] = neighbors
    _gen._adj = adj
    _gen._n_left = n_left
    _gen._n_right = n_right
    return adj


def _gen_nl():
    return _gen._n_left


def _gen_nr():
    return _gen._n_right


INPUT_OVERRIDES = {
    "ADJ": _gen,
    "N_LEFT": _gen_nl,
    "N_RIGHT": _gen_nr,
}
