"""Maximum independent set on trees via dynamic programming.
Bug: in the include-node case, adds the node's own weight twice
(once explicitly and once via initialization), inflating the total."""

CORRECT = r"""
# Maximum weight independent set on a tree via DP
# TREE: adjacency list as dict {node: [neighbors]}
# WEIGHTS: dict {node: weight}
# Root at node 0

tree = dict(TREE)
weights = dict(WEIGHTS)
nodes = sorted(tree.keys())
n = len(nodes)

if n == 0:
    result = (0, [])
else:
    # Build rooted tree with parent pointers via BFS
    root = nodes[0]
    parent = {root: -1}
    children = {v: [] for v in nodes}
    visited = {root}
    queue = [root]
    order = []
    while queue:
        v = queue.pop(0)
        order.append(v)
        for u in tree.get(v, []):
            if u not in visited:
                visited.add(u)
                parent[u] = v
                children[v].append(u)
                queue.append(u)

    # DP: dp[v][0] = max IS weight in subtree(v) excluding v
    #     dp[v][1] = max IS weight in subtree(v) including v
    dp = {v: [0, 0] for v in nodes}

    # Process in reverse BFS order (leaves first)
    for v in reversed(order):
        # Exclude v: children can be included or excluded
        dp[v][0] = 0
        for c in children[v]:
            dp[v][0] += max(dp[c][0], dp[c][1])
        # Include v: children must be excluded
        # CORRECT: add weight once
        dp[v][1] = weights.get(v, 1)
        for c in children[v]:
            dp[v][1] += dp[c][0]

    # Backtrack to find the actual set
    in_set = []
    # Use stack-based backtracking
    stack = [(root, max(dp[root][0], dp[root][1]) == dp[root][1])]
    while stack:
        v, included = stack.pop()
        if included:
            in_set.append(v)
            for c in children[v]:
                stack.append((c, False))
        else:
            for c in children[v]:
                # Pick whichever is better for child
                if dp[c][1] >= dp[c][0]:
                    stack.append((c, True))
                else:
                    stack.append((c, False))

    total = sum(weights.get(v, 1) for v in in_set)
    result = (total, sorted(in_set))
"""

BUGGY = r"""
# Maximum weight independent set on a tree via DP
# TREE: adjacency list as dict {node: [neighbors]}
# WEIGHTS: dict {node: weight}
# Root at node 0

tree = dict(TREE)
weights = dict(WEIGHTS)
nodes = sorted(tree.keys())
n = len(nodes)

if n == 0:
    result = (0, [])
else:
    # Build rooted tree with parent pointers via BFS
    root = nodes[0]
    parent = {root: -1}
    children = {v: [] for v in nodes}
    visited = {root}
    queue = [root]
    order = []
    while queue:
        v = queue.pop(0)
        order.append(v)
        for u in tree.get(v, []):
            if u not in visited:
                visited.add(u)
                parent[u] = v
                children[v].append(u)
                queue.append(u)

    # DP: dp[v][0] = max IS weight in subtree(v) excluding v
    #     dp[v][1] = max IS weight in subtree(v) including v
    dp = {v: [0, 0] for v in nodes}

    # Process in reverse BFS order (leaves first)
    for v in reversed(order):
        # Exclude v: children can be included or excluded
        dp[v][0] = 0
        for c in children[v]:
            dp[v][0] += max(dp[c][0], dp[c][1])
        # Include v: children must be excluded
        # BUG: adds weight of v twice -- once here and once in the loop init
        dp[v][1] = weights.get(v, 1)
        for c in children[v]:
            dp[v][1] += dp[c][0]
        # BUG: adds node weight again
        dp[v][1] += weights.get(v, 1)

    # Backtrack to find the actual set
    in_set = []
    stack = [(root, max(dp[root][0], dp[root][1]) == dp[root][1])]
    while stack:
        v, included = stack.pop()
        if included:
            in_set.append(v)
            for c in children[v]:
                stack.append((c, False))
        else:
            for c in children[v]:
                if dp[c][1] >= dp[c][0]:
                    stack.append((c, True))
                else:
                    stack.append((c, False))

    total = sum(weights.get(v, 1) for v in in_set)
    result = (total, sorted(in_set))
"""


def SPEC(tree, weights, result):
    total, in_set = result
    nodes = sorted(tree.keys())
    if not nodes:
        return total == 0 and in_set == []
    # Check independence: no two adjacent nodes in set
    s = set(in_set)
    for v in in_set:
        for u in tree.get(v, []):
            if u in s:
                return False
    # Check total matches actual weights
    actual_total = sum(weights.get(v, 1) for v in in_set)
    if actual_total != total:
        return False
    # Check optimality: total should equal max possible IS weight
    # Recompute via DP
    root = nodes[0]
    parent_map = {root: -1}
    children_map = {v: [] for v in nodes}
    visited = {root}
    queue = [root]
    order = []
    while queue:
        v = queue.pop(0)
        order.append(v)
        for u in tree.get(v, []):
            if u not in visited:
                visited.add(u)
                parent_map[u] = v
                children_map[v].append(u)
                queue.append(u)
    dp = {v: [0, 0] for v in nodes}
    for v in reversed(order):
        dp[v][0] = sum(max(dp[c][0], dp[c][1]) for c in children_map[v])
        dp[v][1] = weights.get(v, 1) + sum(dp[c][0] for c in children_map[v])
    optimal = max(dp[root][0], dp[root][1])
    return total == optimal


BUG_DESC = (
    "In the include-node DP case, the node's weight is added twice: "
    "once during initialization and once after the children loop. "
    "This inflates dp[v][1], causing the backtracking to select "
    "suboptimal sets whose reported total doesn't match actual weights."
)


def _gen():
    import random
    n = random.randint(4, 10)
    nodes = list(range(n))
    # Build random tree
    tree = {v: [] for v in nodes}
    for i in range(1, n):
        p = random.randint(0, i - 1)
        tree[i].append(p)
        tree[p].append(i)
    weights = {v: random.randint(1, 10) for v in nodes}
    return tree, weights


def _gen_tree():
    return _gen()[0]


def _gen_weights():
    import random
    n = random.randint(4, 10)
    return {v: random.randint(1, 10) for v in range(n)}


INPUT_OVERRIDES = {"TREE": _gen_tree, "WEIGHTS": _gen_weights}
