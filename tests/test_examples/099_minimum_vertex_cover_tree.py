"""Minimum vertex cover on trees via dynamic programming.
Bug: in the don't-take-node case, should force ALL children to be taken,
but only forces the first child, leaving other children optional."""

CORRECT = r"""
# Minimum vertex cover on a tree via DP
# TREE: adjacency list dict {node: [neighbors]}
# ROOT: root node
# Returns (cover_size, cover_set)

tree = dict(TREE)
root = ROOT
nodes = sorted(tree.keys())
n = len(nodes)

if n == 0:
    result = (0, [])
elif n == 1:
    result = (0, [])
else:
    # Build rooted tree
    children = {v: [] for v in nodes}
    visited = set([root])
    queue = [root]
    order = []
    while queue:
        v = queue.pop(0)
        order.append(v)
        for u in tree.get(v, []):
            if u not in visited:
                visited.add(u)
                children[v].append(u)
                queue.append(u)

    # DP:
    # dp[v][0] = min cover size in subtree(v) when v is NOT in cover
    # dp[v][1] = min cover size in subtree(v) when v IS in cover
    dp = {v: [0, 0] for v in nodes}

    # Process leaves first (reverse BFS order)
    for v in reversed(order):
        if not children[v]:
            # Leaf node
            dp[v][0] = 0  # don't take leaf
            dp[v][1] = 1  # take leaf
        else:
            # Don't take v: ALL children must be taken (to cover edges v-child)
            # CORRECT: force all children to be in cover
            dp[v][0] = 0
            for c in children[v]:
                dp[v][0] += dp[c][1]

            # Take v: children can be taken or not (edges v-child are covered by v)
            dp[v][1] = 1
            for c in children[v]:
                dp[v][1] += min(dp[c][0], dp[c][1])

    # Backtrack to find the actual cover
    cover = []
    stack = [(root, dp[root][1] <= dp[root][0])]
    while stack:
        v, taken = stack.pop()
        if taken:
            cover.append(v)
            for c in children[v]:
                # Children are optional
                if dp[c][1] <= dp[c][0]:
                    stack.append((c, True))
                else:
                    stack.append((c, False))
        else:
            # v not taken, all children must be taken
            for c in children[v]:
                stack.append((c, True))

    cover_size = len(cover)
    result = (cover_size, sorted(cover))
"""

BUGGY = r"""
# Minimum vertex cover on a tree via DP
# TREE: adjacency list dict {node: [neighbors]}
# ROOT: root node
# Returns (cover_size, cover_set)

tree = dict(TREE)
root = ROOT
nodes = sorted(tree.keys())
n = len(nodes)

if n == 0:
    result = (0, [])
elif n == 1:
    result = (0, [])
else:
    # Build rooted tree
    children = {v: [] for v in nodes}
    visited = set([root])
    queue = [root]
    order = []
    while queue:
        v = queue.pop(0)
        order.append(v)
        for u in tree.get(v, []):
            if u not in visited:
                visited.add(u)
                children[v].append(u)
                queue.append(u)

    dp = {v: [0, 0] for v in nodes}

    for v in reversed(order):
        if not children[v]:
            dp[v][0] = 0
            dp[v][1] = 1
        else:
            # BUG: only forces first child to be taken when v is not taken
            # Other children get min(take, not take) which is wrong
            # because all edges v-child need to be covered
            dp[v][0] = 0
            first = True
            for c in children[v]:
                if first:
                    dp[v][0] += dp[c][1]  # force first child
                    first = False
                else:
                    dp[v][0] += min(dp[c][0], dp[c][1])  # BUG: others optional

            dp[v][1] = 1
            for c in children[v]:
                dp[v][1] += min(dp[c][0], dp[c][1])

    cover = []
    stack = [(root, dp[root][1] <= dp[root][0])]
    while stack:
        v, taken = stack.pop()
        if taken:
            cover.append(v)
            for c in children[v]:
                if dp[c][1] <= dp[c][0]:
                    stack.append((c, True))
                else:
                    stack.append((c, False))
        else:
            first = True
            for c in children[v]:
                if first:
                    stack.append((c, True))
                    first = False
                else:
                    if dp[c][1] <= dp[c][0]:
                        stack.append((c, True))
                    else:
                        stack.append((c, False))

    cover_size = len(cover)
    result = (cover_size, sorted(cover))
"""


def SPEC(tree, root, result):
    cover_size, cover_set = result
    nodes = sorted(tree.keys())
    n = len(nodes)

    if n <= 1:
        return cover_size == 0

    # Check it's a valid vertex cover: every edge has at least one endpoint in cover
    cs = set(cover_set)
    for v in nodes:
        for u in tree.get(v, []):
            if v not in cs and u not in cs:
                return False

    # Check size matches
    if len(cover_set) != cover_size:
        return False

    # Check minimality: compute optimal via DP
    children = {v: [] for v in nodes}
    visited = set([root])
    queue = [root]
    order = []
    while queue:
        v = queue.pop(0)
        order.append(v)
        for u in tree.get(v, []):
            if u not in visited:
                visited.add(u)
                children[v].append(u)
                queue.append(u)

    dp = {v: [0, 0] for v in nodes}
    for v in reversed(order):
        if not children[v]:
            dp[v][0] = 0
            dp[v][1] = 1
        else:
            dp[v][0] = sum(dp[c][1] for c in children[v])
            dp[v][1] = 1 + sum(min(dp[c][0], dp[c][1]) for c in children[v])

    optimal = min(dp[root][0], dp[root][1])
    return cover_size == optimal


BUG_DESC = (
    "In the don't-take-node case of the DP, only the first child is forced "
    "to be in the cover. Other children are treated as optional (min of take "
    "or not take), but since v is not in the cover, ALL edges from v to its "
    "children must be covered by the children. This under-counts the cover."
)


def _gen_tree():
    import random
    n = random.randint(5, 12)
    tree = {i: [] for i in range(n)}
    for i in range(1, n):
        p = random.randint(0, i - 1)
        tree[i].append(p)
        tree[p].append(i)
    return tree


def _gen_root():
    return 0


INPUT_OVERRIDES = {"TREE": _gen_tree, "ROOT": _gen_root}
