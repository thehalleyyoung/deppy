"""Euler tour representation of trees for subtree sum queries.
Bug: computes subtree by taking [entry, exit] range but uses exclusive
exit index when it should be inclusive, missing the last element."""

CORRECT = r"""
# Euler Tour for subtree sum queries
# Flatten tree into array using DFS entry/exit times, then use prefix sums

def build_adj(edges, n):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj

def euler_tour(adj, root, n):
    # DFS to compute entry and exit times
    entry = [0] * n
    exit_time = [0] * n
    order = []  # nodes in DFS entry order
    timer = [0]
    visited = [False] * n

    def dfs(u, par):
        visited[u] = True
        entry[u] = timer[0]
        order.append(u)
        timer[0] += 1
        for v in adj[u]:
            if v != par and not visited[v]:
                dfs(v, u)
        exit_time[u] = timer[0] - 1  # inclusive exit time

    dfs(root, -1)
    return entry, exit_time, order

def build_prefix_sums(order, values, n):
    # Build prefix sum array based on euler tour order
    prefix = [0] * (len(order) + 1)
    for i in range(len(order)):
        prefix[i + 1] = prefix[i] + values[order[i]]
    return prefix

def subtree_sum(node, entry, exit_time, prefix):
    # CORRECT: inclusive range [entry[node], exit_time[node]]
    l = entry[node]
    r = exit_time[node]
    return prefix[r + 1] - prefix[l]

edges = list(EDGES)
n = NUM_NODES
values = list(VALUES)
root = 0

# Pad values if needed
while len(values) < n:
    values.append(0)

adj = build_adj(edges, n)
entry, exit_time, order = euler_tour(adj, root, n)
prefix = build_prefix_sums(order, values, n)

query_nodes = list(QUERY_NODES)
result = []
for node in query_nodes:
    if 0 <= node < n:
        result.append(subtree_sum(node, entry, exit_time, prefix))
    else:
        result.append(0)
"""

BUGGY = r"""
# Euler Tour for subtree sum queries
# Flatten tree into array using DFS entry/exit times, then use prefix sums

def build_adj(edges, n):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj

def euler_tour(adj, root, n):
    # DFS to compute entry and exit times
    entry = [0] * n
    exit_time = [0] * n
    order = []
    timer = [0]
    visited = [False] * n

    def dfs(u, par):
        visited[u] = True
        entry[u] = timer[0]
        order.append(u)
        timer[0] += 1
        for v in adj[u]:
            if v != par and not visited[v]:
                dfs(v, u)
        exit_time[u] = timer[0] - 1

    dfs(root, -1)
    return entry, exit_time, order

def build_prefix_sums(order, values, n):
    prefix = [0] * (len(order) + 1)
    for i in range(len(order)):
        prefix[i + 1] = prefix[i] + values[order[i]]
    return prefix

def subtree_sum(node, entry, exit_time, prefix):
    # BUG: uses exclusive exit, so range is [entry[node], exit_time[node])
    # This misses the last node in the subtree
    l = entry[node]
    r = exit_time[node]
    return prefix[r] - prefix[l]

edges = list(EDGES)
n = NUM_NODES
values = list(VALUES)
root = 0

# Pad values if needed
while len(values) < n:
    values.append(0)

adj = build_adj(edges, n)
entry, exit_time, order = euler_tour(adj, root, n)
prefix = build_prefix_sums(order, values, n)

query_nodes = list(QUERY_NODES)
result = []
for node in query_nodes:
    if 0 <= node < n:
        result.append(subtree_sum(node, entry, exit_time, prefix))
    else:
        result.append(0)
"""


def SPEC(edges, num_nodes, values, query_nodes, result):
    # Compute subtree sums via DFS
    n = num_nodes
    if n <= 0:
        return result == []
    vals = list(values)
    while len(vals) < n:
        vals.append(0)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)

    def dfs_sum(u, par):
        s = vals[u]
        for v in adj[u]:
            if v != par:
                s += dfs_sum(v, u)
        return s

    if len(result) != len(query_nodes):
        return False
    for i, node in enumerate(query_nodes):
        if 0 <= node < n:
            expected = dfs_sum(node, -1)
            if result[i] != expected:
                return False
    return True


BUG_DESC = (
    "In subtree_sum, uses prefix[r] - prefix[l] which is an exclusive upper "
    "bound, but exit_time is inclusive. Should be prefix[r+1] - prefix[l]. "
    "This omits the last DFS-ordered node in each subtree from the sum."
)


def _gen_edges():
    import random
    n = random.randint(5, 12)
    edges = []
    for i in range(1, n):
        p = random.randint(0, i - 1)
        edges.append((p, i))
    return edges


def _gen_n():
    import random
    return random.randint(5, 12)


def _gen_values():
    import random
    return [random.randint(1, 20) for _ in range(12)]


def _gen_query_nodes():
    import random
    n = random.randint(5, 12)
    return [random.randint(0, n - 1) for _ in range(random.randint(3, 6))]


INPUT_OVERRIDES = {
    "EDGES": _gen_edges,
    "NUM_NODES": _gen_n,
    "VALUES": _gen_values,
    "QUERY_NODES": _gen_query_nodes,
}
