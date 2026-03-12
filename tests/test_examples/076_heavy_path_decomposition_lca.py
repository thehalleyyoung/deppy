"""LCA via heavy path decomposition (heavy-light decomposition).
Bug: when walking up chains, compares chain-head depths incorrectly
(uses > instead of <), moving the wrong node up."""

CORRECT = r"""
# Heavy Path (Heavy-Light) Decomposition for LCA queries
# Decomposes tree into chains; LCA query walks chains upward

def build_tree(adj, root, n):
    # BFS to set parent and depth
    parent = [-1] * n
    depth = [0] * n
    order = []
    visited = [False] * n
    queue = [root]
    visited[root] = True
    while queue:
        node = queue.pop(0)
        order.append(node)
        for nb in adj[node]:
            if not visited[nb]:
                visited[nb] = True
                parent[nb] = node
                depth[nb] = depth[node] + 1
                queue.append(nb)
    return parent, depth, order

def compute_subtree_sizes(adj, parent, order, n):
    size = [1] * n
    # Process in reverse BFS order (leaves first)
    for node in reversed(order):
        for nb in adj[node]:
            if nb != parent[node]:
                size[node] += size[nb]
    return size

def hld(adj, parent, depth, order, size, root, n):
    # For each node, find heavy child (largest subtree)
    heavy = [-1] * n
    for node in order:
        best = -1
        best_size = 0
        for nb in adj[node]:
            if nb != parent[node]:
                if size[nb] > best_size:
                    best_size = size[nb]
                    best = nb
        heavy[node] = best

    # Assign chain heads
    chain_head = [0] * n
    chain_head[root] = root
    for node in order:
        for nb in adj[node]:
            if nb != parent[node]:
                if nb == heavy[node]:
                    chain_head[nb] = chain_head[node]
                else:
                    chain_head[nb] = nb
    return chain_head

def lca_query(u, v, parent, depth, chain_head):
    # Walk up chains until u and v are on the same chain
    while chain_head[u] != chain_head[v]:
        # CORRECT: move the node whose chain head is deeper
        if depth[chain_head[u]] < depth[chain_head[v]]:
            v = parent[chain_head[v]]
        else:
            u = parent[chain_head[u]]
    # Now on same chain, LCA is the shallower node
    if depth[u] < depth[v]:
        return u
    return v

# Build from adjacency list
edges = list(EDGES)
n = NUM_NODES
root = 0
adj = [[] for _ in range(n)]
for u, v in edges:
    adj[u].append(v)
    adj[v].append(u)

parent, depth, order = build_tree(adj, root, n)
size = compute_subtree_sizes(adj, parent, order, n)
chain_head = hld(adj, parent, depth, order, size, root, n)

queries = list(QUERIES)
result = []
for u, v in queries:
    result.append(lca_query(u, v, parent, depth, chain_head))
"""

BUGGY = r"""
# Heavy Path (Heavy-Light) Decomposition for LCA queries
# Decomposes tree into chains; LCA query walks chains upward

def build_tree(adj, root, n):
    # BFS to set parent and depth
    parent = [-1] * n
    depth = [0] * n
    order = []
    visited = [False] * n
    queue = [root]
    visited[root] = True
    while queue:
        node = queue.pop(0)
        order.append(node)
        for nb in adj[node]:
            if not visited[nb]:
                visited[nb] = True
                parent[nb] = node
                depth[nb] = depth[node] + 1
                queue.append(nb)
    return parent, depth, order

def compute_subtree_sizes(adj, parent, order, n):
    size = [1] * n
    for node in reversed(order):
        for nb in adj[node]:
            if nb != parent[node]:
                size[node] += size[nb]
    return size

def hld(adj, parent, depth, order, size, root, n):
    heavy = [-1] * n
    for node in order:
        best = -1
        best_size = 0
        for nb in adj[node]:
            if nb != parent[node]:
                if size[nb] > best_size:
                    best_size = size[nb]
                    best = nb
        heavy[node] = best

    chain_head = [0] * n
    chain_head[root] = root
    for node in order:
        for nb in adj[node]:
            if nb != parent[node]:
                if nb == heavy[node]:
                    chain_head[nb] = chain_head[node]
                else:
                    chain_head[nb] = nb
    return chain_head

def lca_query(u, v, parent, depth, chain_head):
    # Walk up chains until u and v are on the same chain
    iterations = 0
    while chain_head[u] != chain_head[v]:
        iterations += 1
        if iterations > 200:
            break
        # BUG: comparison is inverted (> instead of <)
        # This moves the SHALLOWER chain head up instead of the deeper one
        if depth[chain_head[u]] > depth[chain_head[v]]:
            v = parent[chain_head[v]]
        else:
            u = parent[chain_head[u]]
    if depth[u] < depth[v]:
        return u
    return v

# Build from adjacency list
edges = list(EDGES)
n = NUM_NODES
root = 0
adj = [[] for _ in range(n)]
for u, v in edges:
    adj[u].append(v)
    adj[v].append(u)

parent, depth, order = build_tree(adj, root, n)
size = compute_subtree_sizes(adj, parent, order, n)
chain_head = hld(adj, parent, depth, order, size, root, n)

queries = list(QUERIES)
result = []
for u, v in queries:
    result.append(lca_query(u, v, parent, depth, chain_head))
"""


def SPEC(edges, num_nodes, queries, result):
    # Verify LCA via naive method: walk both nodes up to root, find deepest common
    if num_nodes <= 0:
        return result == []
    n = num_nodes
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    # BFS to get parent/depth
    parent = [-1] * n
    depth = [0] * n
    visited = [False] * n
    queue = [0]
    visited[0] = True
    while queue:
        node = queue.pop(0)
        for nb in adj[node]:
            if not visited[nb]:
                visited[nb] = True
                parent[nb] = node
                depth[nb] = depth[node] + 1
                queue.append(nb)

    def naive_lca(u, v):
        # Get ancestors of u
        ancestors_u = set()
        x = u
        while x != -1:
            ancestors_u.add(x)
            x = parent[x]
        # Walk v up until we find common ancestor
        x = v
        while x not in ancestors_u:
            x = parent[x]
        return x

    if len(result) != len(queries):
        return False
    for i, (u, v) in enumerate(queries):
        expected = naive_lca(u, v)
        if result[i] != expected:
            return False
    return True


BUG_DESC = (
    "In lca_query, when comparing chain head depths to decide which node to "
    "move up, uses > instead of <. This moves the node with the shallower "
    "chain head upward, which can overshoot the LCA or loop incorrectly."
)


def _gen_edges():
    import random
    n = random.randint(6, 15)
    edges = []
    for i in range(1, n):
        p = random.randint(0, i - 1)
        edges.append((p, i))
    return edges


def _gen_n():
    import random
    return random.randint(6, 15)


def _gen_queries():
    import random
    n = random.randint(6, 15)
    queries = []
    for _ in range(random.randint(3, 6)):
        u = random.randint(0, n - 1)
        v = random.randint(0, n - 1)
        queries.append((u, v))
    return queries


INPUT_OVERRIDES = {"EDGES": _gen_edges, "NUM_NODES": _gen_n, "QUERIES": _gen_queries}
