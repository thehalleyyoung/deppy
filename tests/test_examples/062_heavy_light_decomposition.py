"""Heavy-light decomposition for path queries on trees.

Bug: when querying a path, processes the chain of the deeper node but
swaps which node moves up, causing it to skip chain segments and return
incorrect path query results.
"""

CORRECT = r"""
import sys
sys.setrecursionlimit(10000)

def hld_path_query(data):
    n = data["n"]
    edges = data["edges"]
    weights = data["weights"]
    queries = data["queries"]

    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)

    parent = [-1] * n
    depth = [0] * n
    subtree_size = [1] * n
    heavy = [-1] * n

    # BFS to compute parent, depth, subtree_size
    from collections import deque
    order = []
    visited = [False] * n
    queue = deque([0])
    visited[0] = True
    while queue:
        u = queue.popleft()
        order.append(u)
        for v in adj[u]:
            if not visited[v]:
                visited[v] = True
                parent[v] = u
                depth[v] = depth[u] + 1
                queue.append(v)

    # Compute subtree sizes and heavy children (reverse BFS order)
    for u in reversed(order):
        max_size = 0
        for v in adj[u]:
            if v != parent[u]:
                subtree_size[u] += subtree_size[v]
                if subtree_size[v] > max_size:
                    max_size = subtree_size[v]
                    heavy[u] = v

    # Decompose into chains
    head = [0] * n
    pos = [0] * n
    cur_pos = [0]

    stack = [(0, 0)]
    while stack:
        u, h = stack.pop()
        head[u] = h
        pos[u] = cur_pos[0]
        cur_pos[0] += 1
        # Process light children first (so heavy child is processed last / next)
        children = [v for v in adj[u] if v != parent[u]]
        for v in children:
            if v != heavy[u]:
                stack.append((v, v))
        if heavy[u] != -1:
            stack.append((heavy[u], h))

    # Build a simple array for range-max queries (flat array indexed by pos)
    flat = [0] * n
    for i in range(n):
        flat[pos[i]] = weights[i]

    # Sparse table for range max
    import math
    LOG = max(1, int(math.log2(n)) + 1) if n > 0 else 1
    sparse = [[0] * n for _ in range(LOG + 1)]
    for i in range(n):
        sparse[0][i] = flat[i]
    for k in range(1, LOG + 1):
        for i in range(n - (1 << k) + 1):
            sparse[k][i] = max(sparse[k - 1][i], sparse[k - 1][i + (1 << (k - 1))])

    def range_max(l, r):
        if l > r:
            return 0
        k = int(math.log2(r - l + 1))
        return max(sparse[k][l], sparse[k][r - (1 << k) + 1])

    def path_max(u, v):
        res = 0
        while head[u] != head[v]:
            # CORRECT: move the deeper node up
            if depth[head[u]] < depth[head[v]]:
                u, v = v, u
            res = max(res, range_max(pos[head[u]], pos[u]))
            u = parent[head[u]]
        if depth[u] > depth[v]:
            u, v = v, u
        res = max(res, range_max(pos[u], pos[v]))
        return res

    answers = []
    for qu, qv in queries:
        answers.append(path_max(qu, qv))
    return answers

data = DATA
result = hld_path_query(data)
"""

BUGGY = r"""
import sys
sys.setrecursionlimit(10000)

def hld_path_query(data):
    n = data["n"]
    edges = data["edges"]
    weights = data["weights"]
    queries = data["queries"]

    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)

    parent = [-1] * n
    depth = [0] * n
    subtree_size = [1] * n
    heavy = [-1] * n

    from collections import deque
    order = []
    visited = [False] * n
    queue = deque([0])
    visited[0] = True
    while queue:
        u = queue.popleft()
        order.append(u)
        for v in adj[u]:
            if not visited[v]:
                visited[v] = True
                parent[v] = u
                depth[v] = depth[u] + 1
                queue.append(v)

    for u in reversed(order):
        max_size = 0
        for v in adj[u]:
            if v != parent[u]:
                subtree_size[u] += subtree_size[v]
                if subtree_size[v] > max_size:
                    max_size = subtree_size[v]
                    heavy[u] = v

    head = [0] * n
    pos = [0] * n
    cur_pos = [0]

    stack = [(0, 0)]
    while stack:
        u, h = stack.pop()
        head[u] = h
        pos[u] = cur_pos[0]
        cur_pos[0] += 1
        children = [v for v in adj[u] if v != parent[u]]
        for v in children:
            if v != heavy[u]:
                stack.append((v, v))
        if heavy[u] != -1:
            stack.append((heavy[u], h))

    flat = [0] * n
    for i in range(n):
        flat[pos[i]] = weights[i]

    import math
    LOG = max(1, int(math.log2(n)) + 1) if n > 0 else 1
    sparse = [[0] * n for _ in range(LOG + 1)]
    for i in range(n):
        sparse[0][i] = flat[i]
    for k in range(1, LOG + 1):
        for i in range(n - (1 << k) + 1):
            sparse[k][i] = max(sparse[k - 1][i], sparse[k - 1][i + (1 << (k - 1))])

    def range_max(l, r):
        if l > r:
            return 0
        k = int(math.log2(r - l + 1))
        return max(sparse[k][l], sparse[k][r - (1 << k) + 1])

    def path_max(u, v):
        res = 0
        while head[u] != head[v]:
            if depth[head[u]] < depth[head[v]]:
                u, v = v, u
            res = max(res, range_max(pos[head[u]], pos[u]))
            # BUG: moves v up instead of u, skipping segments
            v = parent[head[u]]
        if depth[u] > depth[v]:
            u, v = v, u
        res = max(res, range_max(pos[u], pos[v]))
        return res

    answers = []
    for qu, qv in queries:
        answers.append(path_max(qu, qv))
    return answers

data = DATA
result = hld_path_query(data)
"""


def SPEC(data, result):
    # Brute-force path max via BFS on the tree
    from collections import deque
    n = data["n"]
    edges = data["edges"]
    weights = data["weights"]
    queries = data["queries"]

    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)

    if not isinstance(result, list):
        return False
    if len(result) != len(queries):
        return False

    def bfs_path(src, dst):
        prev = [-1] * n
        visited = [False] * n
        visited[src] = True
        q = deque([src])
        while q:
            u = q.popleft()
            if u == dst:
                break
            for v in adj[u]:
                if not visited[v]:
                    visited[v] = True
                    prev[v] = u
                    q.append(v)
        path = []
        cur = dst
        while cur != -1:
            path.append(cur)
            cur = prev[cur]
        return path

    for i, (qu, qv) in enumerate(queries):
        path = bfs_path(qu, qv)
        expected = max(weights[node] for node in path)
        if result[i] != expected:
            return False
    return True


BUG_DESC = (
    "In path_max, after processing the chain of the deeper node, moves v "
    "up (v = parent[head[u]]) instead of u (u = parent[head[u]]), causing "
    "the query to skip chain segments and potentially loop or return wrong results."
)


def _gen():
    import random
    n = random.randint(8, 16)
    # Generate a random tree
    edges = []
    for i in range(1, n):
        p = random.randint(0, i - 1)
        edges.append([p, i])
    weights = [random.randint(1, 100) for _ in range(n)]
    queries = []
    for _ in range(5):
        u = random.randint(0, n - 1)
        v = random.randint(0, n - 1)
        while v == u:
            v = random.randint(0, n - 1)
        queries.append([u, v])
    return {"n": n, "edges": edges, "weights": weights, "queries": queries}


INPUT_OVERRIDES = {"DATA": _gen}
