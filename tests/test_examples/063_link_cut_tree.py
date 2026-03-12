"""Link-cut tree (splay tree of paths) for dynamic connectivity.

Bug: in the access operation, doesn't cut the preferred child before
splaying, leaving stale preferred paths. This causes find_root to
return wrong roots after link/cut operations.
"""

CORRECT = r"""
class LCTNode:
    def __init__(self, idx):
        self.idx = idx
        self.left = None
        self.right = None
        self.parent = None
        self.rev = False

def is_root(x):
    # x is root of its splay tree if parent is None or parent's children don't include x
    if x.parent is None:
        return True
    return x.parent.left is not x and x.parent.right is not x

def push_down(x):
    if x and x.rev:
        x.left, x.right = x.right, x.left
        if x.left:
            x.left.rev = not x.left.rev
        if x.right:
            x.right.rev = not x.right.rev
        x.rev = False

def rotate(x):
    y = x.parent
    z = y.parent
    if z and not is_root(y):
        if z.left is y:
            z.left = x
        else:
            z.right = x
    x.parent = z
    if y.left is x:
        y.left = x.right
        if x.right:
            x.right.parent = y
        x.right = y
    else:
        y.right = x.left
        if x.left:
            x.left.parent = y
        x.left = y
    y.parent = x

def splay(x):
    while not is_root(x):
        y = x.parent
        if not is_root(y):
            z = y.parent
            push_down(z)
            push_down(y)
            push_down(x)
            if (z.left is y) == (y.left is x):
                rotate(y)
            else:
                rotate(x)
        else:
            push_down(y)
            push_down(x)
        rotate(x)
    push_down(x)

def access(x):
    last = None
    u = x
    while u is not None:
        splay(u)
        # CORRECT: cut the old preferred child
        u.right = last
        last = u
        u = u.parent
    splay(x)

def make_root(x):
    access(x)
    x.rev = not x.rev
    push_down(x)

def find_root(x):
    access(x)
    u = x
    push_down(u)
    while u.left is not None:
        u = u.left
        push_down(u)
    splay(u)
    return u

def link(x, y):
    # Link x to y: make x root of its tree, then attach
    make_root(x)
    x.parent = y

def cut(x, y):
    make_root(x)
    access(y)
    y.left = None
    x.parent = None

def connected(x, y):
    return find_root(x) is find_root(y)

data = DATA
n = data["n"]
ops = data["ops"]

nodes = [LCTNode(i) for i in range(n)]
results = []

for op in ops:
    if op[0] == "link":
        u, v = op[1], op[2]
        if not connected(nodes[u], nodes[v]):
            link(nodes[u], nodes[v])
            results.append("linked")
        else:
            results.append("already_connected")
    elif op[0] == "cut":
        u, v = op[1], op[2]
        if connected(nodes[u], nodes[v]):
            cut(nodes[u], nodes[v])
            results.append("cut")
        else:
            results.append("not_connected")
    elif op[0] == "connected":
        u, v = op[1], op[2]
        results.append(connected(nodes[u], nodes[v]))

result = results
"""

BUGGY = r"""
class LCTNode:
    def __init__(self, idx):
        self.idx = idx
        self.left = None
        self.right = None
        self.parent = None
        self.rev = False

def is_root(x):
    if x.parent is None:
        return True
    return x.parent.left is not x and x.parent.right is not x

def push_down(x):
    if x and x.rev:
        x.left, x.right = x.right, x.left
        if x.left:
            x.left.rev = not x.left.rev
        if x.right:
            x.right.rev = not x.right.rev
        x.rev = False

def rotate(x):
    y = x.parent
    z = y.parent
    if z and not is_root(y):
        if z.left is y:
            z.left = x
        else:
            z.right = x
    x.parent = z
    if y.left is x:
        y.left = x.right
        if x.right:
            x.right.parent = y
        x.right = y
    else:
        y.right = x.left
        if x.left:
            x.left.parent = y
        x.left = y
    y.parent = x

def splay(x):
    while not is_root(x):
        y = x.parent
        if not is_root(y):
            z = y.parent
            push_down(z)
            push_down(y)
            push_down(x)
            if (z.left is y) == (y.left is x):
                rotate(y)
            else:
                rotate(x)
        else:
            push_down(y)
            push_down(x)
        rotate(x)
    push_down(x)

def access(x):
    last = None
    u = x
    while u is not None:
        splay(u)
        # BUG: doesn't set u.right = last (doesn't cut preferred child)
        # This leaves stale preferred paths in the tree
        last = u
        u = u.parent
    splay(x)

def make_root(x):
    access(x)
    x.rev = not x.rev
    push_down(x)

def find_root(x):
    access(x)
    u = x
    push_down(u)
    while u.left is not None:
        u = u.left
        push_down(u)
    splay(u)
    return u

def link(x, y):
    make_root(x)
    x.parent = y

def cut(x, y):
    make_root(x)
    access(y)
    y.left = None
    x.parent = None

def connected(x, y):
    return find_root(x) is find_root(y)

data = DATA
n = data["n"]
ops = data["ops"]

nodes = [LCTNode(i) for i in range(n)]
results = []

for op in ops:
    if op[0] == "link":
        u, v = op[1], op[2]
        if not connected(nodes[u], nodes[v]):
            link(nodes[u], nodes[v])
            results.append("linked")
        else:
            results.append("already_connected")
    elif op[0] == "cut":
        u, v = op[1], op[2]
        if connected(nodes[u], nodes[v]):
            cut(nodes[u], nodes[v])
            results.append("cut")
        else:
            results.append("not_connected")
    elif op[0] == "connected":
        u, v = op[1], op[2]
        results.append(connected(nodes[u], nodes[v]))

result = results
"""


def SPEC(data, result):
    # Simulate with union-find to check connectivity answers
    n = data["n"]
    ops = data["ops"]

    parent = list(range(n))
    rank = [0] * n

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        a, b = find(a), find(b)
        if a == b:
            return False
        if rank[a] < rank[b]:
            a, b = b, a
        parent[b] = a
        if rank[a] == rank[b]:
            rank[a] += 1
        return True

    if not isinstance(result, list):
        return False
    if len(result) != len(ops):
        return False

    # We track connectivity with a simple set-of-edges for cut support
    edges = set()
    adj = [set() for _ in range(n)]

    from collections import deque
    def bfs_connected(src, dst):
        if src == dst:
            return True
        visited = set([src])
        q = deque([src])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if v == dst:
                    return True
                if v not in visited:
                    visited.add(v)
                    q.append(v)
        return False

    for i, op in enumerate(ops):
        if op[0] == "link":
            u, v = op[1], op[2]
            conn = bfs_connected(u, v)
            if not conn:
                adj[u].add(v)
                adj[v].add(u)
                if result[i] != "linked":
                    return False
            else:
                if result[i] != "already_connected":
                    return False
        elif op[0] == "cut":
            u, v = op[1], op[2]
            conn = bfs_connected(u, v)
            if conn:
                adj[u].discard(v)
                adj[v].discard(u)
                if result[i] != "cut":
                    return False
            else:
                if result[i] != "not_connected":
                    return False
        elif op[0] == "connected":
            u, v = op[1], op[2]
            expected = bfs_connected(u, v)
            if result[i] != expected:
                return False
    return True


BUG_DESC = (
    "In access(), the line 'u.right = last' is omitted, so the preferred "
    "child is never updated. This leaves stale preferred paths, causing "
    "find_root to traverse wrong paths and return incorrect roots, which "
    "breaks connectivity queries after link/cut operations."
)


def _gen():
    import random
    # The bug: access(x) doesn't set u.right = last, so preferred child is
    # never updated. This means the splay tree structure doesn't properly
    # reflect the path from x to the root of its represented tree.
    # find_root then traverses wrong paths and returns incorrect roots.
    #
    # To trigger: we need link, cut, then connectivity queries where the
    # stale preferred paths cause find_root to return the wrong node.
    #
    # Key insight: after cutting an edge, the two trees should be disconnected.
    # But with the buggy access, the splay tree still contains old preferred
    # path info, so find_root might still find the old root, making
    # connected() return True when it should return False (or vice versa).
    #
    # Use a small deterministic scenario:
    # 1. Link 0-1, 1-2, 2-3 (chain)
    # 2. Query connected(0,3) -> True
    # 3. Cut 1-2 (breaks chain into {0,1} and {2,3})
    # 4. Query connected(0,3) -> should be False
    # 5. Query connected(0,1) -> should be True
    # 6. Query connected(2,3) -> should be True
    #
    # Multiple link/cut sequences that stress the access bug:
    sequences = [
        {"n": 5, "ops": [
            ["link", 0, 1], ["link", 1, 2], ["link", 2, 3], ["link", 3, 4],
            ["connected", 0, 4],   # True
            ["cut", 1, 2],
            ["connected", 0, 3],   # False
            ["connected", 0, 1],   # True
            ["connected", 2, 4],   # True
            ["link", 1, 3],        # reconnect differently
            ["connected", 0, 4],   # True
            ["cut", 3, 4],
            ["connected", 0, 4],   # False
            ["connected", 0, 3],   # True
        ]},
        {"n": 6, "ops": [
            ["link", 0, 1], ["link", 1, 2], ["link", 2, 3],
            ["link", 4, 5],
            ["connected", 0, 5],   # False
            ["connected", 0, 3],   # True
            ["link", 3, 4],        # connect the two components
            ["connected", 0, 5],   # True
            ["cut", 2, 3],
            ["connected", 0, 5],   # False
            ["connected", 0, 2],   # True
            ["connected", 3, 5],   # True
        ]},
        {"n": 4, "ops": [
            ["link", 0, 1], ["link", 1, 2], ["link", 2, 3],
            ["connected", 0, 3],   # True
            ["cut", 0, 1],
            ["connected", 0, 1],   # False
            ["connected", 1, 3],   # True
            ["link", 0, 2],
            ["connected", 0, 3],   # True
            ["cut", 2, 3],
            ["connected", 0, 3],   # False
        ]},
    ]
    return random.choice(sequences)


INPUT_OVERRIDES = {"DATA": _gen}
