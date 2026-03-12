"""Fenwick tree supporting range updates and point queries.
Bug: in range update [l, r], only updates position l but forgets to
update position r+1 with the negative delta."""

CORRECT = r"""
# Fenwick (Binary Indexed) Tree for range updates and point queries
# Uses difference array technique: to add val to range [l, r],
# add val at l and subtract val at r+1

def fenwick_update(tree, n, i, delta):
    # Add delta at position i (1-indexed)
    while i <= n:
        tree[i] += delta
        i += i & (-i)

def fenwick_query(tree, i):
    # Prefix sum query up to position i (1-indexed) = point value
    s = 0
    while i > 0:
        s += tree[i]
        i -= i & (-i)
    return s

def range_update(tree, n, l, r, val):
    # Add val to all elements in [l, r] (1-indexed)
    # CORRECT: update both l and r+1
    fenwick_update(tree, n, l, val)
    if r + 1 <= n:
        fenwick_update(tree, n, r + 1, -val)

def point_query(tree, i):
    # Query value at position i
    return fenwick_query(tree, i)

# Process operations
ops = list(OPS)
n = N
tree = [0] * (n + 2)

# Initialize with base values
base = list(BASE_VALUES)
for i in range(len(base)):
    if i < n:
        range_update(tree, n, i + 1, i + 1, base[i])

# Apply range updates from ops
for op in ops:
    l, r, val = op
    if 1 <= l <= r <= n:
        range_update(tree, n, l, r, val)

# Collect all point query results
result = []
for i in range(1, n + 1):
    result.append(point_query(tree, i))
"""

BUGGY = r"""
# Fenwick (Binary Indexed) Tree for range updates and point queries
# Uses difference array technique: to add val to range [l, r],
# add val at l and subtract val at r+1

def fenwick_update(tree, n, i, delta):
    # Add delta at position i (1-indexed)
    while i <= n:
        tree[i] += delta
        i += i & (-i)

def fenwick_query(tree, i):
    # Prefix sum query up to position i (1-indexed) = point value
    s = 0
    while i > 0:
        s += tree[i]
        i -= i & (-i)
    return s

def range_update(tree, n, l, r, val):
    # Add val to all elements in [l, r] (1-indexed)
    # BUG: only updates position l, forgets to cancel at r+1
    fenwick_update(tree, n, l, val)
    # Missing: fenwick_update(tree, n, r + 1, -val)

def point_query(tree, i):
    # Query value at position i
    return fenwick_query(tree, i)

# Process operations
ops = list(OPS)
n = N
tree = [0] * (n + 2)

# Initialize with base values
base = list(BASE_VALUES)
for i in range(len(base)):
    if i < n:
        range_update(tree, n, i + 1, i + 1, base[i])

# Apply range updates from ops
for op in ops:
    l, r, val = op
    if 1 <= l <= r <= n:
        range_update(tree, n, l, r, val)

# Collect all point query results
result = []
for i in range(1, n + 1):
    result.append(point_query(tree, i))
"""


def SPEC(ops, n, base_values, result):
    # Simulate range updates naively
    if n <= 0:
        return result == []
    arr = [0] * n
    for i in range(min(len(base_values), n)):
        arr[i] = base_values[i]
    for op in ops:
        l, r, val = op
        if 1 <= l <= r <= n:
            for i in range(l - 1, r):
                arr[i] += val
    return result == arr


BUG_DESC = (
    "In range_update, only calls fenwick_update at position l with +val, "
    "but omits the corresponding fenwick_update at position r+1 with -val. "
    "This means the update leaks past position r, affecting all positions "
    "from l to n instead of just l to r."
)


def _gen_n():
    import random
    return random.randint(5, 15)


def _gen_base():
    import random
    return [random.randint(0, 10) for _ in range(15)]


def _gen_ops():
    import random
    n = random.randint(5, 15)
    ops = []
    for _ in range(random.randint(2, 6)):
        l = random.randint(1, max(1, n - 1))
        r = random.randint(l, n)
        val = random.randint(1, 10)
        ops.append((l, r, val))
    return ops


INPUT_OVERRIDES = {"N": _gen_n, "BASE_VALUES": _gen_base, "OPS": _gen_ops}
