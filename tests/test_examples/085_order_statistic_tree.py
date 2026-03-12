"""Order-statistic tree (augmented BST with size). Bug: select(k) subtracts left.size instead of left.size+1 when going right."""

CORRECT = r"""
# Order-Statistic Tree: BST augmented with subtree sizes
# Supports select(k) = kth smallest (0-indexed) and rank(x)

# Node storage via parallel arrays
MAX_NODES = 200
key = [0] * MAX_NODES
left = [0] * MAX_NODES
right = [0] * MAX_NODES
sz = [0] * MAX_NODES
nc = 0
root = 0  # 0 = null

def new_node(k):
    global nc
    nc += 1
    key[nc] = k
    left[nc] = 0
    right[nc] = 0
    sz[nc] = 1
    return nc

def get_sz(n):
    return sz[n] if n else 0

def update_sz(n):
    if n:
        sz[n] = 1 + get_sz(left[n]) + get_sz(right[n])

def insert_node(node, k):
    if node == 0:
        return new_node(k)
    if k < key[node]:
        left[node] = insert_node(left[node], k)
    elif k > key[node]:
        right[node] = insert_node(right[node], k)
    update_sz(node)
    return node

def select(node, k):
    # Find the k-th smallest element (0-indexed)
    if node == 0:
        return None
    left_size = get_sz(left[node])
    if k < left_size:
        return select(left[node], k)
    elif k == left_size:
        return key[node]
    else:
        # Go right: subtract left subtree size + 1 (for current node)
        return select(right[node], k - left_size - 1)

def rank(node, k):
    # Return the 0-indexed rank of key k
    if node == 0:
        return 0
    if k < key[node]:
        return rank(left[node], k)
    elif k > key[node]:
        return 1 + get_sz(left[node]) + rank(right[node], k)
    else:
        return get_sz(left[node])

# Insert all values
for v in VALUES:
    root = insert_node(root, v)

# Perform select queries (0-indexed)
select_results = []
for k in SELECT_QUERIES:
    select_results.append(select(root, k))

# Perform rank queries
rank_results = []
for v in RANK_QUERIES:
    rank_results.append(rank(root, v))

result = {
    "select": select_results,
    "rank": rank_results,
    "total_size": get_sz(root),
}
"""

BUGGY = r"""
# Order-Statistic Tree: BST augmented with subtree sizes
# Supports select(k) = kth smallest (0-indexed) and rank(x)

MAX_NODES = 200
key = [0] * MAX_NODES
left = [0] * MAX_NODES
right = [0] * MAX_NODES
sz = [0] * MAX_NODES
nc = 0
root = 0

def new_node(k):
    global nc
    nc += 1
    key[nc] = k
    left[nc] = 0
    right[nc] = 0
    sz[nc] = 1
    return nc

def get_sz(n):
    return sz[n] if n else 0

def update_sz(n):
    if n:
        sz[n] = 1 + get_sz(left[n]) + get_sz(right[n])

def insert_node(node, k):
    if node == 0:
        return new_node(k)
    if k < key[node]:
        left[node] = insert_node(left[node], k)
    elif k > key[node]:
        right[node] = insert_node(right[node], k)
    update_sz(node)
    return node

def select(node, k):
    # Find the k-th smallest element (0-indexed)
    if node == 0:
        return None
    left_size = get_sz(left[node])
    if k < left_size:
        return select(left[node], k)
    elif k == left_size:
        return key[node]
    else:
        # BUG: subtracts left_size but NOT +1 for current node
        # This means we overshoot by 1 position when going right
        return select(right[node], k - left_size)

def rank(node, k):
    if node == 0:
        return 0
    if k < key[node]:
        return rank(left[node], k)
    elif k > key[node]:
        return 1 + get_sz(left[node]) + rank(right[node], k)
    else:
        return get_sz(left[node])

# Insert all values
for v in VALUES:
    root = insert_node(root, v)

# Perform select queries (0-indexed)
select_results = []
for k in SELECT_QUERIES:
    select_results.append(select(root, k))

# Perform rank queries
rank_results = []
for v in RANK_QUERIES:
    rank_results.append(rank(root, v))

result = {
    "select": select_results,
    "rank": rank_results,
    "total_size": get_sz(root),
}
"""


def SPEC(values, select_queries, rank_queries, result):
    unique_sorted = sorted(set(values))
    n = len(unique_sorted)

    if result["total_size"] != n:
        return False

    # Check select results
    if len(result["select"]) != len(select_queries):
        return False
    for i, k in enumerate(select_queries):
        if k < 0 or k >= n:
            if result["select"][i] is not None:
                return False
        else:
            if result["select"][i] != unique_sorted[k]:
                return False

    # Check rank results
    if len(result["rank"]) != len(rank_queries):
        return False
    for i, v in enumerate(rank_queries):
        # rank = number of elements strictly less than v
        expected_rank = sum(1 for x in unique_sorted if x < v)
        if result["rank"][i] != expected_rank:
            return False

    return True


BUG_DESC = "In select(k), when going right, subtracts left_size but forgets to subtract 1 for the current node, causing all right-subtree selections to be off by one."


def _gen_values():
    return [20, 10, 30, 5, 15, 25, 35, 3, 7, 12]


def _gen_select():
    # 0-indexed: sorted unique = [3, 5, 7, 10, 12, 15, 20, 25, 30, 35]
    return [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]


def _gen_rank():
    return [3, 10, 20, 35, 1, 50]


INPUT_OVERRIDES = {
    "VALUES": _gen_values,
    "SELECT_QUERIES": _gen_select,
    "RANK_QUERIES": _gen_rank,
}
