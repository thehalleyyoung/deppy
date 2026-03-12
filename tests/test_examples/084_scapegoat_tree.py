"""Scapegoat tree (weight-balanced BST with rebuild). Bug: after rebuilding, doesn't update rebuilt root's size field."""

CORRECT = r"""
# Scapegoat Tree: a weight-balanced BST that rebuilds subtrees when unbalanced
# Alpha parameter controls balance (typically 0.5 < alpha < 1)

ALPHA = 0.7

# Node storage: parallel arrays
keys = [0] * 200
left = [0] * 200
right = [0] * 200
size = [0] * 200
node_count = 0
root = 0  # 0 means null/empty

def new_node(key):
    global node_count
    node_count += 1
    idx = node_count
    keys[idx] = key
    left[idx] = 0
    right[idx] = 0
    size[idx] = 1
    return idx

def get_size(node):
    if node == 0:
        return 0
    return size[node]

def update_size(node):
    if node != 0:
        size[node] = 1 + get_size(left[node]) + get_size(right[node])

def flatten(node, arr):
    # In-order traversal to collect nodes
    if node == 0:
        return
    flatten(left[node], arr)
    arr.append(node)
    flatten(right[node], arr)

def build_balanced(nodes_list, lo, hi):
    if lo > hi:
        return 0
    mid = (lo + hi) // 2
    node = nodes_list[mid]
    left[node] = build_balanced(nodes_list, lo, mid - 1)
    right[node] = build_balanced(nodes_list, mid + 1, hi)
    update_size(node)
    return node

def rebuild(node):
    arr = []
    flatten(node, arr)
    return build_balanced(arr, 0, len(arr) - 1)

def is_unbalanced(node):
    if node == 0:
        return False
    s = get_size(node)
    return (get_size(left[node]) > ALPHA * s or
            get_size(right[node]) > ALPHA * s)

def insert_helper(node, key):
    global root
    if node == 0:
        return new_node(key)
    if key < keys[node]:
        left[node] = insert_helper(left[node], key)
    elif key > keys[node]:
        right[node] = insert_helper(right[node], key)
    else:
        return node  # duplicate
    update_size(node)
    # Check balance and rebuild if necessary
    if is_unbalanced(node):
        node = rebuild(node)
    return node

def insert(key):
    global root
    root = insert_helper(root, key)

def search(node, key):
    if node == 0:
        return False
    if key == keys[node]:
        return True
    elif key < keys[node]:
        return search(left[node], key)
    else:
        return search(right[node], key)

def inorder(node):
    if node == 0:
        return []
    return inorder(left[node]) + [keys[node]] + inorder(right[node])

# Process insertions
for val in VALUES:
    insert(val)

# Check membership
found = []
for q in SEARCH:
    found.append(search(root, q))

# Get sorted output and tree size
sorted_vals = inorder(root)
root_size = get_size(root)

result = {
    "found": found,
    "sorted": sorted_vals,
    "root_size": root_size,
}
"""

BUGGY = r"""
# Scapegoat Tree: a weight-balanced BST that rebuilds subtrees when unbalanced

ALPHA = 0.7

keys = [0] * 200
left = [0] * 200
right = [0] * 200
size = [0] * 200
node_count = 0
root = 0

def new_node(key):
    global node_count
    node_count += 1
    idx = node_count
    keys[idx] = key
    left[idx] = 0
    right[idx] = 0
    size[idx] = 1
    return idx

def get_size(node):
    if node == 0:
        return 0
    return size[node]

def update_size(node):
    if node != 0:
        size[node] = 1 + get_size(left[node]) + get_size(right[node])

def flatten(node, arr):
    if node == 0:
        return
    flatten(left[node], arr)
    arr.append(node)
    flatten(right[node], arr)

def build_balanced(nodes_list, lo, hi):
    if lo > hi:
        return 0
    mid = (lo + hi) // 2
    node = nodes_list[mid]
    left[node] = build_balanced(nodes_list, lo, mid - 1)
    right[node] = build_balanced(nodes_list, mid + 1, hi)
    # BUG: does NOT call update_size(node) here
    # The size field remains stale from before the rebuild
    return node

def rebuild(node):
    arr = []
    flatten(node, arr)
    return build_balanced(arr, 0, len(arr) - 1)

def is_unbalanced(node):
    if node == 0:
        return False
    s = get_size(node)
    return (get_size(left[node]) > ALPHA * s or
            get_size(right[node]) > ALPHA * s)

def insert_helper(node, key):
    global root
    if node == 0:
        return new_node(key)
    if key < keys[node]:
        left[node] = insert_helper(left[node], key)
    elif key > keys[node]:
        right[node] = insert_helper(right[node], key)
    else:
        return node
    update_size(node)
    if is_unbalanced(node):
        node = rebuild(node)
    return node

def insert(key):
    global root
    root = insert_helper(root, key)

def search(node, key):
    if node == 0:
        return False
    if key == keys[node]:
        return True
    elif key < keys[node]:
        return search(left[node], key)
    else:
        return search(right[node], key)

def inorder(node):
    if node == 0:
        return []
    return inorder(left[node]) + [keys[node]] + inorder(right[node])

# Process insertions
for val in VALUES:
    insert(val)

# Check membership
found = []
for q in SEARCH:
    found.append(search(root, q))

sorted_vals = inorder(root)
root_size = get_size(root)

result = {
    "found": found,
    "sorted": sorted_vals,
    "root_size": root_size,
}
"""


def SPEC(values, search, result):
    unique_vals = sorted(set(values))

    # Check sorted output matches
    if result["sorted"] != unique_vals:
        return False

    # Check root_size matches number of unique values
    if result["root_size"] != len(unique_vals):
        return False

    # Check search results
    val_set = set(values)
    if len(result["found"]) != len(search):
        return False
    for i, q in enumerate(search):
        expected = q in val_set
        if result["found"][i] != expected:
            return False

    return True


BUG_DESC = "After rebuilding a subtree into a balanced tree, build_balanced does not call update_size on nodes, leaving stale size fields that cause incorrect balance checks and wrong root_size reports."


def _gen_values():
    # Insert in order that triggers rebuilds, then more inserts that rely on correct sizes
    return [5, 3, 7, 1, 4, 6, 8, 2, 9, 10, 11, 12, 13, 14, 15]


def _gen_search():
    return [1, 5, 10, 15, 16, 0, 7, 8]


INPUT_OVERRIDES = {
    "VALUES": _gen_values,
    "SEARCH": _gen_search,
}
