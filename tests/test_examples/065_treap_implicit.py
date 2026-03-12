"""Implicit treap for array operations (split/merge).

Bug: in split, doesn't update the size of the resulting subtrees after
splitting, causing subsequent rank-based operations to use stale sizes
and produce wrong results.
"""

CORRECT = r"""
import random as _rng

class TreapNode:
    def __init__(self, val, priority=None):
        self.val = val
        self.priority = priority if priority is not None else _rng.random()
        self.left = None
        self.right = None
        self.size = 1

def get_size(node):
    return node.size if node else 0

def update_size(node):
    if node:
        node.size = 1 + get_size(node.left) + get_size(node.right)

def split(node, k):
    # Split into left (first k elements) and right (rest)
    if node is None:
        return None, None
    left_size = get_size(node.left)
    if left_size >= k:
        left, node.left = split(node.left, k)
        # CORRECT: update size after modifying children
        update_size(node)
        return left, node
    else:
        node.right, right = split(node.right, k - left_size - 1)
        # CORRECT: update size after modifying children
        update_size(node)
        return node, right

def merge(left, right):
    if left is None:
        return right
    if right is None:
        return left
    if left.priority > right.priority:
        left.right = merge(left.right, right)
        update_size(left)
        return left
    else:
        right.left = merge(left, right.left)
        update_size(right)
        return right

def insert(root, pos, val):
    new_node = TreapNode(val)
    left, right = split(root, pos)
    return merge(merge(left, new_node), right)

def delete(root, pos):
    left, temp = split(root, pos)
    _, right = split(temp, 1)
    return merge(left, right)

def query_range(root, l, r):
    # Get sum of elements in [l, r) (0-indexed)
    left, temp = split(root, l)
    mid, right = split(temp, r - l)
    # Collect values in mid
    values = []
    def inorder(node):
        if node is None:
            return
        inorder(node.left)
        values.append(node.val)
        inorder(node.right)
    inorder(mid)
    total = sum(values)
    # Merge back
    root = merge(merge(left, mid), right)
    return root, total

def to_list(node):
    if node is None:
        return []
    return to_list(node.left) + [node.val] + to_list(node.right)

data = DATA
_rng.seed(42)

root = None
for val in data["initial"]:
    root = insert(root, get_size(root), val)

results = []
for op in data["ops"]:
    if op[0] == "insert":
        pos, val = op[1], op[2]
        root = insert(root, pos, val)
        results.append("ok")
    elif op[0] == "delete":
        pos = op[1]
        root = delete(root, pos)
        results.append("ok")
    elif op[0] == "query":
        l, r = op[1], op[2]
        root, total = query_range(root, l, r)
        results.append(total)
    elif op[0] == "to_list":
        results.append(to_list(root))

result = results
"""

BUGGY = r"""
import random as _rng

class TreapNode:
    def __init__(self, val, priority=None):
        self.val = val
        self.priority = priority if priority is not None else _rng.random()
        self.left = None
        self.right = None
        self.size = 1

def get_size(node):
    return node.size if node else 0

def update_size(node):
    if node:
        node.size = 1 + get_size(node.left) + get_size(node.right)

def split(node, k):
    if node is None:
        return None, None
    left_size = get_size(node.left)
    if left_size >= k:
        left, node.left = split(node.left, k)
        # BUG: doesn't call update_size(node) here
        return left, node
    else:
        node.right, right = split(node.right, k - left_size - 1)
        # BUG: doesn't call update_size(node) here
        return node, right

def merge(left, right):
    if left is None:
        return right
    if right is None:
        return left
    if left.priority > right.priority:
        left.right = merge(left.right, right)
        update_size(left)
        return left
    else:
        right.left = merge(left, right.left)
        update_size(right)
        return right

def insert(root, pos, val):
    new_node = TreapNode(val)
    left, right = split(root, pos)
    return merge(merge(left, new_node), right)

def delete(root, pos):
    left, temp = split(root, pos)
    _, right = split(temp, 1)
    return merge(left, right)

def query_range(root, l, r):
    left, temp = split(root, l)
    mid, right = split(temp, r - l)
    values = []
    def inorder(node):
        if node is None:
            return
        inorder(node.left)
        values.append(node.val)
        inorder(node.right)
    inorder(mid)
    total = sum(values)
    root = merge(merge(left, mid), right)
    return root, total

def to_list(node):
    if node is None:
        return []
    return to_list(node.left) + [node.val] + to_list(node.right)

data = DATA
_rng.seed(42)

root = None
for val in data["initial"]:
    root = insert(root, get_size(root), val)

results = []
for op in data["ops"]:
    if op[0] == "insert":
        pos, val = op[1], op[2]
        root = insert(root, pos, val)
        results.append("ok")
    elif op[0] == "delete":
        pos = op[1]
        root = delete(root, pos)
        results.append("ok")
    elif op[0] == "query":
        l, r = op[1], op[2]
        root, total = query_range(root, l, r)
        results.append(total)
    elif op[0] == "to_list":
        results.append(to_list(root))

result = results
"""


def SPEC(data, result):
    # Simulate with a plain list
    arr = list(data["initial"])
    ops = data["ops"]

    if not isinstance(result, list):
        return False
    if len(result) != len(ops):
        return False

    for i, op in enumerate(ops):
        if op[0] == "insert":
            pos, val = op[1], op[2]
            arr.insert(pos, val)
            if result[i] != "ok":
                return False
        elif op[0] == "delete":
            pos = op[1]
            if pos < 0 or pos >= len(arr):
                return False
            arr.pop(pos)
            if result[i] != "ok":
                return False
        elif op[0] == "query":
            l, r = op[1], op[2]
            expected = sum(arr[l:r])
            if result[i] != expected:
                return False
        elif op[0] == "to_list":
            if result[i] != arr:
                return False
    return True


BUG_DESC = (
    "In split, after reassigning node.left or node.right, doesn't call "
    "update_size(node). The stale size values cause subsequent split/merge "
    "operations to compute wrong ranks, leading to elements appearing at "
    "wrong positions or queries covering wrong ranges."
)


def _gen():
    import random
    # The bug: split doesn't call update_size after modifying children.
    # After a split, node.size is stale. Subsequent splits use get_size(node.left)
    # to decide whether to go left or right, so stale sizes cause splits at
    # wrong positions, leading to elements at wrong indices.
    #
    # To trigger: we need multiple split operations in sequence. Each insert,
    # delete, and query calls split. After the first split corrupts sizes,
    # the second split goes to the wrong subtree.
    #
    # Strategy: insert several elements, then do queries and to_list to catch
    # wrong positions. Use distinct values so we can detect misorderings.
    #
    # Key: do multiple inserts (each calls split+merge), then verify with to_list.
    # The more split/merge operations, the more sizes diverge.
    initial = [10, 20, 30, 40, 50]
    ops = [
        # Insert at various positions - each split corrupts sizes
        ["insert", 2, 25],   # [10,20,25,30,40,50]
        ["insert", 0, 5],    # [5,10,20,25,30,40,50]
        ["insert", 7, 60],   # [5,10,20,25,30,40,50,60]
        # Now do a to_list to check the array is correct
        ["to_list"],
        # Query ranges - these split and if sizes are wrong, get wrong range
        ["query", 1, 4],     # sum of positions 1..3 = 10+20+25 = 55
        ["query", 0, 3],     # sum of positions 0..2 = 5+10+20 = 35
        # Delete and check again
        ["delete", 3],       # remove position 3 (25) -> [5,10,20,30,40,50,60]
        ["to_list"],
    ]
    return {"initial": initial, "ops": ops}


INPUT_OVERRIDES = {"DATA": _gen}
