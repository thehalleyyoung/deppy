"""Persistent segment tree supporting historical range queries.

Bug: when updating, creates new node for left child but reuses the right
child reference from the wrong version (previous root instead of current
node's right child), corrupting historical queries.
"""

CORRECT = r"""
def solve(data):
    class Node:
        def __init__(self, val=0, left=None, right=None):
            self.val = val
            self.left = left
            self.right = right

    def build(arr, lo, hi):
        if lo == hi:
            return Node(arr[lo])
        mid = (lo + hi) // 2
        left_child = build(arr, lo, mid)
        right_child = build(arr, mid + 1, hi)
        return Node(left_child.val + right_child.val, left_child, right_child)

    def update(node, lo, hi, idx, val):
        if lo == hi:
            return Node(val)
        mid = (lo + hi) // 2
        if idx <= mid:
            new_left = update(node.left, lo, mid, idx, val)
            return Node(new_left.val + node.right.val, new_left, node.right)
        else:
            new_right = update(node.right, mid + 1, hi, idx, val)
            return Node(node.left.val + new_right.val, node.left, new_right)

    def query(node, lo, hi, ql, qr):
        if node is None or ql > hi or qr < lo:
            return 0
        if ql <= lo and hi <= qr:
            return node.val
        mid = (lo + hi) // 2
        return query(node.left, lo, mid, ql, qr) + query(node.right, mid + 1, hi, ql, qr)

    n = len(data["arr"])
    arr = data["arr"]
    updates = data["updates"]
    queries_list = data["queries"]

    roots = [build(arr, 0, n - 1)]
    for upd in updates:
        idx, val = upd
        new_root = update(roots[-1], 0, n - 1, idx, val)
        roots.append(new_root)

    answers = []
    for q in queries_list:
        ver, ql, qr = q
        ans = query(roots[ver], 0, n - 1, ql, qr)
        answers.append(ans)
    return answers

data = DATA
result = solve(data)
"""

BUGGY = r"""
def solve(data):
    class Node:
        def __init__(self, val=0, left=None, right=None):
            self.val = val
            self.left = left
            self.right = right

    def build(arr, lo, hi):
        if lo == hi:
            return Node(arr[lo])
        mid = (lo + hi) // 2
        left_child = build(arr, lo, mid)
        right_child = build(arr, mid + 1, hi)
        return Node(left_child.val + right_child.val, left_child, right_child)

    def update(node, lo, hi, idx, val, old_root):
        if lo == hi:
            return Node(val)
        mid = (lo + hi) // 2
        if idx <= mid:
            new_left = update(node.left, lo, mid, idx, val, old_root)
            # BUG: uses old_root.right instead of node.right
            return Node(new_left.val + old_root.right.val, new_left, old_root.right)
        else:
            new_right = update(node.right, mid + 1, hi, idx, val, old_root)
            # BUG: uses old_root.left instead of node.left
            return Node(old_root.left.val + new_right.val, old_root.left, new_right)

    def query(node, lo, hi, ql, qr):
        if node is None or ql > hi or qr < lo:
            return 0
        if ql <= lo and hi <= qr:
            return node.val
        mid = (lo + hi) // 2
        return query(node.left, lo, mid, ql, qr) + query(node.right, mid + 1, hi, ql, qr)

    n = len(data["arr"])
    arr = data["arr"]
    updates = data["updates"]
    queries_list = data["queries"]

    roots = [build(arr, 0, n - 1)]
    first_root = roots[0]
    for upd in updates:
        idx, val = upd
        new_root = update(roots[-1], 0, n - 1, idx, val, first_root)
        roots.append(new_root)

    answers = []
    for q in queries_list:
        ver, ql, qr = q
        ans = query(roots[ver], 0, n - 1, ql, qr)
        answers.append(ans)
    return answers

data = DATA
result = solve(data)
"""


def SPEC(data, result):
    # Recompute expected answers via brute force
    arr = list(data["arr"])
    updates = data["updates"]
    queries = data["queries"]

    # Build snapshots of the array at each version
    versions = [list(arr)]
    for upd in updates:
        idx, val = upd
        new_arr = list(versions[-1])
        new_arr[idx] = val
        versions.append(new_arr)

    if not isinstance(result, list):
        return False
    if len(result) != len(queries):
        return False

    for i, q in enumerate(queries):
        ver, ql, qr = q
        expected = sum(versions[ver][ql:qr + 1])
        if result[i] != expected:
            return False
    return True


BUG_DESC = (
    "When updating, passes old_root (version 0) as a parameter and uses "
    "old_root.right/left instead of the current node's children. After "
    "multiple updates, historical queries return wrong sums because nodes "
    "reference children from the wrong version."
)


def _gen():
    import random
    n = random.randint(6, 12)
    arr = [random.randint(1, 20) for _ in range(n)]
    # Generate 3 updates, each targeting different positions
    updates = []
    for _ in range(3):
        idx = random.randint(0, n - 1)
        val = random.randint(1, 20)
        updates.append([idx, val])
    # Generate queries across different versions and ranges
    num_versions = len(updates) + 1
    queries = []
    for _ in range(6):
        ver = random.randint(0, num_versions - 1)
        ql = random.randint(0, n - 1)
        qr = random.randint(ql, n - 1)
        queries.append([ver, ql, qr])
    return {"arr": arr, "updates": updates, "queries": queries}


INPUT_OVERRIDES = {"DATA": _gen}
