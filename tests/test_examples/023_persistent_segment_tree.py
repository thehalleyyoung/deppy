"""Persistent (functional) segment tree with point update and range sum query."""

import random

CORRECT = """
def solve(initial_array, operations):
    # Node: [left_child_idx, right_child_idx, value]
    nodes = []
    roots = []
    n = len(initial_array)

    def new_node(val=0, left=None, right=None):
        idx = len(nodes)
        nodes.append([left, right, val])
        return idx

    def build(arr, lo, hi):
        if lo == hi:
            return new_node(val=arr[lo])
        mid = (lo + hi) // 2
        left = build(arr, lo, mid)
        right = build(arr, mid + 1, hi)
        return new_node(val=nodes[left][2] + nodes[right][2], left=left, right=right)

    def update(prev, lo, hi, idx, val):
        if lo == hi:
            return new_node(val=val)
        mid = (lo + hi) // 2
        left_child = nodes[prev][0]
        right_child = nodes[prev][1]
        if idx <= mid:
            new_left = update(left_child, lo, mid, idx, val)
            new_right = right_child
        else:
            new_left = left_child
            new_right = update(right_child, mid + 1, hi, idx, val)
        return new_node(
            val=nodes[new_left][2] + nodes[new_right][2],
            left=new_left,
            right=new_right,
        )

    def query(node, lo, hi, ql, qr):
        if ql <= lo and hi <= qr:
            return nodes[node][2]
        if qr < lo or hi < ql:
            return 0
        mid = (lo + hi) // 2
        return (
            query(nodes[node][0], lo, mid, ql, qr)
            + query(nodes[node][1], mid + 1, hi, ql, qr)
        )

    # Build initial tree as version 0
    root0 = build(initial_array, 0, n - 1)
    roots.append(root0)

    results = []
    for op in operations:
        if op[0] == "update":
            _, version, idx, val = op
            new_root = update(roots[version], 0, n - 1, idx, val)
            roots.append(new_root)
            results.append(("new_version", len(roots) - 1))
        elif op[0] == "query":
            _, version, l, r = op
            ans = query(roots[version], 0, n - 1, l, r)
            results.append(("answer", ans))

    return results
"""

BUGGY = """
def solve(initial_array, operations):
    nodes = []
    roots = []
    n = len(initial_array)

    def new_node(val=0, left=None, right=None):
        idx = len(nodes)
        nodes.append([left, right, val])
        return idx

    def build(arr, lo, hi):
        if lo == hi:
            return new_node(val=arr[lo])
        mid = (lo + hi) // 2
        left = build(arr, lo, mid)
        right = build(arr, mid + 1, hi)
        return new_node(val=nodes[left][2] + nodes[right][2], left=left, right=right)

    def update(prev, lo, hi, idx, val):
        if lo == hi:
            return new_node(val=val)
        mid = (lo + hi) // 2
        left_child = nodes[prev][0]
        right_child = nodes[prev][1]
        if idx <= mid:
            # BUG: uses left_child (old) instead of recursively updated child
            # Creates new node but points to OLD left child, not the updated one
            _updated = update(left_child, lo, mid, idx, val)
            new_left = left_child  # BUG: should be _updated
            new_right = right_child
        else:
            _updated = update(right_child, mid + 1, hi, idx, val)
            new_left = left_child
            new_right = right_child  # BUG: should be _updated
        return new_node(
            val=nodes[new_left][2] + nodes[new_right][2],
            left=new_left,
            right=new_right,
        )

    def query(node, lo, hi, ql, qr):
        if ql <= lo and hi <= qr:
            return nodes[node][2]
        if qr < lo or hi < ql:
            return 0
        mid = (lo + hi) // 2
        return (
            query(nodes[node][0], lo, mid, ql, qr)
            + query(nodes[node][1], mid + 1, hi, ql, qr)
        )

    root0 = build(initial_array, 0, n - 1)
    roots.append(root0)

    results = []
    for op in operations:
        if op[0] == "update":
            _, version, idx, val = op
            new_root = update(roots[version], 0, n - 1, idx, val)
            roots.append(new_root)
            results.append(("new_version", len(roots) - 1))
        elif op[0] == "query":
            _, version, l, r = op
            ans = query(roots[version], 0, n - 1, l, r)
            results.append(("answer", ans))

    return results
"""

BUG_DESC = (
    "During path-copying update, the new node stores a reference to the OLD "
    "child instead of the recursively-updated child. The recursive call is made "
    "but its result is discarded, so updates never propagate and queries on new "
    "versions return stale (original) values."
)


def SPEC(initial_array, operations, result):
    """Verify via naive simulation with per-version arrays."""
    n = len(initial_array)
    versions = [list(initial_array)]  # version 0

    idx = 0
    for op in operations:
        if idx >= len(result):
            return False
        if op[0] == "update":
            _, version, pos, val = op
            if version >= len(versions):
                return False
            new_arr = list(versions[version])
            new_arr[pos] = val
            versions.append(new_arr)
            tag, vid = result[idx]
            if tag != "new_version":
                return False
        elif op[0] == "query":
            _, version, l, r = op
            if version >= len(versions):
                return False
            expected = sum(versions[version][l : r + 1])
            tag, ans = result[idx]
            if tag != "answer" or ans != expected:
                return False
        idx += 1

    return True


def _gen_input():
    n = 8
    initial_array = [random.randint(1, 10) for _ in range(n)]
    operations = []
    num_versions = 1  # version 0 exists

    num_ops = random.randint(8, 12)
    for _ in range(num_ops):
        if random.random() < 0.5 and num_versions > 0:
            # update
            version = random.randint(0, num_versions - 1)
            idx = random.randint(0, n - 1)
            val = random.randint(1, 20)
            operations.append(("update", version, idx, val))
            num_versions += 1
        else:
            # query
            version = random.randint(0, num_versions - 1)
            l = random.randint(0, n - 1)
            r = random.randint(l, n - 1)
            operations.append(("query", version, l, r))

    return {"initial_array": initial_array, "operations": operations}


INPUT_OVERRIDES = {"_gen": _gen_input}
