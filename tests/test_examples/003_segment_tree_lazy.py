"""Segment tree with lazy propagation for range-add updates and range-sum queries.

Bug: When pushing down the lazy value to children, the code multiplies the
lazy value by the PARENT's range length instead of each CHILD's range length.
This overcounts the propagated addition, producing incorrect sums.
"""

CORRECT = r"""
def process_operations(arr, operations):
    n = len(arr)
    size = 4 * n
    tree = [0] * size
    lazy = [0] * size
    query_results = []

    def build(node, start, end):
        if start == end:
            tree[node] = arr[start]
            return
        mid = (start + end) // 2
        build(2 * node, start, mid)
        build(2 * node + 1, mid + 1, end)
        tree[node] = tree[2 * node] + tree[2 * node + 1]

    def push_down(node, start, end):
        if lazy[node] != 0:
            mid = (start + end) // 2
            left_len = mid - start + 1
            right_len = end - mid

            # CORRECT: multiply lazy by each child's range length
            tree[2 * node] += lazy[node] * left_len
            lazy[2 * node] += lazy[node]

            tree[2 * node + 1] += lazy[node] * right_len
            lazy[2 * node + 1] += lazy[node]

            lazy[node] = 0

    def range_update(node, start, end, l, r, val):
        if r < start or end < l:
            return
        if l <= start and end <= r:
            tree[node] += val * (end - start + 1)
            lazy[node] += val
            return
        push_down(node, start, end)
        mid = (start + end) // 2
        range_update(2 * node, start, mid, l, r, val)
        range_update(2 * node + 1, mid + 1, end, l, r, val)
        tree[node] = tree[2 * node] + tree[2 * node + 1]

    def range_query(node, start, end, l, r):
        if r < start or end < l:
            return 0
        if l <= start and end <= r:
            return tree[node]
        push_down(node, start, end)
        mid = (start + end) // 2
        left_sum = range_query(2 * node, start, mid, l, r)
        right_sum = range_query(2 * node + 1, mid + 1, end, l, r)
        return left_sum + right_sum

    if n > 0:
        build(1, 0, n - 1)

    for op in operations:
        if op[0] == 'update':
            _, l, r, val = op
            range_update(1, 0, n - 1, l, r, val)
        elif op[0] == 'query':
            _, l, r = op
            query_results.append(range_query(1, 0, n - 1, l, r))

    return query_results

arr = ARR
operations = OPS
result = process_operations(arr, operations)
"""

BUGGY = r"""
def process_operations(arr, operations):
    n = len(arr)
    size = 4 * n
    tree = [0] * size
    lazy = [0] * size
    query_results = []

    def build(node, start, end):
        if start == end:
            tree[node] = arr[start]
            return
        mid = (start + end) // 2
        build(2 * node, start, mid)
        build(2 * node + 1, mid + 1, end)
        tree[node] = tree[2 * node] + tree[2 * node + 1]

    def push_down(node, start, end):
        if lazy[node] != 0:
            mid = (start + end) // 2
            parent_len = end - start + 1

            # BUG: uses parent_len instead of each child's range length
            tree[2 * node] += lazy[node] * parent_len
            lazy[2 * node] += lazy[node]

            tree[2 * node + 1] += lazy[node] * parent_len
            lazy[2 * node + 1] += lazy[node]

            lazy[node] = 0

    def range_update(node, start, end, l, r, val):
        if r < start or end < l:
            return
        if l <= start and end <= r:
            tree[node] += val * (end - start + 1)
            lazy[node] += val
            return
        push_down(node, start, end)
        mid = (start + end) // 2
        range_update(2 * node, start, mid, l, r, val)
        range_update(2 * node + 1, mid + 1, end, l, r, val)
        tree[node] = tree[2 * node] + tree[2 * node + 1]

    def range_query(node, start, end, l, r):
        if r < start or end < l:
            return 0
        if l <= start and end <= r:
            return tree[node]
        push_down(node, start, end)
        mid = (start + end) // 2
        left_sum = range_query(2 * node, start, mid, l, r)
        right_sum = range_query(2 * node + 1, mid + 1, end, l, r)
        return left_sum + right_sum

    if n > 0:
        build(1, 0, n - 1)

    for op in operations:
        if op[0] == 'update':
            _, l, r, val = op
            range_update(1, 0, n - 1, l, r, val)
        elif op[0] == 'query':
            _, l, r = op
            query_results.append(range_query(1, 0, n - 1, l, r))

    return query_results

arr = ARR
operations = OPS
result = process_operations(arr, operations)
"""


def SPEC(arr, operations, result):
    """Verify by simulating on a naive array."""
    if not isinstance(result, list):
        return False

    naive = list(arr)
    expected = []

    for op in operations:
        if op[0] == 'update':
            _, l, r, val = op
            for i in range(l, r + 1):
                naive[i] += val
        elif op[0] == 'query':
            _, l, r = op
            expected.append(sum(naive[l:r + 1]))

    return result == expected


BUG_DESC = (
    "When pushing down lazy values to children during propagation, the code "
    "multiplies the lazy value by the PARENT's range length instead of each "
    "CHILD's range length. For a parent covering [0,3], the left child covers "
    "[0,1] (length 2) and right covers [2,3] (length 2), but the bug uses "
    "length 4 for both, overcounting the additions."
)


_cached = {}


def _gen_arr():
    """Generate array and paired operations that trigger lazy push_down bug.

    The bug uses parent's range length instead of child's during push_down.
    push_down only happens when a range update covers a node fully, then a
    subsequent query/update needs to descend into that node's children.

    To trigger: do a full-range update, then query a sub-range (which forces
    push_down at a node where left_len != right_len != parent_len).
    We use array sizes >= 4 so that the root covers [0,n-1] and children
    have different lengths than the parent.
    """
    import random
    # Use size 4..8 — small but enough that parent_len != child_len
    n = random.choice([4, 5, 6, 7, 8])
    arr = [random.randint(1, 5) for _ in range(n)]

    ops = []
    # Step 1: range update over the full array — sets lazy at root
    val = random.randint(1, 5)
    ops.append(('update', 0, n - 1, val))
    # Step 2: query a sub-range — forces push_down from root to children
    # The bug will multiply lazy by parent_len instead of child_len
    # Query left half only — this triggers push_down and the child gets
    # parent_len * lazy instead of child_len * lazy
    mid = n // 2
    ops.append(('query', 0, mid))
    # Also query a single element to really expose the difference
    ops.append(('query', 0, 0))
    # Add another update + sub-query cycle
    val2 = random.randint(1, 5)
    ops.append(('update', 0, n - 1, val2))
    ops.append(('query', mid, n - 1))
    ops.append(('query', 0, n - 1))

    _cached['ops'] = ops
    return arr


def _gen_ops():
    if 'ops' in _cached:
        return _cached.pop('ops')
    # Fallback: deterministic trigger case
    return [
        ('update', 0, 3, 3),
        ('query', 0, 1),
        ('query', 0, 0),
        ('update', 0, 3, 2),
        ('query', 2, 3),
    ]


INPUT_OVERRIDES = {
    "arr": _gen_arr,
    "operations": _gen_ops,
}
