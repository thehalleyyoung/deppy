"""Segment tree beats (Ji driver) for range chmin and range sum. Bug: pushdown uses parent's second-max instead of new max value."""

CORRECT = r"""
def solve_beats(nums, ops):
    n = len(nums)
    if n == 0:
        return []
    SIZE = 4 * n
    mx = [0] * SIZE
    sm = [-1] * SIZE
    cm = [0] * SIZE
    ts = [0] * SIZE

    def build(node, lo, hi):
        if lo == hi:
            mx[node] = nums[lo]
            sm[node] = -1
            cm[node] = 1
            ts[node] = nums[lo]
            return
        mid = (lo + hi) // 2
        build(2 * node, lo, mid)
        build(2 * node + 1, mid + 1, hi)
        pull_up(node)

    def pull_up(node):
        lc, rc = 2 * node, 2 * node + 1
        ts[node] = ts[lc] + ts[rc]
        if mx[lc] == mx[rc]:
            mx[node] = mx[lc]
            cm[node] = cm[lc] + cm[rc]
            sm[node] = max(sm[lc], sm[rc])
        elif mx[lc] > mx[rc]:
            mx[node] = mx[lc]
            cm[node] = cm[lc]
            sm[node] = max(sm[lc], mx[rc])
        else:
            mx[node] = mx[rc]
            cm[node] = cm[rc]
            sm[node] = max(mx[lc], sm[rc])

    def push_chmin(node, val):
        if val >= mx[node]:
            return
        ts[node] -= cm[node] * (mx[node] - val)
        mx[node] = val

    def push_down(node):
        if mx[node] < mx[2 * node]:
            push_chmin(2 * node, mx[node])
        if mx[node] < mx[2 * node + 1]:
            push_chmin(2 * node + 1, mx[node])

    def update_chmin(node, lo, hi, ql, qr, val):
        if ql > hi or qr < lo or val >= mx[node]:
            return
        if ql <= lo and hi <= qr and val > sm[node]:
            push_chmin(node, val)
            return
        push_down(node)
        mid = (lo + hi) // 2
        update_chmin(2 * node, lo, mid, ql, qr, val)
        update_chmin(2 * node + 1, mid + 1, hi, ql, qr, val)
        pull_up(node)

    def query_sum(node, lo, hi, ql, qr):
        if ql > hi or qr < lo:
            return 0
        if ql <= lo and hi <= qr:
            return ts[node]
        push_down(node)
        mid = (lo + hi) // 2
        return query_sum(2 * node, lo, mid, ql, qr) + query_sum(2 * node + 1, mid + 1, hi, ql, qr)

    build(1, 0, n - 1)
    answers = []
    for op in ops:
        if op[0] == "chmin":
            _, l, r, val = op
            update_chmin(1, 0, n - 1, l, r, val)
        elif op[0] == "sum":
            _, l, r = op
            answers.append(query_sum(1, 0, n - 1, l, r))
    return answers

nums = list(NUMS)
ops = list(OPS)
result = solve_beats(nums, ops)
"""

BUGGY = r"""
def solve_beats(nums, ops):
    n = len(nums)
    if n == 0:
        return []
    SIZE = 4 * n
    mx = [0] * SIZE
    sm = [-1] * SIZE
    cm = [0] * SIZE
    ts = [0] * SIZE

    def build(node, lo, hi):
        if lo == hi:
            mx[node] = nums[lo]
            sm[node] = -1
            cm[node] = 1
            ts[node] = nums[lo]
            return
        mid = (lo + hi) // 2
        build(2 * node, lo, mid)
        build(2 * node + 1, mid + 1, hi)
        pull_up(node)

    def pull_up(node):
        lc, rc = 2 * node, 2 * node + 1
        ts[node] = ts[lc] + ts[rc]
        if mx[lc] == mx[rc]:
            mx[node] = mx[lc]
            cm[node] = cm[lc] + cm[rc]
            sm[node] = max(sm[lc], sm[rc])
        elif mx[lc] > mx[rc]:
            mx[node] = mx[lc]
            cm[node] = cm[lc]
            sm[node] = max(sm[lc], mx[rc])
        else:
            mx[node] = mx[rc]
            cm[node] = cm[rc]
            sm[node] = max(mx[lc], sm[rc])

    def push_chmin(node, val):
        if val >= mx[node]:
            return
        ts[node] -= cm[node] * (mx[node] - val)
        mx[node] = val

    def push_down(node):
        # BUG: uses sm[node] (second_max) instead of mx[node]
        if sm[node] < mx[2 * node]:
            push_chmin(2 * node, sm[node])
        if sm[node] < mx[2 * node + 1]:
            push_chmin(2 * node + 1, sm[node])

    def update_chmin(node, lo, hi, ql, qr, val):
        if ql > hi or qr < lo or val >= mx[node]:
            return
        if ql <= lo and hi <= qr and val > sm[node]:
            push_chmin(node, val)
            return
        push_down(node)
        mid = (lo + hi) // 2
        update_chmin(2 * node, lo, mid, ql, qr, val)
        update_chmin(2 * node + 1, mid + 1, hi, ql, qr, val)
        pull_up(node)

    def query_sum(node, lo, hi, ql, qr):
        if ql > hi or qr < lo:
            return 0
        if ql <= lo and hi <= qr:
            return ts[node]
        push_down(node)
        mid = (lo + hi) // 2
        return query_sum(2 * node, lo, mid, ql, qr) + query_sum(2 * node + 1, mid + 1, hi, ql, qr)

    build(1, 0, n - 1)
    answers = []
    for op in ops:
        if op[0] == "chmin":
            _, l, r, val = op
            update_chmin(1, 0, n - 1, l, r, val)
        elif op[0] == "sum":
            _, l, r = op
            answers.append(query_sum(1, 0, n - 1, l, r))
    return answers

nums = list(NUMS)
ops = list(OPS)
result = solve_beats(nums, ops)
"""


def SPEC(nums, ops, result):
    # Simulate operations on a plain array to get ground truth
    arr = list(nums)
    n = len(arr)
    expected = []
    for op in ops:
        if op[0] == "chmin":
            _, l, r, val = op
            for i in range(l, r + 1):
                arr[i] = min(arr[i], val)
        elif op[0] == "sum":
            _, l, r = op
            expected.append(sum(arr[l:r + 1]))

    if len(result) != len(expected):
        return False
    for i in range(len(expected)):
        if result[i] != expected[i]:
            return False
    return True


BUG_DESC = "In pushdown, propagates the parent's second_max instead of max_val to children, corrupting child node sums after chmin operations."


def _gen():
    import random
    n = random.randint(6, 12)
    nums = [random.randint(1, 50) for _ in range(n)]
    ops = []
    for _ in range(random.randint(5, 10)):
        l = random.randint(0, n - 1)
        r = random.randint(l, n - 1)
        if random.random() < 0.5:
            val = random.randint(1, 40)
            ops.append(("chmin", l, r, val))
        else:
            ops.append(("sum", l, r))
    # Ensure at least one sum query
    l = random.randint(0, n - 1)
    r = random.randint(l, n - 1)
    ops.append(("sum", l, r))
    return nums, ops

_cached = [None]

def _gen_nums():
    _cached[0] = _gen()
    return _cached[0][0]

def _gen_ops():
    return _cached[0][1]


INPUT_OVERRIDES = {
    "NUMS": _gen_nums,
    "OPS": _gen_ops,
}
