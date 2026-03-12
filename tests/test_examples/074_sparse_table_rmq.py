"""Sparse table for O(1) range minimum queries after O(n log n) build.
Bug: in query, uses max to combine overlapping blocks instead of min."""

CORRECT = r"""
def solve_rmq(nums, queries):
    n = len(nums)
    if n == 0:
        return []

    LOG = [0] * (n + 1)
    for i in range(2, n + 1):
        LOG[i] = LOG[i // 2] + 1
    K = LOG[n] + 1

    table = [[0] * n for _ in range(K)]
    for i in range(n):
        table[0][i] = i

    j = 1
    while (1 << j) <= n:
        i = 0
        while i + (1 << j) - 1 < n:
            left = table[j - 1][i]
            right = table[j - 1][i + (1 << (j - 1))]
            if nums[left] <= nums[right]:
                table[j][i] = left
            else:
                table[j][i] = right
            i += 1
        j += 1

    answers = []
    for l, r in queries:
        l = max(0, l)
        r = min(n - 1, r)
        if l <= r:
            length = r - l + 1
            k = LOG[length]
            left_idx = table[k][l]
            right_idx = table[k][r - (1 << k) + 1]
            if nums[left_idx] <= nums[right_idx]:
                answers.append(nums[left_idx])
            else:
                answers.append(nums[right_idx])
        else:
            answers.append(None)
    return answers

nums = list(NUMS)
queries = list(QUERIES)
result = solve_rmq(nums, queries)
"""

BUGGY = r"""
def solve_rmq(nums, queries):
    n = len(nums)
    if n == 0:
        return []

    LOG = [0] * (n + 1)
    for i in range(2, n + 1):
        LOG[i] = LOG[i // 2] + 1
    K = LOG[n] + 1

    table = [[0] * n for _ in range(K)]
    for i in range(n):
        table[0][i] = i

    j = 1
    while (1 << j) <= n:
        i = 0
        while i + (1 << j) - 1 < n:
            left = table[j - 1][i]
            right = table[j - 1][i + (1 << (j - 1))]
            if nums[left] <= nums[right]:
                table[j][i] = left
            else:
                table[j][i] = right
            i += 1
        j += 1

    answers = []
    for l, r in queries:
        l = max(0, l)
        r = min(n - 1, r)
        if l <= r:
            length = r - l + 1
            k = LOG[length]
            left_idx = table[k][l]
            right_idx = table[k][r - (1 << k) + 1]
            # BUG: returns max instead of min
            if nums[left_idx] >= nums[right_idx]:
                answers.append(nums[left_idx])
            else:
                answers.append(nums[right_idx])
        else:
            answers.append(None)
    return answers

nums = list(NUMS)
queries = list(QUERIES)
result = solve_rmq(nums, queries)
"""


def SPEC(nums, queries, result):
    if not nums:
        return result == []
    n = len(nums)
    expected = []
    for l, r in queries:
        l = max(0, l)
        r = min(n - 1, r)
        if l <= r:
            expected.append(min(nums[l:r + 1]))
        else:
            expected.append(None)
    return result == expected


BUG_DESC = (
    "In query_rmq, when combining the two overlapping blocks, uses >= comparison "
    "and returns the larger value instead of the smaller one. This effectively "
    "turns the range minimum query into a range maximum query."
)


def _gen():
    import random
    n = random.randint(5, 20)
    nums = [random.randint(-100, 100) for _ in range(n)]
    queries = []
    for _ in range(random.randint(3, 8)):
        l = random.randint(0, n - 1)
        r = random.randint(l, n - 1)
        queries.append((l, r))
    return nums, queries

_cached = [None]

def _gen_nums():
    import random
    _cached[0] = _gen()
    return _cached[0][0]

def _gen_queries():
    return _cached[0][1]


INPUT_OVERRIDES = {"NUMS": _gen_nums, "QUERIES": _gen_queries}
