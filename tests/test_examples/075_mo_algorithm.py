"""Mo's algorithm for offline range queries counting distinct elements.
Bug: when removing an element, decrements count but doesn't check if
count reaches 0 to decrement the distinct counter."""

CORRECT = r"""
# Mo's Algorithm for offline range queries - counting distinct elements
# Processes queries in an order that minimizes add/remove operations
import math

def mo_algorithm(arr, queries):
    n = len(arr)
    if n == 0:
        return [0] * len(queries)
    block_size = max(1, int(math.sqrt(n)))

    # Sort queries by (block of left endpoint, right endpoint)
    indexed_queries = [(l, r, i) for i, (l, r) in enumerate(queries)]
    indexed_queries.sort(key=lambda q: (q[0] // block_size, q[1] if (q[0] // block_size) % 2 == 0 else -q[1]))

    count = {}
    distinct = 0
    cur_l = 0
    cur_r = -1
    answers = [0] * len(queries)

    def add(idx):
        nonlocal distinct
        val = arr[idx]
        if val not in count:
            count[val] = 0
        count[val] += 1
        if count[val] == 1:
            distinct += 1

    def remove(idx):
        nonlocal distinct
        val = arr[idx]
        count[val] -= 1
        # CORRECT: check if count reaches 0 to decrement distinct
        if count[val] == 0:
            distinct -= 1

    for l, r, qi in indexed_queries:
        # Expand/shrink current range to [l, r]
        while cur_r < r:
            cur_r += 1
            add(cur_r)
        while cur_l > l:
            cur_l -= 1
            add(cur_l)
        while cur_r > r:
            remove(cur_r)
            cur_r -= 1
        while cur_l < l:
            remove(cur_l)
            cur_l += 1
        answers[qi] = distinct

    return answers

arr = list(ARR)
queries = list(QUERIES)
result = mo_algorithm(arr, queries)
"""

BUGGY = r"""
# Mo's Algorithm for offline range queries - counting distinct elements
# Processes queries in an order that minimizes add/remove operations
import math

def mo_algorithm(arr, queries):
    n = len(arr)
    if n == 0:
        return [0] * len(queries)
    block_size = max(1, int(math.sqrt(n)))

    # Sort queries by (block of left endpoint, right endpoint)
    indexed_queries = [(l, r, i) for i, (l, r) in enumerate(queries)]
    indexed_queries.sort(key=lambda q: (q[0] // block_size, q[1] if (q[0] // block_size) % 2 == 0 else -q[1]))

    count = {}
    distinct = 0
    cur_l = 0
    cur_r = -1
    answers = [0] * len(queries)

    def add(idx):
        nonlocal distinct
        val = arr[idx]
        if val not in count:
            count[val] = 0
        count[val] += 1
        if count[val] == 1:
            distinct += 1

    def remove(idx):
        nonlocal distinct
        val = arr[idx]
        count[val] -= 1
        # BUG: never decrements distinct when count reaches 0
        # The element is "removed" from the count but distinct stays inflated

    for l, r, qi in indexed_queries:
        # Expand/shrink current range to [l, r]
        while cur_r < r:
            cur_r += 1
            add(cur_r)
        while cur_l > l:
            cur_l -= 1
            add(cur_l)
        while cur_r > r:
            remove(cur_r)
            cur_r -= 1
        while cur_l < l:
            remove(cur_l)
            cur_l += 1
        answers[qi] = distinct

    return answers

arr = list(ARR)
queries = list(QUERIES)
result = mo_algorithm(arr, queries)
"""


def SPEC(arr, queries, result):
    # Verify each query answer is the count of distinct elements in arr[l..r]
    if not arr:
        return all(r == 0 for r in result)
    if len(result) != len(queries):
        return False
    for i, (l, r) in enumerate(queries):
        l = max(0, l)
        r = min(len(arr) - 1, r)
        if l > r:
            expected = 0
        else:
            expected = len(set(arr[l:r + 1]))
        if result[i] != expected:
            return False
    return True


BUG_DESC = (
    "In the remove function, decrements count[val] but never checks if it "
    "reaches 0 to decrement the distinct counter. This causes distinct to "
    "only grow, never shrink, giving inflated counts for queries processed "
    "after any removal occurs."
)


def _gen_arr():
    import random
    n = random.randint(6, 15)
    # Use small alphabet to ensure duplicates
    return [random.randint(1, 4) for _ in range(n)]


def _gen_queries():
    import random
    n = random.randint(6, 15)
    queries = []
    for _ in range(random.randint(4, 8)):
        l = random.randint(0, n - 1)
        r = random.randint(l, n - 1)
        queries.append((l, r))
    return queries


INPUT_OVERRIDES = {"ARR": _gen_arr, "QUERIES": _gen_queries}
