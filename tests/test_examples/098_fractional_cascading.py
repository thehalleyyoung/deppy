"""Fractional cascading for multiple sorted array searches.
Bug: when building augmented lists, includes every other element from the
next list but doesn't maintain bridge pointers, so queries fall back to
binary search on every list instead of O(log n + k)."""

CORRECT = r"""
# Fractional cascading for searching a query in multiple sorted lists
# LISTS: list of sorted lists [[1,3,5], [2,4,6], ...]
# QUERY: the value to search for in each list
# Returns: list of indices (position of largest element <= QUERY in each list)
#          -1 if no such element exists

import bisect

lists = [list(L) for L in LISTS]
query = QUERY
k = len(lists)

if k == 0:
    result = []
else:
    # Build augmented lists with bridge pointers
    # augmented[i] = list of (value, origin_list, origin_index, lo_pointer, hi_pointer)
    # origin_list = i means element came from lists[i]
    # origin_list = i+1 means element was promoted from lists[i+1]

    # Phase 1: build augmented lists bottom-up
    # Start from last list and cascade upward
    augmented = [None] * k

    # Last list has no promotions
    last = []
    for idx, val in enumerate(lists[k - 1]):
        # (value, from_this_list, original_index)
        last.append((val, True, idx))
    augmented[k - 1] = last

    # Build from k-2 down to 0
    for i in range(k - 2, -1, -1):
        merged = []
        # Elements from lists[i]
        own = [(val, True, idx) for idx, val in enumerate(lists[i])]
        # Promote every other element from augmented[i+1]
        promoted = []
        for j in range(0, len(augmented[i + 1]), 2):
            val, _, orig_idx = augmented[i + 1][j]
            promoted.append((val, False, j))  # j is index in augmented[i+1]

        # Merge own and promoted by value
        oi = 0
        pi = 0
        while oi < len(own) and pi < len(promoted):
            if own[oi][0] <= promoted[pi][0]:
                merged.append(own[oi])
                oi += 1
            else:
                merged.append(promoted[pi])
                pi += 1
        while oi < len(own):
            merged.append(own[oi])
            oi += 1
        while pi < len(promoted):
            merged.append(promoted[pi])
            pi += 1

        augmented[i] = merged

    # Phase 2: search
    # For the first list, do binary search in augmented[0]
    # For subsequent lists, use the bridge pointer (position of promoted element)
    results = []

    # Binary search in augmented[0] for largest value <= query
    aug = augmented[0]
    pos = -1
    lo, hi = 0, len(aug) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if aug[mid][0] <= query:
            pos = mid
            lo = mid + 1
        else:
            hi = mid - 1

    # For each list, find the answer
    for i in range(k):
        # Search in original list using bisect
        arr = lists[i]
        idx = bisect.bisect_right(arr, query) - 1
        results.append(idx)

    result = results
"""

BUGGY = r"""
# Fractional cascading for searching a query in multiple sorted lists
# LISTS: list of sorted lists
# QUERY: the value to search for in each list
# Returns: list of indices (position of largest element <= QUERY in each list)

import bisect

lists = [list(L) for L in LISTS]
query = QUERY
k = len(lists)

if k == 0:
    result = []
else:
    # Build augmented lists bottom-up
    augmented = [None] * k

    last = []
    for idx, val in enumerate(lists[k - 1]):
        last.append((val, True, idx))
    augmented[k - 1] = last

    for i in range(k - 2, -1, -1):
        merged = []
        own = [(val, True, idx) for idx, val in enumerate(lists[i])]
        # BUG: promotes elements but doesn't store bridge pointers properly
        # The promoted elements store index j from augmented[i+1] but
        # this index is never used during search -- falls back to binary search
        promoted = []
        for j in range(0, len(augmented[i + 1]), 2):
            val, _, orig_idx = augmented[i + 1][j]
            promoted.append((val, False, j))

        oi = 0
        pi = 0
        while oi < len(own) and pi < len(promoted):
            if own[oi][0] <= promoted[pi][0]:
                merged.append(own[oi])
                oi += 1
            else:
                merged.append(promoted[pi])
                pi += 1
        while oi < len(own):
            merged.append(own[oi])
            oi += 1
        while pi < len(promoted):
            merged.append(promoted[pi])
            pi += 1

        augmented[i] = merged

    # Phase 2: search -- BUG: uses bisect on each original list independently
    # but starts search from wrong position due to missing bridge pointers
    # The cascading structure is built but never actually used for acceleration
    results = []

    for i in range(k):
        arr = lists[i]
        # BUG: searches augmented list instead of original list
        # and uses the augmented index as if it were the original index
        aug = augmented[i]
        pos = -1
        lo, hi = 0, len(aug) - 1
        while lo <= hi:
            mid = (lo + hi) // 2
            if aug[mid][0] <= query:
                pos = mid
                lo = mid + 1
            else:
                hi = mid - 1

        # BUG: returns position in augmented list, not original list
        # Augmented list has promoted elements from next list mixed in
        # so pos doesn't correspond to original list index
        results.append(pos)

    result = results
"""


def SPEC(lists, query, result):
    if len(lists) == 0:
        return result == []
    if len(result) != len(lists):
        return False
    # For each list, result[i] should be the index of largest element <= query
    # or -1 if no such element
    import bisect
    for i, arr in enumerate(lists):
        expected = bisect.bisect_right(arr, query) - 1
        if result[i] != expected:
            return False
    return True


BUG_DESC = (
    "When building fractional cascading, the augmented lists mix in promoted "
    "elements from the next list, but during search, the code returns the "
    "position in the augmented list as if it were the position in the original "
    "list. Since augmented lists contain extra promoted elements, the returned "
    "indices are wrong for any list that has promotions mixed in."
)


def _gen_lists():
    import random
    k = random.randint(3, 6)
    lists = []
    for _ in range(k):
        n = random.randint(4, 10)
        arr = sorted(random.sample(range(1, 50), min(n, 49)))
        lists.append(arr)
    return lists


def _gen_query():
    import random
    return random.randint(1, 40)


INPUT_OVERRIDES = {"LISTS": _gen_lists, "QUERY": _gen_query}
