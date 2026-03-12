"""Suffix array construction via O(n log^2 n) doubling algorithm.

Bug: When the suffix at position i+k extends past the end of the string,
the second-half rank should be -1 (a sentinel smaller than any valid rank).
The bug uses 0 instead, which equals a valid rank value, causing certain
suffixes that end before others to sort incorrectly.
"""

CORRECT = r"""
def build_suffix_array(s):
    n = len(s)
    if n == 0:
        return []

    # Initial ranking by single characters
    sa = list(range(n))
    rank = [ord(c) for c in s]
    tmp_rank = [0] * n

    k = 1
    while k < n:
        # Sort by (rank[i], rank[i+k]) pairs
        def sort_key(i):
            second = rank[i + k] if i + k < n else -1  # CORRECT: -1 sentinel
            return (rank[i], second)

        sa.sort(key=sort_key)

        # Recompute ranks
        tmp_rank[sa[0]] = 0
        for i in range(1, n):
            prev_key = (rank[sa[i - 1]],
                        rank[sa[i - 1] + k] if sa[i - 1] + k < n else -1)
            curr_key = (rank[sa[i]],
                        rank[sa[i] + k] if sa[i] + k < n else -1)
            if curr_key == prev_key:
                tmp_rank[sa[i]] = tmp_rank[sa[i - 1]]
            else:
                tmp_rank[sa[i]] = tmp_rank[sa[i - 1]] + 1

        for i in range(n):
            rank[i] = tmp_rank[i]

        # Early termination: all ranks unique
        if rank[sa[n - 1]] == n - 1:
            break

        k *= 2

    return sa

s = STRING
result = build_suffix_array(s)
"""

BUGGY = r"""
def build_suffix_array(s):
    n = len(s)
    if n == 0:
        return []

    # Initial ranking by single characters
    sa = list(range(n))
    rank = [ord(c) for c in s]
    tmp_rank = [0] * n

    k = 1
    while k < n:
        # Sort by (rank[i], rank[i+k]) pairs
        def sort_key(i):
            second = rank[i + k] if i + k < n else 0  # BUG: 0 instead of -1
            return (rank[i], second)

        sa.sort(key=sort_key)

        # Recompute ranks
        tmp_rank[sa[0]] = 0
        for i in range(1, n):
            prev_key = (rank[sa[i - 1]],
                        rank[sa[i - 1] + k] if sa[i - 1] + k < n else 0)
            curr_key = (rank[sa[i]],
                        rank[sa[i] + k] if sa[i] + k < n else 0)
            if curr_key == prev_key:
                tmp_rank[sa[i]] = tmp_rank[sa[i - 1]]
            else:
                tmp_rank[sa[i]] = tmp_rank[sa[i - 1]] + 1

        for i in range(n):
            rank[i] = tmp_rank[i]

        # Early termination: all ranks unique
        if rank[sa[n - 1]] == n - 1:
            break

        k *= 2

    return sa

s = STRING
result = build_suffix_array(s)
"""


def SPEC(s, result):
    """Verify suffix array correctness:
    1) It's a permutation of 0..n-1.
    2) Consecutive suffixes in the array are lexicographically ordered.
    """
    n = len(s)
    if not isinstance(result, list):
        return False
    if len(result) != n:
        return False

    # Check permutation
    if sorted(result) != list(range(n)):
        return False

    # Check lexicographic ordering
    for i in range(n - 1):
        suffix_a = s[result[i]:]
        suffix_b = s[result[i + 1]:]
        if suffix_a > suffix_b:
            return False

    return True


BUG_DESC = (
    "When computing the second-half rank for suffix positions where i+k >= n "
    "(suffix extends past string end), the bug uses 0 as the sentinel instead "
    "of -1. Since 0 can equal a valid rank, shorter suffixes that should sort "
    "before others with the same prefix get compared incorrectly, producing "
    "a wrong suffix array."
)


def _generate_string():
    import random
    length = random.randint(8, 20)
    return ''.join(random.choice('abc') for _ in range(length))


INPUT_OVERRIDES = {
    "STRING": _generate_string,
}
