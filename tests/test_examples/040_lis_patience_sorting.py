"""Longest increasing subsequence via patience sorting with binary search.
Bug: uses bisect_right instead of bisect_left, so equal elements start a new pile
instead of going on top of an existing pile, overcounting the LIS length."""

CORRECT = r"""
# Longest Increasing Subsequence via patience sorting
# Uses binary search to find the correct pile for each card
# Returns both the length and an actual LIS

from bisect import bisect_left

nums = NUMS

n = len(nums)
if n == 0:
    result = {"length": 0, "subsequence": [], "tails": [], "nums": nums}
else:
    # tails[i] = smallest tail element of all increasing subsequences of length i+1
    tails = []
    # For reconstruction: store the predecessor index and pile assignment
    piles = []  # piles[i] = index in tails where nums[i] was placed
    predecessors = [-1] * n
    # For each pile, track which element index is on top
    pile_tops = []

    for i in range(n):
        pos = bisect_left(tails, nums[i])
        if pos == len(tails):
            tails.append(nums[i])
            pile_tops.append(i)
        else:
            tails[pos] = nums[i]
            pile_tops[pos] = i
        piles.append(pos)
        if pos > 0:
            # Find predecessor: the top of the previous pile at this moment
            # We need to track this more carefully for reconstruction
            predecessors[i] = pile_tops[pos - 1]

    lis_length = len(tails)

    # Reconstruct one LIS
    subsequence = []
    idx = pile_tops[lis_length - 1]
    while idx != -1:
        subsequence.append(nums[idx])
        idx = predecessors[idx]
    subsequence.reverse()

    result = {
        "length": lis_length,
        "subsequence": subsequence,
        "tails": tails[:],
        "nums": nums,
    }
"""

BUGGY = r"""
# LIS with bisect_right bug
from bisect import bisect_right

nums = NUMS

n = len(nums)
if n == 0:
    result = {"length": 0, "subsequence": [], "tails": [], "nums": nums}
else:
    tails = []
    piles = []
    predecessors = [-1] * n
    pile_tops = []

    for i in range(n):
        # BUG: uses bisect_right instead of bisect_left
        # This means equal elements go to a NEW pile instead of replacing
        # an existing pile top, causing the LIS length to be overcounted
        # when there are duplicate values
        pos = bisect_right(tails, nums[i])
        if pos == len(tails):
            tails.append(nums[i])
            pile_tops.append(i)
        else:
            tails[pos] = nums[i]
            pile_tops[pos] = i
        piles.append(pos)
        if pos > 0:
            predecessors[i] = pile_tops[pos - 1]

    lis_length = len(tails)

    subsequence = []
    idx = pile_tops[lis_length - 1]
    while idx != -1:
        subsequence.append(nums[idx])
        idx = predecessors[idx]
    subsequence.reverse()

    result = {
        "length": lis_length,
        "subsequence": subsequence,
        "tails": tails[:],
        "nums": nums,
    }
"""

def SPEC(nums, result):
    """Verify LIS correctness."""
    length = result["length"]
    subseq = result["subsequence"]

    if len(nums) == 0:
        return length == 0

    # The subsequence must have the reported length
    if len(subseq) != length:
        return False

    # The subsequence must be strictly increasing
    for i in range(len(subseq) - 1):
        if subseq[i] >= subseq[i + 1]:
            return False

    # Every element of subsequence must appear in nums
    # and in the correct relative order
    j = 0
    for i in range(len(nums)):
        if j < len(subseq) and nums[i] == subseq[j]:
            j += 1
    if j != len(subseq):
        return False

    # Verify the length is optimal (DP check for small inputs)
    n = len(nums)
    if n <= 500:
        dp = [1] * n
        for i in range(1, n):
            for j_idx in range(i):
                if nums[j_idx] < nums[i]:
                    dp[i] = max(dp[i], dp[j_idx] + 1)
        true_lis = max(dp)
        if length != true_lis:
            return False

    return True

BUG_DESC = "Uses bisect_right instead of bisect_left, causing equal elements to start a new pile rather than replacing an existing pile's top, which overcounts the LIS length when duplicates are present."

def _gen():
    import random
    # The bug uses bisect_right instead of bisect_left. With duplicates,
    # bisect_right places equal elements one position later, creating a
    # new pile instead of replacing an existing one. This overcounts.
    #
    # Guaranteed trigger: arrays with consecutive equal values like [k, k].
    # bisect_left([k], k) = 0 (replace), bisect_right([k], k) = 1 (new pile).
    #
    # Strategy: build arrays with many duplicates. Even [1,1] suffices
    # (correct LIS=1, buggy LIS=2), but we add variety.
    n = random.randint(4, 8)
    # Use very small value range to guarantee many duplicates
    max_val = max(2, n // 3)
    nums = [random.randint(1, max_val) for _ in range(n)]
    # Ensure at least one pair of adjacent equal values
    if n >= 2:
        pos = random.randint(0, n - 2)
        nums[pos + 1] = nums[pos]
    return nums

INPUT_OVERRIDES = {"NUMS": _gen}
