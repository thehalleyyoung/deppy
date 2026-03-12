"""Quickselect for finding k-th smallest element using Hoare's partition.
Bug: after partition, recurses on wrong subarray (uses k < pivot_idx instead
of k <= pivot_idx), missing when k equals the pivot position."""

CORRECT = r"""
# Quickselect algorithm for k-th smallest element
# Uses Hoare-style partitioning with median-of-three pivot
import random

def partition(arr, lo, hi):
    # Choose pivot as median of three
    mid = (lo + hi) // 2
    if arr[lo] > arr[mid]:
        arr[lo], arr[mid] = arr[mid], arr[lo]
    if arr[lo] > arr[hi]:
        arr[lo], arr[hi] = arr[hi], arr[lo]
    if arr[mid] > arr[hi]:
        arr[mid], arr[hi] = arr[hi], arr[mid]
    # Use mid as pivot, move to hi-1
    pivot_val = arr[mid]
    arr[mid], arr[hi - 1] = arr[hi - 1], arr[mid]
    pivot_pos = hi - 1
    i = lo
    j = hi - 1
    while True:
        i += 1
        while arr[i] < pivot_val:
            i += 1
        j -= 1
        while arr[j] > pivot_val:
            j -= 1
        if i >= j:
            break
        arr[i], arr[j] = arr[j], arr[i]
    arr[i], arr[pivot_pos] = arr[pivot_pos], arr[i]
    return i

def quickselect(arr, lo, hi, k):
    if lo == hi:
        return arr[lo]
    if hi - lo == 1:
        if arr[lo] > arr[hi]:
            arr[lo], arr[hi] = arr[hi], arr[lo]
        return arr[k]
    pivot_idx = partition(arr, lo, hi)
    # CORRECT: k <= pivot_idx means k is at or left of pivot
    if k <= pivot_idx:
        if k == pivot_idx:
            return arr[pivot_idx]
        return quickselect(arr, lo, pivot_idx - 1, k)
    else:
        return quickselect(arr, pivot_idx + 1, hi, k)

nums = list(NUMS)
n = len(nums)
k = K % n
arr = list(nums)
result = quickselect(arr, 0, n - 1, k)
"""

BUGGY = r"""
# Quickselect algorithm for k-th smallest element
# Uses Hoare-style partitioning with median-of-three pivot
import random

def partition(arr, lo, hi):
    # Choose pivot as median of three
    mid = (lo + hi) // 2
    if arr[lo] > arr[mid]:
        arr[lo], arr[mid] = arr[mid], arr[lo]
    if arr[lo] > arr[hi]:
        arr[lo], arr[hi] = arr[hi], arr[lo]
    if arr[mid] > arr[hi]:
        arr[mid], arr[hi] = arr[hi], arr[mid]
    # Use mid as pivot, move to hi-1
    pivot_val = arr[mid]
    arr[mid], arr[hi - 1] = arr[hi - 1], arr[mid]
    pivot_pos = hi - 1
    i = lo
    j = hi - 1
    while True:
        i += 1
        while arr[i] < pivot_val:
            i += 1
        j -= 1
        while arr[j] > pivot_val:
            j -= 1
        if i >= j:
            break
        arr[i], arr[j] = arr[j], arr[i]
    arr[i], arr[pivot_pos] = arr[pivot_pos], arr[i]
    return i

def quickselect(arr, lo, hi, k):
    if lo == hi:
        return arr[lo]
    if hi - lo == 1:
        if arr[lo] > arr[hi]:
            arr[lo], arr[hi] = arr[hi], arr[lo]
        return arr[k]
    pivot_idx = partition(arr, lo, hi)
    # BUG: uses k < pivot_idx, missing the case k == pivot_idx
    # When k == pivot_idx, element is already at correct position
    # but this recurses into left subarray unnecessarily
    if k < pivot_idx:
        return quickselect(arr, lo, pivot_idx - 1, k)
    else:
        return quickselect(arr, pivot_idx + 1, hi, k)

nums = list(NUMS)
n = len(nums)
k = K % n
arr = list(nums)
result = quickselect(arr, 0, n - 1, k)
"""


def SPEC(nums, k, result):
    # The result should be the k-th smallest element (0-indexed)
    if not nums:
        return True
    n = len(nums)
    ki = k % n
    sorted_nums = sorted(nums)
    expected = sorted_nums[ki]
    return result == expected


BUG_DESC = (
    "After partition, uses k < pivot_idx instead of k <= pivot_idx. "
    "When k equals the pivot position, the element is already in place "
    "but the buggy code recurses into the right subarray (pivot_idx+1..hi), "
    "returning a wrong element."
)


def _gen_nums():
    import random
    n = random.randint(5, 20)
    return [random.randint(-50, 50) for _ in range(n)]


def _gen_k():
    import random
    return random.randint(0, 15)


INPUT_OVERRIDES = {"NUMS": _gen_nums, "K": _gen_k}
