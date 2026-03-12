"""BOUNDS: Bounds violation — refinement gap.

Required section: {i : int | 0 ≤ i < len(seq)}
"""

BUG_TYPE = "INDEX_OOB"

BUGGY_A = r"""
def get_neighbor_pair(grid, row, col):
    current = grid[row][col]
    right = grid[row][col + 1]
    return current, right
"""

SAFE_A = r"""
def get_neighbor_pair(grid, row, col):
    current = grid[row][col]
    if col + 1 < len(grid[row]):
        right = grid[row][col + 1]
    else:
        right = None
    return current, right
"""

BUGGY_B = r"""
def sliding_window_max(arr, k):
    results = []
    for i in range(len(arr)):
        window = arr[i:i + k]
        results.append(max(window))
    results.append(arr[len(arr)])
    return results
"""

SAFE_B = r"""
def sliding_window_max(arr, k):
    results = []
    for i in range(len(arr) - k + 1):
        window = arr[i:i + k]
        results.append(max(window))
    return results
"""

BUGGY_C = r"""
def swap_first_last(lst):
    tmp = lst[0]
    lst[0] = lst[len(lst) - 1]
    lst[len(lst) - 1] = tmp
    return lst
"""

SAFE_C = r"""
def swap_first_last(lst):
    if len(lst) < 2:
        return lst
    tmp = lst[0]
    lst[0] = lst[len(lst) - 1]
    lst[len(lst) - 1] = tmp
    return lst
"""

EXAMPLES = [
    ("grid_neighbor", BUGGY_A, SAFE_A, "col+1 may exceed row length"),
    ("window_oob", BUGGY_B, SAFE_B, "arr[len(arr)] is out of bounds"),
    ("swap_empty", BUGGY_C, SAFE_C, "lst[0] on empty list"),
]

BUG_DESC = "Index access that may exceed sequence bounds."
