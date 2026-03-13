"""FP stress: complex real-world patterns mixing multiple guard types.

These examples combine several guard mechanisms (isinstance + bounds +
try/except + early return) in realistic patterns that a simplistic
analyzer would misclassify.
"""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Real-world complex guard patterns for indexing"

EXAMPLES = [
    (
        "paginated_safe_access",
        '''\
def get_page(items, page_num, page_size):
    start = page_num * page_size
    end = start + page_size
    return [items[i] for i in range(start, end)]
''',
        '''\
def get_page(items, page_num, page_size):
    start = page_num * page_size
    end = min(start + page_size, len(items))
    start = max(0, min(start, len(items)))
    return items[start:end]
''',
        "Clamped start/end + slice (never raises IndexError)",
    ),
    (
        "binary_search_bounds",
        '''\
def binary_search(arr, target):
    lo, hi = 0, len(arr)
    while lo < hi:
        mid = (lo + hi) // 2
        if arr[mid] == target:
            return mid
        elif arr[mid] < target:
            lo = mid + 1
        else:
            hi = mid
    return arr[lo]
''',
        '''\
def binary_search(arr, target):
    lo, hi = 0, len(arr)
    while lo < hi:
        mid = (lo + hi) // 2
        if arr[mid] == target:
            return mid
        elif arr[mid] < target:
            lo = mid + 1
        else:
            hi = mid
    return -1
''',
        "Loop invariant: lo < hi implies mid is valid; return -1 after loop",
    ),
    (
        "sliding_window_safe",
        '''\
def max_window(nums, k):
    best = float('-inf')
    for i in range(len(nums)):
        window_sum = sum(nums[i:i+k])
        best = max(best, window_sum)
    return best
''',
        '''\
def max_window(nums, k):
    if len(nums) < k or k <= 0:
        return 0
    best = sum(nums[:k])
    current = best
    for i in range(k, len(nums)):
        current += nums[i] - nums[i - k]
        best = max(best, current)
    return best
''',
        "Length check + range(k, len) ensures i and i-k in bounds",
    ),
    (
        "matrix_transpose_safe",
        '''\
def transpose(matrix):
    rows = len(matrix)
    cols = len(matrix[0])
    return [[matrix[i][j] for i in range(rows)] for j in range(cols)]
''',
        '''\
def transpose(matrix):
    if not matrix or not matrix[0]:
        return []
    rows = len(matrix)
    cols = len(matrix[0])
    return [[matrix[i][j] for i in range(rows)] for j in range(cols)]
''',
        "Emptiness check before accessing matrix[0] and inner indices",
    ),
    (
        "deque_rotation_safe",
        '''\
def rotate(items, k):
    n = len(items)
    k = k % n
    return items[-k:] + items[:-k]
''',
        '''\
def rotate(items, k):
    if not items:
        return items
    n = len(items)
    k = k % n
    return items[-k:] + items[:-k] if k else items[:]
''',
        "Empty check prevents mod-by-zero; slice is always safe",
    ),
]
