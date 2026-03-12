"""ASSERT_FAIL: Assertion failure — refinement gap.

Required section: {cond : bool | cond is True}
"""

BUG_TYPE = "ASSERT_FAIL"

BUGGY_A = r"""
def process_batch(items, batch_size):
    assert batch_size > 0
    chunks = []
    for i in range(0, len(items), batch_size):
        chunks.append(items[i:i + batch_size])
    return chunks
"""

SAFE_A = r"""
def process_batch(items, batch_size):
    if batch_size <= 0:
        raise ValueError("batch_size must be positive")
    chunks = []
    for i in range(0, len(items), batch_size):
        chunks.append(items[i:i + batch_size])
    return chunks
"""

BUGGY_B = r"""
def matrix_multiply(a, b):
    assert len(a[0]) == len(b)
    rows_a, cols_b = len(a), len(b[0])
    result = [[0] * cols_b for _ in range(rows_a)]
    for i in range(rows_a):
        for j in range(cols_b):
            for k in range(len(b)):
                result[i][j] += a[i][k] * b[k][j]
    return result
"""

SAFE_B = r"""
def matrix_multiply(a, b):
    if len(a[0]) != len(b):
        raise ValueError("incompatible dimensions")
    rows_a, cols_b = len(a), len(b[0])
    result = [[0] * cols_b for _ in range(rows_a)]
    for i in range(rows_a):
        for j in range(cols_b):
            for k in range(len(b)):
                result[i][j] += a[i][k] * b[k][j]
    return result
"""

BUGGY_C = r"""
def pop_min(heap):
    assert len(heap) > 0
    return heap.pop(0)
"""

SAFE_C = r"""
def pop_min(heap):
    if len(heap) == 0:
        raise IndexError("pop from empty heap")
    return heap.pop(0)
"""

EXAMPLES = [
    ("batch_assert", BUGGY_A, SAFE_A, "Uses assert for input validation"),
    ("matmul_assert", BUGGY_B, SAFE_B, "Uses assert for dimension check"),
    ("heap_assert", BUGGY_C, SAFE_C, "Uses assert for non-empty check"),
]

BUG_DESC = "Assert used for input validation; stripped under -O."
