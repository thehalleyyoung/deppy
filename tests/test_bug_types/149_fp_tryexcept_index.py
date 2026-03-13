"""FP stress: try/except wrapping index and key operations.

When IndexError / KeyError is caught, the corresponding INDEX_OOB /
KEY_ERROR bug is handled.  The exception handler site covers the
obstruction in the sheaf section.
"""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Try/except handling index errors"

EXAMPLES = [
    (
        "try_except_indexerror",
        '''\
def get_first(items):
    return items[0]
''',
        '''\
def get_first(items):
    try:
        return items[0]
    except IndexError:
        return None
''',
        "IndexError caught for out-of-bounds access",
    ),
    (
        "try_except_negative_index",
        '''\
def get_last(items):
    return items[-1]
''',
        '''\
def get_last(items):
    try:
        return items[-1]
    except IndexError:
        return None
''',
        "Negative index covered by try/except IndexError",
    ),
    (
        "try_except_lookuperror_base",
        '''\
def get_item(seq, idx):
    return seq[idx]
''',
        '''\
def get_item(seq, idx):
    try:
        return seq[idx]
    except LookupError:
        return None
''',
        "LookupError base class covers both IndexError and KeyError",
    ),
    (
        "try_except_slice_safe",
        '''\
def get_chunk(data, start, end):
    chunk = data[start:end]
    return chunk[0]
''',
        '''\
def get_chunk(data, start, end):
    chunk = data[start:end]
    if chunk:
        return chunk[0]
    return None
''',
        "Emptiness check after slicing guards index access",
    ),
    (
        "try_except_multiple_indices",
        '''\
def get_pair(matrix, row, col):
    return matrix[row][col]
''',
        '''\
def get_pair(matrix, row, col):
    try:
        return matrix[row][col]
    except (IndexError, TypeError):
        return None
''',
        "Double index covered by single try/except",
    ),
]
