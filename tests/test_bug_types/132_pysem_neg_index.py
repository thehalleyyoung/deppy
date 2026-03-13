"""Python semantics: slice and negative indexing — INDEX_OOB, BOUNDS."""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Complex indexing with negative indices and computed offsets"

EXAMPLES = [
    (
        "negative_index_empty",
        # buggy: negative index on potentially empty list
        '''\
def last_element(items):
    data = list(items)
    return data[-1]
''',
        # safe: guard empty
        '''\
def last_element(items):
    data = list(items)
    if data:
        return data[-1]
    return None
''',
        "data may be empty; data[-1] is OOB on empty list",
    ),
    (
        "computed_negative_index",
        # buggy: computed negative index may go past start
        '''\
def get_nth_from_end(seq, n):
    data = list(seq)
    return data[-n]
''',
        # safe: bounds check
        '''\
def get_nth_from_end(seq, n):
    data = list(seq)
    if 0 < n <= len(data):
        return data[-n]
    return None
''',
        "n may exceed len(data); data[-n] wraps incorrectly or OOB",
    ),
    (
        "double_index_chain",
        # buggy: chain of indexes, inner result may be empty
        '''\
def nested_access(matrix, row, col):
    data = list(matrix)
    r = data[row]
    items = list(r)
    return items[col]
''',
        # safe: bounds check both
        '''\
def nested_access(matrix, row, col):
    data = list(matrix)
    if row < len(data):
        r = data[row]
        items = list(r)
        if col < len(items):
            return items[col]
    return None
''',
        "row or col may be OOB",
    ),
]
