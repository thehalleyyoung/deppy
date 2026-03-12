"""Hard INDEX_OOB examples — computed indices, boundary access, post-mutation."""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Index out of bounds in harder patterns"

EXAMPLES = [
    (
        "neighbor_pair",
        # buggy: access i+1 without checking it's in range
        '''\
def pairwise_diff(arr):
    diffs = []
    for i in range(len(arr)):
        diffs.append(arr[i + 1] - arr[i])
    return diffs
''',
        # safe: explicit guard on i+1 within bounds
        '''\
def pairwise_diff(arr):
    diffs = []
    for i in range(len(arr)):
        if i + 1 < len(arr):
            diffs.append(arr[i + 1] - arr[i])
    return diffs
''',
        "Accessing arr[i+1] inside range(len(arr)) goes one past end",
    ),
    (
        "last_elem",
        # buggy: access last element of possibly empty list
        '''\
def get_last(items):
    return items[len(items) - 1]
''',
        # safe: guard emptiness
        '''\
def get_last(items):
    if len(items) > 0:
        return items[len(items) - 1]
    return None
''',
        "Accessing items[len-1] on empty list gives index -1 wrapping to error",
    ),
    (
        "neg_index_param",
        # buggy: negative index from parameter may exceed list length
        '''\
def from_end(data, offset):
    return data[-offset]
''',
        # safe: clamp the offset
        '''\
def from_end(data, offset):
    if offset > len(data):
        return None
    return data[-offset]
''',
        "Negative index from parameter may exceed list length",
    ),
]
