"""Edge-case INDEX_OOB: computed index, negative index, len-based access."""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Index out of bounds in edge-case patterns"

EXAMPLES = [
    (
        "last_element_access",
        # buggy: accessing last element of possibly-empty list
        '''\
def get_last(items):
    return items[-1]
''',
        # safe: length check
        '''\
def get_last(items):
    if len(items) == 0:
        return None
    return items[-1]
''',
        "Negative index on possibly-empty sequence",
    ),
    (
        "computed_offset",
        # buggy: computed index may exceed bounds
        '''\
def get_neighbor(data, pos, offset):
    idx = pos + offset
    return data[idx]
''',
        # safe: bounds check
        '''\
def get_neighbor(data, pos, offset):
    idx = pos + offset
    if idx >= len(data):
        return None
    return data[idx]
''',
        "Computed index may exceed array bounds",
    ),
    (
        "midpoint_access",
        # buggy: access at computed midpoint
        '''\
def get_middle(values):
    mid = len(values) // 2
    return values[mid]
''',
        # safe: length check for empty
        '''\
def get_middle(values):
    if len(values) == 0:
        return None
    mid = len(values) // 2
    return values[mid]
''',
        "Midpoint access on possibly-empty sequence",
    ),
    (
        "second_element",
        # buggy: accessing index 1 on possibly-short list
        '''\
def get_second(items):
    return items[1]
''',
        # safe: length check
        '''\
def get_second(items):
    if len(items) <= 1:
        return None
    return items[1]
''',
        "Fixed index access on possibly-short list",
    ),
]
