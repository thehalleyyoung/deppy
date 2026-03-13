"""Tricky INDEX_OOB: computed index, negative index, pop on empty."""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Tricky out-of-bounds index access patterns"

EXAMPLES = [
    (
        "last_element_direct",
        # buggy: direct negative index on potentially empty list
        '''\
def last_item(items):
    return items[-1]
''',
        # safe: guard length
        '''\
def last_item(items):
    if len(items) == 0:
        return None
    return items[-1]
''',
        "Negative index on possibly empty list",
    ),
    (
        "constant_index",
        # buggy: constant index may be out of bounds
        '''\
def third(items):
    return items[2]
''',
        # safe: check length
        '''\
def third(items):
    if len(items) < 3:
        return None
    return items[2]
''',
        "Constant index on list of unknown length",
    ),
    (
        "midpoint_access",
        # buggy: midpoint of potentially empty list
        '''\
def middle(items):
    mid = len(items) // 2
    return items[mid]
''',
        # safe: guard on non-empty
        '''\
def middle(items):
    if len(items) == 0:
        return None
    mid = len(items) // 2
    return items[mid]
''',
        "Midpoint index on possibly empty list",
    ),
    (
        "second_element",
        # buggy: fixed index 1 on short list
        '''\
def get_second(data):
    return data[1]
''',
        # safe: length guard
        '''\
def get_second(data):
    if len(data) >= 2:
        return data[1]
    return None
''',
        "Fixed index 1 on potentially short list",
    ),
]
