"""Harder INDEX_OOB: computed indices, loop access, emptiness guards."""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Index out of bounds in complex patterns"

EXAMPLES = [
    (
        "second_largest",
        # buggy: assumes at least 2 elements
        '''\
def second_largest(numbers):
    sorted_nums = sorted(numbers, reverse=True)
    return sorted_nums[1]
''',
        # safe: check length first
        '''\
def second_largest(numbers):
    sorted_nums = sorted(numbers, reverse=True)
    if len(sorted_nums) < 2:
        return None
    return sorted_nums[1]
''',
        "Access index 1 without checking list has >= 2 elements",
    ),
    (
        "midpoint_value",
        # buggy: empty list makes mid = 0 but list empty
        '''\
def midpoint_value(data):
    mid = len(data) // 2
    return data[mid]
''',
        # safe: emptiness guard
        '''\
def midpoint_value(data):
    if not data:
        return None
    mid = len(data) // 2
    return data[mid]
''',
        "Computed midpoint index on possibly empty list",
    ),
    (
        "circular_next",
        # buggy: modular index on empty sequence
        '''\
def circular_next(items, current_idx):
    nxt = (current_idx + 1) % len(items)
    return items[nxt]
''',
        # safe: check items is non-empty
        '''\
def circular_next(items, current_idx):
    if not items:
        return None
    nxt = (current_idx + 1) % len(items)
    return items[nxt]
''',
        "Modular index access on potentially empty sequence",
    ),
]
