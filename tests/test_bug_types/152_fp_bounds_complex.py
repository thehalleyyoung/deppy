"""FP stress: bounds checks before indexing (complex patterns).

Real code often computes bounds in complex ways: clamp-then-index,
min/max-then-index, modular arithmetic, or compare against len().
"""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Complex bounds checks before indexing"

EXAMPLES = [
    (
        "clamp_before_index",
        '''\
def get_clamped(items, idx):
    return items[idx]
''',
        '''\
def get_clamped(items, idx):
    safe_idx = max(0, min(idx, len(items) - 1))
    return items[safe_idx]
''',
        "Clamp index to valid range before access",
    ),
    (
        "modular_index",
        '''\
def circular_get(ring, pos):
    return ring[pos]
''',
        '''\
def circular_get(ring, pos):
    if not ring:
        return None
    return ring[pos % len(ring)]
''',
        "Modular arithmetic + emptiness check ensures valid index",
    ),
    (
        "enumerate_safe",
        '''\
def find_idx(items, target):
    for item in items:
        if item == target:
            return items.index(item)
    return items[len(items)]
''',
        '''\
def find_idx(items, target):
    for i, item in enumerate(items):
        if item == target:
            return i
    return -1
''',
        "enumerate gives indices within bounds by construction",
    ),
    (
        "range_len_iteration",
        '''\
def sum_pairs(items):
    total = 0
    for i in range(len(items)):
        total += items[i] + items[i + 1]
    return total
''',
        '''\
def sum_pairs(items):
    total = 0
    for i in range(len(items) - 1):
        total += items[i] + items[i + 1]
    return total
''',
        "range(len-1) ensures i+1 is within bounds",
    ),
    (
        "len_check_before_pop",
        '''\
def pop_first(stack):
    return stack.pop(0)
''',
        '''\
def pop_first(stack):
    if len(stack) > 0:
        return stack.pop(0)
    return None
''',
        "Length check before pop prevents IndexError",
    ),
]
