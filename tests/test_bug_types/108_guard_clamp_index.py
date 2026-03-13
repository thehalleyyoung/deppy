"""Guard stress: min/max clamping as INDEX_OOB/BOUNDS guards.

Clamping via min(idx, len(seq)-1) or max(0, idx) creates a
section in the valid-index sub-presheaf [0, len(seq)).  The
restriction map from this section to the INDEX_OOB requirement
is total — no gluing obstruction.
"""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Min/max clamping guards for indexing"

EXAMPLES = [
    (
        "min_clamp_index",
        # buggy: index may exceed length
        '''\
def get_at(items, idx):
    i = idx
    return items[i]
''',
        # safe: clamp to valid range
        '''\
def get_at(items, idx):
    i = min(idx, len(items) - 1)
    return items[i]
''',
        "min() clamp creates valid-index section",
    ),
    (
        "max_clamp_index",
        # buggy: negative index may wrap incorrectly
        '''\
def get_at_safe(items, idx):
    i = idx
    return items[i]
''',
        # safe: max(0, idx) ensures non-negative
        '''\
def get_at_safe(items, idx):
    i = max(0, idx)
    return items[i]
''',
        "max(0, ...) ensures non-negative index",
    ),
    (
        "double_clamp",
        # buggy: index completely unchecked
        '''\
def clamped_get(arr, pos):
    p = pos
    return arr[p]
''',
        # safe: double clamp to [0, len-1]
        '''\
def clamped_get(arr, pos):
    p = max(0, min(pos, len(arr) - 1))
    return arr[p]
''',
        "Double clamp to valid range",
    ),
]
