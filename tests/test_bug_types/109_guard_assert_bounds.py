"""Guard stress: assert-based INDEX_OOB and BOUNDS guards.

`assert len(items) > idx` introduces a covering sieve restriction
that ensures the index is within bounds.  The continuation carries
a valid-index section.
"""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Assert-based bounds guards"

EXAMPLES = [
    (
        "assert_len_gt_index",
        # buggy: index without bounds check
        '''\
def get_element(items, idx):
    data = items
    i = idx
    return data[i]
''',
        # safe: assert ensures bounds
        '''\
def get_element(items, idx):
    assert len(items) > idx
    return items[idx]
''',
        "Assert len > idx before indexing",
    ),
    (
        "assert_nonempty",
        # buggy: access first without check
        '''\
def head(lst):
    items = lst
    return items[0]
''',
        # safe: assert non-empty
        '''\
def head(lst):
    items = lst
    assert len(items) > 0
    return items[0]
''',
        "Assert non-empty before index 0",
    ),
    (
        "assert_two_elements",
        # buggy: access second element without check
        '''\
def pair(data):
    items = data
    return items[0], items[1]
''',
        # safe: assert at least 2 elements
        '''\
def pair(data):
    items = data
    assert len(items) >= 2
    return items[0], items[1]
''',
        "Assert >= 2 before indices 0 and 1",
    ),
]
