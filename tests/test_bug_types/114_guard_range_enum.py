"""Guard stress: enumerate / range-based loop guards.

When iterating with `for i in range(len(lst)):`, the loop variable `i`
is bounded by `len(lst)` — the loop creates a covering sieve over the
valid-index sub-presheaf.  `lst[i]` inside the loop should carry a
valid-index section.
"""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Range/enumerate loop guards"

EXAMPLES = [
    (
        "range_len_loop",
        # buggy: access first element without check — may be empty
        '''\
def double_all(lst):
    items = lst
    return items[0] * 2
''',
        # safe: range(len()) loop bounds the index
        '''\
def double_all(lst):
    result = []
    for i in range(len(lst)):
        result.append(lst[i] * 2)
    return result
''',
        "range(len()) provides valid-index section",
    ),
    (
        "enumerate_loop",
        # buggy: access element without bounds check
        '''\
def get_pair(data):
    items = data
    return items[0]
''',
        # safe: enumerate provides valid indices
        '''\
def get_pair(data):
    result = []
    for i, val in enumerate(data):
        result.append((i, data[i]))
    return result
''',
        "enumerate() provides valid-index section",
    ),
    (
        "zip_index",
        # buggy: index last element without check
        '''\
def combine(values):
    items = values
    return items[0]
''',
        # safe: enumerate+zip provides bounded index
        '''\
def combine(keys, values):
    result = []
    for i, (k, v) in enumerate(zip(keys, values)):
        result.append(values[i])
    return result
''',
        "Enumerate+zip provides bounded index",
    ),
]
