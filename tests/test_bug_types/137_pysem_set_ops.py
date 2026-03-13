"""Python semantics: set and frozenset operations — KEY_ERROR, TYPE_ERROR."""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Set operations and missing element access patterns"

EXAMPLES = [
    (
        "set_remove_missing",
        # buggy: set.remove raises KeyError if missing
        '''\
def cleanup(items, to_remove):
    s = set(items)
    for r in to_remove:
        s.remove(r)
    return s
''',
        # safe: use discard
        '''\
def cleanup(items, to_remove):
    s = set(items)
    for r in to_remove:
        s.discard(r)
    return s
''',
        "s.remove(r) raises KeyError if r not in s",
    ),
    (
        "dict_keyview_access",
        # buggy: iterate key view then access dict
        '''\
def first_key_value(d, required_key):
    return d[required_key]
''',
        # safe: check membership
        '''\
def first_key_value(d, required_key):
    if required_key in d:
        return d[required_key]
    return None
''',
        "required_key may not be in d",
    ),
    (
        "pop_from_empty",
        # buggy: pop from potentially empty set/dict
        '''\
def drain_set(s):
    results = []
    item = s.pop()
    results.append(item)
    return results
''',
        # safe: guard empty
        '''\
def drain_set(s):
    results = []
    if s:
        item = s.pop()
        results.append(item)
    return results
''',
        "s.pop() on empty set raises KeyError",
    ),
]
