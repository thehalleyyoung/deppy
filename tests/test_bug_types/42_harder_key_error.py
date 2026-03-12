"""Harder KEY_ERROR: computed keys, nested dicts, compound membership guards."""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Key error in complex dict access patterns"

EXAMPLES = [
    (
        "config_cascade",
        # buggy: override dict may not have the key
        '''\
def get_setting(defaults, overrides, key):
    if key in overrides:
        return overrides[key]
    return defaults[key]
''',
        # safe: check both dicts
        '''\
def get_setting(defaults, overrides, key):
    if key in overrides:
        return overrides[key]
    if key in defaults:
        return defaults[key]
    return None
''',
        "Dict access where fallback dict may also lack the key",
    ),
    (
        "aggregate_by_group",
        # buggy: first access to group key without initialization
        '''\
def aggregate(items, key_fn, val_fn):
    groups = {}
    for item in items:
        k = key_fn(item)
        groups[k] += val_fn(item)
    return groups
''',
        # safe: use .get() with default to avoid KeyError
        '''\
def aggregate(items, key_fn, val_fn):
    groups = {}
    for item in items:
        k = key_fn(item)
        groups[k] = groups.get(k, 0) + val_fn(item)
    return groups
''',
        "AugAssign on dict key that may not exist yet",
    ),
    (
        "cross_reference",
        # buggy: second dict may not have matching key
        '''\
def cross_ref(names, scores):
    results = []
    for name in names:
        s = scores[name]
        results.append((name, s))
    return results
''',
        # safe: membership guard inside loop
        '''\
def cross_ref(names, scores):
    results = []
    for name in names:
        if name in scores:
            s = scores[name]
            results.append((name, s))
    return results
''',
        "Dict access with key from another collection that may not be present",
    ),
]
