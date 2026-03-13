"""Python semantics: dict operations — KEY_ERROR, NULL_PTR, TYPE_ERROR."""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Dictionary access patterns and missing keys"

EXAMPLES = [
    (
        "dict_pop_keyerror",
        # buggy: pop without default on possibly missing key
        '''\
def remove_key(d, key):
    removed = d.pop(key)
    return removed
''',
        # safe: pop with default
        '''\
def remove_key(d, key):
    removed = d.pop(key, None)
    return removed
''',
        "d.pop(key) raises KeyError if key missing",
    ),
    (
        "dict_update_access",
        # buggy: update then access key that wasn't in update
        '''\
def merge_and_get(base, extra, key):
    merged = {}
    merged.update(base)
    return merged[key]
''',
        # safe: check key
        '''\
def merge_and_get(base, extra, key):
    merged = {}
    merged.update(base)
    merged.update(extra)
    return merged.get(key, None)
''',
        "key may not be in base; merged[key] raises KeyError",
    ),
    (
        "nested_dict_access",
        # buggy: chain of dict accesses, inner may miss
        '''\
def deep_get(config, section, key):
    return config[section][key]
''',
        # safe: guard both levels
        '''\
def deep_get(config, section, key):
    if section in config:
        return config[section].get(key, None)
    return None
''',
        "config[section] or inner [key] may raise KeyError",
    ),
    (
        "dict_literal_missing_key",
        # buggy: access key that was never set
        '''\
def lookup(kind):
    table = {"a": 1, "b": 2}
    return table[kind]
''',
        # safe: use .get with default
        '''\
def lookup(kind):
    table = {"a": 1, "b": 2}
    return table.get(kind, 0)
''',
        "table[kind] may raise KeyError if kind not in {a, b}",
    ),
]
