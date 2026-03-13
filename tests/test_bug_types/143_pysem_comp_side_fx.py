"""Python semantics: comprehension with side effects — KEY_ERROR, DIV_ZERO."""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Dict comprehension and conditional dict access"

EXAMPLES = [
    (
        "dictcomp_missing_key",
        # buggy: dict comprehension accesses key that may not exist
        '''\
def invert_mapping(d, keys):
    return {d[k]: k for k in keys}
''',
        # safe: filter to existing keys
        '''\
def invert_mapping(d, keys):
    return {d[k]: k for k in keys if k in d}
''',
        "d[k] raises KeyError if k not in d",
    ),
    (
        "dict_merge_access",
        # buggy: merge dicts then access possibly missing key
        '''\
def combined_lookup(d1, d2, key):
    merged = {**d1, **d2}
    return merged[key]
''',
        # safe: check key
        '''\
def combined_lookup(d1, d2, key):
    merged = {**d1, **d2}
    return merged.get(key, None)
''',
        "key may not be in either d1 or d2",
    ),
    (
        "json_path_access",
        # buggy: nested json access without checking
        '''\
def extract_field(data, field):
    section = data["config"]
    return section[field]
''',
        # safe: guard both levels
        '''\
def extract_field(data, field):
    section = data.get("config", {})
    return section.get(field, None)
''',
        "data['config'] may be missing; section[field] may be missing",
    ),
    (
        "setcomp_key_miss",
        # buggy: set comp uses dict access that may miss
        '''\
def unique_values(records, field):
    return {r[field] for r in records}
''',
        # safe: use .get
        '''\
def unique_values(records, field):
    return {r.get(field) for r in records if field in r}
''',
        "r[field] raises KeyError if field not in record",
    ),
]
