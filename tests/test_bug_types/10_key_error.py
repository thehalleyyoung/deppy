"""KEY_ERROR: dictionary key missing — sheaf stalk has no `has_key` section."""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Dictionary key error"

EXAMPLES = [
    (
        "config_lookup",
        # buggy: direct key access on dict from unknown source
        '''\
def get_setting(config, name):
    return config[name]
''',
        # safe: .get() with default provides a fallback section
        '''\
def get_setting(config, name):
    return config.get(name, None)
''',
        "Direct dict[key] without membership check",
    ),
    (
        "nested_dict",
        # buggy: nested access without checking intermediate keys
        '''\
def get_nested(data, section, key):
    return data[section][key]
''',
        # safe: early-return guards ensure each key exists before access
        '''\
def get_nested(data, section, key):
    if section not in data:
        return None
    sub = data[section]
    if key not in sub:
        return None
    return sub[key]
''',
        "Nested dict access without key checks",
    ),
    (
        "counter_update",
        # buggy: assume key exists in counter dict
        '''\
def increment(counts, item):
    counts[item] += 1
    return counts
''',
        # safe: use .get() to provide default
        '''\
def increment(counts, item):
    counts[item] = counts.get(item, 0) + 1
    return counts
''',
        "Counter update assumes key present",
    ),
]
