"""Harder TYPE_CONFUSION: method calls on wrong receiver types."""

BUG_TYPE = "TYPE_CONFUSION"
BUG_DESC = "Type confusion in complex receiver patterns"

EXAMPLES = [
    (
        "sort_input",
        # buggy: calling .sort() on something that might be a string
        '''\
def normalize_input(data):
    cleaned = preprocess(data)
    cleaned.sort()
    return cleaned
''',
        # safe: isinstance guard
        '''\
def normalize_input(data):
    cleaned = preprocess(data)
    if isinstance(cleaned, list):
        cleaned.sort()
    return cleaned
''',
        "Calling list method .sort() on unverified return type",
    ),
    (
        "upper_from_mapping",
        # buggy: value from dict may not be a string
        '''\
def format_name(record, field):
    raw = record.get(field)
    return raw.upper()
''',
        # safe: isinstance check
        '''\
def format_name(record, field):
    raw = record.get(field)
    if isinstance(raw, str):
        return raw.upper()
    return str(raw)
''',
        "Calling .upper() on dict value that may not be a string",
    ),
    (
        "extend_from_source",
        # buggy: source may return non-list, calling .extend()
        '''\
def merge_data(base, source_fn):
    extra = source_fn()
    base.extend(extra)
    return base
''',
        # safe: isinstance guard
        '''\
def merge_data(base, source_fn):
    extra = source_fn()
    if isinstance(extra, list):
        base.extend(extra)
    return base
''',
        "Calling .extend() on result of unknown function",
    ),
]
