"""Edge-case TYPE_CONFUSION: method calls on wrong receiver type."""

BUG_TYPE = "TYPE_CONFUSION"
BUG_DESC = "Type confusion calling methods on wrong type"

EXAMPLES = [
    (
        "strip_non_string",
        # buggy: calling .strip() on possibly-non-string
        '''\
def clean_input(value):
    return value.strip()
''',
        # safe: isinstance check first
        '''\
def clean_input(value):
    if isinstance(value, str):
        return value.strip()
    return str(value).strip()
''',
        "Calling str method on possibly non-string value",
    ),
    (
        "append_to_non_list",
        # buggy: calling .append() on possibly-non-list
        '''\
def add_item(collection, item):
    collection.append(item)
''',
        # safe: isinstance guard
        '''\
def add_item(collection, item):
    if isinstance(collection, list):
        collection.append(item)
''',
        "Calling list method on possibly non-list value",
    ),
    (
        "split_numeric",
        # buggy: calling .split() on possibly numeric value
        '''\
def parse_tokens(raw):
    parts = raw.split(",")
    return parts
''',
        # safe: isinstance check
        '''\
def parse_tokens(raw):
    if isinstance(raw, str):
        parts = raw.split(",")
        return parts
    return []
''',
        "Calling .split() on possibly non-string input",
    ),
    (
        "sort_non_list",
        # buggy: calling .sort() on possibly-non-list
        '''\
def order_items(data):
    data.sort()
    return data
''',
        # safe: isinstance guard
        '''\
def order_items(data):
    if isinstance(data, list):
        data.sort()
    return data
''',
        "Calling .sort() on possibly non-list value",
    ),
]
