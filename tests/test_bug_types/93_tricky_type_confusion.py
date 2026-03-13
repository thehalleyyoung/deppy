"""Tricky TYPE_CONFUSION: method calls on wrong type."""

BUG_TYPE = "TYPE_CONFUSION"
BUG_DESC = "Tricky type confusion with wrong method calls"

EXAMPLES = [
    (
        "strip_non_string",
        # buggy: strip on integer
        '''\
def clean(value):
    return value.strip()
''',
        # safe: convert to string first
        '''\
def clean(value):
    return str(value).strip()
''',
        "Calling strip() on potentially non-string value",
    ),
    (
        "append_non_list",
        # buggy: append on string
        '''\
def add_item(container, item):
    container.append(item)
    return container
''',
        # safe: type check
        '''\
def add_item(container, item):
    if isinstance(container, list):
        container.append(item)
    return container
''',
        "Calling append() on potentially non-list value",
    ),
    (
        "split_numeric",
        # buggy: split on integer
        '''\
def parse_parts(data):
    return data.split(",")
''',
        # safe: convert to string first
        '''\
def parse_parts(data):
    return str(data).split(",")
''',
        "Calling split() on potentially non-string value",
    ),
    (
        "sort_non_list",
        # buggy: sort on string
        '''\
def order(collection):
    collection.sort()
    return collection
''',
        # safe: type check
        '''\
def order(collection):
    if isinstance(collection, list):
        collection.sort()
    return collection
''',
        "Calling sort() on potentially non-list value",
    ),
]
