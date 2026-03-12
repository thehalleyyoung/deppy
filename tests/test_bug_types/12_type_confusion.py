"""TYPE_CONFUSION: method call requires a specific carrier type but the
object's presheaf section does not provably carry that type.
"""

BUG_TYPE = "TYPE_CONFUSION"
BUG_DESC = "Type confusion on method call"

EXAMPLES = [
    (
        "upper_on_any",
        # buggy: .upper() on unknown-type parameter
        '''\
def normalize(data):
    return data.upper()
''',
        # safe: explicit str() ensures carrier = str
        '''\
def normalize(data):
    return str(data).upper()
''',
        ".upper() requires carrier(obj) = str",
    ),
    (
        "append_on_any",
        # buggy: .append() on unknown-type parameter
        '''\
def add_item(collection, item):
    collection.append(item)
    return collection
''',
        # safe: isinstance guard verifies carrier = list
        '''\
def add_item(collection, item):
    if isinstance(collection, list):
        collection.append(item)
    return collection
''',
        ".append() requires carrier(obj) = list",
    ),
    (
        "split_on_any",
        # buggy: .split() on unknown-type parameter
        '''\
def tokenize(text):
    return text.split()
''',
        # safe: str() coercion
        '''\
def tokenize(text):
    return str(text).split()
''',
        ".split() requires carrier(obj) = str",
    ),
]
