"""FP stress: standard-library return-type guarantees.

Calls to well-known stdlib functions have guaranteed return types.
E.g., str.split() always returns list[str] (never None), len() returns
int, dict.keys() returns a view.  Deppy must not fire NULL_PTR /
TYPE_ERROR on these.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Stdlib return guarantees prevent None"

EXAMPLES = [
    (
        "str_split_never_none",
        '''\
def first_word(text):
    parts = text
    return parts[0].upper()
''',
        '''\
def first_word(text):
    parts = text.split()
    if parts:
        return parts[0].upper()
    return ""
''',
        "split() returns list (never None); emptiness checked",
    ),
    (
        "sorted_returns_list",
        '''\
def smallest(data):
    s = data
    return s[0]
''',
        '''\
def smallest(data):
    s = sorted(data)
    if s:
        return s[0]
    return None
''',
        "sorted() always returns a list",
    ),
    (
        "str_format_returns_str",
        '''\
def greet(name):
    msg = name
    return msg.encode()
''',
        '''\
def greet(name):
    msg = "Hello, {}".format(name)
    return msg.encode()
''',
        "str.format() always returns str",
    ),
    (
        "dict_get_with_default",
        '''\
def lookup(config, key):
    val = config.get(key)
    return val + 1
''',
        '''\
def lookup(config, key):
    val = config.get(key, 0)
    return val + 1
''',
        "dict.get with default never returns None",
    ),
    (
        "list_comprehension_returns_list",
        '''\
def doubled(data):
    result = data
    return result[0]
''',
        '''\
def doubled(data):
    result = [x * 2 for x in data]
    if result:
        return result[0]
    return 0
''',
        "List comprehension always returns a list",
    ),
]
