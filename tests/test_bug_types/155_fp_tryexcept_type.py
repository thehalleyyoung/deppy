"""FP stress: exception handling for TYPE_ERROR.

try/except TypeError wrapping operations that might fail on wrong types.
The exception handler site covers the type-error obstruction.
"""

BUG_TYPE = "TYPE_ERROR"
BUG_DESC = "Try/except TypeError handling"

EXAMPLES = [
    (
        "try_except_typeerror_add",
        '''\
def combine(a, b):
    return a + b
''',
        '''\
def combine(a, b):
    try:
        return a + b
    except TypeError:
        return str(a) + str(b)
''',
        "TypeError caught, falls back to string concatenation",
    ),
    (
        "try_except_typeerror_iter",
        '''\
def to_list(x):
    return list(x)
''',
        '''\
def to_list(x):
    try:
        return list(x)
    except TypeError:
        return [x]
''',
        "TypeError caught when x is not iterable",
    ),
    (
        "try_except_typeerror_subscript",
        '''\
def get_item(obj, key):
    return obj[key]
''',
        '''\
def get_item(obj, key):
    try:
        return obj[key]
    except (TypeError, KeyError, IndexError):
        return None
''',
        "Multiple exception types caught for subscript",
    ),
    (
        "try_except_typeerror_call",
        '''\
def invoke(fn, arg):
    return fn(arg)
''',
        '''\
def invoke(fn, arg):
    try:
        return fn(arg)
    except TypeError:
        return None
''',
        "TypeError caught when fn is not callable",
    ),
    (
        "try_except_typeerror_comparison",
        '''\
def is_bigger(a, b):
    return a > b
''',
        '''\
def is_bigger(a, b):
    try:
        return a > b
    except TypeError:
        return False
''',
        "TypeError caught when types are not comparable",
    ),
]
