"""Guard stress: exception handler variants.

A try/except block creates a covering sieve {try-body, handler-body}.
The key question is whether the engine recognizes DIVERSE exception
handler patterns: tuple exceptions, base classes, nested try blocks,
try/except/else, and finally-with-return.
"""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Exception handler variant guards"

EXAMPLES = [
    (
        "except_tuple",
        # buggy: dict access without guard
        '''\
def get_val(data, key):
    d = data
    return d[key]
''',
        # safe: tuple of exception types
        '''\
def get_val(data, key):
    d = data
    try:
        return d[key]
    except (KeyError, TypeError):
        return None
''',
        "Tuple exception handler covers KEY_ERROR",
    ),
    (
        "except_lookup_base",
        # buggy: subscript without guard
        '''\
def lookup(mapping, k):
    m = mapping
    return m[k]
''',
        # safe: LookupError base class covers KeyError + IndexError
        '''\
def lookup(mapping, k):
    m = mapping
    try:
        return m[k]
    except LookupError:
        return None
''',
        "LookupError base class as guard",
    ),
    (
        "except_nested_try",
        # buggy: no guard
        '''\
def deep_get(data, k1, k2):
    d = data
    return d[k1]
''',
        # safe: nested try blocks
        '''\
def deep_get(data, k1, k2):
    d = data
    try:
        try:
            return d[k1]
        except KeyError:
            return d[k2]
    except KeyError:
        return None
''',
        "Nested try/except both guard KEY_ERROR",
    ),
]
