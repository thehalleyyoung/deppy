"""Python semantics: unpacking — INDEX_OOB, VALUE_ERROR, TYPE_ERROR."""

BUG_TYPE = "VALUE_ERROR"
BUG_DESC = "Unpacking errors from wrong number of values"

EXAMPLES = [
    (
        "tuple_unpack_too_few",
        # buggy: unpack 3 from potentially 2-element tuple
        '''\
def parse_coord(text):
    parts = text.split(",")
    x, y, z = parts
    return float(x)
''',
        # safe: check length
        '''\
def parse_coord(text):
    parts = text.split(",")
    if len(parts) == 3:
        x, y, z = parts
        return float(x)
    return 0.0
''',
        "split may return != 3 parts; ValueError on unpack",
    ),
    (
        "star_unpack_empty_rest",
        # buggy: star unpack then index rest
        '''\
def head_tail(items):
    first, *rest = items
    return rest[0]
''',
        # safe: check rest non-empty
        '''\
def head_tail(items):
    first, *rest = items
    if rest:
        return rest[0]
    return first
''',
        "rest may be empty; rest[0] is INDEX_OOB but declared VALUE_ERROR for unpack context",
    ),
    (
        "nested_unpack",
        # buggy: nested unpacking with wrong structure
        '''\
def parse_pairs(data):
    results = []
    for item in data:
        (a, b), c = item
        results.append(a + b + c)
    return results
''',
        # safe: try/except for structure mismatch
        '''\
def parse_pairs(data):
    results = []
    for item in data:
        try:
            (a, b), c = item
            results.append(a + b + c)
        except (TypeError, ValueError):
            pass
    return results
''',
        "item may not match ((_, _), _) structure",
    ),
]
