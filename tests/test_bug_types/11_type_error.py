"""TYPE_ERROR: carrier mismatch — the operation site requires a specific
type carrier, but the presheaf section at the argument site carries an
incompatible type.
"""

BUG_TYPE = "TYPE_ERROR"
BUG_DESC = "Type error on operator / builtin"

EXAMPLES = [
    (
        "subtract_unguarded",
        # buggy: subtraction on unknown-type params — no type guard
        '''\
def diff(a, b):
    return a - b
''',
        # safe: isinstance guard certifies numeric carrier
        '''\
def diff(a, b):
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return a - b
    return None
''',
        "Operator requires compatible carriers; isinstance guard resolves",
    ),
    (
        "multiply_unguarded",
        # buggy: multiplication on unknown types
        '''\
def scale(value, factor):
    return value * factor
''',
        # safe: isinstance guard before operator
        '''\
def scale(value, factor):
    if isinstance(value, (int, float)) and isinstance(factor, (int, float)):
        return value * factor
    return 0
''',
        "Multiplication with unknown carrier needs type guard",
    ),
    (
        "add_try_except",
        # buggy: add on unknown types
        '''\
def combine(a, b):
    return a + b
''',
        # safe: try/except TypeError catches carrier mismatch
        '''\
def combine(a, b):
    try:
        return a + b
    except TypeError:
        return None
''',
        "try/except TypeError guards carrier mismatch",
    ),
]
