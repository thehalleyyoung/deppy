"""Guard stress: compound conditions protecting multiple bug types.

A compound `and` condition creates a covering sieve where each
conjunct refines a different dimension of the stalk.  All refinements
hold simultaneously on the body's open set.
"""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Compound condition guards"

EXAMPLES = [
    (
        "compound_none_and_zero",
        # buggy: no guards at all
        '''\
def safe_ratio(obj):
    x = obj
    return 100 / x.value
''',
        # safe: compound check guards both NULL_PTR and DIV_ZERO
        '''\
def safe_ratio(obj):
    x = obj
    if x is not None and x.value != 0:
        return 100 / x.value
    return 0
''',
        "Compound guards: None + zero check",
    ),
    (
        "compound_bounds_and_div",
        # buggy: divide by list length without checks
        '''\
def average(numbers):
    items = numbers
    return sum(items) / len(items)
''',
        # safe: truthiness implies non-empty → len > 0
        '''\
def average(numbers):
    items = numbers
    if items and len(items) > 0:
        return sum(items) / len(items)
    return 0
''',
        "Compound: truthiness + len > 0",
    ),
    (
        "compound_isinstance_arith",
        # buggy: divide without type check — might get a non-numeric value
        '''\
def offset(value, delta):
    x = value
    y = delta
    return x / y
''',
        # safe: isinstance guards both operands + nonzero check
        '''\
def offset(value, delta):
    x = value
    y = delta
    if isinstance(x, (int, float)) and isinstance(y, (int, float)) and y != 0:
        return x / y
    return 0
''',
        "Compound isinstance + nonzero guards for division",
    ),
]
