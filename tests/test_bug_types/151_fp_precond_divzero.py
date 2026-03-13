"""FP stress: defensive parameter validation at function entry.

Real-world functions validate inputs at the top and raise/return early.
Everything after the validation block is in the "safe section" of the
sheaf, where the validated predicates hold.
"""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Precondition validation guards division"

EXAMPLES = [
    (
        "raise_on_zero_param",
        '''\
def ratio(a, b):
    return a / b
''',
        '''\
def ratio(a, b):
    if b == 0:
        raise ValueError("b must not be zero")
    return a / b
''',
        "Raise ValueError when b is zero",
    ),
    (
        "return_early_on_zero",
        '''\
def percentage(part, total):
    return (part / total) * 100
''',
        '''\
def percentage(part, total):
    if total == 0:
        return 0.0
    return (part / total) * 100
''',
        "Early return prevents division by zero",
    ),
    (
        "assert_nonzero",
        '''\
def speed(distance, time):
    return distance / time
''',
        '''\
def speed(distance, time):
    assert time != 0, "time must be nonzero"
    return distance / time
''',
        "Assert narrows time to nonzero",
    ),
    (
        "multi_param_validation",
        '''\
def normalize(vec):
    magnitude = sum(x**2 for x in vec) ** 0.5
    return [x / magnitude for x in vec]
''',
        '''\
def normalize(vec):
    if not vec:
        return []
    magnitude = sum(x**2 for x in vec) ** 0.5
    if magnitude == 0:
        return vec
    return [x / magnitude for x in vec]
''',
        "Empty check + zero magnitude check before division",
    ),
    (
        "conditional_divisor_nonzero",
        '''\
def weighted_avg(values, weights):
    total_w = sum(weights)
    return sum(v * w for v, w in zip(values, weights)) / total_w
''',
        '''\
def weighted_avg(values, weights):
    total_w = sum(weights)
    if total_w == 0:
        return 0.0
    return sum(v * w for v, w in zip(values, weights)) / total_w
''',
        "Sum of weights checked before use as divisor",
    ),
]
