"""Tricky TYPE_ERROR: binary ops on mixed types."""

BUG_TYPE = "TYPE_ERROR"
BUG_DESC = "Tricky type error with mixed-type arithmetic"

EXAMPLES = [
    (
        "string_minus_int",
        # buggy: string minus integer
        '''\
def compute_diff(label, offset):
    return label - offset
''',
        # safe: convert first
        '''\
def compute_diff(label, offset):
    return int(label) - offset
''',
        "String used in subtraction with integer",
    ),
    (
        "concat_string_int",
        # buggy: string + integer
        '''\
def build_id(prefix, number):
    return prefix + number
''',
        # safe: convert to string
        '''\
def build_id(prefix, number):
    return prefix + str(number)
''',
        "String concatenated with integer via + operator",
    ),
    (
        "multiply_types",
        # buggy: dict * list
        '''\
def scale(config, factors):
    return config * factors
''',
        # safe: type check
        '''\
def scale(config, factors):
    if isinstance(config, (int, float)) and isinstance(factors, (int, float)):
        return config * factors
    return None
''',
        "Multiplication of incompatible types",
    ),
]
