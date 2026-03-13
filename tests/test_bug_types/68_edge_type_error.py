"""Edge-case TYPE_ERROR: mixed operands, string arithmetic, list addition."""

BUG_TYPE = "TYPE_ERROR"
BUG_DESC = "Type error in edge-case operator patterns"

EXAMPLES = [
    (
        "string_minus",
        # buggy: subtraction on string operands
        '''\
def diff_labels(a, b):
    return a - b
''',
        # safe: isinstance guard
        '''\
def diff_labels(a, b):
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return a - b
    return 0
''',
        "Subtraction on possibly-string operands",
    ),
    (
        "concat_mixed",
        # buggy: addition of possibly mismatched types
        '''\
def build_label(prefix, count):
    return prefix + count
''',
        # safe: isinstance guard
        '''\
def build_label(prefix, count):
    if isinstance(count, str):
        return prefix + count
    return prefix + str(count)
''',
        "Addition of possibly mismatched string and int types",
    ),
    (
        "multiply_types",
        # buggy: multiplication of possibly incompatible types
        '''\
def scale(factor, base):
    return factor * base
''',
        # safe: isinstance guard
        '''\
def scale(factor, base):
    if not isinstance(factor, (int, float)):
        raise TypeError("factor must be numeric")
    return factor * base
''',
        "Multiplication of possibly incompatible types",
    ),
]
