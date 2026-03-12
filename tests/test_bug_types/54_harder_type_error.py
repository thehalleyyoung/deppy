"""Harder TYPE_ERROR: mixed-type operations from different sources."""

BUG_TYPE = "TYPE_ERROR"
BUG_DESC = "Type error in complex mixed-type operations"

EXAMPLES = [
    (
        "sum_mixed_sources",
        # buggy: concatenating string config value with int
        '''\
def build_message(config, count):
    prefix = config.get("prefix")
    return prefix + count
''',
        # safe: isinstance guard ensures compatible types
        '''\
def build_message(config, count):
    prefix = config.get("prefix")
    if isinstance(prefix, str):
        return prefix + str(count)
    return str(count)
''',
        "Adding string from config to integer without type check",
    ),
    (
        "accumulate_values",
        # buggy: initial value is string, loop adds numbers
        '''\
def total_scores(scores):
    result = ""
    for s in scores:
        result = result + s
    return result
''',
        # safe: ensure type consistency via isinstance
        '''\
def total_scores(scores):
    result = 0
    for s in scores:
        if isinstance(s, int):
            result = result + s
    return result
''',
        "Accumulator initialized as string but loop values may be numeric",
    ),
    (
        "merge_values",
        # buggy: subtracting possibly incompatible types
        '''\
def compute_delta(current, previous):
    delta = current - previous
    return delta
''',
        # safe: isinstance guard
        '''\
def compute_delta(current, previous):
    if isinstance(current, (int, float)):
        delta = current - previous
        return delta
    return None
''',
        "Subtraction of values with potentially incompatible types",
    ),
]
