"""Tricky DIV_ZERO: stalk-based resolution, truthiness guard, constant divisor."""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Tricky division by zero requiring stalk analysis"

EXAMPLES = [
    (
        "guarded_by_truthiness",
        # buggy: divisor might be zero, no guard
        '''\
def safe_ratio(num, den):
    return num / den
''',
        # safe: truthiness check on divisor
        '''\
def safe_ratio(num, den):
    if den:
        return num / den
    return 0.0
''',
        "Division where truthiness guard makes divisor non-zero",
    ),
    (
        "divisor_from_len",
        # buggy: len() result could be zero
        '''\
def average(items):
    total = sum(items)
    count = len(items)
    return total / count
''',
        # safe: check len before division
        '''\
def average(items):
    total = sum(items)
    count = len(items)
    if count == 0:
        return 0.0
    return total / count
''',
        "Division by len() which could be zero for empty input",
    ),
    (
        "cascaded_div",
        # buggy: chain of divisions
        '''\
def triple_ratio(a, b, c):
    return a / b / c
''',
        # safe: guard both
        '''\
def triple_ratio(a, b, c):
    if b == 0:
        return 0.0
    if c == 0:
        return 0.0
    return a / b / c
''',
        "Cascaded division needing guards on both divisors",
    ),
]
