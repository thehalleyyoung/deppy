"""Edge-case DIV_ZERO: floor-div, modulo, chained ops, multi-divisor."""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Division by zero in edge-case patterns"

EXAMPLES = [
    (
        "floor_div_zero",
        # buggy: floor division by parameter that may be zero
        '''\
def page_count(total_items, page_size):
    return total_items // page_size
''',
        # safe: guard on divisor
        '''\
def page_count(total_items, page_size):
    if page_size == 0:
        return 0
    return total_items // page_size
''',
        "Floor division by possibly-zero parameter",
    ),
    (
        "modulo_zero",
        # buggy: modulo by parameter
        '''\
def wrap_index(idx, size):
    return idx % size
''',
        # safe: guard on divisor
        '''\
def wrap_index(idx, size):
    if size == 0:
        return 0
    return idx % size
''',
        "Modulo by possibly-zero value",
    ),
    (
        "computed_divisor",
        # buggy: divisor is result of subtraction
        '''\
def growth_rate(current, previous):
    diff = current - previous
    return current / diff
''',
        # safe: guard on computed divisor
        '''\
def growth_rate(current, previous):
    diff = current - previous
    if diff != 0:
        return current / diff
    return 0.0
''',
        "Division by computed value that could be zero",
    ),
    (
        "multi_division",
        # buggy: two divisions in sequence, second divisor unguarded
        '''\
def normalize_ratio(a, b, c):
    ratio = a / b
    return ratio / c
''',
        # safe: guard both divisors
        '''\
def normalize_ratio(a, b, c):
    if b == 0:
        return 0.0
    if c == 0:
        return 0.0
    ratio = a / b
    return ratio / c
''',
        "Multiple divisions each needing their own guard",
    ),
]
