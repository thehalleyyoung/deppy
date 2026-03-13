"""Python semantics: boolean short-circuit — DIV_ZERO, NULL_PTR, INDEX_OOB."""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Short-circuit evaluation in boolean expressions"

EXAMPLES = [
    (
        "and_short_circuit_safe",
        # buggy: does NOT short-circuit, divides first
        '''\
def safe_divide(a, b):
    return a / b
''',
        # safe: short-circuit and
        '''\
def safe_divide(a, b):
    return a / b if b != 0 else 0
''',
        "b may be 0; a / b is div-by-zero",
    ),
    (
        "or_chain_div",
        # buggy: or chain doesn't protect division
        '''\
def weighted_avg(values, weights):
    total_weight = sum(weights)
    return sum(v * w for v, w in zip(values, weights)) / total_weight
''',
        # safe: guard zero total
        '''\
def weighted_avg(values, weights):
    total_weight = sum(weights)
    if total_weight == 0:
        return 0.0
    return sum(v * w for v, w in zip(values, weights)) / total_weight
''',
        "total_weight may be 0",
    ),
    (
        "conditional_expr_div",
        # buggy: conditional expression but division on wrong branch
        '''\
def ratio(a, b, default=1):
    denom = b if b else default
    result = a / denom
    extra = a / b
    return result + extra
''',
        # safe: use guarded denom throughout
        '''\
def ratio(a, b, default=1):
    denom = b if b else default
    result = a / denom
    extra = a / denom
    return result + extra
''',
        "a / b on last line still unguarded even though denom is safe",
    ),
]
