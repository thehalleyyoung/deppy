"""Hard DIV_ZERO examples — trickier patterns that stress the analysis."""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Division by zero in harder patterns"

EXAMPLES = [
    (
        "filtered_avg",
        # buggy: filter may leave empty list, then divide by count
        '''\
def filtered_average(items, threshold):
    filtered = [x for x in items if x > threshold]
    total = sum(filtered)
    count = len(filtered)
    return total / count
''',
        # safe: guard the count
        '''\
def filtered_average(items, threshold):
    filtered = [x for x in items if x > threshold]
    total = sum(filtered)
    count = len(filtered)
    if count == 0:
        return 0.0
    return total / count
''',
        "Division by len() of filtered list which may be empty",
    ),
    (
        "ratio_accum",
        # buggy: accumulator that stays zero when no positive values
        '''\
def positive_ratio(values):
    pos_sum = 0
    neg_sum = 0
    for v in values:
        if v > 0:
            pos_sum += v
        else:
            neg_sum += v
    return neg_sum / pos_sum
''',
        # safe: check accumulator before dividing
        '''\
def positive_ratio(values):
    pos_sum = 0
    neg_sum = 0
    for v in values:
        if v > 0:
            pos_sum += v
        else:
            neg_sum += v
    if pos_sum == 0:
        return 0.0
    return neg_sum / pos_sum
''',
        "Division by accumulator that stays zero when all values non-positive",
    ),
    (
        "pct_of_max",
        # buggy: max of empty sequence may not be caught; denominator from parameter
        '''\
def percent_of_max(values, baseline):
    diff = max(values) - baseline
    return diff / baseline
''',
        # safe: guard baseline
        '''\
def percent_of_max(values, baseline):
    if baseline == 0:
        return 0.0
    diff = max(values) - baseline
    return diff / baseline
''',
        "Division by function parameter that may be zero",
    ),
]
