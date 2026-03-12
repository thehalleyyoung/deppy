"""Harder DIV_ZERO: multi-step computation, nested control flow, non-obvious guards."""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Division by zero in complex multi-step patterns"

EXAMPLES = [
    (
        "weighted_mean",
        # buggy: weights sum may be zero after filtering
        '''\
def weighted_mean(values, weights, mask):
    total = 0
    w_sum = 0
    for i in range(len(values)):
        if mask[i]:
            total += values[i] * weights[i]
            w_sum += weights[i]
    avg = total / w_sum
    return avg
''',
        # safe: truthiness guard on w_sum
        '''\
def weighted_mean(values, weights, mask):
    total = 0
    w_sum = 0
    for i in range(len(values)):
        if mask[i]:
            total += values[i] * weights[i]
            w_sum += weights[i]
    if not w_sum:
        return 0.0
    avg = total / w_sum
    return avg
''',
        "Division by weight sum that may stay zero when mask filters everything",
    ),
    (
        "normalize_scores",
        # buggy: max and min could be equal, making range zero
        '''\
def normalize_scores(scores):
    lo = min(scores)
    hi = max(scores)
    span = hi - lo
    return [(s - lo) / span for s in scores]
''',
        # safe: check span
        '''\
def normalize_scores(scores):
    lo = min(scores)
    hi = max(scores)
    span = hi - lo
    if span == 0:
        return [0.0 for s in scores]
    return [(s - lo) / span for s in scores]
''',
        "Division by span that is zero when all scores equal",
    ),
    (
        "harmonic_mean",
        # buggy: element could be zero in list
        '''\
def harmonic_mean(values):
    n = len(values)
    reciprocal_sum = 0
    for v in values:
        reciprocal_sum += 1.0 / v
    return n / reciprocal_sum
''',
        # safe: skip zero values
        '''\
def harmonic_mean(values):
    n = len(values)
    reciprocal_sum = 0
    for v in values:
        if v:
            reciprocal_sum += 1.0 / v
    if not reciprocal_sum:
        return 0.0
    return n / reciprocal_sum
''',
        "Division by element in loop that could be zero",
    ),
]
