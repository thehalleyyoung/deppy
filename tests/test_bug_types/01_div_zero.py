"""DIV_ZERO: Division by zero — refinement gap.

Required section: {divisor : int | divisor ≠ 0}
"""

BUG_TYPE = "DIV_ZERO"

# ── Example A: average of empty list ──────────────────────────────────

BUGGY_A = r"""
def average(values):
    total = 0
    count = 0
    for v in values:
        total += v
        count += 1
    return total / count
"""

SAFE_A = r"""
def average(values):
    total = 0
    count = 0
    for v in values:
        total += v
        count += 1
    if count == 0:
        return 0.0
    return total / count
"""

# ── Example B: normalize vector ───────────────────────────────────────

BUGGY_B = r"""
def normalize(vec):
    mag = sum(x * x for x in vec) ** 0.5
    return [x / mag for x in vec]
"""

SAFE_B = r"""
def normalize(vec):
    mag = sum(x * x for x in vec) ** 0.5
    if mag == 0:
        return vec
    return [x / mag for x in vec]
"""

# ── Example C: weighted percentage ────────────────────────────────────

BUGGY_C = r"""
def weighted_pct(scores, weights):
    total_weight = sum(weights)
    return sum(s * w for s, w in zip(scores, weights)) / total_weight
"""

SAFE_C = r"""
def weighted_pct(scores, weights):
    total_weight = sum(weights)
    if total_weight == 0:
        raise ValueError("weights sum to zero")
    return sum(s * w for s, w in zip(scores, weights)) / total_weight
"""

EXAMPLES = [
    ("average_empty", BUGGY_A, SAFE_A, "Divides by count without checking count != 0"),
    ("normalize_zero_vec", BUGGY_B, SAFE_B, "Divides by magnitude without checking mag != 0"),
    ("weighted_pct", BUGGY_C, SAFE_C, "Divides by total_weight without checking != 0"),
]

BUG_DESC = "Division by zero when divisor can be zero on valid input paths."
