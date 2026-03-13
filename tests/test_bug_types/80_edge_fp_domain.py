"""Edge-case FP_DOMAIN: log of subtraction, sqrt of diff, acos of ratio."""

BUG_TYPE = "FP_DOMAIN"
BUG_DESC = "Floating-point domain error in edge-case patterns"

EXAMPLES = [
    (
        "log_of_subtraction",
        # buggy: log of possibly-negative subtraction
        '''\
import math
def log_decline(before, after):
    return math.log(before - after)
''',
        # safe: guard positivity
        '''\
import math
def log_decline(before, after):
    diff = before - after
    if diff > 0:
        return math.log(diff)
    return 0.0
''',
        "math.log of subtraction that may be non-positive",
    ),
    (
        "sqrt_of_difference",
        # buggy: sqrt of possibly-negative expression
        '''\
import math
def rms_error(expected, actual):
    return math.sqrt(expected - actual)
''',
        # safe: guard non-negativity
        '''\
import math
def rms_error(expected, actual):
    diff = expected - actual
    if diff >= 0:
        return math.sqrt(diff)
    return 0.0
''',
        "math.sqrt of difference that may be negative",
    ),
    (
        "acos_of_ratio",
        # buggy: acos of arbitrary ratio
        '''\
import math
def angle_between(dot_product, magnitude):
    return math.acos(dot_product / magnitude)
''',
        # safe: clamp ratio
        '''\
import math
def angle_between(dot_product, magnitude):
    if magnitude == 0:
        return 0.0
    ratio = max(-1.0, min(dot_product / magnitude, 1.0))
    return math.acos(ratio)
''',
        "math.acos of unclamped ratio outside [-1, 1]",
    ),
    (
        "log2_count",
        # buggy: log2 of count that may be zero
        '''\
import math
def bit_width(count):
    return math.log2(count)
''',
        # safe: guard positivity
        '''\
import math
def bit_width(count):
    if count > 0:
        return math.log2(count)
    return 0.0
''',
        "math.log2 of count that may be zero or negative",
    ),
]
