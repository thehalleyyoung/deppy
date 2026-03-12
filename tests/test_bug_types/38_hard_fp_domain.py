"""Hard FP_DOMAIN + VALUE_ERROR examples — deeper math domain and parsing patterns."""

BUG_TYPE = "FP_DOMAIN"
BUG_DESC = "Floating-point domain error in harder patterns"

EXAMPLES = [
    (
        "log_ratio",
        # buggy: log of ratio where denominator may make it negative
        '''\
import math
def log_ratio(a, b):
    return math.log(a - b)
''',
        # safe: guard domain
        '''\
import math
def log_ratio(a, b):
    diff = a - b
    if diff > 0:
        return math.log(diff)
    return float('-inf')
''',
        "math.log of expression (a-b) which may be <= 0",
    ),
    (
        "acos_unscaled",
        # buggy: acos of value that may be outside [-1,1]
        '''\
import math
def angle_between(dot_product):
    return math.acos(dot_product)
''',
        # safe: clamp input
        '''\
import math
def angle_between(dot_product):
    clamped = max(-1.0, min(1.0, dot_product))
    return math.acos(clamped)
''',
        "math.acos of unclamped parameter, may exceed [-1,1] domain",
    ),
    (
        "sqrt_difference",
        # buggy: sqrt of (a - b) where a may be less than b
        '''\
import math
def distance(a, b):
    return math.sqrt(a - b)
''',
        # safe: use abs
        '''\
import math
def distance(a, b):
    return math.sqrt(abs(a - b))
''',
        "math.sqrt of expression that may be negative",
    ),
]
