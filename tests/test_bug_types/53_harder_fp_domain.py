"""Harder FP_DOMAIN: math domain errors in multi-step computation."""

BUG_TYPE = "FP_DOMAIN"
BUG_DESC = "Floating-point domain error in complex math patterns"

EXAMPLES = [
    (
        "entropy_calc",
        # buggy: log of probability that could be zero
        '''\
import math
def entropy(probs):
    total = 0.0
    for p in probs:
        total -= p * math.log(p)
    return total
''',
        # safe: guard against zero probability
        '''\
import math
def entropy(probs):
    total = 0.0
    for p in probs:
        if p > 0:
            total -= p * math.log(p)
    return total
''',
        "Log of probability that may be zero in entropy calculation",
    ),
    (
        "distance_sqrt",
        # buggy: sqrt of difference that could be negative
        '''\
import math
def distance_metric(a, b):
    diff = a - b
    return math.sqrt(diff)
''',
        # safe: use abs to ensure non-negative
        '''\
import math
def distance_metric(a, b):
    diff = a - b
    return math.sqrt(abs(diff))
''',
        "Square root of difference that could be negative",
    ),
    (
        "angle_from_ratio",
        # buggy: asin argument may be outside [-1, 1]
        '''\
import math
def elevation_angle(height, distance):
    ratio = height / distance
    return math.asin(ratio)
''',
        # safe: clamp ratio to valid domain
        '''\
import math
def elevation_angle(height, distance):
    if distance == 0:
        return 0.0
    ratio = height / distance
    clamped = max(-1.0, min(ratio, 1.0))
    return math.asin(clamped)
''',
        "asin of ratio that may be outside [-1, 1] domain",
    ),
]
