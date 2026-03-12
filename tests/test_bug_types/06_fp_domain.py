"""FP_DOMAIN: Floating-point domain error — refinement gap.

Required section: {x : float | x ∈ domain(f)}
"""

BUG_TYPE = "FP_DOMAIN"

BUGGY_A = r"""
import math

def compute_log_ratio(a, b):
    return math.log(a) - math.log(b)
"""

SAFE_A = r"""
import math

def compute_log_ratio(a, b):
    if a <= 0 or b <= 0:
        raise ValueError("arguments must be positive")
    return math.log(a) - math.log(b)
"""

BUGGY_B = r"""
import math

def safe_sqrt(x):
    return math.sqrt(x)
"""

SAFE_B = r"""
import math

def safe_sqrt(x):
    if x < 0:
        raise ValueError("cannot take sqrt of negative")
    return math.sqrt(x)
"""

BUGGY_C = r"""
import math

def inverse_sin(ratio):
    return math.asin(ratio)
"""

SAFE_C = r"""
import math

def inverse_sin(ratio):
    if ratio < -1.0 or ratio > 1.0:
        raise ValueError("asin domain is [-1, 1]")
    return math.asin(ratio)
"""

EXAMPLES = [
    ("log_nonpositive", BUGGY_A, SAFE_A, "math.log(x) requires x > 0"),
    ("sqrt_negative", BUGGY_B, SAFE_B, "math.sqrt(x) requires x >= 0"),
    ("asin_domain", BUGGY_C, SAFE_C, "math.asin(x) requires -1 <= x <= 1"),
]

BUG_DESC = "Math function called on value outside its domain."
