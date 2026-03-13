"""FP stress: guard patterns for INTEGER_OVERFLOW.

Real code guards against overflow via range checks, clamping,
bit masking, and min/max bounds before arithmetic.
"""

BUG_TYPE = "INTEGER_OVERFLOW"
BUG_DESC = "Overflow prevention via range checks"

EXAMPLES = [
    (
        "clamp_before_shift",
        '''\
def shift_left(x, n):
    return x << n
''',
        '''\
def shift_left(x, n):
    n = min(n, 63)
    return x << n
''',
        "Clamp shift amount prevents overflow",
    ),
    (
        "check_before_multiply",
        '''\
def factorial(n):
    result = 1
    for i in range(1, n + 1):
        result *= i
    return result
''',
        '''\
def factorial(n):
    if n > 20:
        raise OverflowError("n too large")
    result = 1
    for i in range(1, n + 1):
        result *= i
    return result
''',
        "Bound check on n prevents combinatorial overflow",
    ),
    (
        "mask_to_width",
        '''\
def add_u32(a, b):
    return a + b
''',
        '''\
def add_u32(a, b):
    return (a + b) & 0xFFFFFFFF
''',
        "Bit mask constrains result to 32-bit range",
    ),
    (
        "safe_power",
        '''\
def big_pow(base, exp):
    return base ** exp
''',
        '''\
def big_pow(base, exp):
    if exp > 1000 or base > 10000:
        raise ValueError("too large")
    return base ** exp
''',
        "Bounds on base and exp prevent overflow",
    ),
    (
        "checked_addition",
        '''\
def accumulate(items):
    total = 0
    for x in items:
        total += x
    return total
''',
        '''\
MAX_TOTAL = 10**15

def accumulate(items):
    total = 0
    for x in items:
        total += x
        if total > MAX_TOTAL:
            raise OverflowError("accumulator overflow")
    return total
''',
        "Running overflow check in accumulation loop",
    ),
]
