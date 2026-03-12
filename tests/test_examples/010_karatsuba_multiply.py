"""Karatsuba multiplication for large integers represented as digit lists.

Implements the Karatsuba algorithm which splits numbers at the midpoint
and computes three recursive products instead of four, combining them
with appropriate shifts. Numbers are represented as lists of digits in
base 10, most significant digit first.

Bug: when computing the cross term, the algorithm should subtract
a_low * b_low from the middle product, but instead subtracts
a_high * b_low. This produces an incorrect cross term.
"""

CORRECT = r"""
def digits_to_int(digits):
    # Convert digit list (MSB first) to integer.
    if not digits:
        return 0
    result = 0
    for d in digits:
        result = result * 10 + d
    return result

def int_to_digits(n):
    # Convert non-negative integer to digit list (MSB first).
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 10)
        n //= 10
    digits.reverse()
    return digits

def add_digit_lists(a, b):
    # Add two digit lists, return digit list.
    return int_to_digits(digits_to_int(a) + digits_to_int(b))

def subtract_digit_lists(a, b):
    # Subtract b from a (a >= b assumed), return digit list.
    val = digits_to_int(a) - digits_to_int(b)
    if val < 0:
        val = 0
    return int_to_digits(val)

def shift_digits(a, n):
    # Multiply digit list by 10^n (append n zeros).
    if a == [0]:
        return [0]
    return a + [0] * n

def karatsuba(a, b):
    # Karatsuba multiplication of two digit lists.
    # a, b: lists of digits (MSB first), no leading zeros except [0].
    # Returns product as digit list, MSB first, no leading zeros.

    # Base case: single digit multiplication
    if len(a) == 1 or len(b) == 1:
        product = digits_to_int(a) * digits_to_int(b)
        return int_to_digits(product)

    # Make both lists the same length by padding shorter one
    n = max(len(a), len(b))
    while len(a) < n:
        a = [0] + a
    while len(b) < n:
        b = [0] + b

    # Split at midpoint
    mid = n // 2
    shift = n - mid  # number of digits in the low part

    a_high = a[:mid] if a[:mid] else [0]
    a_low = a[mid:] if a[mid:] else [0]
    b_high = b[:mid] if b[:mid] else [0]
    b_low = b[mid:] if b[mid:] else [0]

    # Remove leading zeros
    while len(a_high) > 1 and a_high[0] == 0:
        a_high = a_high[1:]
    while len(a_low) > 1 and a_low[0] == 0:
        a_low = a_low[1:]
    while len(b_high) > 1 and b_high[0] == 0:
        b_high = b_high[1:]
    while len(b_low) > 1 and b_low[0] == 0:
        b_low = b_low[1:]

    # Three recursive multiplications
    z2 = karatsuba(a_high, b_high)           # a_high * b_high
    z0 = karatsuba(a_low, b_low)             # a_low * b_low

    # Cross term: (a_high + a_low)(b_high + b_low) - z2 - z0
    sum_a = add_digit_lists(a_high, a_low)
    sum_b = add_digit_lists(b_high, b_low)
    z1_full = karatsuba(sum_a, sum_b)

    # CORRECT: subtract z2 and z0 from the full product
    z1 = subtract_digit_lists(z1_full, z2)
    z1 = subtract_digit_lists(z1, z0)

    # Combine: z2 * 10^(2*shift) + z1 * 10^shift + z0
    term2 = shift_digits(z2, 2 * shift)
    term1 = shift_digits(z1, shift)

    result = add_digit_lists(add_digit_lists(term2, term1), z0)

    # Remove leading zeros
    while len(result) > 1 and result[0] == 0:
        result = result[1:]

    return result

a_digits = A_DIGITS
b_digits = B_DIGITS
result = karatsuba(a_digits, b_digits)
"""

BUGGY = r"""
def digits_to_int(digits):
    # Convert digit list (MSB first) to integer.
    if not digits:
        return 0
    result = 0
    for d in digits:
        result = result * 10 + d
    return result

def int_to_digits(n):
    # Convert non-negative integer to digit list (MSB first).
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 10)
        n //= 10
    digits.reverse()
    return digits

def add_digit_lists(a, b):
    # Add two digit lists, return digit list.
    return int_to_digits(digits_to_int(a) + digits_to_int(b))

def subtract_digit_lists(a, b):
    # Subtract b from a (a >= b assumed), return digit list.
    val = digits_to_int(a) - digits_to_int(b)
    if val < 0:
        val = 0
    return int_to_digits(val)

def shift_digits(a, n):
    # Multiply digit list by 10^n (append n zeros).
    if a == [0]:
        return [0]
    return a + [0] * n

def karatsuba(a, b):
    # Karatsuba multiplication of two digit lists.
    # a, b: lists of digits (MSB first), no leading zeros except [0].
    # Returns product as digit list, MSB first, no leading zeros.

    # Base case: single digit multiplication
    if len(a) == 1 or len(b) == 1:
        product = digits_to_int(a) * digits_to_int(b)
        return int_to_digits(product)

    # Make both lists the same length by padding shorter one
    n = max(len(a), len(b))
    while len(a) < n:
        a = [0] + a
    while len(b) < n:
        b = [0] + b

    # Split at midpoint
    mid = n // 2
    shift = n - mid  # number of digits in the low part

    a_high = a[:mid] if a[:mid] else [0]
    a_low = a[mid:] if a[mid:] else [0]
    b_high = b[:mid] if b[:mid] else [0]
    b_low = b[mid:] if b[mid:] else [0]

    # Remove leading zeros
    while len(a_high) > 1 and a_high[0] == 0:
        a_high = a_high[1:]
    while len(a_low) > 1 and a_low[0] == 0:
        a_low = a_low[1:]
    while len(b_high) > 1 and b_high[0] == 0:
        b_high = b_high[1:]
    while len(b_low) > 1 and b_low[0] == 0:
        b_low = b_low[1:]

    # Three recursive multiplications
    z2 = karatsuba(a_high, b_high)           # a_high * b_high
    z0 = karatsuba(a_low, b_low)             # a_low * b_low

    # Cross term: (a_high + a_low)(b_high + b_low) - z2 - z0
    sum_a = add_digit_lists(a_high, a_low)
    sum_b = add_digit_lists(b_high, b_low)
    z1_full = karatsuba(sum_a, sum_b)

    # BUG: subtracts a_high*b_low instead of a_low*b_low (z0)
    # Should be: z1 = z1_full - z2 - z0
    # Instead:   z1 = z1_full - z2 - (a_high * b_low)
    z1 = subtract_digit_lists(z1_full, z2)
    wrong_term = karatsuba(a_high, b_low)    # BUG: should be z0
    z1 = subtract_digit_lists(z1, wrong_term)

    # Combine: z2 * 10^(2*shift) + z1 * 10^shift + z0
    term2 = shift_digits(z2, 2 * shift)
    term1 = shift_digits(z1, shift)

    result = add_digit_lists(add_digit_lists(term2, term1), z0)

    # Remove leading zeros
    while len(result) > 1 and result[0] == 0:
        result = result[1:]

    return result

a_digits = A_DIGITS
b_digits = B_DIGITS
result = karatsuba(a_digits, b_digits)
"""


def SPEC(a_digits, b_digits, result):
    """Verify Karatsuba multiplication:
    1) Convert inputs and result to Python ints, check product matches.
    2) No leading zeros (except for the number 0 itself).
    """
    if not isinstance(result, list):
        return False

    # Check all elements are valid digits
    for d in result:
        if not isinstance(d, int) or d < 0 or d > 9:
            return False

    # Check no leading zeros (except [0])
    if len(result) > 1 and result[0] == 0:
        return False

    # Convert to integers and verify
    def to_int(digits):
        val = 0
        for d in digits:
            val = val * 10 + d
        return val

    a_val = to_int(a_digits)
    b_val = to_int(b_digits)
    expected = a_val * b_val
    actual = to_int(result)

    if actual != expected:
        return False

    # Check input validity (no leading zeros except [0])
    if len(a_digits) > 1 and a_digits[0] == 0:
        return False
    if len(b_digits) > 1 and b_digits[0] == 0:
        return False

    return True


BUG_DESC = (
    "When computing the Karatsuba cross term, the algorithm should compute "
    "(a_high + a_low) * (b_high + b_low) - a_high*b_high - a_low*b_low. "
    "The bug subtracts a_high*b_low instead of a_low*b_low for the second "
    "subtraction. Since a_high*b_low != a_low*b_low in general, this "
    "produces an incorrect cross term and therefore a wrong product."
)


def _generate_a():
    """Generate digit list for Karatsuba that triggers the bug.

    The bug subtracts a_high*b_low instead of z0=a_low*b_low.
    These differ whenever a_high != a_low. We need numbers with at
    least 2 digits (so Karatsuba recurses, not base case) and where
    a_high != a_low. Using 4 digits ensures: a = [d1,d2,d3,d4],
    a_high = [d1,d2], a_low = [d3,d4]. Making d1 != d3 or d2 != d4
    ensures a_high != a_low.
    """
    import random
    # 4 digits: split into high=[d1,d2], low=[d3,d4]
    # Ensure high != low by making first digits different
    d1 = random.randint(1, 9)  # nonzero leading digit
    d2 = random.randint(0, 9)
    # Make low part different from high part
    d3 = random.randint(0, 9)
    d4 = random.randint(0, 9)
    while [d3, d4] == [d1, d2]:
        d3 = random.randint(0, 9)
        d4 = random.randint(0, 9)
    return [d1, d2, d3, d4]


def _generate_b():
    import random
    # Also 4 digits, nonzero leading digit, different high/low
    d1 = random.randint(1, 9)
    d2 = random.randint(0, 9)
    d3 = random.randint(0, 9)
    d4 = random.randint(0, 9)
    while [d3, d4] == [d1, d2]:
        d3 = random.randint(0, 9)
        d4 = random.randint(0, 9)
    return [d1, d2, d3, d4]


INPUT_OVERRIDES = {
    "a": _generate_a,
    "b": _generate_b,
}
