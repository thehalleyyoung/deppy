"""Pollard's rho algorithm for integer factorization.

Bug: When the GCD step finds g == n (the trivial factor), the correct
implementation retries with a different constant c. The bug instead returns n
as a "prime factor" without retrying, so composite numbers can appear in the
output factorization.
"""

CORRECT = r"""
import math

def factorize(n):
    if n <= 1:
        return []
    factors = _pollard_rho(n)
    factors.sort()
    return factors

def _is_prime_trial(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True

def _pollard_rho(n, c=1):
    if n <= 1:
        return []
    if n == 2:
        return [2]
    if n % 2 == 0:
        return [2] + _pollard_rho(n // 2)
    if _is_prime_trial(n):
        return [n]
    # Try to find a non-trivial factor using rho
    for c_val in range(c, c + 20):
        x = 2
        y = 2
        d = 1
        f = lambda z, cv=c_val: (z * z + cv) % n
        steps = 0
        while d == 1 and steps < 1000000:
            x = f(x)
            y = f(f(y))
            d = math.gcd(abs(x - y), n)
            steps += 1
        if d != 1 and d != n:
            # CORRECT: found non-trivial factor, recurse on both parts
            factors_a = _pollard_rho(d)
            factors_b = _pollard_rho(n // d)
            return factors_a + factors_b
        # If d == n, try next c value (retry)
    # Fallback: brute force for small factors
    for i in range(2, min(n, 10000)):
        if n % i == 0:
            return [i] + _pollard_rho(n // i)
    return [n]

num = NUMBER
result = factorize(num)
"""

BUGGY = r"""
import math

def factorize(n):
    if n <= 1:
        return []
    factors = _pollard_rho(n)
    factors.sort()
    return factors

def _is_prime_trial(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True

def _pollard_rho(n, c=1):
    if n <= 1:
        return []
    if n == 2:
        return [2]
    if n % 2 == 0:
        return [2] + _pollard_rho(n // 2)
    if _is_prime_trial(n):
        return [n]
    # Try to find a non-trivial factor using rho
    x = 2
    y = 2
    d = 1
    f = lambda z: (z * z + c) % n
    steps = 0
    while d == 1 and steps < 1000000:
        x = f(x)
        y = f(f(y))
        d = math.gcd(abs(x - y), n)
        steps += 1
    if d != 1 and d != n:
        factors_a = _pollard_rho(d)
        factors_b = _pollard_rho(n // d)
        return factors_a + factors_b
    # BUG: when d == n (trivial factor), should retry with different c
    # Instead, returns n directly as a factor without checking primality
    # This means composite numbers can appear in the factorization
    return [n]

num = NUMBER
result = factorize(num)
"""


def SPEC(NUMBER, result):
    """Verify factorization correctness:
    1) Product of all returned factors equals n.
    2) Each returned factor is prime.
    3) Factors are sorted in non-decreasing order.
    """
    if not isinstance(result, list):
        return False
    if len(result) == 0:
        return NUMBER <= 1

    # Check product equals n
    product = 1
    for f in result:
        if not isinstance(f, int):
            return False
        product *= f
    if product != NUMBER:
        return False

    # Check each factor is prime via trial division
    def is_prime(p):
        if p < 2:
            return False
        if p < 4:
            return True
        if p % 2 == 0 or p % 3 == 0:
            return False
        i = 5
        while i * i <= p:
            if p % i == 0 or p % (i + 2) == 0:
                return False
            i += 6
        return True

    for f in result:
        if not is_prime(f):
            return False

    # Check sorted
    for i in range(len(result) - 1):
        if result[i] > result[i + 1]:
            return False

    return True


BUG_DESC = (
    "When the GCD step yields d == n (the trivial factor), the correct "
    "implementation retries with a different constant c in the polynomial "
    "f(x) = x^2 + c. The bug instead returns n directly as a 'prime factor' "
    "without retrying, so composite numbers may appear in the factorization "
    "list, violating the primality requirement."
)


def _generate_number():
    import random
    # Numbers specifically chosen to trigger the bug where Pollard rho
    # with c=1 returns d==n (the trivial factor). The buggy version
    # does not retry with different c values, so it returns the composite
    # number itself as a "factor".
    # These semiprimes and perfect squares are known to cause d==n with c=1.
    hard_numbers = [
        3589, 3569, 3149, 3127, 3869, 4307,  # semiprimes that trigger d==n
        1681,  # 41^2 - perfect square
        37 * 97, 43 * 83, 47 * 67, 53 * 59, 53 * 73, 59 * 73,
    ]
    return random.choice(hard_numbers)


INPUT_OVERRIDES = {
    "NUMBER": _generate_number,
}
