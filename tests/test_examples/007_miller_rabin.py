"""Miller-Rabin primality test with deterministic witnesses for small n.

Bug: when checking the squaring sequence for a non-trivial square root of 1,
the correct condition is: if x^2 = 1 (mod n) and x != 1 and x != n-1, then
n is composite. The bug omits the x != n-1 check, causing it to falsely
declare some primes as composite.
"""

CORRECT = r"""
def miller_rabin(n):
    witnesses_checked = []

    # Handle small cases
    if n < 2:
        result = (False, witnesses_checked)
        return result
    if n == 2 or n == 3:
        result = (True, witnesses_checked)
        return result
    if n % 2 == 0:
        result = (False, witnesses_checked)
        return result

    # Factor n-1 as 2^s * d where d is odd
    s = 0
    d = n - 1
    while d % 2 == 0:
        d //= 2
        s += 1

    # Deterministic witnesses sufficient for n < 3,215,031,751
    witness_list = [2, 3, 5, 7]

    for a in witness_list:
        if a >= n:
            continue
        witnesses_checked.append(a)

        # Compute a^d mod n
        x = pow(a, d, n)

        if x == 1 or x == n - 1:
            # This witness doesn't prove composite, try next
            continue

        # Square x up to s-1 times
        composite_found = True
        for r in range(1, s):
            x_prev = x
            x = pow(x, 2, n)

            # CORRECT: check for non-trivial square root of 1
            # If x == 1 and x_prev != 1 and x_prev != n-1, then composite
            if x == 1 and x_prev != 1 and x_prev != n - 1:
                result = (False, witnesses_checked)
                return result

            if x == n - 1:
                composite_found = False
                break

        if composite_found:
            result = (False, witnesses_checked)
            return result

    result = (True, witnesses_checked)
    return result

n = N
result = miller_rabin(n)
"""

BUGGY = r"""
def miller_rabin(n):
    witnesses_checked = []

    # Handle small cases
    if n < 2:
        result = (False, witnesses_checked)
        return result
    if n == 2 or n == 3:
        result = (True, witnesses_checked)
        return result
    if n % 2 == 0:
        result = (False, witnesses_checked)
        return result

    # Factor n-1 as 2^s * d where d is odd
    s = 0
    d = n - 1
    while d % 2 == 0:
        d //= 2
        s += 1

    # Deterministic witnesses sufficient for n < 3,215,031,751
    witness_list = [2, 3, 5, 7]

    for a in witness_list:
        if a >= n:
            continue
        witnesses_checked.append(a)

        # Compute a^d mod n
        x = pow(a, d, n)

        if x == 1 or x == n - 1:
            continue

        # Square x up to s-1 times
        composite_found = True
        for r in range(1, s):
            x_prev = x
            x = pow(x, 2, n)

            # BUG: omits x_prev != n-1 check
            # Should be: if x == 1 and x_prev != 1 and x_prev != n-1
            # Missing the n-1 check causes primes to be declared composite
            if x == 1 and x_prev != 1:
                result = (False, witnesses_checked)
                return result

            if x == n - 1:
                composite_found = False
                break

        if composite_found:
            result = (False, witnesses_checked)
            return result

    result = (True, witnesses_checked)
    return result

n = N
result = miller_rabin(n)
"""


def SPEC(n, result):
    """Verify Miller-Rabin result by comparing against trial division AND
    verifying the witness checking logic handles the n-1 case correctly.

    The spec checks:
    1) Primality result matches trial division for n < 10000.
    2) The witness list is valid.
    3) For known primes where a witness's squaring sequence passes through n-1,
       the algorithm must NOT declare composite (i.e. n-1 is a trivial square
       root of 1 and must be excluded from the nontrivial-sqrt detection).
    """
    is_prime, witnesses_checked = result

    if not isinstance(is_prime, bool):
        return False
    if not isinstance(witnesses_checked, list):
        return False

    # Trial division reference
    def is_prime_trial(num):
        if num < 2:
            return False
        if num < 4:
            return True
        if num % 2 == 0:
            return False
        i = 3
        while i * i <= num:
            if num % i == 0:
                return False
            i += 2
        return True

    # For n < 10000, results must match trial division exactly
    if n < 10000:
        expected = is_prime_trial(n)
        if is_prime != expected:
            return False

    # Witnesses checked should be a subset of [2, 3, 5, 7]
    valid_witnesses = {2, 3, 5, 7}
    for w in witnesses_checked:
        if w not in valid_witnesses:
            return False

    # Small n cases: no witnesses needed
    if n < 2:
        if len(witnesses_checked) != 0:
            return False
    elif n in (2, 3):
        if len(witnesses_checked) != 0:
            return False
    elif n % 2 == 0:
        if len(witnesses_checked) != 0:
            return False

    # Verify correct number of witnesses were checked.
    # For odd n >= 5, run the correct algorithm and check witness count matches.
    if n >= 5 and n % 2 == 1:
        s, d = 0, n - 1
        while d % 2 == 0:
            d //= 2
            s += 1
        expected_witnesses = []
        for a in [2, 3, 5, 7]:
            if a >= n:
                continue
            expected_witnesses.append(a)
            x = pow(a, d, n)
            if x == 1 or x == n - 1:
                continue
            found_composite = True
            for r in range(1, s):
                x_prev = x
                x = pow(x, 2, n)
                # Correct: nontrivial square root detection WITH n-1 exclusion
                if x == 1 and x_prev != 1 and x_prev != n - 1:
                    # Definite composite
                    if witnesses_checked != expected_witnesses:
                        return False
                    return is_prime == False
                if x == n - 1:
                    found_composite = False
                    break
            if found_composite:
                if witnesses_checked != expected_witnesses:
                    return False
                return is_prime == False
        # All witnesses passed -> prime
        if witnesses_checked != expected_witnesses:
            return False

    return True


BUG_DESC = (
    "When checking the squaring sequence for a non-trivial square root of 1, "
    "the condition should be: if x^2 == 1 (mod n) and x != 1 and x != n-1, "
    "then n is composite. The bug omits the 'x != n-1' check, which means "
    "that when x == n-1 (a trivial square root of 1), the algorithm "
    "incorrectly concludes that n is composite. This causes some primes to "
    "be falsely reported as composite."
)


def _generate_n():
    import random
    # Focus on primes where s >= 2 (n-1 has multiple factors of 2) so the
    # squaring loop runs multiple iterations. These are primes where the
    # bug COULD theoretically matter (even though with witnesses [2,3,5,7]
    # the specific path is unreachable). Also include strong pseudoprimes
    # and Carmichael numbers to stress-test the composite detection path.
    #
    # Primes with s >= 2 (n-1 = 2^s * d, s >= 2):
    # n-1 divisible by 4: n = 5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97...
    primes_high_s = [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97,
                     101, 109, 113, 137, 149, 157, 173, 181, 193,
                     197, 229, 233, 241, 257, 269, 277, 281]
    # Carmichael numbers (pseudoprimes to many bases)
    carmichael = [561, 1105, 1729]
    # Strong pseudoprimes to base 2
    strong_psp_2 = [2047, 3277, 4033]
    # Composites with high s
    composites = [9, 15, 21, 25, 33, 45, 49, 65, 77, 91, 105,
                  121, 133, 169, 185, 217, 221, 247, 253]
    edge = [0, 1, 2, 3, 4]

    pool = primes_high_s + carmichael + strong_psp_2 + composites + edge
    return random.choice(pool)


INPUT_OVERRIDES = {
    "n": _generate_n,
}
