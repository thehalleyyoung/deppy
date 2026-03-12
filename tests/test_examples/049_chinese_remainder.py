"""Chinese Remainder Theorem solver for systems of modular congruences.

Given a system x = a_i (mod m_i) where the moduli are pairwise coprime,
finds the unique solution x modulo M = product of all m_i using the
extended Euclidean algorithm to compute Bezout coefficients.

Bug: in the extended GCD, the recurrence for Bezout coefficients swaps
the quotient and remainder roles. Specifically, it uses (a % b) where
it should use (a // b) in the coefficient update, producing incorrect
Bezout coefficients and therefore wrong CRT solutions.
"""

CORRECT = r"""
def extended_gcd(a, b):
    # Returns (gcd, x, y) such that a*x + b*y = gcd(a, b)
    if b == 0:
        return (a, 1, 0)
    g, x1, y1 = extended_gcd(b, a % b)
    # CORRECT: x = y1, y = x1 - (a // b) * y1
    x = y1
    y = x1 - (a // b) * y1
    return (g, x, y)

def chinese_remainder_theorem(congruences):
    # congruences: list of (remainder, modulus) pairs
    # Returns (solution, combined_modulus) where solution is in [0, combined_modulus)
    if not congruences:
        return (0, 1)

    # Verify pairwise coprimality
    moduli = [m for _, m in congruences]
    for i in range(len(moduli)):
        for j in range(i + 1, len(moduli)):
            g, _, _ = extended_gcd(moduli[i], moduli[j])
            if g != 1:
                return None  # Not pairwise coprime

    # Compute product of all moduli
    M = 1
    for _, m in congruences:
        M *= m

    # Compute solution using CRT formula
    solution = 0
    for a_i, m_i in congruences:
        M_i = M // m_i
        # Find M_i_inv such that M_i * M_i_inv = 1 (mod m_i)
        g, x, _ = extended_gcd(M_i, m_i)
        M_i_inv = x % m_i
        solution += a_i * M_i * M_i_inv
        solution %= M

    return (solution % M, M)

def solve_system(congruences):
    # Solve and verify the system
    result = chinese_remainder_theorem(congruences)
    if result is None:
        return {"solution": None, "modulus": None, "valid": False}
    sol, mod = result
    # Verify
    valid = True
    for a_i, m_i in congruences:
        if sol % m_i != a_i % m_i:
            valid = False
            break
    return {"solution": sol, "modulus": mod, "valid": valid}

congruences = CONGRUENCES
result = solve_system(congruences)
"""

BUGGY = r"""
def extended_gcd(a, b):
    # Returns (gcd, x, y) such that a*x + b*y = gcd(a, b)
    if b == 0:
        return (a, 1, 0)
    g, x1, y1 = extended_gcd(b, a % b)
    # BUG: uses (a % b) instead of (a // b) in the coefficient update
    # Correct: y = x1 - (a // b) * y1
    # Buggy:   y = x1 - (a % b) * y1
    x = y1
    y = x1 - (a % b) * y1  # BUG: a % b instead of a // b
    return (g, x, y)

def chinese_remainder_theorem(congruences):
    if not congruences:
        return (0, 1)

    moduli = [m for _, m in congruences]
    for i in range(len(moduli)):
        for j in range(i + 1, len(moduli)):
            g, _, _ = extended_gcd(moduli[i], moduli[j])
            if g != 1:
                return None

    M = 1
    for _, m in congruences:
        M *= m

    solution = 0
    for a_i, m_i in congruences:
        M_i = M // m_i
        g, x, _ = extended_gcd(M_i, m_i)
        M_i_inv = x % m_i
        solution += a_i * M_i * M_i_inv
        solution %= M

    return (solution % M, M)

def solve_system(congruences):
    result = chinese_remainder_theorem(congruences)
    if result is None:
        return {"solution": None, "modulus": None, "valid": False}
    sol, mod = result
    valid = True
    for a_i, m_i in congruences:
        if sol % m_i != a_i % m_i:
            valid = False
            break
    return {"solution": sol, "modulus": mod, "valid": valid}

congruences = CONGRUENCES
result = solve_system(congruences)
"""


def SPEC(congruences, result):
    if not isinstance(result, dict):
        return False
    if "solution" not in result or "modulus" not in result or "valid" not in result:
        return False

    if not congruences:
        return result["solution"] == 0 and result["modulus"] == 1

    # Check moduli are pairwise coprime
    import math
    moduli = [m for _, m in congruences]
    for i in range(len(moduli)):
        for j in range(i + 1, len(moduli)):
            if math.gcd(moduli[i], moduli[j]) != 1:
                return result["solution"] is None

    # The solution must satisfy all congruences
    sol = result["solution"]
    M = result["modulus"]

    expected_M = 1
    for _, m in congruences:
        expected_M *= m
    if M != expected_M:
        return False

    if sol < 0 or sol >= M:
        return False

    for a_i, m_i in congruences:
        if sol % m_i != a_i % m_i:
            return False

    if not result["valid"]:
        return False

    return True


BUG_DESC = (
    "In the extended GCD, the Bezout coefficient update should be "
    "y = x1 - (a // b) * y1, using integer division. The bug uses "
    "(a % b) (the remainder) instead of (a // b) (the quotient). "
    "This produces incorrect Bezout coefficients, which means the "
    "modular inverse computation in CRT is wrong, yielding an "
    "incorrect solution to the system of congruences."
)


def _gen_congruences():
    import random
    # The bug: uses (a % b) instead of (a // b) in extended GCD coefficient update.
    # These differ when a // b != a % b, which happens when a >= 2*b or
    # when the quotient and remainder differ (most cases with non-trivial division).
    #
    # The bug produces wrong Bezout coefficients, leading to wrong modular inverses.
    # Larger moduli (where M_i / m_i is larger) make the quotient differ more
    # from the remainder, reliably triggering the bug.
    #
    # Use coprime sets with at least one modulus >= 7 to ensure M_i is large
    # enough that a//b != a%b in the recursive calls.
    coprime_sets = [
        [7, 11, 13],     # M_i values: 143, 91, 77 -- large quotients
        [5, 7, 11],      # M_i values: 77, 55, 35
        [7, 11],         # M_i values: 11, 7
        [5, 11, 13],     # M_i values: 143, 65, 55
        [7, 13, 17],     # M_i values: 221, 119, 91
    ]
    moduli = random.choice(coprime_sets)
    congruences = []
    for m in moduli:
        a = random.randint(0, m - 1)
        congruences.append((a, m))
    return congruences


INPUT_OVERRIDES = {
    "CONGRUENCES": _gen_congruences,
}
