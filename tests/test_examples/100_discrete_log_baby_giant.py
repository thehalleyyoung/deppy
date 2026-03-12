"""Baby-step giant-step algorithm for discrete logarithm.
Bug: computes giant step as g^m mod p instead of g^(-m) mod p
(no modular inverse), so giant steps go in the wrong direction
and miss the match."""

CORRECT = r"""
# Baby-step giant-step for discrete logarithm
# Find x such that G^x = H mod P
# G: generator, H: target, P: prime modulus
# Returns x or -1 if not found
#
# The algorithm splits the search space [0, n) where n = p-1
# into m = ceil(sqrt(n)) baby steps and m giant steps.
# We write x = i*m + j, so g^x = g^(i*m) * g^j = h
# Rearranging: g^j = h * g^(-i*m)
# Baby step: precompute g^j for j=0..m-1
# Giant step: compute h * g^(-m*i) for i=0..m-1 and look up in table

import math

g = G
h = H
p = P

# Validate inputs
if p < 2:
    result = -1
elif h % p == 0:
    result = -1
elif g % p == 0:
    result = -1
else:
    # Order of the group is at most p-1
    n = p - 1
    m = int(math.isqrt(n)) + 1

    # Baby step: compute table of g^j mod p for j = 0, 1, ..., m-1
    baby_table = {}
    power = 1  # g^0 = 1
    for j in range(m):
        # Store the first occurrence of each residue
        if power not in baby_table:
            baby_table[power] = j
        power = (power * g) % p

    # Giant step: compute g^(-m) mod p
    # CORRECT: use modular inverse of g^m via Fermat's little theorem
    # Since p is prime, g^(p-1) = 1 mod p, so g^(-1) = g^(p-2) mod p
    gm = pow(g, m, p)
    gm_inv = pow(gm, p - 2, p)

    # Verify the inverse is correct: gm * gm_inv should be 1 mod p
    assert (gm * gm_inv) % p == 1

    # Now check h * (g^(-m))^i for i = 0, 1, ..., m-1
    # If we find gamma = h * g^(-m*i) in baby_table with value j,
    # then g^j = h * g^(-m*i), so g^(i*m + j) = h, and x = i*m + j
    gamma = h % p
    found = -1
    for i in range(m):
        if gamma in baby_table:
            x_candidate = i * m + baby_table[gamma]
            # Verify this candidate
            if pow(g, x_candidate, p) == h % p:
                found = x_candidate
                break
        gamma = (gamma * gm_inv) % p

    result = found
"""

BUGGY = r"""
# Baby-step giant-step for discrete logarithm
# Find x such that G^x = H mod P
# G: generator, H: target, P: prime modulus
# Returns x or -1 if not found
#
# We write x = i*m + j so g^x = g^(i*m + j) = h
# Need to find j in baby table matching h * g^(-i*m)

import math

g = G
h = H
p = P

if p < 2:
    result = -1
elif h % p == 0:
    result = -1
elif g % p == 0:
    result = -1
else:
    n = p - 1
    m = int(math.isqrt(n)) + 1

    # Baby step: compute table of g^j mod p for j = 0, 1, ..., m-1
    baby_table = {}
    power = 1
    for j in range(m):
        if power not in baby_table:
            baby_table[power] = j
        power = (power * g) % p

    # Giant step: compute g^m mod p
    # BUG: uses g^m instead of g^(-m) -- no modular inverse
    # This means we compute h * g^(im) instead of h * g^(-im)
    # so the giant steps search in the wrong direction and miss the match
    gm = pow(g, m, p)
    # BUG: should compute gm_inv = pow(gm, p - 2, p) for modular inverse
    # Instead uses gm directly, which goes forward instead of backward

    gamma = h % p
    found = -1
    for i in range(m):
        if gamma in baby_table:
            x_candidate = i * m + baby_table[gamma]
            # Even with verification, the candidate will be wrong
            # because gamma was computed with wrong direction
            if pow(g, x_candidate, p) == h % p:
                found = x_candidate
                break
        # BUG: multiplies by gm instead of gm_inv
        gamma = (gamma * gm) % p

    result = found
"""


def SPEC(g, h, p, result):
    # If result is -1, verify that no solution exists in [0, p-1)
    if result == -1:
        # Check brute force for small p
        if p <= 1000:
            power = 1
            for x in range(p):
                if power == h % p:
                    return False  # solution exists but wasn't found
                power = (power * g) % p
        return True
    # If result >= 0, verify g^result = h mod p
    if result < 0:
        return False
    return pow(g, result, p) == h % p


BUG_DESC = (
    "Giant step multiplies by g^m instead of g^(-m) mod p. Without the "
    "modular inverse, the algorithm searches h*g^(im) instead of h*g^(-im), "
    "which means giant steps go in the wrong direction in the group and "
    "almost never find a match in the baby-step table."
)


def _gen_g():
    import random
    # Small primes for testing, with known generators
    primes_and_gens = [
        (23, 5), (29, 2), (31, 3), (37, 2), (41, 7),
        (43, 3), (47, 5), (53, 2), (59, 2), (61, 2),
    ]
    prime, gen = random.choice(primes_and_gens)
    return gen


def _gen_h():
    import random
    return random.randint(1, 50)


def _gen_p():
    import random
    return random.choice([23, 29, 31, 37, 41, 43, 47, 53, 59, 61])


INPUT_OVERRIDES = {"G": _gen_g, "H": _gen_h, "P": _gen_p}
