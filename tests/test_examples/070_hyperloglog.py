"""HyperLogLog cardinality estimation.

Bug: in the harmonic mean calculation, uses arithmetic mean instead of
harmonic mean of the register estimates, causing systematic overestimation
of cardinality.
"""

CORRECT = r"""
import math

def hyperloglog(data):
    stream = data["stream"]
    p = data["precision"]  # number of bits for register index
    m = 1 << p  # number of registers

    # Alpha constant for bias correction
    if m == 16:
        alpha = 0.673
    elif m == 32:
        alpha = 0.697
    elif m == 64:
        alpha = 0.709
    else:
        alpha = 0.7213 / (1.0 + 1.079 / m)

    registers = [0] * m

    def hash_value(x):
        # Simple but deterministic hash for reproducibility
        h = hash(x) & 0xFFFFFFFFFFFFFFFF
        return h

    def rho(w, max_width=64 - 8):
        # Position of leftmost 1-bit (1-indexed)
        if w == 0:
            return max_width
        r = 1
        while (w & 1) == 0 and r <= max_width:
            w >>= 1
            r += 1
        return r

    # Process stream
    for item in stream:
        h = hash_value(item)
        # Use first p bits as register index
        j = h & (m - 1)
        # Use remaining bits for rho
        w = h >> p
        registers[j] = max(registers[j], rho(w))

    # CORRECT: Harmonic mean estimation
    # E = alpha * m^2 / sum(2^(-M[j]))
    indicator_sum = 0.0
    for reg in registers:
        indicator_sum += 2.0 ** (-reg)
    raw_estimate = alpha * m * m / indicator_sum

    # Small range correction
    if raw_estimate <= 2.5 * m:
        zeros = registers.count(0)
        if zeros > 0:
            estimate = m * math.log(m / zeros)
        else:
            estimate = raw_estimate
    # Large range correction
    elif raw_estimate > (1.0 / 30.0) * (1 << 32):
        estimate = -(1 << 32) * math.log(1.0 - raw_estimate / (1 << 32))
    else:
        estimate = raw_estimate

    return {
        "estimate": int(round(estimate)),
        "raw_estimate": raw_estimate,
        "num_registers": m,
        "empty_registers": registers.count(0),
        "max_register": max(registers)
    }

data = DATA
result = hyperloglog(data)
"""

BUGGY = r"""
import math

def hyperloglog(data):
    stream = data["stream"]
    p = data["precision"]
    m = 1 << p

    if m == 16:
        alpha = 0.673
    elif m == 32:
        alpha = 0.697
    elif m == 64:
        alpha = 0.709
    else:
        alpha = 0.7213 / (1.0 + 1.079 / m)

    registers = [0] * m

    def hash_value(x):
        h = hash(x) & 0xFFFFFFFFFFFFFFFF
        return h

    def rho(w, max_width=64 - 8):
        if w == 0:
            return max_width
        r = 1
        while (w & 1) == 0 and r <= max_width:
            w >>= 1
            r += 1
        return r

    for item in stream:
        h = hash_value(item)
        j = h & (m - 1)
        w = h >> p
        registers[j] = max(registers[j], rho(w))

    # BUG: Uses arithmetic mean instead of harmonic mean
    # Correct: alpha * m^2 / sum(2^(-M[j]))
    # Bug: alpha * m * (1/m) * sum(2^(M[j]))
    indicator_sum = 0.0
    for reg in registers:
        indicator_sum += 2.0 ** reg  # BUG: +reg instead of -reg
    raw_estimate = alpha * indicator_sum / m  # arithmetic mean * alpha * m

    if raw_estimate <= 2.5 * m:
        zeros = registers.count(0)
        if zeros > 0:
            estimate = m * math.log(m / zeros)
        else:
            estimate = raw_estimate
    elif raw_estimate > (1.0 / 30.0) * (1 << 32):
        estimate = -(1 << 32) * math.log(1.0 - raw_estimate / (1 << 32))
    else:
        estimate = raw_estimate

    return {
        "estimate": int(round(estimate)),
        "raw_estimate": raw_estimate,
        "num_registers": m,
        "empty_registers": registers.count(0),
        "max_register": max(registers)
    }

data = DATA
result = hyperloglog(data)
"""


def SPEC(data, result):
    if not isinstance(result, dict):
        return False
    if "estimate" not in result or "raw_estimate" not in result:
        return False

    stream = data["stream"]
    true_cardinality = len(set(stream))
    estimate = result["estimate"]
    m = result.get("num_registers", 0)

    # Basic structural checks
    if not isinstance(estimate, (int, float)):
        return False
    if estimate < 0:
        return False

    # HyperLogLog should give a reasonable estimate
    # Standard error is ~1.04/sqrt(m)
    # We allow a generous 3x standard error for small inputs
    if true_cardinality == 0:
        return estimate == 0

    std_error = 1.04 / math.sqrt(m) if m > 0 else 1.0
    # Allow estimate within factor of (1 +/- 3*std_error) of true value
    # But also clamp for very small cardinalities
    lower = true_cardinality * max(0.1, 1.0 - 3 * std_error)
    upper = true_cardinality * (1.0 + 3 * std_error) + 5

    if estimate < lower or estimate > upper:
        return False

    # Metadata checks
    if result.get("empty_registers", -1) < 0:
        return False
    if result.get("max_register", -1) < 0:
        return False

    return True


BUG_DESC = (
    "In the raw estimate computation, uses 2^(+M[j]) instead of 2^(-M[j]) "
    "and computes an arithmetic-like aggregate instead of the harmonic mean. "
    "This causes massive overestimation of cardinality because register values "
    "are exponentiated positively rather than negatively."
)


def _gen():
    import random
    # Generate a stream with known cardinality
    n_unique = random.randint(50, 200)
    unique_items = list(range(n_unique))
    # Each item appears 1-5 times
    stream = []
    for item in unique_items:
        stream.extend([item] * random.randint(1, 5))
    random.shuffle(stream)
    # Use precision 5 (32 registers) for reasonable accuracy
    return {"stream": stream, "precision": 5}


INPUT_OVERRIDES = {"DATA": _gen}
