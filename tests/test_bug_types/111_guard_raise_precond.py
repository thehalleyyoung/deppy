"""Guard stress: precondition raise as early return equivalent.

`if not P: raise ValueError(...)` is functionally identical to
`if not P: return ...` — both restrict the continuation to the
open set where P holds.  But raise-as-precondition may appear
in nested positions that the engine doesn't check for early_return.
"""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Raise-as-precondition guards"

EXAMPLES = [
    (
        "raise_valueerror_precond",
        # buggy: divide without guard
        '''\
def ratio(a, b):
    denom = b
    return a / denom
''',
        # safe: raise ValueError as precondition
        '''\
def ratio(a, b):
    denom = b
    if denom == 0:
        raise ValueError("cannot divide by zero")
    return a / denom
''',
        "Raise ValueError as precondition",
    ),
    (
        "raise_assertion_precond",
        # buggy: modulo without guard
        '''\
def modular(val, base):
    b = base
    return val % b
''',
        # safe: raise AssertionError
        '''\
def modular(val, base):
    b = base
    if b <= 0:
        raise AssertionError("base must be positive")
    return val % b
''',
        "Raise assertion as precondition",
    ),
    (
        "raise_runtime_precond",
        # buggy: floor div without guard
        '''\
def split_evenly(total, parts):
    n = parts
    return total // n
''',
        # safe: raise RuntimeError
        '''\
def split_evenly(total, parts):
    n = parts
    if n == 0:
        raise RuntimeError("parts must not be zero")
    return total // n
''',
        "Raise RuntimeError as precondition",
    ),
]
