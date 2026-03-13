"""Guard stress: nested early returns (not at function top level).

A nested `if bad: return` inside a for-loop or another if-block
creates a section refinement, but the early_return guard extractor
only checks top-level function-body ifs.  The code after the nested
return still lives on the refined open set.
"""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Nested early return guards"

EXAMPLES = [
    (
        "nested_return_in_loop",
        # buggy: divide without zero check
        '''\
def safe_divide(a, b):
    x = b
    return a / x
''',
        # safe: nested return inside conditional guards the division
        '''\
def safe_divide(a, b):
    x = b
    for _attempt in range(1):
        if x == 0:
            return 0
    return a / x
''',
        "Nested return in loop as guard",
    ),
    (
        "nested_return_in_if",
        # buggy: modulo without guard
        '''\
def modular(val, mod):
    m = mod
    return val % m
''',
        # safe: nested return
        '''\
def modular(val, mod):
    m = mod
    if True:
        if m == 0:
            return val
    return val % m
''',
        "Nested return in nested if as guard",
    ),
    (
        "top_level_return_guard",
        # buggy: no guard
        '''\
def divide_safe(a, b):
    d = b
    return a / d
''',
        # safe: top-level early return (should always work)
        '''\
def divide_safe(a, b):
    d = b
    if d == 0:
        return 0
    return a / d
''',
        "Standard early return (baseline)",
    ),
]
