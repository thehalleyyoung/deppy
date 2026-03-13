"""Guard stress: assert-based arithmetic refinements.

`assert n != 0` introduces a section on the {n ≠ 0} sub-presheaf,
making the divisor site's restriction map total.
"""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Assert-based division guards"

EXAMPLES = [
    (
        "assert_nonzero_div",
        # buggy: divide by possibly-zero parameter
        '''\
def ratio(a, b):
    denom = b
    return a / denom
''',
        # safe: assert refines to nonzero section
        '''\
def ratio(a, b):
    denom = b
    assert denom != 0
    return a / denom
''',
        "Assert nonzero before division",
    ),
    (
        "assert_positive_div",
        # buggy: floor-divide by unchecked value
        '''\
def pages(total, size):
    n = size
    return total // n
''',
        # safe: assert positive implies nonzero
        '''\
def pages(total, size):
    n = size
    assert n > 0, "page size must be positive"
    return total // n
''',
        "Assert positive before floor division",
    ),
    (
        "assert_modulo",
        # buggy: modulo by possibly-zero
        '''\
def wrap(idx, width):
    w = width
    return idx % w
''',
        # safe: assert refines to nonzero
        '''\
def wrap(idx, width):
    w = width
    assert w > 0
    return idx % w
''',
        "Assert before modulo",
    ),
]
