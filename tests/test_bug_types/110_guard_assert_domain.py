"""Guard stress: FP_DOMAIN with assert and compound guards.

For math.sqrt(x), `assert x >= 0` introduces a section on the
non-negative sub-presheaf.  Similarly, compound conditions like
`if x is not None and x >= 0:` refine both the None and domain
dimensions simultaneously.
"""

BUG_TYPE = "FP_DOMAIN"
BUG_DESC = "Assert and compound guards for math domain"

EXAMPLES = [
    (
        "assert_nonneg_sqrt",
        # buggy: sqrt of possibly-negative
        '''\
import math
def root(x):
    val = x
    return math.sqrt(val)
''',
        # safe: assert non-negative
        '''\
import math
def root(x):
    val = x
    assert val >= 0
    return math.sqrt(val)
''',
        "Assert >= 0 before sqrt",
    ),
    (
        "assert_positive_log",
        # buggy: log of possibly-non-positive
        '''\
import math
def log_val(x):
    val = x
    return math.log(val)
''',
        # safe: assert positive
        '''\
import math
def log_val(x):
    val = x
    assert val > 0, "must be positive for log"
    return math.log(val)
''',
        "Assert > 0 before log",
    ),
    (
        "compound_positive_sqrt",
        # buggy: sqrt without guard
        '''\
import math
def safe_sqrt(x):
    val = x
    return math.sqrt(val)
''',
        # safe: isinstance + range check
        '''\
import math
def safe_sqrt(x):
    val = x
    if isinstance(val, (int, float)) and val >= 0:
        return math.sqrt(val)
    return 0.0
''',
        "Compound isinstance + range check",
    ),
]
