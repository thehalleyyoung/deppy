"""UNINIT_MEMORY: Uninitialized variable — refinement gap.

Required section: {x : T | initialized(x)}
"""

BUG_TYPE = "UNBOUND_VAR"

BUGGY_A = r"""
def classify(score):
    if score >= 90:
        grade = "A"
    elif score >= 80:
        grade = "B"
    elif score >= 70:
        grade = "C"
    return grade
"""

SAFE_A = r"""
def classify(score):
    if score >= 90:
        grade = "A"
    elif score >= 80:
        grade = "B"
    elif score >= 70:
        grade = "C"
    else:
        grade = "F"
    return grade
"""

BUGGY_B = r"""
def find_extremes(values):
    for v in values:
        if v > max_val:
            max_val = v
        if v < min_val:
            min_val = v
    return min_val, max_val
"""

SAFE_B = r"""
def find_extremes(values):
    min_val = float('inf')
    max_val = float('-inf')
    for v in values:
        if v > max_val:
            max_val = v
        if v < min_val:
            min_val = v
    return min_val, max_val
"""

BUGGY_C = r"""
def process_response(response):
    if response.status == 200:
        result = response.json()
    elif response.status == 404:
        result = None
    return result
"""

SAFE_C = r"""
def process_response(response):
    result = None
    if response.status == 200:
        result = response.json()
    elif response.status == 404:
        result = None
    return result
"""

EXAMPLES = [
    ("grade_missing_else", BUGGY_A, SAFE_A, "grade unbound when score < 70"),
    ("extremes_no_init", BUGGY_B, SAFE_B, "min_val/max_val used before assignment"),
    ("response_missing_path", BUGGY_C, SAFE_C, "result unbound on non-200/404 status"),
]

BUG_DESC = "Variable used before assignment on some execution paths."
