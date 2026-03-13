"""FP stress: try/except wrapping every risky operation.

When a try/except block catches exactly the exception that would be
raised by the risky operation, the bug is HANDLED, not present.
The sheaf section on the exception-handler site covers the obstruction.
"""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Try/except handling division by zero"

EXAMPLES = [
    (
        "try_except_zerodiv",
        '''\
def ratio(a, b):
    return a / b
''',
        '''\
def ratio(a, b):
    try:
        return a / b
    except ZeroDivisionError:
        return float('inf')
''',
        "ZeroDivisionError caught, handled gracefully",
    ),
    (
        "try_except_generic_arith",
        '''\
def compute(a, b):
    return a % b
''',
        '''\
def compute(a, b):
    try:
        return a % b
    except (ZeroDivisionError, ArithmeticError):
        return 0
''',
        "Tuple exception catch covers ZeroDivisionError",
    ),
    (
        "try_except_with_logging",
        '''\
def safe_div(x, y):
    return x / y
''',
        '''\
def safe_div(x, y):
    try:
        return x / y
    except ZeroDivisionError as e:
        print(f"Warning: {e}")
        return 0.0
''',
        "Exception caught and logged, returns safe default",
    ),
    (
        "try_except_base_exception",
        '''\
def divide(num, den):
    return num / den
''',
        '''\
def divide(num, den):
    try:
        return num / den
    except Exception:
        return None
''',
        "Broad except catches all arithmetic errors",
    ),
    (
        "nested_try_inner_div",
        '''\
def compute(a, b, c):
    temp = a / b
    return temp / c
''',
        '''\
def compute(a, b, c):
    try:
        temp = a / b
        return temp / c
    except ZeroDivisionError:
        return 0
''',
        "Both divisions covered by single try/except",
    ),
]
