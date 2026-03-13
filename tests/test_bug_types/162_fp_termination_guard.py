"""FP stress: guard patterns for NON_TERMINATION.

Loops with clear termination conditions: bounded iteration, convergent
values, explicit break/return, or fuel-based limits.
"""

BUG_TYPE = "NON_TERMINATION"
BUG_DESC = "Loops with provable termination"

EXAMPLES = [
    (
        "fuel_limited_while",
        '''\
def converge(x):
    while x != 1:
        if x % 2 == 0:
            x = x // 2
        else:
            x = 3 * x + 1
    return x
''',
        '''\
def converge(x):
    fuel = 10000
    while x != 1 and fuel > 0:
        if x % 2 == 0:
            x = x // 2
        else:
            x = 3 * x + 1
        fuel -= 1
    return x
''',
        "Fuel counter guarantees termination",
    ),
    (
        "for_loop_bounded",
        '''\
def find_zero(f, a, b):
    while True:
        mid = (a + b) / 2
        if f(mid) < 0:
            a = mid
        else:
            b = mid
    return mid
''',
        '''\
def find_zero(f, a, b):
    for _ in range(100):
        mid = (a + b) / 2
        if abs(f(mid)) < 1e-10:
            return mid
        if f(mid) < 0:
            a = mid
        else:
            b = mid
    return (a + b) / 2
''',
        "for-range gives bounded iteration count",
    ),
    (
        "decreasing_variant",
        '''\
def gcd(a, b):
    while a != b:
        if a > b:
            a = a - b
        else:
            b = b - a
    return a
''',
        '''\
def gcd(a, b):
    a, b = abs(a), abs(b)
    while b != 0:
        a, b = b, a % b
    return a
''',
        "Euclidean GCD: b strictly decreases each iteration",
    ),
    (
        "break_guarantees_exit",
        '''\
def search(data, target):
    i = 0
    while True:
        if data[i] == target:
            return i
        i += 1
''',
        '''\
def search(data, target):
    for i in range(len(data)):
        if data[i] == target:
            return i
    return -1
''',
        "for-range replaces while-True with bounded iteration",
    ),
    (
        "recursion_with_base_case",
        '''\
def depth(node):
    return 1 + max(depth(node.left), depth(node.right))
''',
        '''\
def depth(node):
    if node is None:
        return 0
    return 1 + max(depth(node.left), depth(node.right))
''',
        "Base case (None check) ensures recursion terminates on finite trees",
    ),
]
