"""STACK_OVERFLOW: Unbounded recursion — resource lifetime obstruction.

Required section: recursion_depth bounded by ranking function.
"""

BUG_TYPE = "STACK_OVERFLOW"

BUGGY_A = r"""
def flatten(lst):
    result = []
    for item in lst:
        if isinstance(item, list):
            result.extend(flatten(item))
        else:
            result.append(item)
    return result
"""

SAFE_A = r"""
def flatten(lst, max_depth=100):
    result = []
    for item in lst:
        if isinstance(item, list) and max_depth > 0:
            result.extend(flatten(item, max_depth - 1))
        else:
            result.append(item)
    return result
"""

BUGGY_B = r"""
def fibonacci(n):
    if n <= 0:
        return 0
    return fibonacci(n - 1) + fibonacci(n - 2)
"""

SAFE_B = r"""
def fibonacci(n):
    if n <= 0:
        return 0
    if n <= 2:
        return 1
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a
"""

BUGGY_C = r"""
def traverse(node):
    result = [node.value]
    for child in node.children:
        result.extend(traverse(child))
    return result
"""

SAFE_C = r"""
import sys

def traverse(node, depth=0):
    if depth > sys.getrecursionlimit() // 2:
        return [node.value]
    result = [node.value]
    for child in node.children:
        result.extend(traverse(child, depth + 1))
    return result
"""

EXAMPLES = [
    ("flatten_cyclic", BUGGY_A, SAFE_A, "flatten on cyclic list causes infinite recursion"),
    ("fib_huge_n", BUGGY_B, SAFE_B, "fibonacci(10000) blows the stack"),
    ("tree_deep", BUGGY_C, SAFE_C, "deep tree traversal without depth limit"),
]

BUG_DESC = "Recursive function without base case or depth limit."
