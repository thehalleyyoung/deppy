"""Edge-case STACK_OVERFLOW: missing base case, no depth budget."""

BUG_TYPE = "STACK_OVERFLOW"
BUG_DESC = "Stack overflow from unbounded recursion"

EXAMPLES = [
    (
        "factorial_no_base",
        # buggy: recursive factorial with no base case guard
        '''\
def factorial(n):
    return n * factorial(n - 1)
''',
        # safe: explicit depth budget
        '''\
def factorial(n, _depth=0, _max=1000):
    if _depth >= _max:
        return 1
    return n * factorial(n - 1, _depth + 1, _max)
''',
        "Recursive function without depth budget",
    ),
    (
        "tree_traverse_no_bound",
        # buggy: recursive tree traversal without depth limit
        '''\
def count_nodes(node):
    if node is None:
        return 0
    return 1 + count_nodes(node.left) + count_nodes(node.right)
''',
        # safe: depth budget parameter
        '''\
def count_nodes(node, _depth=0, _max=1000):
    if _depth >= _max:
        return 0
    if node is None:
        return 0
    return 1 + count_nodes(node.left, _depth + 1, _max) + count_nodes(node.right, _depth + 1, _max)
''',
        "Tree traversal without depth budget despite base case",
    ),
    (
        "flatten_recursive",
        # buggy: list flattening without depth limit
        '''\
def flatten(lst):
    result = []
    for item in lst:
        if isinstance(item, list):
            result.extend(flatten(item))
        else:
            result.append(item)
    return result
''',
        # safe: try/except RecursionError
        '''\
def flatten(lst):
    try:
        result = []
        for item in lst:
            if isinstance(item, list):
                result.extend(flatten(item))
            else:
                result.append(item)
        return result
    except RecursionError:
        return lst
''',
        "Recursive flattening without depth protection",
    ),
    (
        "power_recursive",
        # buggy: no depth budget
        '''\
def power(base, exp):
    if exp == 0:
        return 1
    return base * power(base, exp - 1)
''',
        # safe: depth budget
        '''\
def power(base, exp, _depth=0, _max=1000):
    if _depth >= _max:
        return 1
    if exp == 0:
        return 1
    return base * power(base, exp - 1, _depth + 1, _max)
''',
        "Recursive power without depth budget",
    ),
]
