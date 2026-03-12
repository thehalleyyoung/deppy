"""Hard STACK_OVERFLOW examples — indirect recursion patterns, accumulating without base case."""

BUG_TYPE = "STACK_OVERFLOW"
BUG_DESC = "Stack overflow from deeper recursion patterns"

EXAMPLES = [
    (
        "power_no_base",
        # buggy: recursive power with no base case for n=0
        '''\
def power(base, n):
    return base * power(base, n - 1)
''',
        # safe: base case
        '''\
def power(base, n, depth=0):
    if n <= 0:
        return 1
    if depth > 500:
        return 1
    return base * power(base, n - 1, depth + 1)
''',
        "Recursive power without base case blows stack on n=0 or negative",
    ),
    (
        "list_sum_no_guard",
        # buggy: recursive sum without empty-list guard
        '''\
def rsum(lst):
    return lst[0] + rsum(lst[1:])
''',
        # safe: depth budget
        '''\
def rsum(lst, depth=0):
    if not lst or depth > 500:
        return 0
    return lst[0] + rsum(lst[1:], depth + 1)
''',
        "Recursive list sum without base case",
    ),
    (
        "tree_count_unbounded",
        # buggy: counts nodes in a tree with no depth bound
        '''\
def count_nodes(node):
    if node is None:
        return 0
    return 1 + count_nodes(node.left) + count_nodes(node.right)
''',
        # safe: depth budget
        '''\
def count_nodes(node, depth=0):
    if node is None or depth > 500:
        return 0
    return 1 + count_nodes(node.left, depth + 1) + count_nodes(node.right, depth + 1)
''',
        "Tree traversal without depth limit on adversarial (deep) trees",
    ),
]
