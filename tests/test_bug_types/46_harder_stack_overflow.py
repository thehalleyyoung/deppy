"""Harder STACK_OVERFLOW: recursive traversal with base case but no depth budget."""

BUG_TYPE = "STACK_OVERFLOW"
BUG_DESC = "Stack overflow from unbounded recursion in complex patterns"

EXAMPLES = [
    (
        "flatten_nested",
        # buggy: no depth limit on nested list flattening
        '''\
def flatten(obj):
    if not isinstance(obj, list):
        return [obj]
    result = []
    for item in obj:
        result.extend(flatten(item))
    return result
''',
        # safe: explicit depth budget
        '''\
def flatten(obj, depth=0):
    if depth > 1000:
        return [obj]
    if not isinstance(obj, list):
        return [obj]
    result = []
    for item in obj:
        result.extend(flatten(item, depth=depth + 1))
    return result
''',
        "Recursive flatten with no depth limit on self-referential structures",
    ),
    (
        "json_walk",
        # buggy: recursive JSON walker without depth cap
        '''\
def count_keys(obj):
    if not isinstance(obj, dict):
        return 0
    total = len(obj)
    for v in obj.values():
        total += count_keys(v)
    return total
''',
        # safe: depth parameter with budget
        '''\
def count_keys(obj, depth=0):
    if depth > 500:
        return 0
    if not isinstance(obj, dict):
        return 0
    total = len(obj)
    for v in obj.values():
        total += count_keys(v, depth=depth + 1)
    return total
''',
        "Recursive dict walker without depth budget",
    ),
    (
        "binary_repr",
        # buggy: recursive binary conversion, no depth cap
        '''\
def to_binary(n):
    if n == 0:
        return "0"
    return to_binary(n // 2) + str(n % 2)
''',
        # safe: add depth budget
        '''\
def to_binary(n, depth=0):
    if depth > 100:
        return ""
    if n == 0:
        return "0"
    return to_binary(n // 2, depth=depth + 1) + str(n % 2)
''',
        "Recursive number conversion with base case but no depth budget",
    ),
]
