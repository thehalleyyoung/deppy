"""Guard stress: ternary / conditional expression guards.

An ast.IfExp creates a branched covering sieve just like ast.If:
the true-branch expression lives on the open set where the test holds.
Attribute access in the true branch of `x.attr if x is not None else d`
lives on the non-None fiber — no gluing obstruction.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Ternary expression guards"

EXAMPLES = [
    (
        "ternary_not_none",
        # buggy: attribute access on possibly-None
        '''\
def get_name(user):
    obj = user
    return obj.name
''',
        # safe: ternary guards the access in the true branch
        '''\
def get_name(user):
    obj = user
    return obj.name if obj is not None else "unknown"
''',
        "Ternary guards attribute access in true branch",
    ),
    (
        "ternary_method_call",
        # buggy: method call on possibly-None
        '''\
def format_item(item):
    val = item
    return val.display()
''',
        # safe: ternary with None check
        '''\
def format_item(item):
    val = item
    return val.display() if val is not None else ""
''',
        "Ternary guards method call",
    ),
    (
        "ternary_nested",
        # buggy: access without guard
        '''\
def safe_len(collection):
    obj = collection
    return obj.size
''',
        # safe: nested ternary
        '''\
def safe_len(collection):
    obj = collection
    return obj.size if obj is not None else 0
''',
        "Nested ternary None guard",
    ),
]
