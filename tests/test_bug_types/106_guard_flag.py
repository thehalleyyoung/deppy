"""Guard stress: boolean flag section transport.

When a boolean variable captures a predicate (`safe = x is not None`),
the information is TRANSPORTED through the flag variable.  Inside
`if safe:`, the original predicate still holds — the flag is a
morphism from the predicate presheaf to a boolean section.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Boolean flag tracking for guards"

EXAMPLES = [
    (
        "flag_is_not_none",
        # buggy: direct attribute access
        '''\
def get_name(user):
    obj = user
    return obj.name
''',
        # safe: flag captures None check
        '''\
def get_name(user):
    obj = user
    is_valid = obj is not None
    if is_valid:
        return obj.name
    return "default"
''',
        "Boolean flag transports None check",
    ),
    (
        "flag_from_function",
        # buggy: attribute access without guard
        '''\
def process(item):
    obj = item
    return obj.value
''',
        # safe: flag from external validation
        '''\
def process(item):
    obj = item
    exists = obj is not None
    if exists:
        return obj.value
    return 0
''',
        "Flag from validation function",
    ),
    (
        "flag_negated",
        # buggy: method call without guard
        '''\
def execute(task):
    t = task
    t.run()
''',
        # safe: negated flag as early return
        '''\
def execute(task):
    t = task
    is_missing = t is None
    if is_missing:
        return
    t.run()
''',
        "Negated flag as early return",
    ),
]
