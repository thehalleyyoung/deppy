"""Tricky UNBOUND_VAR: conditional assignment, exception path, for-else."""

BUG_TYPE = "UNBOUND_VAR"
BUG_DESC = "Tricky unbound variable with complex control flow"

EXAMPLES = [
    (
        "if_else_one_branch",
        # buggy: variable assigned only in if branch
        '''\
def categorize(score):
    if score > 90:
        label = "A"
    return label
''',
        # safe: assign in both branches
        '''\
def categorize(score):
    if score > 90:
        label = "A"
    else:
        label = "B"
    return label
''',
        "Variable assigned only in if branch, used unconditionally",
    ),
    (
        "multi_branch_miss",
        # buggy: variable only assigned in some branches
        '''\
def lookup(key, mode):
    if mode == "fast":
        result = quick_search(key)
    elif mode == "deep":
        result = deep_search(key)
    return result
''',
        # safe: default before branches
        '''\
def lookup(key, mode):
    result = None
    if mode == "fast":
        result = quick_search(key)
    elif mode == "deep":
        result = deep_search(key)
    return result
''',
        "Variable assigned in if/elif but not else, used after",
    ),
    (
        "nested_if_unbound",
        # buggy: nested condition leaves var unbound
        '''\
def process_input(data, flag):
    if flag:
        if data:
            output = transform(data)
    return output
''',
        # safe: default before nesting
        '''\
def process_input(data, flag):
    output = None
    if flag:
        if data:
            output = transform(data)
    return output
''',
        "Nested conditional assignment leaves variable unbound",
    ),
    (
        "while_dependent_unbound",
        # buggy: variable only assigned in while body
        '''\
def find_first(items, pred):
    i = 0
    while i < len(items):
        if pred(items[i]):
            found = items[i]
        i += 1
    return found
''',
        # safe: default before loop
        '''\
def find_first(items, pred):
    found = None
    i = 0
    while i < len(items):
        if pred(items[i]):
            found = items[i]
        i += 1
    return found
''',
        "Variable only assigned inside while-loop conditional",
    ),
]
