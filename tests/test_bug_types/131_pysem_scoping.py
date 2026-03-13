"""Python semantics: global/nonlocal scoping — UNBOUND_VAR, NULL_PTR."""

BUG_TYPE = "UNBOUND_VAR"
BUG_DESC = "Scoping pitfalls with global, nonlocal, and nested functions"

EXAMPLES = [
    (
        "global_unbound",
        # buggy: refers to global that may not exist
        '''\
def reset_counter():
    global counter
    counter = 0

def get_count():
    return counter_typo
''',
        # safe: correct name
        '''\
counter = 0

def reset_counter():
    global counter
    counter = 0

def get_count():
    global counter
    return counter
''',
        "counter_typo is never defined",
    ),
    (
        "nested_scope_shadow",
        # buggy: inner function shadows variable, outer tries to use it
        '''\
def outer():
    result = compute_value()
    def inner():
        result = None
        return result
    inner()
    return missing_var
''',
        # safe: proper scope
        '''\
def outer():
    result = compute_value()
    def inner():
        local_result = None
        return local_result
    inner()
    return result
''',
        "missing_var is never defined",
    ),
    (
        "conditional_nonlocal",
        # buggy: nonlocal only assigned in one branch
        '''\
def tracker(condition):
    def update():
        nonlocal state
        if condition:
            state = "active"
    state = "initial"
    update()
    return unrelated_name
''',
        # safe: return state
        '''\
def tracker(condition):
    def update():
        nonlocal state
        if condition:
            state = "active"
    state = "initial"
    update()
    return state
''',
        "unrelated_name is never defined",
    ),
]
