"""Tricky NULL_PTR: re-assignment patterns, multiple None sources."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Tricky null pointer with complex None flow"

EXAMPLES = [
    (
        "reassigned_to_none",
        # buggy: variable re-assigned to None then used
        '''\
def process(data):
    result = compute(data)
    result = None
    return result.value
''',
        # safe: don't re-assign to None
        '''\
def process(data):
    result = compute(data)
    if result is not None:
        return result.value
    return None
''',
        "Variable explicitly set to None then attribute accessed",
    ),
    (
        "none_default_param_like",
        # buggy: variable set to None, conditionally overwritten
        '''\
def find_handler(registry, name):
    handler = None
    if name in registry:
        handler = registry[name]
    handler.execute()
''',
        # safe: check before use
        '''\
def find_handler(registry, name):
    handler = None
    if name in registry:
        handler = registry[name]
    if handler is not None:
        handler.execute()
''',
        "Variable initialized to None, conditionally assigned, used unconditionally",
    ),
    (
        "copied_none",
        # buggy: copy propagation of None
        '''\
def use_alias(data):
    x = None
    y = x
    return y.attr
''',
        # safe: check alias
        '''\
def use_alias(data):
    x = None
    y = x
    if y is not None:
        return y.attr
    return None
''',
        "None propagated through variable copy then attribute accessed",
    ),
]
