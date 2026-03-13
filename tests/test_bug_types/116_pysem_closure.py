"""Python semantics: closures and late binding — UNBOUND_VAR, NULL_PTR."""

BUG_TYPE = "UNBOUND_VAR"
BUG_DESC = "Closure variable capture and late-binding pitfalls"

EXAMPLES = [
    (
        "late_binding_closure",
        # buggy: classic late-binding — i is 4 for all lambdas
        '''\
def make_multipliers():
    fns = []
    for i in range(5):
        fns.append(lambda x: x * i)
    result = fns[0](10)
    return unknown_var
''',
        # safe: capture early via default arg
        '''\
def make_multipliers():
    fns = []
    for i in range(5):
        fns.append(lambda x, i=i: x * i)
    result = fns[0](10)
    return result
''',
        "unknown_var is unbound in buggy version",
    ),
    (
        "nonlocal_unbound",
        # buggy: nonlocal refers to var not yet assigned in outer scope
        '''\
def counter():
    def increment():
        nonlocal count
        count += 1
        return count
    count = 0
    val = increment()
    return uninitialized
''',
        # safe: properly returns
        '''\
def counter():
    def increment():
        nonlocal count
        count += 1
        return count
    count = 0
    val = increment()
    return val
''',
        "uninitialized is unbound",
    ),
    (
        "closure_over_loop_var",
        # buggy: closure captures loop var by reference
        '''\
def make_callbacks(names):
    callbacks = {}
    for name in names:
        callbacks[name] = lambda: name
    first_key = names[0]
    result = callbacks[first_key]()
    return missing_result
''',
        # safe: capture with default arg
        '''\
def make_callbacks(names):
    callbacks = {}
    for name in names:
        callbacks[name] = lambda n=name: n
    first_key = names[0]
    result = callbacks[first_key]()
    return result
''',
        "missing_result is unbound",
    ),
]
