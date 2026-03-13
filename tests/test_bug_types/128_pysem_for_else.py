"""Python semantics: for/else and while/else — UNBOUND_VAR, INDEX_OOB."""

BUG_TYPE = "UNBOUND_VAR"
BUG_DESC = "Variable only bound inside loop; else clause or post-loop uses it"

EXAMPLES = [
    (
        "for_else_unbound",
        # buggy: variable only assigned inside loop
        '''\
def find_item(items, target):
    for item in items:
        if item == target:
            found = item
            break
    else:
        pass
    return found
''',
        # safe: initialize before loop
        '''\
def find_item(items, target):
    found = None
    for item in items:
        if item == target:
            found = item
            break
    return found
''',
        "found may never be assigned if items empty or no match",
    ),
    (
        "while_else_unbound",
        # buggy: var set inside while, used after
        '''\
def drain_queue(q):
    while not q.empty():
        last = q.get()
    return last
''',
        # safe: init before
        '''\
def drain_queue(q):
    last = None
    while not q.empty():
        last = q.get()
    return last
''',
        "last unbound if queue already empty",
    ),
    (
        "loop_var_scope_leak",
        # buggy: loop var leaks scope but may never execute
        '''\
def process_nonempty(items):
    for x in items:
        pass
    return unknown_result
''',
        # safe: handle empty
        '''\
def process_nonempty(items):
    result = None
    for x in items:
        result = x
    return result
''',
        "unknown_result is never defined",
    ),
]
