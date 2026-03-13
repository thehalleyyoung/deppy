"""Edge-case UNBOUND_VAR: nested if, loop-dependent, with-block."""

BUG_TYPE = "UNBOUND_VAR"
BUG_DESC = "Unbound variable in edge-case control flow"

EXAMPLES = [
    (
        "nested_branch_bind",
        # buggy: variable bound only in deeply nested branch
        '''\
def categorize(x, y):
    if x > 0:
        if y > 0:
            label = "both_positive"
    return label
''',
        # safe: default binding
        '''\
def categorize(x, y):
    label = "unknown"
    if x > 0:
        if y > 0:
            label = "both_positive"
    return label
''',
        "Variable bound only in deeply nested if branch",
    ),
    (
        "for_break_bind",
        # buggy: variable only bound if loop body hits condition
        '''\
def first_over(values, threshold):
    for v in values:
        if v > threshold:
            result = v
            break
    return result
''',
        # safe: default before loop
        '''\
def first_over(values, threshold):
    result = None
    for v in values:
        if v > threshold:
            result = v
            break
    return result
''',
        "Variable bound inside loop conditional, may never execute",
    ),
    (
        "multi_branch_partial",
        # buggy: only some branches bind the variable
        '''\
def grade(score):
    if score >= 90:
        letter = "A"
    elif score >= 80:
        letter = "B"
    return letter
''',
        # safe: cover all branches
        '''\
def grade(score):
    letter = "F"
    if score >= 90:
        letter = "A"
    elif score >= 80:
        letter = "B"
    return letter
''',
        "Variable not bound in else branch of if-elif chain",
    ),
    (
        "while_dependent_bind",
        # buggy: variable only bound if while condition is true
        '''\
def consume_queue(queue):
    while len(queue) > 0:
        item = queue.pop(0)
    return item
''',
        # safe: default before loop
        '''\
def consume_queue(queue):
    item = None
    while len(queue) > 0:
        item = queue.pop(0)
    return item
''',
        "Variable bound inside while loop, empty loop leaves unbound",
    ),
]
