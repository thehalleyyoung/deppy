"""Tricky NON_TERMINATION: counter going wrong way, missing increment, always-true."""

BUG_TYPE = "NON_TERMINATION"
BUG_DESC = "Tricky infinite loop with subtle counter errors"

EXAMPLES = [
    (
        "wrong_direction_decrement",
        # buggy: counter decrements but loop checks <
        '''\
def count_up(n):
    i = 0
    while i < n:
        process(i)
        i -= 1
    return i
''',
        # safe: correct increment direction
        '''\
def count_up(n):
    i = 0
    while i < n:
        process(i)
        i += 1
    return i
''',
        "Counter decrements but loop condition expects increase",
    ),
    (
        "forgot_increment",
        # buggy: no increment in loop body
        '''\
def drain(queue):
    idx = 0
    while idx < len(queue):
        process(queue[idx])
    return "done"
''',
        # safe: increment index
        '''\
def drain(queue):
    idx = 0
    while idx < len(queue):
        process(queue[idx])
        idx += 1
    return "done"
''',
        "While loop with no increment of loop variable",
    ),
    (
        "wrong_var_incremented",
        # buggy: increments wrong variable
        '''\
def scan(items, limit):
    i = 0
    j = 0
    while i < limit:
        process(items[j])
        j += 1
    return j
''',
        # safe: increment loop variable
        '''\
def scan(items, limit):
    i = 0
    j = 0
    while i < limit:
        process(items[j])
        j += 1
        i += 1
    return j
''',
        "Loop increments j but loop condition checks i",
    ),
    (
        "increment_past_limit",
        # buggy: incrementing by 2 but checking > instead of >=
        '''\
def step_through(data):
    pos = 0
    while pos != len(data):
        process(data[pos])
        pos += 2
    return pos
''',
        # safe: use < comparison
        '''\
def step_through(data):
    pos = 0
    while pos < len(data):
        process(data[pos])
        pos += 2
    return pos
''',
        "Step-by-2 with equality check may skip termination value",
    ),
]
