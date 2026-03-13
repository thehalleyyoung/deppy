"""Edge-case NON_TERMINATION: wrong-direction counter, unchanged condition."""

BUG_TYPE = "NON_TERMINATION"
BUG_DESC = "Non-termination in edge-case loop patterns"

EXAMPLES = [
    (
        "increment_wrong_dir",
        # buggy: loop counts up but condition expects decrease
        '''\
def drain(n):
    i = n
    while i > 0:
        i += 1
''',
        # safe: decrement toward zero
        '''\
def drain(n):
    i = n
    while i > 0:
        i -= 1
''',
        "Loop variable moves away from termination condition",
    ),
    (
        "forgot_decrement",
        # buggy: loop variable never modified
        '''\
def countdown(n):
    while n > 0:
        do_work(n)
''',
        # safe: decrement in body
        '''\
def countdown(n):
    while n > 0:
        do_work(n)
        n -= 1
''',
        "While loop body does not modify loop variable",
    ),
    (
        "wrong_var_modified",
        # buggy: modifies a different variable than the loop condition
        '''\
def process_remaining(count):
    done = 0
    while count > 0:
        done += 1
''',
        # safe: modify the correct variable
        '''\
def process_remaining(count):
    done = 0
    while count > 0:
        done += 1
        count -= 1
''',
        "Loop body modifies wrong variable, loop variable unchanged",
    ),
    (
        "increment_past_limit",
        # buggy: incrementing when should decrement toward limit
        '''\
def approach_zero(x):
    while x >= 0:
        x += 1
''',
        # safe: decrement
        '''\
def approach_zero(x):
    while x >= 0:
        x -= 1
''',
        "Loop increments when condition expects decrement",
    ),
]
