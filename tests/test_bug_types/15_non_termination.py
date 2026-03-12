"""NON_TERMINATION: while loop without ranking function — the loop
variable is never modified in the body, so the ranking presheaf
has no well-founded descent.
"""

BUG_TYPE = "NON_TERMINATION"
BUG_DESC = "Non-termination (no ranking function)"

EXAMPLES = [
    (
        "spin_loop",
        # buggy: while condition variable not modified
        '''\
def drain(queue):
    while len(queue) > 0:
        pass
''',
        # safe: pop modifies the loop variable
        '''\
def drain(queue):
    while len(queue) > 0:
        queue.pop()
''',
        "while len(q) > 0 with no body modification",
    ),
    (
        "counter_stuck",
        # buggy: counter checked but never incremented
        '''\
def wait_for(count, limit):
    while count < limit:
        print("waiting")
''',
        # safe: counter incremented in body
        '''\
def wait_for(count, limit):
    while count < limit:
        print("waiting")
        count += 1
''',
        "while count < limit without incrementing count",
    ),
    (
        "flag_loop",
        # buggy: flag checked but never set
        '''\
def poll(done):
    while not done:
        process()
''',
        # safe: flag is set in the body (break as evidence)
        '''\
def poll(done):
    while not done:
        result = process()
        if result:
            done = True
''',
        "while not done without setting done",
    ),
]
