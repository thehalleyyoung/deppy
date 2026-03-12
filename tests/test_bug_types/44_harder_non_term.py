"""Harder NON_TERMINATION: wrong direction, stale inner var, unmodified condition."""

BUG_TYPE = "NON_TERMINATION"
BUG_DESC = "Non-termination in complex while loop patterns"

EXAMPLES = [
    (
        "countdown_wrong_op",
        # buggy: uses += instead of -= in countdown
        '''\
def drain_queue(queue, limit):
    count = limit
    while count > 0:
        item = queue.pop()
        process(item)
        count += 1
    return "done"
''',
        # safe: correct decrement
        '''\
def drain_queue(queue, limit):
    count = limit
    while count > 0:
        item = queue.pop()
        process(item)
        count -= 1
    return "done"
''',
        "Counter increments instead of decrements toward zero",
    ),
    (
        "index_never_advances",
        # buggy: loop var i is never modified
        '''\
def scan_until(data, target):
    i = 0
    while i < len(data):
        if data[i] == target:
            return i
    return -1
''',
        # safe: increment i each iteration
        '''\
def scan_until(data, target):
    i = 0
    while i < len(data):
        if data[i] == target:
            return i
        i += 1
    return -1
''',
        "Loop index never incremented, causing infinite loop when target not found",
    ),
    (
        "convergence_wrong_sign",
        # buggy: gap should shrink but += makes it grow
        '''\
def converge(start, target, step):
    gap = target - start
    while gap > 0:
        adjust(gap)
        gap += step
    return gap
''',
        # safe: decrement gap
        '''\
def converge(start, target, step):
    gap = target - start
    while gap > 0:
        adjust(gap)
        gap -= step
    return gap
''',
        "Gap variable increases instead of decreasing toward zero",
    ),
]
