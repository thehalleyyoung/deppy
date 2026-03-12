"""Hard NON_TERMINATION examples — wrong direction counter, stale condition, deeper patterns."""

BUG_TYPE = "NON_TERMINATION"
BUG_DESC = "Non-termination in harder patterns"

EXAMPLES = [
    (
        "wrong_direction",
        # buggy: counter goes the wrong way relative to the condition
        '''\
def countdown_broken(n):
    i = 0
    while i < n:
        i -= 1
    return i
''',
        # safe: increment toward the bound
        '''\
def countdown_broken(n):
    i = 0
    while i < n:
        i += 1
    return i
''',
        "Counter decrements when condition checks less-than — never reaches bound",
    ),
    (
        "stale_var",
        # buggy: loop condition uses a variable that is never reassigned in body
        '''\
def drain_queue(q, limit):
    count = 0
    while count < limit:
        q.pop(0)
    return q
''',
        # safe: increment count in body
        '''\
def drain_queue(q, limit):
    count = 0
    while count < limit:
        q.pop(0)
        count += 1
    return q
''',
        "Loop condition variable not modified in the loop body",
    ),
    (
        "nested_while_stuck",
        # buggy: inner loop variable not modified
        '''\
def process_matrix(rows):
    i = 0
    while i < len(rows):
        j = 0
        while j < len(rows[i]):
            rows[i][j] *= 2
        i += 1
    return rows
''',
        # safe: increment j
        '''\
def process_matrix(rows):
    i = 0
    while i < len(rows):
        j = 0
        while j < len(rows[i]):
            rows[i][j] *= 2
            j += 1
        i += 1
    return rows
''',
        "Inner while loop variable j not incremented in body",
    ),
]
