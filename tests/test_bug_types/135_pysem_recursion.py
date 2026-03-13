"""Python semantics: recursion depth and termination — STACK_OVERFLOW, NON_TERMINATION."""

BUG_TYPE = "NON_TERMINATION"
BUG_DESC = "Recursion that may not terminate or stack overflow"

EXAMPLES = [
    (
        "mutual_recursion_loop",
        # buggy: mutual recursion with no base case convergence
        '''\
def is_even(n):
    if n == 0:
        return True
    return is_odd(n + 1)

def is_odd(n):
    if n == 0:
        return False
    return is_even(n - 1)
''',
        # safe: converge toward 0
        '''\
def is_even(n):
    if n == 0:
        return True
    return is_odd(n - 1)

def is_odd(n):
    if n == 0:
        return False
    return is_even(n - 1)
''',
        "is_even calls is_odd(n+1) which calls is_even(n); cycle doesn't shrink",
    ),
    (
        "while_missing_update",
        # buggy: while loop condition never changes
        '''\
def consume(data):
    idx = 0
    while idx < len(data):
        process(data[idx])
    return idx
''',
        # safe: increment idx
        '''\
def consume(data):
    idx = 0
    while idx < len(data):
        process(data[idx])
        idx += 1
    return idx
''',
        "idx never incremented; infinite loop",
    ),
    (
        "retry_no_backoff",
        # buggy: retry loop with condition that can't change
        '''\
def fetch_with_retry(url, retries):
    result = None
    while result is None:
        result = try_fetch(url)
    return result
''',
        # safe: bounded retries
        '''\
def fetch_with_retry(url, retries):
    result = None
    attempts = 0
    while result is None and attempts < retries:
        result = try_fetch(url)
        attempts += 1
    return result
''',
        "If try_fetch always returns None, loop never terminates",
    ),
]
