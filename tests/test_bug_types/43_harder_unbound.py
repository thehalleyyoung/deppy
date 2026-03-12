"""Harder UNBOUND_VAR: deeply nested conditional binding, exception paths."""

BUG_TYPE = "UNBOUND_VAR"
BUG_DESC = "Unbound variable in complex control flow"

EXAMPLES = [
    (
        "nested_conditional_bind",
        # buggy: result only bound inside nested if
        '''\
def classify(value, threshold, strict):
    if value > threshold:
        if strict:
            label = "high_strict"
        else:
            label = "high"
    return label
''',
        # safe: default binding before conditional
        '''\
def classify(value, threshold, strict):
    label = "normal"
    if value > threshold:
        if strict:
            label = "high_strict"
        else:
            label = "high"
    return label
''',
        "Variable only bound inside nested if branches, not on else path",
    ),
    (
        "loop_dependent_bind",
        # buggy: best only bound if loop body executes AND condition met
        '''\
def find_best(candidates, score_fn, min_score):
    for c in candidates:
        s = score_fn(c)
        if s >= min_score:
            best = c
    return best
''',
        # safe: default before loop
        '''\
def find_best(candidates, score_fn, min_score):
    best = None
    for c in candidates:
        s = score_fn(c)
        if s >= min_score:
            best = c
    return best
''',
        "Variable bound inside for loop conditional, empty loop leaves unbound",
    ),
    (
        "exception_path_bind",
        # buggy: conn only bound in try, used after except
        '''\
def fetch_data(url, retries):
    try:
        conn = open_connection(url)
    except TimeoutError:
        log("timeout")
    data = conn.read()
    return data
''',
        # safe: bind data before try to guarantee it exists at return
        '''\
def fetch_data(url, retries):
    data = None
    try:
        conn = open_connection(url)
        data = conn.read()
    except TimeoutError:
        log("timeout")
    return data
''',
        "Variable bound in try block, used after except that may skip binding",
    ),
]
