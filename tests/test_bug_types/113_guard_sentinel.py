"""Guard stress: sentinel + conditional binding patterns.

A sentinel pattern like `result = None; for ...: if ...: result = X`
followed by `if result is not None: result.method()` combines
conditional binding with a post-loop null guard.  The engine must
recognize the if-guard even though the variable is only conditionally bound.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Sentinel patterns with conditional binding"

EXAMPLES = [
    (
        "sentinel_search",
        # buggy: use sentinel without checking
        '''\
def find_first(items, pred):
    found = None
    for item in items:
        if pred(item):
            found = item
            break
    return found.value
''',
        # safe: check sentinel before use
        '''\
def find_first(items, pred):
    found = None
    for item in items:
        if pred(item):
            found = item
            break
    if found is not None:
        return found.value
    return None
''',
        "Sentinel checked before attribute access",
    ),
    (
        "sentinel_accumulator",
        # buggy: use result without check
        '''\
def best_match(candidates, score_fn):
    best = None
    for c in candidates:
        s = score_fn(c)
        if best is None or s > best:
            best = c
    return best.name
''',
        # safe: guard after loop
        '''\
def best_match(candidates, score_fn):
    best = None
    for c in candidates:
        s = score_fn(c)
        if best is None or s > best:
            best = c
    if best is not None:
        return best.name
    return "none"
''',
        "Sentinel accumulator with post-loop guard",
    ),
    (
        "sentinel_flag_combined",
        # buggy: no guard on conditional result
        '''\
def find_handler(events, kind):
    handler = None
    for ev in events:
        if ev == kind:
            handler = ev
    handler.process()
''',
        # safe: guard before use
        '''\
def find_handler(events, kind):
    handler = None
    for ev in events:
        if ev == kind:
            handler = ev
    if handler is not None:
        handler.process()
''',
        "Sentinel with None guard before method call",
    ),
]
