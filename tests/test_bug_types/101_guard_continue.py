"""Guard stress: continue/break as loop-local early returns.

Inside a loop, `if bad: continue` creates a covering sieve split
analogous to an early return — the continuation of the loop body
(after the if) lives on the open set where `bad` is false.
This is a loop-local section refinement.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Continue-as-guard patterns"

EXAMPLES = [
    (
        "continue_skip_none",
        # buggy: attribute access on possibly-None items
        '''\
def collect_names(items):
    results = []
    for item in items:
        results.append(item.name)
    return results
''',
        # safe: continue skips None items
        '''\
def collect_names(items):
    results = []
    for item in items:
        if item is None:
            continue
        results.append(item.name)
    return results
''',
        "Continue skips None items in loop",
    ),
    (
        "continue_skip_none_method",
        # buggy: method call on possibly-None
        '''\
def invoke_all(handlers):
    for handler in handlers:
        handler.execute()
''',
        # safe: continue guard
        '''\
def invoke_all(handlers):
    for handler in handlers:
        if handler is None:
            continue
        handler.execute()
''',
        "Continue guards method call in loop",
    ),
    (
        "continue_skip_invalid",
        # buggy: access without type check
        '''\
def sum_values(records):
    total = 0
    for rec in records:
        total += rec.value
    return total
''',
        # safe: continue with isinstance guard
        '''\
def sum_values(records):
    total = 0
    for rec in records:
        if not hasattr(rec, 'value'):
            continue
        total += rec.value
    return total
''',
        "Continue with hasattr guard",
    ),
]
