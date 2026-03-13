"""FP stress: guard patterns for UNBOUND_VAR.

Variables that appear unbound on some paths but are always bound by the
time they're used — due to conditional assignment in all branches,
default values, or exception handlers.
"""

BUG_TYPE = "UNBOUND_VAR"
BUG_DESC = "Variables always bound before use through all-path assignment"

EXAMPLES = [
    (
        "all_branches_assign",
        '''\
def classify(x):
    if x > 0:
        label = "positive"
    return label
''',
        '''\
def classify(x):
    if x > 0:
        label = "positive"
    elif x < 0:
        label = "negative"
    else:
        label = "zero"
    return label
''',
        "All if/elif/else branches assign label",
    ),
    (
        "default_before_conditional",
        '''\
def status(code):
    if code == 200:
        msg = "ok"
    return msg
''',
        '''\
def status(code):
    msg = "unknown"
    if code == 200:
        msg = "ok"
    elif code == 404:
        msg = "not found"
    return msg
''',
        "Default assignment before conditional guarantees binding",
    ),
    (
        "try_except_binds",
        '''\
def parse(text):
    result = int(text)
    return result
''',
        '''\
def parse(text):
    try:
        result = int(text)
    except ValueError:
        result = 0
    return result
''',
        "Both try and except branches bind result",
    ),
    (
        "loop_with_else_binds",
        '''\
def find(items, target):
    for item in items:
        if item == target:
            found = item
            break
    return found
''',
        '''\
def find(items, target):
    for item in items:
        if item == target:
            found = item
            break
    else:
        found = None
    return found
''',
        "for/else ensures found is always bound",
    ),
    (
        "walrus_always_binds",
        '''\
def first_match(items, pred):
    for item in items:
        if pred(item):
            result = item
    return result
''',
        '''\
def first_match(items, pred):
    result = None
    for item in items:
        if pred(item):
            result = item
            break
    return result
''',
        "Default + break ensures result is always bound",
    ),
]
