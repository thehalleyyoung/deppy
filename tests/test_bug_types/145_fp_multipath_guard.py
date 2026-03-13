"""FP stress: multi-path guard patterns.

Real code often guards through multiple converging paths — every branch
either guards, returns early, or raises, so the continuation is safe.
A naïve analyzer that doesn't track all paths will fire falsely.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Multi-path convergence guards"

EXAMPLES = [
    (
        "all_branches_guard_or_return",
        '''\
def process(obj):
    x = obj
    return x.name
''',
        '''\
def process(obj):
    x = obj
    if x is None:
        return "default"
    return x.name
''',
        "Early return on None makes continuation safe",
    ),
    (
        "all_branches_assign_safe",
        '''\
def get_val(data):
    result = data
    return result.strip()
''',
        '''\
def get_val(data):
    if data is None:
        result = ""
    else:
        result = data
    return result.strip()
''',
        "All branches assign non-None to result",
    ),
    (
        "guard_via_raise_in_helper",
        '''\
def compute(cfg):
    x = cfg
    return x.timeout * 2
''',
        '''\
def validate(cfg):
    if cfg is None:
        raise ValueError("cfg required")

def compute(cfg):
    validate(cfg)
    return cfg.timeout * 2
''',
        "Precondition via helper raises on None",
    ),
    (
        "guard_across_try_else",
        '''\
def fetch(d, key):
    val = d.get(key)
    return val.upper()
''',
        '''\
def fetch(d, key):
    try:
        val = d[key]
    except KeyError:
        val = "fallback"
    return val.upper()
''',
        "try/except guarantees val is always a string",
    ),
    (
        "nested_guard_convergence",
        '''\
def process(items, idx):
    item = items[idx]
    return item.value
''',
        '''\
def process(items, idx):
    if idx < 0 or idx >= len(items):
        return None
    item = items[idx]
    if item is None:
        return 0
    return item.value
''',
        "Both bounds and None are guarded before .value access",
    ),
]
