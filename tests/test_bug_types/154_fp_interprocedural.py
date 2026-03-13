"""FP stress: complex interprocedural guards.

Guards established in one function that protect code in another.
A callee validates before use; a caller validates before passing.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Cross-function guards"

EXAMPLES = [
    (
        "callee_validates_param",
        '''\
def use_connection(conn):
    return conn.execute("SELECT 1")
''',
        '''\
def use_connection(conn):
    if conn is None:
        raise RuntimeError("no connection")
    return conn.execute("SELECT 1")
''',
        "Callee self-validates its parameter",
    ),
    (
        "caller_validates_before_pass",
        '''\
def worker(item):
    return item.process()

def dispatch(items):
    for item in items:
        worker(item)
''',
        '''\
def worker(item):
    return item.process()

def dispatch(items):
    for item in items:
        if item is not None:
            worker(item)
''',
        "Caller filters None before passing to worker",
    ),
    (
        "factory_guarantees_nonnull",
        '''\
def create_obj():
    obj = None
    return obj

def use_obj():
    obj = create_obj()
    return obj.value
''',
        '''\
def create_obj():
    return {"value": 42}

def use_obj():
    obj = create_obj()
    return obj["value"]
''',
        "Factory returns dict literal (never None), safe to access",
    ),
    (
        "filter_none_with_comprehension",
        '''\
def sum_values(items):
    total = 0
    for item in items:
        total += item.amount
    return total
''',
        '''\
def sum_values(items):
    total = 0
    valid_items = [item for item in items if item is not None]
    for item in valid_items:
        total += item.amount
    return total
''',
        "List comprehension filters None before iteration",
    ),
    (
        "guard_by_construction",
        '''\
def first(items):
    return items[0].name
''',
        '''\
def make_items():
    return [type("Item", (), {"name": "a"})()]

def first():
    items = make_items()
    return items[0].name
''',
        "items constructed with known length and non-None elements",
    ),
]
