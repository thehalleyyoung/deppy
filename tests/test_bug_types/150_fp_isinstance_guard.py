"""FP stress: isinstance/type narrowing guards for TYPE_ERROR.

An isinstance() check narrows the type section to a specific fiber in
the presheaf.  Operations that would be invalid on the unchecked type
become valid after the check.
"""

BUG_TYPE = "TYPE_ERROR"
BUG_DESC = "isinstance guards prevent type errors"

EXAMPLES = [
    (
        "isinstance_before_arithmetic",
        '''\
def double(x):
    return x * 2
''',
        '''\
def double(x):
    if isinstance(x, (int, float)):
        return x * 2
    return 0
''',
        "isinstance ensures x supports multiplication",
    ),
    (
        "isinstance_before_str_ops",
        '''\
def normalize(val):
    return val.strip().lower()
''',
        '''\
def normalize(val):
    if isinstance(val, str):
        return val.strip().lower()
    return str(val).strip().lower()
''',
        "isinstance(str) before string methods",
    ),
    (
        "isinstance_union_dispatch",
        '''\
def process(data):
    return data["key"]
''',
        '''\
def process(data):
    if isinstance(data, dict):
        return data.get("key")
    elif isinstance(data, list):
        return data[0] if data else None
    return None
''',
        "isinstance-based dispatch handles each type safely",
    ),
    (
        "callable_check_before_call",
        '''\
def run(callback, arg):
    return callback(arg)
''',
        '''\
def run(callback, arg):
    if callable(callback):
        return callback(arg)
    return None
''',
        "callable() check before invocation",
    ),
    (
        "type_coercion_safe",
        '''\
def add_values(a, b):
    return a + b
''',
        '''\
def add_values(a, b):
    return float(a) + float(b)
''',
        "float() coercion ensures numeric types",
    ),
]
