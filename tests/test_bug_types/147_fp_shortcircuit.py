"""FP stress: short-circuit boolean evaluation as guards.

Python's `and` / `or` short-circuit: `x and x.attr` never evaluates
x.attr when x is falsy.  `x or default` guarantees the result is
truthy.  These are implicit guards that a sheaf-theoretic analysis must
recognize via the restriction map on the boolean site cover.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Short-circuit guards"

EXAMPLES = [
    (
        "and_guards_attr",
        '''\
def get_name(user):
    u = user
    return u.name
''',
        '''\
def get_name(user):
    return user and user.name
''',
        "`and` short-circuits: user.name only evaluated when user is truthy",
    ),
    (
        "or_provides_fallback",
        '''\
def get_host(config):
    host = config.get("host")
    return host.lower()
''',
        '''\
def get_host(config):
    host = config.get("host") or "localhost"
    return host.lower()
''',
        "`or` guarantees host is truthy (a real string)",
    ),
    (
        "and_chain_safe",
        '''\
def deep_access(obj):
    x = obj
    return x.a.b.c
''',
        '''\
def deep_access(obj):
    return obj and obj.a and obj.a.b and obj.a.b.c
''',
        "Chained `and` guards each level of attribute access",
    ),
    (
        "ternary_none_safe",
        '''\
def length(lst):
    x = lst
    return len(x)
''',
        '''\
def length(lst):
    return len(lst) if lst is not None else 0
''',
        "Ternary guards None before len()",
    ),
    (
        "or_default_arithmetic",
        '''\
def safe_divide(a, b):
    return a / b
''',
        '''\
def safe_divide(a, b):
    divisor = b or 1
    return a / divisor
''',
        "`or 1` ensures divisor is never zero",
    ),
]
