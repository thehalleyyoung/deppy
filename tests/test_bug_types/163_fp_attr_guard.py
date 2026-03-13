"""FP stress: exception-guarded attribute/method access.

When attribute access is wrapped in try/except AttributeError, the
potential NULL_PTR or TYPE_ERROR is fully handled.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Try/except AttributeError guards attribute access"

EXAMPLES = [
    (
        "try_except_attributeerror",
        '''\
def get_name(obj):
    return obj.name
''',
        '''\
def get_name(obj):
    try:
        return obj.name
    except AttributeError:
        return "unknown"
''',
        "AttributeError caught for None/missing attribute",
    ),
    (
        "getattr_with_default",
        '''\
def get_label(obj):
    return obj.label
''',
        '''\
def get_label(obj):
    return getattr(obj, 'label', 'default')
''',
        "getattr with default never raises",
    ),
    (
        "hasattr_before_access",
        '''\
def get_size(obj):
    return obj.size
''',
        '''\
def get_size(obj):
    if hasattr(obj, 'size'):
        return obj.size
    return 0
''',
        "hasattr check before attribute access",
    ),
    (
        "optional_chaining_pattern",
        '''\
def get_city(user):
    return user.address.city
''',
        '''\
def get_city(user):
    addr = getattr(user, 'address', None)
    if addr is None:
        return None
    return getattr(addr, 'city', None)
''',
        "Optional chaining via getattr+None check",
    ),
    (
        "try_multiple_attrs",
        '''\
def describe(obj):
    return f"{obj.name}: {obj.desc}"
''',
        '''\
def describe(obj):
    try:
        return f"{obj.name}: {obj.desc}"
    except (AttributeError, TypeError):
        return "unknown"
''',
        "Both attribute accesses covered by single try/except",
    ),
]
