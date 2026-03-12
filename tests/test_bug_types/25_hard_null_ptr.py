"""Hard NULL_PTR examples — chained attributes, conditional None, deeper patterns."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Null dereference in harder patterns"

EXAMPLES = [
    (
        "chained_attr",
        # buggy: a.b may be None, then .c dereferences it
        '''\
def get_city(user):
    addr = user.address
    return addr.city
''',
        # safe: guard intermediate
        '''\
def get_city(user):
    addr = user.address
    if addr is not None:
        return addr.city
    return ""
''',
        "Chained attribute where intermediate may be None",
    ),
    (
        "conditional_none",
        # buggy: result is None on the else branch, then used unconditionally
        '''\
def find_and_format(items, target):
    result = None
    for item in items:
        if item == target:
            result = item
    return result.upper()
''',
        # safe: check result before calling method
        '''\
def find_and_format(items, target):
    result = None
    for item in items:
        if item == target:
            result = item
    if result is not None:
        return result.upper()
    return ""
''',
        "Variable initialized to None, conditionally set, then dereferenced",
    ),
    (
        "dict_get_chain",
        # buggy: .get() may return None, then access attribute on it
        '''\
def user_email(db, uid):
    user = db.get(uid)
    return user.email
''',
        # safe: guard the get result
        '''\
def user_email(db, uid):
    user = db.get(uid)
    if user is not None:
        return user.email
    return None
''',
        "dict.get() returns None when key absent, then attribute access",
    ),
]
