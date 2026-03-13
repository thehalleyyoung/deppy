"""Edge-case NULL_PTR: chained attribute, dict.get, conditional assignment."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Null pointer in edge-case patterns"

EXAMPLES = [
    (
        "chained_attr_access",
        # buggy: deep attribute chain on possibly-None variable
        '''\
def get_city(user):
    profile = lookup(user)
    return profile.address.city
''',
        # safe: None check before chained access
        '''\
def get_city(user):
    profile = lookup(user)
    if profile is not None:
        return profile.address.city
    return ""
''',
        "Deep attribute chain on result of function call assigned to variable",
    ),
    (
        "dict_get_attr",
        # buggy: dict.get() returns None by default, then attribute access
        '''\
def user_email(users, uid):
    user = users.get(uid)
    return user.email
''',
        # safe: None check
        '''\
def user_email(users, uid):
    user = users.get(uid)
    if user is not None:
        return user.email
    return ""
''',
        "Attribute access on dict.get() result that may be None",
    ),
    (
        "conditional_init_attr",
        # buggy: assigned only in one branch, used unconditionally
        '''\
def select_handler(config, mode):
    handler = None
    if mode == "fast":
        handler = FastHandler(config)
    handler.run()
''',
        # safe: check before use
        '''\
def select_handler(config, mode):
    handler = None
    if mode == "fast":
        handler = FastHandler(config)
    if handler is not None:
        handler.run()
''',
        "Attribute access on variable initialized to None, conditionally reassigned",
    ),
    (
        "search_result_attr",
        # buggy: search may return None
        '''\
def display_match(pattern, text):
    match = find_match(pattern, text)
    return match.group
''',
        # safe: check result
        '''\
def display_match(pattern, text):
    match = find_match(pattern, text)
    if match is not None:
        return match.group
    return ""
''',
        "Attribute access on search result that may be None",
    ),
]
