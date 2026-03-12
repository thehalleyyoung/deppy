"""Harder unknown module tests: null pointer from unknown library results."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Null pointer dereference on unknown library return values"

EXAMPLES = [
    (
        "unknown_find_result",
        # buggy: unknown library find may return None
        '''\
import db_orm
def get_user_role(user_id):
    user = db_orm.find_by_id("users", user_id)
    return user.role
''',
        # safe: null check
        '''\
import db_orm
def get_user_role(user_id):
    user = db_orm.find_by_id("users", user_id)
    if user is not None:
        return user.role
    return "unknown"
''',
        "Attribute access on result from unknown ORM that may return None",
    ),
    (
        "unknown_parse_result",
        # buggy: parser may return None
        '''\
import custom_parser
def extract_title(html):
    doc = custom_parser.parse(html)
    return doc.title
''',
        # safe: guard against None
        '''\
import custom_parser
def extract_title(html):
    doc = custom_parser.parse(html)
    if doc:
        return doc.title
    return ""
''',
        "Attribute access on unknown parser result that may be None",
    ),
    (
        "unknown_cache_get",
        # buggy: cache miss returns None
        '''\
import redis_client
def get_cached_name(key):
    entry = redis_client.get(key)
    return entry.decode()
''',
        # safe: null check
        '''\
import redis_client
def get_cached_name(key):
    entry = redis_client.get(key)
    if entry is not None:
        return entry.decode()
    return ""
''',
        "Method call on cache result that may be None",
    ),
]
