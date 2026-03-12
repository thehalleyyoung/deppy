"""UNKNOWN_MODULE: resilience test — the detector should still find bugs
when code uses unknown/third-party modules, by applying pessimistic
presheaf sections to unknown return values.

These tests verify the sheaf gluing obstruction approach degrades
gracefully: even when we cannot resolve a module, the restriction map
from the unknown call's stalk (all-UNKNOWN) to the requirement site
still reveals obstructions.
"""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Null dereference through unknown module return"

EXAMPLES = [
    (
        "unknown_return_deref",
        # buggy: use return value from unknown lib without None check
        '''\
import acme_lib
def process(data):
    result = acme_lib.transform(data)
    return result.values()
''',
        # safe: guard against None from unknown call
        '''\
import acme_lib
def process(data):
    result = acme_lib.transform(data)
    if result is not None:
        return result.values()
    return []
''',
        "Unknown module return may be None; attribute access needs guard",
    ),
    (
        "unknown_chained_deref",
        # buggy: chained attribute on unknown module return
        '''\
import unknown_db
def get_user_name(uid):
    user = unknown_db.find_user(uid)
    return user.profile.name
''',
        # safe: check each level for None
        '''\
import unknown_db
def get_user_name(uid):
    user = unknown_db.find_user(uid)
    if user is not None:
        return user.profile.name
    return ""
''',
        "Chained deref on unknown return needs None guard",
    ),
    (
        "aliased_unknown_import",
        # buggy: aliased import, return used without check
        '''\
import acme_processing as ap
def run(items):
    out = ap.batch_run(items)
    return out.summary()
''',
        # safe: None guard
        '''\
import acme_processing as ap
def run(items):
    out = ap.batch_run(items)
    if out is not None:
        return out.summary()
    return {}
''',
        "Aliased unknown import return needs None guard",
    ),
]
