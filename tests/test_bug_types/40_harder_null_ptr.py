"""Harder NULL_PTR: multi-step attribute access, nested control flow, truthiness guards."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Null pointer dereference in complex patterns"

EXAMPLES = [
    (
        "lookup_then_use",
        # buggy: dict.get returns None, then access attribute on result
        '''\
def get_user_email(registry, uid):
    user = registry.get(uid)
    return user.email
''',
        # safe: truthiness guard
        '''\
def get_user_email(registry, uid):
    user = registry.get(uid)
    if user:
        return user.email
    return None
''',
        "Attribute access on dict.get result which may be None",
    ),
    (
        "nested_optional",
        # buggy: first lookup may be None, then chain
        '''\
def get_address_city(records, name):
    record = records.get(name)
    addr = record.address
    return addr.city
''',
        # safe: guard each level
        '''\
def get_address_city(records, name):
    record = records.get(name)
    if record is not None:
        addr = record.address
        if addr is not None:
            return addr.city
    return None
''',
        "Chained attribute access through multiple optional levels",
    ),
    (
        "find_in_list",
        # buggy: dict.get() may return None, then access attribute on it
        '''\
def first_active_name(records, target_id):
    found = records.get(target_id)
    return found.name
''',
        # safe: check found before use
        '''\
def first_active_name(records, target_id):
    found = records.get(target_id)
    if found is not None:
        return found.name
    return ""
''',
        "Attribute access on dict.get() result that may be None",
    ),
]
