"""Hard KEY_ERROR examples — pop without default, nested access, computed keys."""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Key error in harder patterns"

EXAMPLES = [
    (
        "nested_get",
        # buggy: outer key may exist but inner key may not
        '''\
def get_setting(config, section, key):
    if section in config:
        return config[section][key]
    return None
''',
        # safe: check both levels
        '''\
def get_setting(config, section, key):
    if section in config:
        if key in config[section]:
            return config[section][key]
    return None
''',
        "Nested dict: outer key guarded but inner key not checked",
    ),
    (
        "remove_entry",
        # buggy: delete dict entry without checking existence
        '''\
def remove_user(users, uid):
    name = users[uid]
    del users[uid]
    return name
''',
        # safe: check first
        '''\
def remove_user(users, uid):
    if uid in users:
        name = users[uid]
        del users[uid]
        return name
    return None
''',
        "Direct dict access + del without membership check",
    ),
    (
        "multi_key",
        # buggy: access multiple keys, any might be missing
        '''\
def format_record(rec):
    name = rec["name"]
    age = rec["age"]
    city = rec["city"]
    return f"{name}, {age}, {city}"
''',
        # safe: guard all keys
        '''\
def format_record(rec):
    if "name" in rec and "age" in rec and "city" in rec:
        name = rec["name"]
        age = rec["age"]
        city = rec["city"]
        return f"{name}, {age}, {city}"
    return ""
''',
        "Multiple direct dict accesses on same dict, any key might be absent",
    ),
]
