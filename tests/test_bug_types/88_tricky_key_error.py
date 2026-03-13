"""Tricky KEY_ERROR: nested dict, iteration-dependent key, format string key."""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Tricky key error with complex access patterns"

EXAMPLES = [
    (
        "nested_dict_access",
        # buggy: nested dict access without key check
        '''\
def get_city(user):
    return user["address"]["city"]
''',
        # safe: check keys at each level
        '''\
def get_city(user):
    if "address" in user and "city" in user["address"]:
        return user["address"]["city"]
    return ""
''',
        "Nested dict access without key existence checks",
    ),
    (
        "required_keys_batch",
        # buggy: accessing multiple keys without check
        '''\
def summarize(record):
    name = record["name"]
    age = record["age"]
    return f"{name}: {age}"
''',
        # safe: check all keys
        '''\
def summarize(record):
    if "name" in record and "age" in record:
        name = record["name"]
        age = record["age"]
        return f"{name}: {age}"
    return ""
''',
        "Multiple required keys accessed without membership test",
    ),
    (
        "counter_increment",
        # buggy: counter increment without default
        '''\
def count_words(text, counts):
    for word in text.split():
        counts[word] += 1
    return counts
''',
        # safe: check key first
        '''\
def count_words(text, counts):
    for word in text.split():
        if word in counts:
            counts[word] += 1
        else:
            counts[word] = 1
    return counts
''',
        "Dict counter increment without key existence check",
    ),
]
