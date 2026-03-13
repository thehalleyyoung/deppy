"""Python semantics: default mutable arguments — KEY_ERROR, NULL_PTR."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Mutable default argument and None-default pitfalls"

EXAMPLES = [
    (
        "mutable_default_none_return",
        # buggy: function returns None when default list is empty
        '''\
def find_first(items, pred, results=[]):
    for item in items:
        if pred(item):
            results.append(item)
    if results:
        return results[0]

def use(data, pred):
    result = find_first(data, pred)
    return result.strip()
''',
        # safe: guard None return
        '''\
def find_first(items, pred, results=None):
    if results is None:
        results = []
    for item in items:
        if pred(item):
            results.append(item)
    if results:
        return results[0]
    return ""

def use(data, pred):
    result = find_first(data, pred)
    return result.strip()
''',
        "find_first returns None when no match; .strip() on None",
    ),
    (
        "none_default_deref",
        # buggy: None default then dereference
        '''\
def process(data, config=None):
    timeout = config.get("timeout", 30)
    return timeout
''',
        # safe: guard None
        '''\
def process(data, config=None):
    if config is None:
        config = {}
    timeout = config.get("timeout", 30)
    return timeout
''',
        "config is None by default; .get() on None",
    ),
    (
        "optional_callback_none",
        # buggy: optional callback called without None check
        '''\
def transform(data, callback=None):
    result = callback(data)
    return result
''',
        # safe: guard callback
        '''\
def transform(data, callback=None):
    if callback is not None:
        return callback(data)
    return data
''',
        "callback is None by default; None() is not callable",
    ),
]
