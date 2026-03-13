"""Guard stress: walrus operator (:=) patterns.

The walrus operator `(name := expr)` binds and tests in one expression.
Patterns like `if (n := len(data)) > 0:` create a covering sieve split
where the body carries both the binding section (n is bound) and the
refinement section (n > 0 → data is non-empty → INDEX_OOB resolved).
"""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Walrus operator guard patterns"

EXAMPLES = [
    (
        "walrus_len_guard",
        # buggy: index without length check
        '''\
def first(data):
    items = data
    return items[0]
''',
        # safe: walrus binds len and guards in one expression
        '''\
def first(data):
    items = data
    if (n := len(items)) > 0:
        return items[0]
    return None
''',
        "Walrus len check before indexing",
    ),
    (
        "walrus_none_guard",
        # buggy: index without None/length check
        '''\
def try_parse(text):
    result = list(text)
    return result[0]
''',
        # safe: walrus with None check then index
        '''\
def try_parse(text):
    if (result := list(text)) and len(result) > 0:
        return result[0]
    return ""
''',
        "Walrus with None + length check",
    ),
    (
        "walrus_len_second",
        # buggy: access second element without check
        '''\
def second(data):
    items = data
    return items[1]
''',
        # safe: walrus len >= 2 check
        '''\
def second(data):
    items = data
    if (n := len(items)) >= 2:
        return items[1]
    return None
''',
        "Walrus len >= 2 before index 1",
    ),
]
