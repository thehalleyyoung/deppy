"""FP stress: ASSERT_FAIL with valid assertions.

Assertions that cannot fail because their predicates are always true
by construction.  The sheaf section at the assert site provably
satisfies the assertion predicate.
"""

BUG_TYPE = "ASSERT_FAIL"
BUG_DESC = "Assertions that are provably true"

EXAMPLES = [
    (
        "assert_after_construction",
        '''\
def make_list():
    result = []
    assert len(result) > 0
    return result
''',
        '''\
def make_list():
    result = [1, 2, 3]
    assert len(result) > 0
    return result
''',
        "Literal list construction guarantees non-empty",
    ),
    (
        "assert_after_append",
        '''\
def build():
    items = []
    assert items
    return items
''',
        '''\
def build():
    items = []
    items.append(42)
    assert items
    return items
''',
        "append() guarantees non-empty",
    ),
    (
        "assert_type_after_isinstance",
        '''\
def check(x):
    assert isinstance(x, int)
    return x + 1
''',
        '''\
def check(x):
    x = int(x)
    assert isinstance(x, int)
    return x + 1
''',
        "int() coercion guarantees isinstance(int) holds",
    ),
    (
        "assert_range_after_clamp",
        '''\
def bounded(x):
    assert 0 <= x <= 100
    return x
''',
        '''\
def bounded(x):
    x = max(0, min(x, 100))
    assert 0 <= x <= 100
    return x
''',
        "Clamp guarantees range assertion holds",
    ),
    (
        "assert_nonnone_after_check",
        '''\
def process(val):
    assert val is not None
    return val.strip()
''',
        '''\
def process(val):
    if val is None:
        val = ""
    assert val is not None
    return val.strip()
''',
        "Conditional assignment ensures non-None before assert",
    ),
]
