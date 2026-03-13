"""Edge-case ASSERT_FAIL: assert with complex conditions."""

BUG_TYPE = "ASSERT_FAIL"
BUG_DESC = "Assert fail in edge-case assertion patterns"

EXAMPLES = [
    (
        "assert_range",
        # buggy: assert on range condition
        '''\
def set_volume(level):
    assert 0 <= level <= 100
    apply_volume(level)
''',
        # safe: if-guard instead of assert
        '''\
def set_volume(level):
    if not (0 <= level <= 100):
        return
    apply_volume(level)
''',
        "Assert on range condition that may fail",
    ),
    (
        "assert_type",
        # buggy: assert on isinstance
        '''\
def process_item(item):
    assert isinstance(item, dict)
    return item.keys()
''',
        # safe: if-guard instead of assert
        '''\
def process_item(item):
    if not isinstance(item, dict):
        return None
    return item.keys()
''',
        "Assert on type check that may fail",
    ),
    (
        "assert_nonempty",
        # buggy: assert on non-empty sequence
        '''\
def first_element(items):
    assert len(items) > 0
    return items[0]
''',
        # safe: if-guard instead of assert
        '''\
def first_element(items):
    if not items:
        return None
    return items[0]
''',
        "Assert on non-empty that may fail with empty input",
    ),
    (
        "assert_not_none",
        # buggy: assert value is not None
        '''\
def use_result(result):
    assert result is not None
    return result.value
''',
        # safe: if-guard instead of assert
        '''\
def use_result(result):
    if result is None:
        return None
    return result.value
''',
        "Assert on not-None that may fail",
    ),
]
