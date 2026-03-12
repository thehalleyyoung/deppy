"""Harder ASSERT_FAIL: assertions in complex control flow."""

BUG_TYPE = "ASSERT_FAIL"
BUG_DESC = "Assertion failure in complex patterns"

EXAMPLES = [
    (
        "assert_after_transform",
        # buggy: assertion on transformed value that could fail
        '''\
def validate_and_process(items):
    cleaned = [x.strip() for x in items]
    total = sum(len(c) for c in cleaned)
    assert total > 0
    return cleaned
''',
        # safe: try/except guard
        '''\
def validate_and_process(items):
    try:
        cleaned = [x.strip() for x in items]
        total = sum(len(c) for c in cleaned)
        assert total > 0
    except AssertionError:
        return []
    return cleaned
''',
        "Assertion on computed total that may be zero",
    ),
    (
        "assert_config_valid",
        # buggy: assertion on config value from external source
        '''\
def setup(config):
    port = config.get("port", 0)
    assert port > 0
    host = config.get("host", "")
    assert len(host) > 0
    return (host, port)
''',
        # safe: try/except around assertions
        '''\
def setup(config):
    try:
        port = config.get("port", 0)
        assert port > 0
        host = config.get("host", "")
        assert len(host) > 0
    except AssertionError:
        return ("localhost", 8080)
    return (host, port)
''',
        "Assertions on config values that may not satisfy constraints",
    ),
    (
        "assert_invariant",
        # buggy: assertion on loop invariant
        '''\
def process_pairs(data):
    assert len(data) % 2 == 0
    pairs = []
    for i in range(0, len(data), 2):
        pairs.append((data[i], data[i+1]))
    return pairs
''',
        # safe: try/except
        '''\
def process_pairs(data):
    try:
        assert len(data) % 2 == 0
    except AssertionError:
        data = data[:len(data) - 1]
    pairs = []
    for i in range(0, len(data), 2):
        pairs.append((data[i], data[i+1]))
    return pairs
''',
        "Assertion on data length invariant that may not hold",
    ),
]
