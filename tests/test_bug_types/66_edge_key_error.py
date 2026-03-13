"""Edge-case KEY_ERROR: nested dict, augmented assign, dynamic key."""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Key error in edge-case dict patterns"

EXAMPLES = [
    (
        "nested_dict_access",
        # buggy: inner dict key not checked
        '''\
def get_nested(data, section, field):
    if section in data:
        return data[section][field]
    return None
''',
        # safe: check both levels
        '''\
def get_nested(data, section, field):
    if section in data:
        inner = data[section]
        if field in inner:
            return inner[field]
    return None
''',
        "Nested dict access where inner key may be missing",
    ),
    (
        "counter_increment",
        # buggy: augmented assign on missing key
        '''\
def count_words(words):
    counts = {}
    for w in words:
        counts[w] += 1
    return counts
''',
        # safe: use .get() default
        '''\
def count_words(words):
    counts = {}
    for w in words:
        counts[w] = counts.get(w, 0) + 1
    return counts
''',
        "Augmented assign on dict key before initialization",
    ),
    (
        "two_dict_lookup",
        # buggy: key from one dict used in another
        '''\
def translate(word, en_to_code, code_to_name):
    code = en_to_code[word]
    return code_to_name[code]
''',
        # safe: membership checks
        '''\
def translate(word, en_to_code, code_to_name):
    if word in en_to_code:
        code = en_to_code[word]
        if code in code_to_name:
            return code_to_name[code]
    return None
''',
        "Chained dict lookups where intermediate key may be missing",
    ),
    (
        "config_required_key",
        # buggy: accessing required config that may be absent
        '''\
def init_service(config):
    host = config["host"]
    port = config["port"]
    return connect(host, port)
''',
        # safe: membership checks for each key
        '''\
def init_service(config):
    if "host" in config and "port" in config:
        host = config["host"]
        port = config["port"]
        return connect(host, port)
    return None
''',
        "Multiple required dict keys that may be absent",
    ),
]
