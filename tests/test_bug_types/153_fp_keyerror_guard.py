"""FP stress: try/except for KEY_ERROR.

When a dict access is wrapped in try/except KeyError, the bug is
handled.  Also tests dict.get(), dict.setdefault(), `in` checks.
"""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Dict access guarded by try/except or membership check"

EXAMPLES = [
    (
        "try_except_keyerror",
        '''\
def get_setting(config, name):
    return config[name]
''',
        '''\
def get_setting(config, name):
    try:
        return config[name]
    except KeyError:
        return None
''',
        "KeyError caught explicitly",
    ),
    (
        "in_check_before_access",
        '''\
def get_value(d, key):
    return d[key]
''',
        '''\
def get_value(d, key):
    if key in d:
        return d[key]
    return None
''',
        "Membership check before dict access",
    ),
    (
        "dict_get_default",
        '''\
def fetch_port(config):
    return config["port"]
''',
        '''\
def fetch_port(config):
    return config.get("port", 8080)
''',
        "dict.get with default avoids KeyError",
    ),
    (
        "setdefault_then_access",
        '''\
def ensure_and_get(d, key):
    return d[key]
''',
        '''\
def ensure_and_get(d, key):
    d.setdefault(key, [])
    return d[key]
''',
        "setdefault ensures key exists before access",
    ),
    (
        "nested_dict_safe",
        '''\
def deep_get(d, k1, k2):
    return d[k1][k2]
''',
        '''\
def deep_get(d, k1, k2):
    inner = d.get(k1)
    if inner is None:
        return None
    return inner.get(k2)
''',
        "Safe nested dict access via .get() chain",
    ),
]
