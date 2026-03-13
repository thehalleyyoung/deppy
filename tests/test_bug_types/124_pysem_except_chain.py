"""Python semantics: exception chaining — KEY_ERROR, NULL_PTR, RUNTIME_ERROR."""

BUG_TYPE = "KEY_ERROR"
BUG_DESC = "Exception chaining and re-raise patterns with missing keys"

EXAMPLES = [
    (
        "except_reraise_keyerror",
        # buggy: catches KeyError, but re-accesses same missing key
        '''\
def get_config(settings, key):
    try:
        return settings[key]
    except KeyError:
        default = settings["default"]
        return default
''',
        # safe: use .get
        '''\
def get_config(settings, key):
    try:
        return settings[key]
    except KeyError:
        return settings.get("default", None)
''',
        "settings['default'] may also be missing",
    ),
    (
        "chained_except_miss",
        # buggy: exception handler accesses dict that may lack key
        '''\
def lookup_chain(primary, fallback, key):
    try:
        return primary[key]
    except KeyError:
        return fallback[key]
''',
        # safe: guard fallback too
        '''\
def lookup_chain(primary, fallback, key):
    try:
        return primary[key]
    except KeyError:
        return fallback.get(key, None)
''',
        "fallback[key] may also raise KeyError",
    ),
    (
        "except_wrong_type_access",
        # buggy: handler assumes dict structure
        '''\
def safe_access(data, path):
    try:
        result = data[path[0]]
        return result[path[1]]
    except (KeyError, IndexError):
        return data[path[2]]
''',
        # safe: use get with default
        '''\
def safe_access(data, path):
    try:
        result = data[path[0]]
        return result[path[1]]
    except (KeyError, IndexError):
        if len(path) > 2 and path[2] in data:
            return data[path[2]]
        return None
''',
        "path[2] may be OOB and data[path[2]] may miss; but KEY_ERROR is main bug",
    ),
]
