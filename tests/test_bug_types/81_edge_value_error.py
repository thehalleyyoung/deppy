"""Edge-case VALUE_ERROR: int parse, float parse, tuple unpack."""

BUG_TYPE = "VALUE_ERROR"
BUG_DESC = "Value error in edge-case parse/unpack patterns"

EXAMPLES = [
    (
        "int_from_input",
        # buggy: int() on raw input
        '''\
def parse_age(text):
    age = int(text)
    return age
''',
        # safe: try/except
        '''\
def parse_age(text):
    try:
        age = int(text)
    except ValueError:
        age = 0
    return age
''',
        "int() on arbitrary string input",
    ),
    (
        "float_from_config",
        # buggy: float() on config value
        '''\
def get_threshold(config_str):
    return float(config_str)
''',
        # safe: try/except
        '''\
def get_threshold(config_str):
    try:
        return float(config_str)
    except ValueError:
        return 0.0
''',
        "float() on possibly non-numeric string",
    ),
    (
        "triple_unpack",
        # buggy: tuple unpack assuming 3 elements
        '''\
def parse_rgb(pixel):
    r, g, b = pixel
    return r + g + b
''',
        # safe: length check
        '''\
def parse_rgb(pixel):
    if len(pixel) != 3:
        return 0
    r, g, b = pixel
    return r + g + b
''',
        "Tuple unpack assuming exact length",
    ),
    (
        "pair_unpack",
        # buggy: pair unpack on variable-length data
        '''\
def split_header(line):
    key, value = line.split(":")
    return key, value
''',
        # safe: length guard
        '''\
def split_header(line):
    parts = line.split(":")
    if len(parts) != 2:
        return "", ""
    key, value = parts
    return key, value
''',
        "Pair unpack on split result with variable number of parts",
    ),
]
