"""Python semantics: type coercion and isinstance checks — TYPE_ERROR, TYPE_CONFUSION."""

BUG_TYPE = "TYPE_ERROR"
BUG_DESC = "Implicit type coercion failures and operator mismatches"

EXAMPLES = [
    (
        "str_int_concat",
        # buggy: concatenate str and int
        '''\
def make_label(name, count):
    return name + count
''',
        # safe: convert
        '''\
def make_label(name, count):
    return name + str(count)
''',
        "str + int is TypeError",
    ),
    (
        "list_extend_noniter",
        # buggy: extend with non-iterable
        '''\
def collect(items, extra):
    result = list(items)
    result.extend(extra)
    return result + 42
''',
        # safe: proper types
        '''\
def collect(items, extra):
    result = list(items)
    result.extend(extra)
    return result + [42]
''',
        "list + int is TypeError",
    ),
    (
        "format_type_mismatch",
        # buggy: format spec for wrong type
        '''\
def report(name, score):
    total = name + score
    return "{:.2f}".format(total)
''',
        # safe: ensure numeric
        '''\
def report(name, score):
    total = float(score)
    return "{:.2f}".format(total)
''',
        "name + score: str + int is TypeError",
    ),
    (
        "comparison_type_error",
        # buggy: compare incompatible types
        '''\
def find_max(items):
    best = items[0]
    for item in items[1:]:
        if item > best:
            best = item
    return best + None
''',
        # safe: proper comparison
        '''\
def find_max(items):
    best = items[0]
    for item in items[1:]:
        if item > best:
            best = item
    return best
''',
        "best + None is TypeError",
    ),
]
