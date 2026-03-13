"""Python semantics: match/case (structural pattern matching) — TYPE_ERROR, NULL_PTR."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Match/case patterns that allow None through"

EXAMPLES = [
    (
        "match_wildcard_none",
        # buggy: wildcard match catches None, dereferences
        '''\
def process_event(event):
    match event:
        case {"type": "click", "data": data}:
            return data
        case _:
            data = None
    return data.strip()
''',
        # safe: guard None in wildcard
        '''\
def process_event(event):
    match event:
        case {"type": "click", "data": data}:
            return data
        case _:
            data = ""
    return data.strip()
''',
        "wildcard sets data=None; .strip() on None",
    ),
    (
        "match_missing_case",
        # buggy: no default case, result may be unset
        '''\
def classify(value):
    match value:
        case int():
            label = "integer"
        case str():
            label = "string"
    result = None
    return result.upper()
''',
        # safe: default case
        '''\
def classify(value):
    match value:
        case int():
            label = "integer"
        case str():
            label = "string"
        case _:
            label = "unknown"
    return label.upper()
''',
        "result is always None; .upper() on None",
    ),
]
