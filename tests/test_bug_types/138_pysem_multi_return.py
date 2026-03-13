"""Python semantics: multiple return paths — NULL_PTR, UNBOUND_VAR."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Functions with implicit None return on some paths"

EXAMPLES = [
    (
        "implicit_none_return",
        # buggy: function returns None implicitly on some paths
        '''\
def find_record(db, key):
    for record in db:
        if record["id"] == key:
            return record

def use_record(db, key):
    rec = find_record(db, key)
    return rec["name"]
''',
        # safe: guard None
        '''\
def find_record(db, key):
    for record in db:
        if record["id"] == key:
            return record
    return None

def use_record(db, key):
    rec = find_record(db, key)
    if rec is not None:
        return rec["name"]
    return ""
''',
        "find_record returns None if not found; rec['name'] on None",
    ),
    (
        "early_return_none",
        # buggy: early return produces None, caller dereferences
        '''\
def parse_response(text):
    if not text:
        return
    return text.split("|")

def get_first(text):
    parts = parse_response(text)
    return parts[0]
''',
        # safe: guard return
        '''\
def parse_response(text):
    if not text:
        return []
    return text.split("|")

def get_first(text):
    parts = parse_response(text)
    if parts:
        return parts[0]
    return ""
''',
        "parse_response returns None for empty text; parts[0] on None",
    ),
    (
        "method_chain_none",
        # buggy: method returns None, chain continues
        '''\
class Builder:
    def __init__(self):
        self.parts = []
    def add(self, part):
        self.parts.append(part)

def build():
    b = Builder()
    result = b.add("x")
    return result.upper()
''',
        # safe: check return
        '''\
class Builder:
    def __init__(self):
        self.parts = []
    def add(self, part):
        self.parts.append(part)
        return self

def build():
    b = Builder()
    result = b.add("x")
    return str(result)
''',
        "add() returns None; .upper() on None is NULL_PTR",
    ),
]
