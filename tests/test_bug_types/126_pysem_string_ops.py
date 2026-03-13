"""Python semantics: string operations — INDEX_OOB, DIV_ZERO, KEY_ERROR."""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "String indexing and split pitfalls"

EXAMPLES = [
    (
        "split_index_empty",
        # buggy: split then index without length check
        '''\
def get_domain(email):
    parts = email.split("@")
    return parts[1]
''',
        # safe: check split length
        '''\
def get_domain(email):
    parts = email.split("@")
    if len(parts) > 1:
        return parts[1]
    return ""
''',
        "email may not contain @; parts has 1 element, parts[1] OOB",
    ),
    (
        "rsplit_index",
        # buggy: rsplit with limit then wrong index
        '''\
def get_extension(filename):
    parts = filename.rsplit(".", 1)
    return parts[1]
''',
        # safe: check parts
        '''\
def get_extension(filename):
    parts = filename.rsplit(".", 1)
    if len(parts) > 1:
        return parts[1]
    return ""
''',
        "filename may have no dot; parts[1] OOB",
    ),
    (
        "partition_index",
        # buggy: partition returns 3-tuple but code indexes past it
        '''\
def parse_header(line):
    parts = line.partition(":")
    collected = list(parts)
    return collected[3]
''',
        # safe: valid index
        '''\
def parse_header(line):
    parts = line.partition(":")
    collected = list(parts)
    return collected[2]
''',
        "partition always returns 3 elements; collected[3] is OOB",
    ),
]
