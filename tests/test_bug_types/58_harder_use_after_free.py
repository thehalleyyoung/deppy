"""Harder USE_AFTER_FREE: read/write after close in complex control flow."""

BUG_TYPE = "USE_AFTER_FREE"
BUG_DESC = "Use after close in complex patterns"

EXAMPLES = [
    (
        "read_after_conditional_close",
        # buggy: file closed in branch, then read unconditionally
        '''\
def process_file(path, should_close):
    f = open(path)
    data = f.read()
    if should_close:
        f.close()
    summary = f.readline()
    return summary
''',
        # safe: use with block
        '''\
def process_file(path, should_close):
    with open(path) as f:
        data = f.read()
        summary = f.readline()
    return summary
''',
        "File read after conditional close",
    ),
    (
        "write_after_close",
        # buggy: close then write
        '''\
def save_report(path, header, body):
    f = open(path, "w")
    f.write(header)
    f.close()
    f.write(body)
    return path
''',
        # safe: write all before close
        '''\
def save_report(path, header, body):
    with open(path, "w") as f:
        f.write(header)
        f.write(body)
    return path
''',
        "Write to file after it has been closed",
    ),
    (
        "seek_after_close",
        # buggy: seek after close in error recovery
        '''\
def reread(path):
    f = open(path)
    f.read()
    f.close()
    f.seek(0)
    return f.read()
''',
        # safe: reopen or use with
        '''\
def reread(path):
    with open(path) as f:
        data = f.read()
    return data
''',
        "Seek and read after file close",
    ),
]
