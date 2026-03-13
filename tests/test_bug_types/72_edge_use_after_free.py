"""Edge-case USE_AFTER_FREE: read after close, seek after close."""

BUG_TYPE = "USE_AFTER_FREE"
BUG_DESC = "Use after close in edge-case file patterns"

EXAMPLES = [
    (
        "read_after_close",
        # buggy: read after explicit close
        '''\
def peek_and_close(path):
    f = open(path)
    f.close()
    header = f.read(10)
    return header
''',
        # safe: read before close
        '''\
def peek_and_close(path):
    f = open(path)
    header = f.read(10)
    f.close()
    return header
''',
        "File read after explicit close",
    ),
    (
        "seek_after_close",
        # buggy: seek after close
        '''\
def rewind_closed(f):
    f.close()
    f.seek(0)
    return f.read()
''',
        # safe: use with statement
        '''\
def rewind_closed(f):
    f.seek(0)
    data = f.read()
    f.close()
    return data
''',
        "File seek after close",
    ),
    (
        "write_after_close",
        # buggy: write after close
        '''\
def append_then_close(log_file, msg):
    log_file.close()
    log_file.write(msg)
''',
        # safe: write before close
        '''\
def append_then_close(log_file, msg):
    log_file.write(msg)
    log_file.close()
''',
        "File write after close",
    ),
]
