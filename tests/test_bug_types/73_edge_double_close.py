"""Edge-case DOUBLE_CLOSE: sequential close, close-in-loop."""

BUG_TYPE = "DOUBLE_CLOSE"
BUG_DESC = "Double close in edge-case file patterns"

EXAMPLES = [
    (
        "explicit_double_close",
        # buggy: two close calls on same handle
        '''\
def finalize(stream):
    stream.close()
    cleanup()
    stream.close()
''',
        # safe: close only once
        '''\
def finalize(stream):
    stream.close()
    cleanup()
''',
        "Explicit double close on same file handle",
    ),
    (
        "close_then_with",
        # buggy: close then use in with implies second close
        '''\
def reopen_close(path):
    f = open(path)
    f.close()
    f.close()
    return "done"
''',
        # safe: single close
        '''\
def reopen_close(path):
    f = open(path)
    data = f.read()
    f.close()
    return data
''',
        "File handle closed twice explicitly",
    ),
    (
        "paired_close_calls",
        # buggy: close called twice with work between
        '''\
def flush_and_close(writer):
    writer.flush()
    writer.close()
    writer.close()
''',
        # safe: single close
        '''\
def flush_and_close(writer):
    writer.flush()
    writer.close()
''',
        "Close called twice with intermediate work",
    ),
]
