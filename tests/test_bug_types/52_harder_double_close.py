"""Harder DOUBLE_CLOSE: control-flow separated closes, conditional close paths."""

BUG_TYPE = "DOUBLE_CLOSE"
BUG_DESC = "Double close in complex control flow patterns"

EXAMPLES = [
    (
        "error_path_double",
        # buggy: close in error handling AND in finally-like cleanup
        '''\
def read_and_process(path):
    f = open(path)
    try:
        data = f.read()
        f.close()
    except IOError:
        f.close()
    f.close()
    return data
''',
        # safe: use with statement
        '''\
def read_and_process(path):
    with open(path) as f:
        data = f.read()
    return data
''',
        "File closed in try, except, AND after block - triple close possible",
    ),
    (
        "conditional_close_dup",
        # buggy: close called in branch and again unconditionally
        '''\
def flush_and_close(handle, urgent):
    if urgent:
        handle.flush()
        handle.close()
    handle.close()
''',
        # safe: close only once
        '''\
def flush_and_close(handle, urgent):
    if urgent:
        handle.flush()
    handle.close()
''',
        "Handle closed inside conditional and then unconditionally again",
    ),
    (
        "loop_reclose",
        # buggy: close inside loop then again after
        '''\
def process_files(paths):
    for path in paths:
        f = open(path)
        data = f.read()
        f.close()
        f.close()
    return "done"
''',
        # safe: single close per file
        '''\
def process_files(paths):
    for path in paths:
        f = open(path)
        data = f.read()
        f.close()
    return "done"
''',
        "File closed twice inside loop body",
    ),
]
