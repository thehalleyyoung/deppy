"""Hard DOUBLE_CLOSE examples — close in both try and finally, conditional close paths."""

BUG_TYPE = "DOUBLE_CLOSE"
BUG_DESC = "Double close in harder patterns"

EXAMPLES = [
    (
        "try_finally_double",
        # buggy: close in try body AND finally → double close on success path
        '''\
def read_safe(path):
    f = open(path)
    try:
        data = f.read()
        f.close()
    finally:
        f.close()
    return data
''',
        # safe: only close in finally
        '''\
def read_safe(path):
    f = open(path)
    try:
        data = f.read()
    finally:
        f.close()
    return data
''',
        "close() in both try body and finally → double close on normal path",
    ),
    (
        "branch_double_close",
        # buggy: close on both branches of if, then close again after
        '''\
def process_file(f, mode):
    if mode == "fast":
        data = f.readline()
        f.close()
    else:
        data = f.read()
        f.close()
    f.close()
    return data
''',
        # safe: close only once after the branch
        '''\
def process_file(f, mode):
    if mode == "fast":
        data = f.readline()
    else:
        data = f.read()
    f.close()
    return data
''',
        "File closed in both if/else branches and then again after",
    ),
    (
        "loop_close",
        # buggy: file closed inside a loop that runs more than once
        '''\
def close_all(handles):
    for h in handles:
        h.close()
    for h in handles:
        h.close()
''',
        # safe: close only once
        '''\
def close_all(handles):
    for h in handles:
        h.close()
''',
        "Closing all handles in a second loop after already closing in first loop",
    ),
]
