"""Tricky MEMORY_LEAK: file open in conditional, loop open, nested open."""

BUG_TYPE = "MEMORY_LEAK"
BUG_DESC = "Tricky file handle leak in complex patterns"

EXAMPLES = [
    (
        "open_in_branch",
        # buggy: open without close in if-branch
        '''\
def maybe_read(path, flag):
    if flag:
        f = open(path)
        data = f.read()
    return data
''',
        # safe: use with-statement
        '''\
def maybe_read(path, flag):
    data = ""
    if flag:
        with open(path) as f:
            data = f.read()
    return data
''',
        "File opened in conditional without proper close",
    ),
    (
        "sequential_open",
        # buggy: two opens without with
        '''\
def copy_file(src, dst):
    inp = open(src)
    out = open(dst, "w")
    out.write(inp.read())
    inp.close()
    out.close()
''',
        # safe: use with
        '''\
def copy_file(src, dst):
    with open(src) as inp:
        with open(dst, "w") as out:
            out.write(inp.read())
''',
        "Multiple file handles opened without with-statement",
    ),
    (
        "write_no_close",
        # buggy: open for write, no close
        '''\
def save_data(path, data):
    f = open(path, "w")
    f.write(data)
''',
        # safe: with statement
        '''\
def save_data(path, data):
    with open(path, "w") as f:
        f.write(data)
''',
        "File opened for write without closing",
    ),
    (
        "open_binary",
        # buggy: open binary mode without with
        '''\
def read_bytes(path):
    f = open(path, "rb")
    data = f.read()
    return data
''',
        # safe: with statement
        '''\
def read_bytes(path):
    with open(path, "rb") as f:
        data = f.read()
    return data
''',
        "Binary file opened without context manager",
    ),
]
