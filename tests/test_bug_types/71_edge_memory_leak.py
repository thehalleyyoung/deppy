"""Edge-case MEMORY_LEAK: open in branch, open with mode, multiple opens."""

BUG_TYPE = "MEMORY_LEAK"
BUG_DESC = "Memory leak from unclosed file handles"

EXAMPLES = [
    (
        "open_in_branch",
        # buggy: open outside with in conditional branch
        '''\
def load_config(path, fallback):
    if path:
        f = open(path)
        data = f.read()
        return data
    return fallback
''',
        # safe: with statement
        '''\
def load_config(path, fallback):
    if path:
        with open(path) as f:
            data = f.read()
            return data
    return fallback
''',
        "File opened in conditional branch without context manager",
    ),
    (
        "binary_open_leak",
        # buggy: binary mode open without with
        '''\
def read_bytes(path):
    f = open(path, "rb")
    content = f.read()
    return content
''',
        # safe: with statement
        '''\
def read_bytes(path):
    with open(path, "rb") as f:
        content = f.read()
    return content
''',
        "Binary file opened without context manager",
    ),
    (
        "write_no_close",
        # buggy: open for writing without with
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
        "File opened for writing without context manager",
    ),
    (
        "sequential_opens",
        # buggy: two sequential file opens without with
        '''\
def merge_files(path_a, path_b):
    fa = open(path_a)
    fb = open(path_b)
    return fa.read() + fb.read()
''',
        # safe: both in with
        '''\
def merge_files(path_a, path_b):
    with open(path_a) as fa:
        with open(path_b) as fb:
            return fa.read() + fb.read()
''',
        "Multiple file handles opened without context managers",
    ),
]
