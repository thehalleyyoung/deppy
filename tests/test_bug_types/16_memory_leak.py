"""MEMORY_LEAK: resource opened without context manager — the lifecycle
presheaf requires CLOSED on all exit paths, but open() without `with`
may leak the file handle.
"""

BUG_TYPE = "MEMORY_LEAK"
BUG_DESC = "Resource leak (open without context manager)"

EXAMPLES = [
    (
        "file_read_leak",
        # buggy: open without with, no close
        '''\
def read_config(path):
    fh = open(path)
    data = fh.read()
    return data
''',
        # safe: context manager ensures cleanup
        '''\
def read_config(path):
    with open(path) as fh:
        data = fh.read()
    return data
''',
        "open() without context manager may leak handle",
    ),
    (
        "write_leak",
        # buggy: open for writing without with
        '''\
def save_result(path, content):
    fh = open(path, 'w')
    fh.write(content)
''',
        # safe: context manager
        '''\
def save_result(path, content):
    with open(path, 'w') as fh:
        fh.write(content)
''',
        "open('w') without context manager may leak handle",
    ),
    (
        "multi_file_leak",
        # buggy: multiple opens without context managers
        '''\
def merge_files(path_a, path_b):
    fa = open(path_a)
    fb = open(path_b)
    return fa.read() + fb.read()
''',
        # safe: nested context managers
        '''\
def merge_files(path_a, path_b):
    with open(path_a) as fa:
        with open(path_b) as fb:
            return fa.read() + fb.read()
''',
        "Multiple open() calls without context managers",
    ),
]
