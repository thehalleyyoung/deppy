"""Hard MEMORY_LEAK + USE_AFTER_FREE examples — early return, conditional close, exception paths."""

BUG_TYPE = "MEMORY_LEAK"
BUG_DESC = "Memory leak in harder patterns"

EXAMPLES = [
    (
        "early_return_leak",
        # buggy: file opened, early return skips close
        '''\
def read_header(path):
    f = open(path)
    header = f.readline()
    if not header:
        return None
    data = f.read()
    f.close()
    return data
''',
        # safe: use with-statement
        '''\
def read_header(path):
    with open(path) as f:
        header = f.readline()
        if not header:
            return None
        data = f.read()
    return data
''',
        "Early return skips f.close(), leaking the file handle",
    ),
    (
        "conditional_open",
        # buggy: file opened inside condition, close only in one branch
        '''\
def maybe_read(path, flag):
    if flag:
        f = open(path)
        data = f.read()
    return data
''',
        # safe: close in same branch
        '''\
def maybe_read(path, flag):
    if flag:
        with open(path) as f:
            data = f.read()
        return data
    return ""
''',
        "File opened conditionally but never closed on that path",
    ),
    (
        "exception_path_leak",
        # buggy: exception between open and close leaks
        '''\
def parse_file(path):
    f = open(path)
    content = f.read()
    result = int(content)
    f.close()
    return result
''',
        # safe: with-statement ensures close on exception
        '''\
def parse_file(path):
    with open(path) as f:
        content = f.read()
        result = int(content)
    return result
''',
        "Exception from int() between open and close leaks the file",
    ),
]
