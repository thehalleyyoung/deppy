"""Tricky USE_AFTER_FREE: read/write/seek after close."""

BUG_TYPE = "USE_AFTER_FREE"
BUG_DESC = "Tricky use-after-close patterns"

EXAMPLES = [
    (
        "read_after_close_conditional",
        # buggy: close then read
        '''\
def read_config(path, flag):
    f = open(path)
    f.close()
    data = f.read()
    return data
''',
        # safe: read before close
        '''\
def read_config(path, flag):
    f = open(path)
    data = f.read()
    f.close()
    return data
''',
        "File read after close",
    ),
    (
        "write_after_close",
        # buggy: write after close
        '''\
def log_message(path, msg):
    f = open(path, "a")
    f.close()
    f.write(msg)
''',
        # safe: write before close
        '''\
def log_message(path, msg):
    f = open(path, "a")
    f.write(msg)
    f.close()
''',
        "File write after close",
    ),
    (
        "seek_after_close",
        # buggy: seek after close
        '''\
def rewind_and_read(path):
    f = open(path, "rb")
    f.close()
    f.seek(0)
    return f.read()
''',
        # safe: seek before close
        '''\
def rewind_and_read(path):
    f = open(path, "rb")
    f.seek(0)
    data = f.read()
    f.close()
    return data
''',
        "File seek after close",
    ),
]
