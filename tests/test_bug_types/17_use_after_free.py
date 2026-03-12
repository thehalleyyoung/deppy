"""USE_AFTER_FREE: using a resource after it has been closed — the
lifecycle presheaf transitions OPEN -> CLOSED at the close site,
and any subsequent use requires OPEN, creating a gluing obstruction.
"""

BUG_TYPE = "USE_AFTER_FREE"
BUG_DESC = "Use after close"

EXAMPLES = [
    (
        "read_after_close",
        # buggy: read() after close()
        '''\
def process_file(path):
    fh = open(path)
    fh.close()
    data = fh.read()
    return data
''',
        # safe: read before close
        '''\
def process_file(path):
    fh = open(path)
    data = fh.read()
    fh.close()
    return data
''',
        ".read() after .close() violates lifecycle presheaf",
    ),
    (
        "write_after_close",
        # buggy: write() after close()
        '''\
def log_and_close(fh, msg):
    fh.close()
    fh.write(msg)
''',
        # safe: write before close
        '''\
def log_and_close(fh, msg):
    fh.write(msg)
    fh.close()
''',
        ".write() after .close()",
    ),
    (
        "seek_after_close",
        # buggy: seek() after close()
        '''\
def rewind_file(fh):
    fh.close()
    fh.seek(0)
''',
        # safe: seek before close
        '''\
def rewind_file(fh):
    fh.seek(0)
    fh.close()
''',
        ".seek() after .close()",
    ),
]
