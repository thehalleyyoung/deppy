"""Python semantics: context managers — USE_AFTER_FREE, DOUBLE_CLOSE, NULL_PTR."""

BUG_TYPE = "USE_AFTER_FREE"
BUG_DESC = "Use of resource after context manager __exit__"

EXAMPLES = [
    (
        "use_after_with",
        # buggy: read from file after with block
        '''\
def read_first_line(path):
    with open(path) as f:
        pass
    return f.readline()
''',
        # safe: read inside with
        '''\
def read_first_line(path):
    with open(path) as f:
        line = f.readline()
    return line
''',
        "f is closed after with; f.readline() is use-after-close",
    ),
    (
        "nested_ctx_use_after",
        # buggy: nested context managers, use outer after inner exits
        '''\
def copy_file(src, dst):
    with open(src) as fin:
        with open(dst, 'w') as fout:
            fout.write(fin.read())
        fout.write("done")
''',
        # safe: all writes inside inner with
        '''\
def copy_file(src, dst):
    with open(src) as fin:
        with open(dst, 'w') as fout:
            fout.write(fin.read())
            fout.write("done")
''',
        "fout is closed after inner with exits; write is use-after-close",
    ),
    (
        "custom_ctx_use_after",
        # buggy: custom context manager, use after exit
        '''\
class Connection:
    def __enter__(self):
        self.conn = create_connection()
        return self
    def __exit__(self, *args):
        self.conn.close()
        self.conn = None

def query(db):
    with Connection() as c:
        pass
    result = c.conn.execute("SELECT 1")
    return result
''',
        # safe: query inside with
        '''\
class Connection:
    def __enter__(self):
        self.conn = create_connection()
        return self
    def __exit__(self, *args):
        self.conn.close()
        self.conn = None

def query(db):
    with Connection() as c:
        result = c.conn.execute("SELECT 1")
    return result
''',
        "c.conn is None after __exit__; .execute on None",
    ),
]
