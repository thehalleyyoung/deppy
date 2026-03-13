"""FP stress: resource management guards (MEMORY_LEAK).

Context managers (with statement), try/finally blocks, and explicit
close() calls prevent resource leaks.  The sheaf section on the
resource site has a well-defined restriction to the cleanup site.
"""

BUG_TYPE = "MEMORY_LEAK"
BUG_DESC = "Resource management via context managers and finally"

EXAMPLES = [
    (
        "with_statement_file",
        '''\
def read_file(path):
    f = open(path)
    data = f.read()
    return data
''',
        '''\
def read_file(path):
    with open(path) as f:
        data = f.read()
    return data
''',
        "Context manager ensures file is closed",
    ),
    (
        "try_finally_close",
        '''\
def read_data(path):
    f = open(path)
    content = f.read()
    return content
''',
        '''\
def read_data(path):
    f = open(path)
    try:
        content = f.read()
    finally:
        f.close()
    return content
''',
        "try/finally ensures close even on exception",
    ),
    (
        "nested_with",
        '''\
def copy_file(src, dst):
    f1 = open(src)
    f2 = open(dst, 'w')
    f2.write(f1.read())
''',
        '''\
def copy_file(src, dst):
    with open(src) as f1:
        with open(dst, 'w') as f2:
            f2.write(f1.read())
''',
        "Nested context managers for both files",
    ),
    (
        "contextlib_closing",
        '''\
def fetch_url(url):
    import urllib.request
    resp = urllib.request.urlopen(url)
    data = resp.read()
    return data
''',
        '''\
def fetch_url(url):
    import urllib.request
    from contextlib import closing
    with closing(urllib.request.urlopen(url)) as resp:
        data = resp.read()
    return data
''',
        "contextlib.closing wraps non-CM resource",
    ),
    (
        "explicit_cleanup_pattern",
        '''\
def process_connections(hosts):
    conns = [connect(h) for h in hosts]
    results = [c.query("SELECT 1") for c in conns]
    return results
''',
        '''\
def connect(h):
    return type("Conn", (), {"query": lambda self, q: q, "close": lambda self: None})()

def process_connections(hosts):
    conns = [connect(h) for h in hosts]
    try:
        results = [c.query("SELECT 1") for c in conns]
    finally:
        for c in conns:
            c.close()
    return results
''',
        "try/finally closes all connections",
    ),
]
