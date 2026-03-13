"""Python semantics: memory and resource management — MEMORY_LEAK, DOUBLE_CLOSE."""

BUG_TYPE = "MEMORY_LEAK"
BUG_DESC = "Resource and memory leaks from Python patterns"

EXAMPLES = [
    (
        "file_not_closed",
        # buggy: open file handle never closed
        '''\
def read_config(path):
    f = open(path)
    data = f.read()
    return data
''',
        # safe: use with
        '''\
def read_config(path):
    with open(path) as f:
        data = f.read()
    return data
''',
        "f is never closed; resource leak",
    ),
    (
        "socket_not_closed",
        # buggy: socket opened but not closed on error path
        '''\
import socket

def send_data(host, port, data):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.connect((host, port))
    s.sendall(data)
    response = s.recv(1024)
    return response
''',
        # safe: close in finally
        '''\
import socket

def send_data(host, port, data):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        s.connect((host, port))
        s.sendall(data)
        response = s.recv(1024)
        return response
    finally:
        s.close()
''',
        "socket never closed; resource leak",
    ),
    (
        "tempfile_leak",
        # buggy: temp file created but not cleaned up
        '''\
import tempfile

def process_data(data):
    tmp = tempfile.NamedTemporaryFile(delete=False)
    tmp.write(data)
    path = tmp.name
    return path
''',
        # safe: use context manager
        '''\
import tempfile

def process_data(data):
    with tempfile.NamedTemporaryFile(delete=False) as tmp:
        tmp.write(data)
        path = tmp.name
    return path
''',
        "NamedTemporaryFile not closed; file descriptor leak",
    ),
]
