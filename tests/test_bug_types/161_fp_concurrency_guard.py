"""FP stress: data-race and deadlock guards.

Proper use of locks, atomic operations, and thread-safe patterns
prevents DATA_RACE and DEADLOCK.
"""

BUG_TYPE = "DATA_RACE"
BUG_DESC = "Proper synchronization prevents data races"

EXAMPLES = [
    (
        "lock_protects_shared",
        '''\
import threading

counter = 0

def increment():
    global counter
    counter += 1
''',
        '''\
import threading

counter = 0
lock = threading.Lock()

def increment():
    global counter
    with lock:
        counter += 1
''',
        "Lock context manager protects shared counter",
    ),
    (
        "rlock_reentrant",
        '''\
import threading

data = []

def add(item):
    data.append(item)

def add_batch(items):
    for item in items:
        add(item)
''',
        '''\
import threading

data = []
lock = threading.RLock()

def add(item):
    with lock:
        data.append(item)

def add_batch(items):
    with lock:
        for item in items:
            add(item)
''',
        "RLock allows reentrant locking",
    ),
    (
        "local_data_no_race",
        '''\
import threading

total = 0

def worker(items):
    global total
    for x in items:
        total += x
''',
        '''\
import threading

def worker(items):
    local_total = 0
    for x in items:
        local_total += x
    return local_total
''',
        "Thread-local computation — no shared state",
    ),
    (
        "queue_thread_safe",
        '''\
import threading

results = []

def producer(data):
    results.append(data)

def consumer():
    return results.pop(0)
''',
        '''\
import queue

q = queue.Queue()

def producer(data):
    q.put(data)

def consumer():
    return q.get()
''',
        "Queue is thread-safe by design",
    ),
    (
        "immutable_shared_data",
        '''\
import threading

config = {"timeout": 30}

def update_config(key, val):
    config[key] = val

def read_config(key):
    return config[key]
''',
        '''\
import threading

config = (("timeout", 30),)

def read_config(key):
    for k, v in config:
        if k == key:
            return v
    return None
''',
        "Immutable tuple — no mutation possible, no race",
    ),
]
