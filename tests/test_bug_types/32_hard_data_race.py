"""Hard DATA_RACE examples — more complex shared mutation patterns in threads."""

BUG_TYPE = "DATA_RACE"
BUG_DESC = "Data race in harder patterns"

EXAMPLES = [
    (
        "dict_setitem_race",
        # buggy: shared dict mutated from thread without lock
        '''\
import threading
results = {}
def worker(key, value):
    results[key] = value
t = threading.Thread(target=worker, args=("a", 1))
''',
        # safe: lock protects mutation
        '''\
import threading
results = {}
lock = threading.Lock()
def worker(key, value):
    with lock:
        results[key] = value
t = threading.Thread(target=worker, args=("a", 1))
''',
        "Dict mutation in thread target without synchronization",
    ),
    (
        "list_insert_race",
        # buggy: shared list insert from thread code
        '''\
import threading
data = []
def producer(items):
    for item in items:
        data.insert(0, item)
t = threading.Thread(target=producer, args=([1,2,3],))
''',
        # safe: with lock
        '''\
import threading
data = []
lock = threading.Lock()
def producer(items):
    for item in items:
        with lock:
            data.insert(0, item)
t = threading.Thread(target=producer, args=([1,2,3],))
''',
        "list.insert in thread target without lock",
    ),
    (
        "shared_remove_race",
        # buggy: shared list remove from thread
        '''\
import threading
pool = [1, 2, 3]
def cleanup(val):
    pool.remove(val)
t = threading.Thread(target=cleanup, args=(2,))
''',
        # safe: with lock
        '''\
import threading
pool = [1, 2, 3]
lock = threading.Lock()
def cleanup(val):
    with lock:
        pool.remove(val)
t = threading.Thread(target=cleanup, args=(2,))
''',
        "list.remove in thread target without synchronization",
    ),
]
