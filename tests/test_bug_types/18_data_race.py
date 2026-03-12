"""DATA_RACE: shared mutable state accessed from a thread target
without holding a lock — the synchronization presheaf has no
consistent global section over the concurrent cover.
"""

BUG_TYPE = "DATA_RACE"
BUG_DESC = "Data race on shared mutable state"

EXAMPLES = [
    (
        "append_no_lock",
        # buggy: append to shared list inside thread target without lock
        '''\
import threading
results = []
def worker(items):
    for item in items:
        results.append(item)
t = threading.Thread(target=worker, args=([1, 2],))
''',
        # safe: use a lock
        '''\
import threading
results = []
lock = threading.Lock()
def worker(items):
    for item in items:
        with lock:
            results.append(item)
t = threading.Thread(target=worker, args=([1, 2],))
''',
        "Unprotected .append() on shared list in thread target",
    ),
    (
        "pop_no_lock",
        # buggy: pop from shared list without lock
        '''\
import threading
task_queue = [1, 2, 3]
def consumer():
    while task_queue:
        task_queue.pop()
t = threading.Thread(target=consumer)
''',
        # safe: use a lock
        '''\
import threading
task_queue = [1, 2, 3]
lock = threading.Lock()
def consumer():
    while task_queue:
        with lock:
            task_queue.pop()
t = threading.Thread(target=consumer)
''',
        "Unprotected .pop() on shared list in thread target",
    ),
    (
        "extend_no_lock",
        # buggy: extend shared list without lock
        '''\
import threading
data = []
def loader(batch):
    data.extend(batch)
t = threading.Thread(target=loader, args=([10, 20],))
''',
        # safe: protected with lock
        '''\
import threading
data = []
lock = threading.Lock()
def loader(batch):
    with lock:
        data.extend(batch)
t = threading.Thread(target=loader, args=([10, 20],))
''',
        "Unprotected .extend() on shared list in thread target",
    ),
]
