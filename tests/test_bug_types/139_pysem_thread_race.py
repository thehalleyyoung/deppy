"""Python semantics: data race with threading — DATA_RACE, DEADLOCK."""

BUG_TYPE = "DATA_RACE"
BUG_DESC = "Shared mutable state between threads without synchronization"

EXAMPLES = [
    (
        "thread_shared_counter",
        # buggy: shared counter without lock
        '''\
import threading
counter = 0

def increment():
    global counter
    for _ in range(1000):
        counter += 1

def run():
    t1 = threading.Thread(target=increment)
    t2 = threading.Thread(target=increment)
    t1.start()
    t2.start()
    t1.join()
    t2.join()
    return counter
''',
        # safe: use lock
        '''\
import threading
counter = 0
lock = threading.Lock()

def increment():
    global counter
    for _ in range(1000):
        with lock:
            counter += 1

def run():
    t1 = threading.Thread(target=increment)
    t2 = threading.Thread(target=increment)
    t1.start()
    t2.start()
    t1.join()
    t2.join()
    return counter
''',
        "counter += 1 is not atomic; race between t1 and t2",
    ),
    (
        "thread_shared_list",
        # buggy: shared list modified from two threads
        '''\
import threading

def producer(items, data):
    for d in data:
        items.append(d)

def consumer(items, results):
    while items:
        results.append(items.pop(0))

def run(data):
    items = []
    results = []
    t1 = threading.Thread(target=producer, args=(items, data))
    t2 = threading.Thread(target=consumer, args=(items, results))
    t1.start()
    t2.start()
    t1.join()
    t2.join()
    return results
''',
        # safe: use queue
        '''\
import threading
import queue

def producer(q, data):
    for d in data:
        q.put(d)
    q.put(None)

def consumer(q, results):
    while True:
        item = q.get()
        if item is None:
            break
        results.append(item)

def run(data):
    q = queue.Queue()
    results = []
    t1 = threading.Thread(target=producer, args=(q, data))
    t2 = threading.Thread(target=consumer, args=(q, results))
    t1.start()
    t2.start()
    t1.join()
    t2.join()
    return results
''',
        "items list modified by two threads without sync",
    ),
]
