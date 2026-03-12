"""Harder DATA_RACE: shared state mutation via method calls and subscript in threads."""

BUG_TYPE = "DATA_RACE"
BUG_DESC = "Data race in complex thread patterns"

EXAMPLES = [
    (
        "counter_threads",
        # buggy: multiple threads calling .append on shared list
        '''\
import threading
def parallel_collect(items, transform):
    results = []
    def worker(chunk):
        for item in chunk:
            results.append(transform(item))
    mid = len(items) // 2
    t1 = threading.Thread(target=worker, args=(items[:mid],))
    t2 = threading.Thread(target=worker, args=(items[mid:],))
    t1.start()
    t2.start()
    t1.join()
    t2.join()
    return results
''',
        # safe: use a lock to protect shared list
        '''\
import threading
def parallel_collect(items, transform):
    results = []
    lock = threading.Lock()
    def worker(chunk):
        for item in chunk:
            with lock:
                results.append(transform(item))
    mid = len(items) // 2
    t1 = threading.Thread(target=worker, args=(items[:mid],))
    t2 = threading.Thread(target=worker, args=(items[mid:],))
    t1.start()
    t2.start()
    t1.join()
    t2.join()
    return results
''',
        "Multiple threads appending to same shared list without synchronization",
    ),
    (
        "shared_dict_update",
        # buggy: threads writing to shared dict via subscript
        '''\
import threading
def parallel_index(docs, analyzer):
    index = {}
    def process(doc):
        for term in analyzer(doc):
            index[term] = doc
    threads = []
    for doc in docs:
        t = threading.Thread(target=process, args=(doc,))
        threads.append(t)
        t.start()
    for t in threads:
        t.join()
    return index
''',
        # safe: use a lock
        '''\
import threading
def parallel_index(docs, analyzer):
    index = {}
    lock = threading.Lock()
    def process(doc):
        for term in analyzer(doc):
            with lock:
                index[term] = doc
    threads = []
    for doc in docs:
        t = threading.Thread(target=process, args=(doc,))
        threads.append(t)
        t.start()
    for t in threads:
        t.join()
    return index
''',
        "Threads writing to shared dict via subscript without lock",
    ),
    (
        "accumulator_race",
        # buggy: threads calling extend on shared list
        '''\
import threading
def gather_stats(sources, fetch_fn):
    all_stats = []
    def fetcher(src):
        data = fetch_fn(src)
        all_stats.extend(data)
    threads = []
    for s in sources:
        t = threading.Thread(target=fetcher, args=(s,))
        threads.append(t)
        t.start()
    for t in threads:
        t.join()
    return all_stats
''',
        # safe: use lock to protect shared list
        '''\
import threading
def gather_stats(sources, fetch_fn):
    all_stats = []
    lock = threading.Lock()
    def fetcher(src):
        data = fetch_fn(src)
        with lock:
            all_stats.extend(data)
    threads = []
    for s in sources:
        t = threading.Thread(target=fetcher, args=(s,))
        threads.append(t)
        t.start()
    for t in threads:
        t.join()
    return all_stats
''',
        "Multiple threads calling extend on shared list",
    ),
]
