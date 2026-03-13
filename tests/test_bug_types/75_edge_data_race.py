"""Edge-case DATA_RACE: multiple shared mutations, append in thread."""

BUG_TYPE = "DATA_RACE"
BUG_DESC = "Data race in edge-case threading patterns"

EXAMPLES = [
    (
        "shared_list_extend",
        # buggy: extend on shared list in thread target
        '''\
import threading
def batch_load(urls, results):
    def loader(batch):
        for url in batch:
            data = fetch(url)
            results.extend(data)
    t = threading.Thread(target=loader, args=(urls,))
    t.start()
    t.join()
''',
        # safe: use lock
        '''\
import threading
def batch_load(urls, results):
    lock = threading.Lock()
    def loader(batch):
        for url in batch:
            data = fetch(url)
            with lock:
                results.extend(data)
    t = threading.Thread(target=loader, args=(urls,))
    t.start()
    t.join()
''',
        "Shared list extended without lock in thread",
    ),
    (
        "shared_dict_update",
        # buggy: dict subscript assignment in thread target
        '''\
import threading
def parallel_index(docs, index):
    def indexer(doc):
        for word in doc.split():
            index[word] = doc
    threads = []
    for d in docs:
        t = threading.Thread(target=indexer, args=(d,))
        threads.append(t)
        t.start()
    for t in threads:
        t.join()
''',
        # safe: use lock
        '''\
import threading
def parallel_index(docs, index):
    lock = threading.Lock()
    def indexer(doc):
        for word in doc.split():
            with lock:
                index[word] = doc
    threads = []
    for d in docs:
        t = threading.Thread(target=indexer, args=(d,))
        threads.append(t)
        t.start()
    for t in threads:
        t.join()
''',
        "Shared dict modified without lock in thread",
    ),
    (
        "shared_counter_append",
        # buggy: append to shared list from thread
        '''\
import threading
def collect_results(items, output):
    def worker(item):
        result = process(item)
        output.append(result)
    threads = []
    for item in items:
        t = threading.Thread(target=worker, args=(item,))
        threads.append(t)
        t.start()
    for t in threads:
        t.join()
''',
        # safe: use lock
        '''\
import threading
def collect_results(items, output):
    lock = threading.Lock()
    def worker(item):
        result = process(item)
        with lock:
            output.append(result)
    threads = []
    for item in items:
        t = threading.Thread(target=worker, args=(item,))
        threads.append(t)
        t.start()
    for t in threads:
        t.join()
''',
        "Shared list append from multiple threads without lock",
    ),
]
