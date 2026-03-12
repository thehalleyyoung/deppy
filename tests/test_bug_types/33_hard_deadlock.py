"""Hard DEADLOCK examples — nested with-statements, reentrant patterns."""

BUG_TYPE = "DEADLOCK"
BUG_DESC = "Deadlock from harder lock-ordering patterns"

EXAMPLES = [
    (
        "transfer_deadlock",
        # buggy: transfer between accounts locks in parameter order → inconsistent
        '''\
import threading
lock_a = threading.Lock()
lock_b = threading.Lock()
def transfer_ab(amount):
    with lock_a:
        with lock_b:
            pass
def transfer_ba(amount):
    with lock_b:
        with lock_a:
            pass
''',
        # safe: always lock in canonical (sorted) order
        '''\
import threading
lock_a = threading.Lock()
lock_b = threading.Lock()
def transfer_ab(amount):
    with lock_a:
        with lock_b:
            pass
def transfer_ba(amount):
    with lock_a:
        with lock_b:
            pass
''',
        "Two functions acquire same locks in opposite order",
    ),
    (
        "four_way_cycle",
        # buggy: four locks, circular dependency
        '''\
import threading
l1 = threading.Lock()
l2 = threading.Lock()
l3 = threading.Lock()
l4 = threading.Lock()
def w1():
    with l1:
        with l2:
            pass
def w2():
    with l2:
        with l3:
            pass
def w3():
    with l3:
        with l4:
            pass
def w4():
    with l4:
        with l1:
            pass
''',
        # safe: all acquire in order l1,l2,l3,l4
        '''\
import threading
l1 = threading.Lock()
l2 = threading.Lock()
l3 = threading.Lock()
l4 = threading.Lock()
def w1():
    with l1:
        with l2:
            pass
def w2():
    with l2:
        with l3:
            pass
def w3():
    with l3:
        with l4:
            pass
def w4():
    with l1:
        with l4:
            pass
''',
        "Four locks forming a cycle through four functions",
    ),
    (
        "acquire_release_deadlock",
        # buggy: explicit acquire in opposite orders
        '''\
import threading
m = threading.Lock()
n = threading.Lock()
def f():
    m.acquire()
    n.acquire()
    n.release()
    m.release()
def g():
    n.acquire()
    m.acquire()
    m.release()
    n.release()
''',
        # safe: same order
        '''\
import threading
m = threading.Lock()
n = threading.Lock()
def f():
    m.acquire()
    n.acquire()
    n.release()
    m.release()
def g():
    m.acquire()
    n.acquire()
    n.release()
    m.release()
''',
        "Explicit acquire/release in opposite order across functions",
    ),
]
