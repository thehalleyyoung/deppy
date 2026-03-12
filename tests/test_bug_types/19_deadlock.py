"""DEADLOCK: cyclic lock ordering — the lock-ordering presheaf O has
no consistent global section when two functions acquire the same
locks in opposite order.
"""

BUG_TYPE = "DEADLOCK"
BUG_DESC = "Deadlock from cyclic lock ordering"

EXAMPLES = [
    (
        "classic_ab_ba",
        # buggy: function f acquires a then b, function g acquires b then a
        '''\
import threading
lock_a = threading.Lock()
lock_b = threading.Lock()
def transfer_forward():
    lock_a.acquire()
    lock_b.acquire()
    lock_b.release()
    lock_a.release()
def transfer_backward():
    lock_b.acquire()
    lock_a.acquire()
    lock_a.release()
    lock_b.release()
''',
        # safe: consistent ordering (always a before b)
        '''\
import threading
lock_a = threading.Lock()
lock_b = threading.Lock()
def transfer_forward():
    lock_a.acquire()
    lock_b.acquire()
    lock_b.release()
    lock_a.release()
def transfer_backward():
    lock_a.acquire()
    lock_b.acquire()
    lock_b.release()
    lock_a.release()
''',
        "A→B vs B→A lock ordering creates potential deadlock",
    ),
    (
        "three_locks_cycle",
        # buggy: three locks with cyclic ordering (x→y, y→z, z→x)
        '''\
import threading
x = threading.Lock()
y = threading.Lock()
z = threading.Lock()
def f1():
    x.acquire()
    y.acquire()
    y.release()
    x.release()
def f2():
    y.acquire()
    z.acquire()
    z.release()
    y.release()
def f3():
    z.acquire()
    x.acquire()
    x.release()
    z.release()
''',
        # safe: consistent total order (x < y < z)
        '''\
import threading
x = threading.Lock()
y = threading.Lock()
z = threading.Lock()
def f1():
    x.acquire()
    y.acquire()
    y.release()
    x.release()
def f2():
    y.acquire()
    z.acquire()
    z.release()
    y.release()
def f3():
    x.acquire()
    z.acquire()
    z.release()
    x.release()
''',
        "Three-lock cycle creates potential deadlock",
    ),
    (
        "with_locks_cycle",
        # buggy: using `with` statement but opposite ordering
        '''\
import threading
m = threading.Lock()
n = threading.Lock()
def op_a():
    m.acquire()
    n.acquire()
    n.release()
    m.release()
def op_b():
    n.acquire()
    m.acquire()
    m.release()
    n.release()
''',
        # safe: same ordering
        '''\
import threading
m = threading.Lock()
n = threading.Lock()
def op_a():
    m.acquire()
    n.acquire()
    n.release()
    m.release()
def op_b():
    m.acquire()
    n.acquire()
    n.release()
    m.release()
''',
        "Lock ordering cycle with context managers",
    ),
]
