"""Edge-case DEADLOCK: nested lock acquisition, AB-BA pattern."""

BUG_TYPE = "DEADLOCK"
BUG_DESC = "Deadlock from lock ordering violations"

EXAMPLES = [
    (
        "nested_with_locks",
        # buggy: AB then BA ordering
        '''\
import threading
def transfer(a_lock, b_lock, amount):
    with a_lock:
        with b_lock:
            do_transfer(amount)
def reverse_transfer(a_lock, b_lock, amount):
    with b_lock:
        with a_lock:
            do_transfer(amount)
''',
        # safe: consistent ordering
        '''\
import threading
def transfer(a_lock, b_lock, amount):
    with a_lock:
        with b_lock:
            do_transfer(amount)
def reverse_transfer(a_lock, b_lock, amount):
    with a_lock:
        with b_lock:
            do_transfer(amount)
''',
        "Lock acquisition in opposite order causes deadlock",
    ),
    (
        "three_lock_cycle",
        # buggy: A->B, B->C, C->A forms a cycle
        '''\
import threading
def step1(lock_a, lock_b):
    with lock_a:
        with lock_b:
            work1()
def step2(lock_b, lock_c):
    with lock_b:
        with lock_c:
            work2()
def step3(lock_c, lock_a):
    with lock_c:
        with lock_a:
            work3()
''',
        # safe: consistent global order
        '''\
import threading
def step1(lock_a, lock_b):
    with lock_a:
        with lock_b:
            work1()
def step2(lock_a, lock_b, lock_c):
    with lock_b:
        with lock_c:
            work2()
def step3(lock_a, lock_c):
    with lock_a:
        with lock_c:
            work3()
''',
        "Three-lock cycle creating potential deadlock",
    ),
    (
        "acquire_method_cycle",
        # buggy: acquire calls in cycle
        '''\
import threading
def op_forward(m1, m2):
    m1.acquire()
    m2.acquire()
    compute()
    m2.release()
    m1.release()
def op_backward(m1, m2):
    m2.acquire()
    m1.acquire()
    compute()
    m1.release()
    m2.release()
''',
        # safe: consistent ordering
        '''\
import threading
def op_forward(m1, m2):
    m1.acquire()
    m2.acquire()
    compute()
    m2.release()
    m1.release()
def op_backward(m1, m2):
    m1.acquire()
    m2.acquire()
    compute()
    m2.release()
    m1.release()
''',
        "Lock acquire/release in opposite order",
    ),
]
