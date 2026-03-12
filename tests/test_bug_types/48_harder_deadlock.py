"""Harder DEADLOCK: more complex lock-ordering patterns."""

BUG_TYPE = "DEADLOCK"
BUG_DESC = "Deadlock from inconsistent lock ordering in complex patterns"

EXAMPLES = [
    (
        "swap_accounts",
        # buggy: two threads may lock accounts in opposite order
        '''\
import threading
def transfer(lock_a, lock_b, amount):
    lock_a.acquire()
    lock_b.acquire()
    do_transfer(amount)
    lock_b.release()
    lock_a.release()
def reverse_transfer(lock_a, lock_b, amount):
    lock_b.acquire()
    lock_a.acquire()
    do_transfer(-amount)
    lock_a.release()
    lock_b.release()
''',
        # safe: consistent ordering via id comparison
        '''\
import threading
def transfer(lock_a, lock_b, amount):
    first, second = sorted([lock_a, lock_b], key=id)
    first.acquire()
    second.acquire()
    do_transfer(amount)
    second.release()
    first.release()
def reverse_transfer(lock_a, lock_b, amount):
    first, second = sorted([lock_a, lock_b], key=id)
    first.acquire()
    second.acquire()
    do_transfer(-amount)
    second.release()
    first.release()
''',
        "Two functions lock same pair of locks in opposite order",
    ),
    (
        "pipeline_stage_locks",
        # buggy: stage A locks X then Y, stage B locks Y then X
        '''\
import threading
def stage_a(lock_x, lock_y, data):
    lock_x.acquire()
    preprocess(data)
    lock_y.acquire()
    result = combine(data)
    lock_y.release()
    lock_x.release()
    return result
def stage_b(lock_x, lock_y, data):
    lock_y.acquire()
    validate(data)
    lock_x.acquire()
    result = finalize(data)
    lock_x.release()
    lock_y.release()
    return result
''',
        # safe: always lock X before Y
        '''\
import threading
def stage_a(lock_x, lock_y, data):
    lock_x.acquire()
    preprocess(data)
    lock_y.acquire()
    result = combine(data)
    lock_y.release()
    lock_x.release()
    return result
def stage_b(lock_x, lock_y, data):
    lock_x.acquire()
    validate(data)
    lock_y.acquire()
    result = finalize(data)
    lock_y.release()
    lock_x.release()
    return result
''',
        "Pipeline stages acquire locks in inconsistent order",
    ),
    (
        "nested_resource_lock",
        # buggy: three locks acquired in cyclic order across functions
        '''\
import threading
def op_alpha(la, lb, lc):
    la.acquire()
    lb.acquire()
    process_alpha()
    lb.release()
    la.release()
def op_beta(la, lb, lc):
    lb.acquire()
    lc.acquire()
    process_beta()
    lc.release()
    lb.release()
def op_gamma(la, lb, lc):
    lc.acquire()
    la.acquire()
    process_gamma()
    la.release()
    lc.release()
''',
        # safe: always acquire in order la, lb, lc
        '''\
import threading
def op_alpha(la, lb, lc):
    la.acquire()
    lb.acquire()
    process_alpha()
    lb.release()
    la.release()
def op_beta(la, lb, lc):
    la.acquire()
    lb.acquire()
    lc.acquire()
    process_beta()
    lc.release()
    lb.release()
    la.release()
def op_gamma(la, lb, lc):
    la.acquire()
    lc.acquire()
    process_gamma()
    lc.release()
    la.release()
''',
        "Three locks acquired in cyclic order across three functions",
    ),
]
