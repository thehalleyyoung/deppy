"""
deppy.concurrency — Concurrency verification constructs.

Provides Lock, atomic operations, and parallel safety decorators for
``from deppy.concurrency import Lock, lock_inv, parallel_safe``.
"""
from __future__ import annotations
from typing import Any, Callable, TypeVar
import threading

T = TypeVar("T")


class Lock:
    """A verified lock with an associated invariant."""
    def __init__(self, inv=None, name: str = ""):
        self._lock = threading.Lock()
        self.inv = inv
        self.name = name

    def acquire(self):
        self._lock.acquire()

    def release(self):
        self._lock.release()

    def __enter__(self):
        self._lock.acquire()
        return self

    def __exit__(self, *args):
        self._lock.release()


def lock_inv(lock: Lock, inv):
    """Associate an invariant with a lock."""
    lock.inv = inv
    return lock


class Condition:
    """A verified condition variable."""
    def __init__(self, lock: Lock = None):
        self._cond = threading.Condition(lock._lock if lock else None)

    def wait(self):
        self._cond.wait()

    def notify(self, n: int = 1):
        self._cond.notify(n)

    def notify_all(self):
        self._cond.notify_all()

    def __enter__(self):
        self._cond.acquire()
        return self

    def __exit__(self, *args):
        self._cond.release()


class Semaphore:
    """A verified semaphore."""
    def __init__(self, value: int = 1):
        self._sem = threading.Semaphore(value)
        self.initial_value = value

    def acquire(self):
        self._sem.acquire()

    def release(self):
        self._sem.release()

    def __enter__(self):
        self._sem.acquire()
        return self

    def __exit__(self, *args):
        self._sem.release()


def parallel_safe(fn):
    """Decorator marking a function as safe for parallel execution."""
    fn._deppy_parallel_safe = True
    return fn


def spawn(fn, *args, **kwargs):
    """Spawn a thread to run fn (verified version)."""
    t = threading.Thread(target=fn, args=args, kwargs=kwargs)
    t.start()
    return t


def join_all(threads):
    """Join all threads."""
    for t in threads:
        t.join()


def atomic_cas(ref, expected, desired) -> bool:
    """Compare-and-swap (specification-level — Python uses GIL for atomicity)."""
    if ref.value == expected:
        ref.value = desired
        return True
    return False
