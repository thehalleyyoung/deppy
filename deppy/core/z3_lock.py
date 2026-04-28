"""Global re-entrant lock around all Z3 invocations.

Z3's C-side reference counting (``Z3_inc_ref`` / ``Z3_dec_ref``) is not
thread-safe.  Calling ``z3.Int("x")`` from two threads concurrently can
race the per-context ref-counts and cause a SIGSEGV.

We serialise every Z3 entry point through ``Z3_LOCK``.  Use it via::

    with Z3_LOCK:
        # any z3.* call

The lock is re-entrant so a Z3 call that internally invokes another
Z3 call (via a callback) doesn't deadlock.

Discovery context: ``examples/bst_proof.py`` reproducibly segfaulted
when run through the parallel verifier in ``simple_parallel.py``.
The fix is purely defensive — Z3 itself is already correct, but its
external reference count needs serialisation.
"""
from __future__ import annotations

import threading


# Single module-level re-entrant lock.  Importing this module multiple
# times via different code paths gives the *same* lock instance because
# Python's import system caches modules.
Z3_LOCK: threading.RLock = threading.RLock()


__all__ = ["Z3_LOCK"]
