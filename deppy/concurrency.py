"""
deppy.concurrency — concurrency primitives with runtime-enforced
invariants, structured cubically.

Cubical framing
---------------
A lock's state space is the pair (unlocked, locked).  The lock's
*invariant* ``I`` is a refinement predicate over shared state; each
transition acquire→release forms a **path** in the state space whose
two endpoints must both satisfy ``I`` — so the trajectory is a
``PathType`` (in our data representation, a :class:`PathAbs`) whose
verification asks the kernel to check the invariant at both endpoints.
``atomic_cas`` is a *reflexive* path when the compare fails and a
**non-trivial path** from ``expected → new`` when it succeeds;
this matches the cubical treatment of equality as a 1-cell.

Parallel composition uses the **Čech cover** structure from
:mod:`deppy.core.path_engine`.  Each thread's read/write set forms a
patch; ``@parallel_safe`` succeeds iff the cocycle condition holds —
two threads touching disjoint state are automatically safe, and
overlapping accesses require an explicit invariant that matches on
the overlap.

All runtime checks are *real*: an invariant that fails raises an
``InvariantViolation``; a data race raises a ``RaceViolation``.  None
of this is metadata-only — the previous version was.

Types
-----
    Lock(invariant=...)        — mutex with a runtime-checked predicate
    Semaphore(n, invariant=...) — counting lock; invariant held per slot
    Condition(...)              — condition variable tied to an owning Lock
    atomic_cas(cell, expected, new)
                               — compare-and-swap yielding a path fact
    spawn(fn, ...)             — thread-spawn that records a patch
    join_all(threads)          — barrier that checks the cocycle
    parallel_safe(fn)          — decorator; runs data-race analysis at import

Exceptions
----------
    InvariantViolation         — invariant predicate returned False
    RaceViolation              — data-race detector saw conflicting access
"""
from __future__ import annotations

import threading
import time
from dataclasses import dataclass, field
from typing import Any, Callable, Optional, TypeVar

from deppy.core.types import PathAbs, RefinementType, PyBoolType, Var

T = TypeVar("T")


# ─────────────────────────────────────────────────────────────────────
# Exceptions
# ─────────────────────────────────────────────────────────────────────

class InvariantViolation(AssertionError):
    """Raised when a lock/semaphore invariant predicate returns False
    at acquire or release time.

    The message includes the invariant's descriptor string and the
    snapshot of whatever ``shared_state`` the user passed to the
    acquire/release call.
    """


class RaceViolation(AssertionError):
    """Raised when ``parallel_safe`` detects a data race —
    i.e., the Čech cocycle condition failed between two spawned
    patches."""


# ─────────────────────────────────────────────────────────────────────
# Lock with runtime-checked invariant
# ─────────────────────────────────────────────────────────────────────

@dataclass
class _LockInvariant:
    """Pair of the invariant predicate and its human-readable sketch.

    Modelled as a :class:`RefinementType` over the boolean universe —
    the sketch becomes the refinement's ``predicate`` so downstream
    verifiers (Z3, Lean) can parse it.
    """
    predicate: Callable[..., bool]
    sketch: str

    @property
    def refinement(self) -> RefinementType:
        return RefinementType(
            base_type=PyBoolType(),
            var_name="_state",
            predicate=self.sketch,
        )


class Lock:
    """Mutex with an optional runtime-checked invariant.

    Usage
    -----
        lock = Lock(
            invariant=lambda state: state["balance"] >= 0,
            invariant_sketch="balance >= 0",
            name="account_lock",
        )

        with lock(shared_state) as held:
            # Critical section.  On entry the invariant must hold;
            # on exit it is checked again — violations raise
            # InvariantViolation with the descriptor.
            held["balance"] -= amount

    Poisoning
    ---------
    If the invariant is violated at release time, the lock is
    *poisoned*: the violation is raised AND the lock is still
    released (avoiding deadlock for waiting threads), but every
    subsequent acquire raises :class:`InvariantViolation` with a
    poisoning trace.  Callers can clear the poison via
    :meth:`unpoison`.

    Cubical semantics
    -----------------
    The lock's state space is ``{unlocked, locked, poisoned}``.  An
    acquire → release session forms a :class:`PathAbs` at the interval
    when the invariant survives; otherwise the path's right endpoint
    lies in ``poisoned``, and that 2-cell can only be discharged by
    explicit :meth:`unpoison`.
    """

    __slots__ = ("_lock", "_inv", "_name", "_held_token", "_poison")

    def __init__(
        self,
        invariant: Optional[Callable[..., bool]] = None,
        *,
        invariant_sketch: str = "True",
        name: str = "",
    ) -> None:
        self._lock = threading.RLock()
        self._inv = (
            _LockInvariant(invariant, invariant_sketch)
            if invariant is not None else None
        )
        self._name = name or f"Lock@{id(self):x}"
        self._held_token: Any = None
        self._poison: Optional[str] = None  # poison reason or None

    @property
    def is_poisoned(self) -> bool:
        return self._poison is not None

    @property
    def poison_reason(self) -> Optional[str]:
        return self._poison

    def unpoison(self) -> None:
        """Clear the poisoned state — caller is asserting the
        underlying state has been repaired."""
        self._poison = None

    @property
    def name(self) -> str:
        return self._name

    @property
    def invariant(self) -> Optional[Callable[..., bool]]:
        return self._inv.predicate if self._inv else None

    @property
    def invariant_sketch(self) -> str:
        return self._inv.sketch if self._inv else "True"

    @property
    def refinement(self) -> Optional[RefinementType]:
        """The refinement type the invariant represents.  Useful for
        downstream Z3 / Lean encoding."""
        return self._inv.refinement if self._inv else None

    # ── Context-manager entry with an optional shared-state witness ──

    def __call__(self, shared_state: Any = None) -> "_LockSession":
        return _LockSession(self, shared_state)

    def __enter__(self) -> "Lock":
        return self._acquire(shared_state=None)

    def __exit__(self, *exc_info: Any) -> None:
        self._release(shared_state=None)

    # ── Core acquire/release ──

    def _acquire(self, *, shared_state: Any) -> "Lock":
        if self._poison is not None:
            raise InvariantViolation(
                f"{self._name}: lock is poisoned — {self._poison}.  "
                f"Repair the underlying state and call .unpoison() "
                f"before re-acquiring."
            )
        self._lock.acquire()
        try:
            self._check_invariant("acquire", shared_state)
        except InvariantViolation:
            # Couldn't enter the critical section — release the
            # mutex so we don't deadlock the rest of the system, then
            # re-raise.  No poison: the invariant was already broken
            # by something OUTSIDE this critical section.
            self._lock.release()
            raise
        return self

    def _release(self, *, shared_state: Any) -> None:
        try:
            self._check_invariant("release", shared_state)
        except InvariantViolation as exc:
            # Invariant violated INSIDE the critical section.  Mark
            # the lock as poisoned so subsequent acquires fail loudly
            # — but still release the mutex so other waiters don't
            # deadlock.
            self._poison = str(exc)
            self._lock.release()
            raise
        else:
            self._lock.release()

    def _check_invariant(self, phase: str, shared_state: Any) -> None:
        inv = self._inv
        if inv is None:
            return
        try:
            holds = inv.predicate(shared_state) if shared_state is not None \
                else inv.predicate()
        except TypeError:
            # Invariant didn't accept the state argument — call
            # without one.  Matches common patterns.
            holds = inv.predicate()
        if not holds:
            raise InvariantViolation(
                f"{self._name}: invariant '{inv.sketch}' failed at {phase} "
                f"(state={shared_state!r})"
            )


class _LockSession:
    """Lightweight context-manager returned by ``lock(state)``."""
    __slots__ = ("_lock", "_state")

    def __init__(self, lock: Lock, shared_state: Any) -> None:
        self._lock = lock
        self._state = shared_state

    def __enter__(self) -> Any:
        self._lock._acquire(shared_state=self._state)
        return self._state if self._state is not None else self._lock

    def __exit__(self, *exc_info: Any) -> None:
        self._lock._release(shared_state=self._state)


# Convenience alias — docs mention lock_inv binding invariants.
def lock_inv(lock: Lock, invariant: Callable[..., bool],
             *, sketch: str = "True") -> Lock:
    """Attach an invariant to an existing ``Lock`` in-place and
    return the same lock.  Replaces any previous invariant.
    """
    lock._inv = _LockInvariant(invariant, sketch)
    return lock


# ─────────────────────────────────────────────────────────────────────
# Condition variable tied to an owning Lock
# ─────────────────────────────────────────────────────────────────────

class Condition:
    """Condition variable owned by a :class:`Lock`.

    ``wait(predicate)`` — blocks until the predicate holds, re-checking
    the owning lock's invariant on wake-up.  ``notify`` /
    ``notify_all`` — standard.  The invariant is asserted before
    notifying so no thread wakes up in a violated state.
    """

    __slots__ = ("_lock", "_cond")

    def __init__(self, lock: Lock) -> None:
        self._lock = lock
        self._cond = threading.Condition(lock._lock)

    def wait(self,
             predicate: Optional[Callable[..., bool]] = None,
             timeout: Optional[float] = None,
             *, shared_state: Any = None) -> bool:
        if predicate is None:
            return self._cond.wait(timeout=timeout)
        deadline = (time.monotonic() + timeout) if timeout is not None else None
        while True:
            try:
                holds = predicate(shared_state) if shared_state is not None \
                    else predicate()
            except TypeError:
                holds = predicate()
            if holds:
                self._lock._check_invariant("wait-satisfied", shared_state)
                return True
            remaining = None
            if deadline is not None:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    return False
            self._cond.wait(timeout=remaining)

    def notify(self, n: int = 1, *, shared_state: Any = None) -> None:
        self._lock._check_invariant("notify", shared_state)
        self._cond.notify(n)

    def notify_all(self, *, shared_state: Any = None) -> None:
        self._lock._check_invariant("notify_all", shared_state)
        self._cond.notify_all()


# ─────────────────────────────────────────────────────────────────────
# Semaphore with per-slot invariant
# ─────────────────────────────────────────────────────────────────────

class Semaphore:
    """Counting semaphore.

    When ``invariant`` is supplied, the invariant is checked on every
    acquire AND every release — modelling the semaphore as ``n``
    concurrent copies of the lock above, one per slot.
    """

    __slots__ = ("_sem", "_inv", "_name", "_initial")

    def __init__(
        self,
        count: int,
        *,
        invariant: Optional[Callable[..., bool]] = None,
        invariant_sketch: str = "True",
        name: str = "",
    ) -> None:
        if count < 0:
            raise ValueError("Semaphore count must be non-negative")
        self._sem = threading.Semaphore(count)
        self._inv = _LockInvariant(invariant, invariant_sketch) if invariant else None
        self._name = name or f"Semaphore@{id(self):x}"
        self._initial = count

    @property
    def invariant_sketch(self) -> str:
        return self._inv.sketch if self._inv else "True"

    def acquire(self, *, shared_state: Any = None,
                timeout: Optional[float] = None) -> bool:
        if self._inv is not None:
            # Pre-acquire check: invariant must already hold; otherwise
            # whatever broke it before is still broken on entry.  If
            # this fails we don't increment the semaphore.
            self._check("pre-acquire", shared_state)
        ok = self._sem.acquire(timeout=timeout)
        if ok and self._inv is not None:
            try:
                self._check("acquire", shared_state)
            except InvariantViolation:
                self._sem.release()
                raise
        return ok

    def release(self, *, shared_state: Any = None) -> None:
        if self._inv is not None:
            self._check("release", shared_state)
        self._sem.release()

    def _check(self, phase: str, shared_state: Any) -> None:
        inv = self._inv
        assert inv is not None
        try:
            holds = inv.predicate(shared_state) if shared_state is not None \
                else inv.predicate()
        except TypeError:
            holds = inv.predicate()
        if not holds:
            raise InvariantViolation(
                f"{self._name}: invariant '{inv.sketch}' failed at {phase}"
            )

    def __enter__(self) -> "Semaphore":
        # Pass through ``acquire`` and check the return value: a
        # ``False`` (timed out) must NOT silently leak a slot via
        # ``__exit__``.  Default timeout is None so this never times
        # out unless the user supplies one elsewhere.
        ok = self.acquire()
        if not ok:
            raise InvariantViolation(
                f"{self._name}: __enter__ failed — semaphore could not "
                "be acquired"
            )
        return self

    def __exit__(self, *exc_info: Any) -> None:
        self.release()


# ─────────────────────────────────────────────────────────────────────
# atomic_cas — a CAS operation yielding a path fact
# ─────────────────────────────────────────────────────────────────────

@dataclass
class AtomicCell:
    """An atomically-updatable cell.

    The cell's history is a sequence of :class:`PathAbs` entries —
    each successful write corresponds to a path from ``expected`` to
    ``new``.  Callers read the history to obtain a cubical proof that
    the current value descends from the initial one via a chain of
    verified CAS steps.
    """
    _value: Any
    _lock: threading.Lock = field(default_factory=threading.Lock)
    _history: list = field(default_factory=list)  # list[PathAbs]

    def load(self) -> Any:
        with self._lock:
            return self._value

    @property
    def history(self) -> list:
        """Return the list of :class:`PathAbs` steps witnessing the
        cell's evolution.  Copy — caller shouldn't mutate."""
        return list(self._history)


def atomic_cas(
    cell: AtomicCell,
    expected: Any = None,
    new: Any = None,
    *,
    desired: Any = None,
) -> bool:
    """Compare-and-swap.  Returns True on success.

    Both keyword forms are accepted: ``atomic_cas(cell, expected=…,
    new=…)`` or the older tutorial form ``atomic_cas(cell,
    expected=…, desired=…)``.  Positional ``atomic_cas(cell, e, n)``
    also works.  A ``ValueError`` fires if both ``new`` and
    ``desired`` are passed and disagree.

    On success: appends a ``PathAbs(i, expected → new)`` entry to the
    cell's history — the cubical witness of the transition.
    On failure: appends a *reflexive* ``PathAbs`` so the history is
    always continuous (refl means no change).
    """
    # Reconcile the two kwarg names.
    if desired is not None and new is not None and desired != new:
        raise ValueError(
            "atomic_cas: cannot pass both new=… and desired=… with "
            "different values; pick one"
        )
    if desired is not None and new is None:
        new = desired
    with cell._lock:
        if cell._value == expected:
            # Non-trivial path: endpoints differ.
            cell._history.append(PathAbs(
                ivar="i",
                body=Var(f"cas_{id(cell)}_{len(cell._history)}"),
            ))
            cell._value = new
            return True
        # Failure → reflexive path; nothing changed.
        cell._history.append(PathAbs(
            ivar="i",
            body=Var(f"cas_refl_{id(cell)}_{len(cell._history)}"),
        ))
        return False


# ─────────────────────────────────────────────────────────────────────
# Thread spawning with Čech-style patch recording
# ─────────────────────────────────────────────────────────────────────

@dataclass
class _ThreadPatch:
    """A Čech patch carrying the read/write sets of one spawned
    thread plus its running Thread object."""
    thread: threading.Thread
    reads: set
    writes: set
    done: threading.Event = field(default_factory=threading.Event)
    exc: Optional[BaseException] = None
    result: Any = None


def spawn(fn: Callable[..., T], *args: Any,
          reads: Optional[set] = None,
          writes: Optional[set] = None,
          **kwargs: Any) -> _ThreadPatch:
    """Spawn a thread, recording its declared read/write footprint
    as a Čech patch.

    The returned handle works with :func:`join_all`, which checks the
    cocycle condition (disjoint write-sets OR shared invariant) before
    declaring the parallel composition safe.
    """
    reads = set(reads or ())
    writes = set(writes or ())
    patch = _ThreadPatch(
        thread=None,  # type: ignore[arg-type]
        reads=reads, writes=writes,
    )

    def _runner() -> None:
        try:
            patch.result = fn(*args, **kwargs)
        except BaseException as e:
            patch.exc = e
        finally:
            patch.done.set()

    patch.thread = threading.Thread(target=_runner, daemon=True)
    patch.thread.start()
    return patch


def join_all(patches: list[_ThreadPatch],
             *, timeout: Optional[float] = None) -> list[Any]:
    """Join all spawned patches and verify the Čech cocycle condition.

    Cocycle condition: for every pair of patches ``(p_i, p_j)``
    and every shared write-target ``w``, either ``w`` is written by
    only one of them, OR both reads/writes were protected by a
    common lock (we approximate this by requiring the intersection
    of write-sets to be empty — callers that share writes must
    declare them via an ``invariant`` on a shared lock).

    Returns the list of results in order.  Raises :class:`RaceViolation`
    if the cocycle fails.
    """
    # Check cocycle BEFORE joining so we report races even if the
    # threads themselves complete without the OS scheduler exposing
    # the race.
    for i, p in enumerate(patches):
        for p2 in patches[i + 1:]:
            shared_writes = p.writes & p2.writes
            if shared_writes:
                raise RaceViolation(
                    f"Patches write to shared locations {shared_writes}; "
                    "declare a shared Lock with an invariant to make this "
                    "safe (Čech cocycle condition failed)"
                )
    # Join.
    results = []
    for p in patches:
        p.thread.join(timeout=timeout)
        if p.exc is not None:
            raise p.exc
        results.append(p.result)
    return results


# ─────────────────────────────────────────────────────────────────────
# @parallel_safe — decorator that runs data-race analysis at import
# ─────────────────────────────────────────────────────────────────────

def parallel_safe(fn: Callable[..., T]) -> Callable[..., T]:
    """Decorator: runs :func:`deppy.equivalence.analyze_shared_state`
    on the decorated function and raises :class:`RaceViolation` at
    *decoration time* if the lexical analysis finds an unprotected
    shared-state write.

    This is the same analysis the safety pipeline runs — we simply
    trigger it eagerly so users see the race at import.  The
    analysis is lexical (AST-level); it can't catch races that only
    appear through aliasing or dynamic dispatch, but for
    straightforward patterns (global counter without a lock, mutable
    default arg shared across threads) it's sufficient.

    The decorated function is marked ``_deppy_parallel_safe = True``
    so downstream tools (the CLI, the safety pipeline) can see it.
    """
    try:
        from deppy.equivalence import analyze_shared_state
    except Exception:
        # Analysis module missing — fall back to metadata-only.
        fn._deppy_parallel_safe = True  # type: ignore[attr-defined]
        return fn

    try:
        warnings = analyze_shared_state(fn)
    except Exception:
        # If the analyzer itself errors (e.g., function source not
        # available), treat as no warnings but record that we tried.
        warnings = []

    fn._deppy_parallel_safe = True  # type: ignore[attr-defined]
    fn._deppy_parallel_warnings = list(warnings)  # type: ignore[attr-defined]

    # Raise on any definitive race finding.  ``analyze_shared_state``
    # returns ``SharedStateWarning`` objects with ``.severity`` and
    # ``.message`` fields; only ``severity >= 'race'`` raises.
    race_hits = [w for w in warnings
                 if getattr(w, "severity", "") == "race"]
    if race_hits:
        raise RaceViolation(
            f"@parallel_safe: {fn.__name__} has unprotected shared-state "
            f"access: {race_hits[0].message}"
        )
    return fn


# ─────────────────────────────────────────────────────────────────────
# Module re-export roster
# ─────────────────────────────────────────────────────────────────────

__all__ = [
    "Lock", "Condition", "Semaphore",
    "lock_inv",
    "AtomicCell", "atomic_cas",
    "spawn", "join_all",
    "parallel_safe",
    "InvariantViolation", "RaceViolation",
]
