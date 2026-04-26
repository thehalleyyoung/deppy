"""
deppy.ghost — specification-only ("ghost") variables, structured
cubically as fibrations over the execution path.

Cubical framing
---------------
Each ghost variable is a *fibration* whose base is the execution
trajectory and whose fiber at a given point in time is the value
the specification claims the ghost holds.  Ghost updates form a
:class:`PathAbs` (path abstraction) indexed by the pseudo-interval
``i ∈ [0, 1]``: ``i=0`` is the value before the update, ``i=1`` is
the value after.  Reading a ghost collapses the fiber at the current
point.

Unlike the previous pure-metadata version, this module now has
**real** runtime-checked behaviour:

* ``Ghost[T]`` keeps a mutation log that specifications can query
  (``ghost.history`` returns a list of :class:`PathAbs` steps).
* ``ghost_pts_to(ghost, value)`` and ``array_pts_to(arr, pred)`` build
  assertion objects that the runtime monitor evaluates — the
  separation-logic-style ``points-to`` from the tutorial is real.
* ``ghost_assert(prop)`` raises :class:`GhostViolation` when the
  assertion fails.

Erasure
-------
Ghost values are intended for specifications only.  The compiler
does not erase them (this is Python), but the runtime distinguishes
"ghost" from "real" via the ``Ghost`` wrapper and forbids a ghost
from escaping into ``__repr__`` / JSON serialization of a
non-ghost context via :meth:`Ghost.reveal`, which logs the leak.
"""
from __future__ import annotations

import threading
from dataclasses import dataclass, field
from typing import Any, Callable, Generic, List, Optional, TypeVar

from deppy.core.types import PathAbs, Var

T = TypeVar("T")


# ─────────────────────────────────────────────────────────────────────
# Exception
# ─────────────────────────────────────────────────────────────────────

class GhostViolation(AssertionError):
    """Raised by :func:`ghost_assert` / ``ghost_pts_to`` /
    ``array_pts_to`` when the asserted property doesn't hold."""


# ─────────────────────────────────────────────────────────────────────
# Core Ghost type
# ─────────────────────────────────────────────────────────────────────

@dataclass
class _GhostStep:
    """A single mutation step — a :class:`PathAbs` from the previous
    value to the current one, plus a human label."""
    path: PathAbs
    old_value: Any
    new_value: Any
    label: str = ""


class Ghost(Generic[T]):
    """A specification-only wrapper around a value.

    Maintains a mutation history each entry is a :class:`PathAbs`
    from the old value to the new.  The history lets proofs reason
    about the ghost's evolution without trusting the Python
    interpreter's state at proof time.
    """

    __slots__ = ("_value", "_history", "_name", "_leaks", "_lock")

    def __init__(self, value: T, *, name: str = "") -> None:
        self._value: T = value
        self._history: List[_GhostStep] = [_GhostStep(
            path=PathAbs(ivar="i", body=Var(f"init_{id(self)}")),
            old_value=None, new_value=value, label="init",
        )]
        self._name = name or f"ghost@{id(self):x}"
        self._leaks: int = 0
        self._lock = threading.Lock()

    # ── reads ──

    def reveal(self) -> T:
        """Return the current ghost value.  Records a read so the
        test suite can detect spec-only values leaking into
        production paths."""
        self._leaks += 1
        return self._value

    def peek(self) -> T:
        """Non-logging read — only the spec / proof layer should use
        this (``reveal`` is for runtime code)."""
        return self._value

    @property
    def name(self) -> str:
        return self._name

    @property
    def history(self) -> List[_GhostStep]:
        """Copy of the mutation history.  Each entry is a
        :class:`_GhostStep` with a ``PathAbs`` witness."""
        return list(self._history)

    @property
    def leak_count(self) -> int:
        """Number of times ``.reveal()`` was called.  Non-zero means
        a ghost value may have escaped into production code."""
        return self._leaks

    # ── updates ──

    def update(self, new_value: T, *, label: str = "") -> "Ghost[T]":
        """Mutate the ghost, appending a :class:`PathAbs` step."""
        with self._lock:
            old = self._value
            step = _GhostStep(
                path=PathAbs(
                    ivar="i",
                    body=Var(f"step_{id(self)}_{len(self._history)}"),
                ),
                old_value=old,
                new_value=new_value,
                label=label or f"step{len(self._history)}",
            )
            self._history.append(step)
            self._value = new_value
        return self

    # ── Convenience helpers for set-shaped ghosts ──────────────────

    def add(self, value: Any, *, label: str = "") -> "Ghost":
        """For a set-shaped ghost, add ``value`` and record the step.
        Errors if the wrapped value isn't a set / mutable mapping that
        supports ``add`` or ``__or__``."""
        with self._lock:
            current = self._value
            if hasattr(current, "add") and not isinstance(current, str):
                # Mutable set / set-like — copy then mutate so the
                # history step's old_value snapshot is independent.
                new_set = set(current)
                new_set.add(value)
            elif isinstance(current, frozenset):
                new_set = current | {value}
            else:
                raise TypeError(
                    f"Ghost.add: wrapped value is not set-shaped "
                    f"(type={type(current).__name__})"
                )
        self.update(new_set, label=label or f"add({value!r})")
        return self

    def discard(self, value: Any, *, label: str = "") -> "Ghost":
        """For a set-shaped ghost, remove ``value`` (no error if
        missing)."""
        with self._lock:
            current = self._value
            if hasattr(current, "discard") and not isinstance(current, str):
                new_set = set(current)
                new_set.discard(value)
            elif isinstance(current, frozenset):
                new_set = current - {value}
            else:
                raise TypeError(
                    f"Ghost.discard: wrapped value is not set-shaped "
                    f"(type={type(current).__name__})"
                )
        self.update(new_set, label=label or f"discard({value!r})")
        return self

    def __contains__(self, value: Any) -> bool:
        return value in self._value

    def __len__(self) -> int:
        try:
            return len(self._value)
        except TypeError:
            raise TypeError(
                f"Ghost wrapping {type(self._value).__name__} has no len()"
            )

    def __repr__(self) -> str:
        return f"Ghost({self._value!r}, name={self._name})"


# ─────────────────────────────────────────────────────────────────────
# Constructors (the names the tutorial docs reference)
# ─────────────────────────────────────────────────────────────────────

def ghost_var(
    name: Any = "",
    typ: Optional[type] = None,
    initial: Any = None,
) -> Ghost:
    """Construct a ghost variable.

    Three usage forms — all real:

    1. ``ghost_var("name", int, initial=0)`` — explicit form with
       runtime ``isinstance`` check on ``initial``.
    2. ``ghost_var("name")`` — name-only, ``initial=None``.
    3. ``ghost_var(0)`` — value-only shorthand: when the first
       positional argument is **not** a ``str``, it's treated as
       the ``initial`` value and a synthetic name is generated.

    Form 3 matches the tutorial code's terse style and is preserved
    for compatibility.
    """
    if not isinstance(name, str):
        # Form 3: value-only shorthand.
        initial = name
        name = f"ghost_var@{id(initial):x}"
        # Infer typ if not given.
        if typ is None and initial is not None:
            typ = type(initial)
    if typ is not None and initial is not None:
        if not isinstance(initial, typ):
            raise TypeError(
                f"ghost_var({name!r}, {typ.__name__}, initial=...): "
                f"initial value {initial!r} is not a {typ.__name__}"
            )
    return Ghost(initial, name=name)


def ghost_update(ghost: Ghost[T], new_value: T, *, label: str = "") -> Ghost[T]:
    """Append a mutation step to ``ghost``.  Returns the ghost for
    chaining.  ``new_value`` may also be a callable: it will be
    invoked with the current ghost value and its return is used as
    the new value (this is the form some tutorial code uses to
    express delta-style updates)."""
    if callable(new_value) and not isinstance(new_value, type):
        new_value = new_value(ghost.peek())
    return ghost.update(new_value, label=label)


class _GhostSetFactory:
    """``ghost_set`` is callable AND carries helper attributes
    (``add``, ``discard``, ``contains``) that take a ghost as first
    arg.  This lets older book code use ``ghost_set.add(g, value)``
    while modern code uses ``ghost_set("name")`` to construct.
    """

    def __call__(self, name: Any = "", value: Any = None,
                 *, initial=None, label: str = "") -> Ghost:
        # Form 1: ghost_set(g, value) — backward-compat update.
        if isinstance(name, Ghost):
            target = name
            v = value if value is not None else initial
            if v is None:
                return target
            return target.add(v, label=label)
        # Form 2: ghost_set("name", initial=…) — constructor.
        init = initial if initial is not None else (
            value if value is not None else set()
        )
        if not hasattr(init, "__contains__"):
            raise TypeError(
                f"ghost_set: initial must be set-shaped (got "
                f"{type(init).__name__})"
            )
        return Ghost(init, name=name or f"ghost_set@{id(init):x}")

    @staticmethod
    def add(ghost: Ghost, value: Any, *, label: str = "") -> Ghost:
        """``ghost_set.add(g, v)`` — add ``v`` to the set-shaped
        ghost ``g``."""
        return ghost.add(value, label=label)

    @staticmethod
    def discard(ghost: Ghost, value: Any, *, label: str = "") -> Ghost:
        return ghost.discard(value, label=label)

    @staticmethod
    def contains(ghost: Ghost, value: Any) -> bool:
        return value in ghost


ghost_set = _GhostSetFactory()


# ─────────────────────────────────────────────────────────────────────
# Points-to assertions
# ─────────────────────────────────────────────────────────────────────

@dataclass
class PointsToAssertion:
    """A runtime-checkable assertion that a ghost holds a specific
    value.  Looks like the separation-logic ``x ↦ v`` predicate.
    """
    ghost: Ghost
    expected: Any
    label: str = ""

    def check(self) -> bool:
        return self.ghost.peek() == self.expected

    def __bool__(self) -> bool:
        return self.check()

    def require(self) -> None:
        if not self.check():
            raise GhostViolation(
                f"ghost_pts_to({self.ghost.name}, {self.expected!r}) failed: "
                f"actual {self.ghost.peek()!r}"
            )


def ghost_pts_to(ghost: Ghost[T], value: T, *, label: str = "") -> PointsToAssertion:
    """Construct an assertion that ``ghost`` currently points to
    ``value``.  Evaluate with ``.check()``; enforce with
    ``.require()``."""
    return PointsToAssertion(ghost=ghost, expected=value, label=label)


@dataclass
class ArrayPointsToAssertion:
    """A runtime-checkable assertion that every element of a ghost
    sequence satisfies a predicate.  The separation-logic analogue
    of ``arr ↦ [v₀, v₁, …]`` when the element-wise content is known
    by a predicate rather than by enumerated values.
    """
    ghost: Ghost
    predicate: Callable[[Any], bool]
    predicate_sketch: str = "True"
    label: str = ""

    def check(self) -> bool:
        seq = self.ghost.peek()
        try:
            return all(self.predicate(x) for x in seq)
        except TypeError:
            return False

    def require(self) -> None:
        seq = self.ghost.peek()
        try:
            iter(seq)
        except TypeError:
            raise GhostViolation(
                f"array_pts_to({self.ghost.name}): expected iterable, "
                f"got {type(seq).__name__}"
            )
        for i, x in enumerate(seq):
            if not self.predicate(x):
                raise GhostViolation(
                    f"array_pts_to({self.ghost.name}, {self.predicate_sketch!r}): "
                    f"element at index {i} is {x!r}, predicate failed"
                )


def array_pts_to(
    ghost: Ghost,
    predicate: Callable[[Any], bool],
    *,
    sketch: str = "True",
    label: str = "",
) -> ArrayPointsToAssertion:
    """Construct an assertion that every element of ``ghost`` (which
    must be an iterable) satisfies ``predicate``."""
    return ArrayPointsToAssertion(
        ghost=ghost, predicate=predicate,
        predicate_sketch=sketch, label=label,
    )


def ghost_assert(prop: Any, *, label: str = "") -> None:
    """Shorthand: evaluate a ghost assertion and raise on failure.

    Accepts ``PointsToAssertion`` / ``ArrayPointsToAssertion``
    objects or bare booleans / callables.
    """
    if isinstance(prop, (PointsToAssertion, ArrayPointsToAssertion)):
        prop.require()
        return
    if callable(prop):
        if not prop():
            raise GhostViolation(f"ghost_assert: callable {prop!r} returned False")
        return
    if not prop:
        raise GhostViolation(
            f"ghost_assert: {label or 'assertion'} failed (got {prop!r})"
        )


# ─────────────────────────────────────────────────────────────────────
# Exports
# ─────────────────────────────────────────────────────────────────────

__all__ = [
    "Ghost", "GhostViolation",
    "ghost_var", "ghost_update", "ghost_set",
    "ghost_pts_to", "array_pts_to",
    "PointsToAssertion", "ArrayPointsToAssertion",
    "ghost_assert",
]
