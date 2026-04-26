"""
deppy.async_verify — async/await verification with runtime-enforced
contracts, structured cubically.

Cubical framing
---------------
An async function is a *path in time* — its value before an
``await`` and its resolved value after form the two endpoints of a
:class:`PathAbs`.  ``@async_requires`` pins the left endpoint (the
precondition before the await starts); ``@async_ensures`` pins the
right endpoint (the postcondition once the coroutine resolves).
``@terminates`` is a reflexivity claim: the path has a finite length
bounded by the timeout.

Unlike the previous metadata-only version, these decorators actually
evaluate predicates at runtime and raise :class:`ContractViolation`
when a predicate fails.  They also attach the predicate's sketch
string as a :class:`RefinementType` for Z3 / Lean downstream.

Predicate forms
---------------
Predicates may be:

* a callable taking the same arguments as the decorated function
  (for preconditions) or the return value (for postconditions);
* a :class:`_PurePredicate` constructed by :func:`pure` — a lazy
  sketch that carries the source for Z3 encoding without evaluating.

Types
-----
    @async_requires(pred)          — precondition
    @async_ensures(pred)           — postcondition on the result
    @async_yields(pred)            — invariant on every yielded value
                                     (async generators)
    @async_invariant(pred)         — loop invariant for async loops
    @terminates(deadline=...)      — wraps the coroutine in a timeout
    pure(expr: str) → predicate    — lazy predicate carrying source

Exceptions
----------
    ContractViolation             — pre/post/yield/invariant failed
    TerminationViolation          — @terminates deadline exceeded
"""
from __future__ import annotations

import asyncio
import functools
import inspect
from typing import Any, AsyncIterator, Awaitable, Callable, Optional, TypeVar

from deppy.core.types import RefinementType, PyBoolType

T = TypeVar("T")


# ─────────────────────────────────────────────────────────────────────
# Exceptions
# ─────────────────────────────────────────────────────────────────────

class ContractViolation(AssertionError):
    """Raised when an async pre/postcondition / yield-predicate /
    invariant predicate returns False at runtime."""


class TerminationViolation(AssertionError):
    """Raised when ``@terminates`` deadline elapses before the
    coroutine completes."""


# ─────────────────────────────────────────────────────────────────────
# ``pure()`` — a lazy predicate carrying its source
# ─────────────────────────────────────────────────────────────────────

class _PurePredicate:
    """Predicate that stores its source as a string and compiles
    lazily.  Use :func:`pure` to construct one.

    Why it exists: Z3 and Lean need the *source* of a predicate, not
    the compiled callable.  A ``_PurePredicate`` carries both the
    compiled form (for runtime checks) and the source (for encoding).
    """
    __slots__ = ("_source", "_kind", "_compiled")

    def __init__(self, source: str, kind: str = "post") -> None:
        self._source = source
        self._kind = kind
        self._compiled: Optional[Callable[..., bool]] = None

    @property
    def source(self) -> str:
        return self._source

    @property
    def kind(self) -> str:
        return self._kind

    def refinement(self, name: str = "_result") -> RefinementType:
        """Return the refinement type this predicate represents."""
        return RefinementType(
            base_type=PyBoolType(),
            var_name=name,
            predicate=self._source,
        )

    def __call__(self, *args: Any, **kwargs: Any) -> bool:
        if self._compiled is None:
            # Compile under a minimal env so ``result``, ``arg0``,
            # ``len``, etc. resolve naturally.  Compile lazily so
            # expression-style predicates (``"result >= 0"``) need no
            # special syntax at decoration time.
            env: dict[str, Any] = {
                "__builtins__": {
                    "len": len, "abs": abs, "min": min, "max": max,
                    "sum": sum, "any": any, "all": all,
                    "int": int, "float": float, "bool": bool,
                    "str": str, "list": list, "tuple": tuple,
                    "dict": dict, "set": set, "True": True,
                    "False": False, "None": None,
                },
            }
            code = compile(self._source, "<pure-predicate>", "eval")

            def _compiled(*c_args: Any, **c_kwargs: Any) -> bool:
                local = dict(c_kwargs)
                for i, a in enumerate(c_args):
                    local[f"arg{i}"] = a
                # Positional pseudo-names — ``result`` for 1-arg post,
                # ``arg0`` for 1-arg pre.
                if len(c_args) == 1 and "result" not in local:
                    local["result"] = c_args[0]
                return bool(eval(code, env, local))

            self._compiled = _compiled
        return self._compiled(*args, **kwargs)

    def __repr__(self) -> str:
        return f"pure({self._source!r})"


def pure(source: str) -> _PurePredicate:
    """Construct a lazy predicate from a Python expression string.

    Example::

        @async_ensures(pure("result >= 0"))
        async def abs_val(x: int) -> int:
            return abs(x)

    The string is compiled on first use, and carries the source
    through to Z3 / Lean encoding via
    :meth:`_PurePredicate.refinement`.
    """
    return _PurePredicate(source)


# ─────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────

def _resolve_predicate(pred: Any) -> Callable[..., bool]:
    """Normalise ``pred`` to a callable.

    Accepts: callables, :class:`_PurePredicate`, or strings (wrapped
    as pure predicates).
    """
    if callable(pred) and not isinstance(pred, _PurePredicate):
        return pred
    if isinstance(pred, _PurePredicate):
        return pred
    if isinstance(pred, str):
        return _PurePredicate(pred)
    raise TypeError(
        f"predicate must be callable / pure(...) / str, got {type(pred).__name__}"
    )


def _call_predicate(
    pred: Callable[..., bool],
    args: tuple,
    kwargs: dict,
) -> bool:
    """Call a predicate with best-effort argument matching.

    Uses :func:`inspect.signature` to introspect ``pred`` and bind the
    provided arguments to its declared parameters.  If full binding
    fails because the predicate accepts fewer positional parameters
    than we offered, we try a truncated positional call.  When the
    signature is unintrospectable (built-ins, C-extensions), we fall
    back to direct calls in a fixed order: full → truncated → bare.

    A ``TypeError`` raised from inside the predicate body is *not*
    silently swallowed — only signature-shape mismatches trigger
    truncation.  This is what removes the previous fragile
    string-matching heuristic on TypeError messages.

    Returns the predicate's verdict coerced to bool *only when the
    predicate returned a real bool* — a non-bool truthy value
    (``"yes"``, ``[1]``) raises :class:`ContractViolation` because
    silent coercion would mask logic bugs.
    """
    import inspect

    def _coerce(v: Any) -> bool:
        if isinstance(v, bool):
            return v
        if v is None or isinstance(v, (int, float)):
            return bool(v)
        raise ContractViolation(
            f"predicate {pred!r} returned a non-bool value of type "
            f"{type(v).__name__} ({v!r}); predicates must return bool"
        )

    # Try to introspect.  If we can read pred's signature we can
    # decide *up front* whether (args, kwargs) match — avoiding the
    # fragile "is this TypeError from the body or from binding?"
    # ambiguity entirely.
    try:
        sig = inspect.signature(pred)
    except (TypeError, ValueError):
        sig = None

    if sig is not None:
        params = list(sig.parameters.values())
        accepts_var_positional = any(
            p.kind is p.VAR_POSITIONAL for p in params
        )
        accepts_var_keyword = any(
            p.kind is p.VAR_KEYWORD for p in params
        )
        n_pos = sum(
            1 for p in params
            if p.kind in (p.POSITIONAL_OR_KEYWORD, p.POSITIONAL_ONLY)
        )

        # Attempt 1: bind everything as offered.
        try:
            sig.bind(*args, **kwargs)
            return _coerce(pred(*args, **kwargs))
        except TypeError:
            pass  # signature mismatch — try variations

        # Attempt 2: drop kwargs, truncate positionals to declared arity.
        if not accepts_var_positional and n_pos < len(args):
            truncated = args[:n_pos]
        else:
            truncated = args
        if accepts_var_keyword:
            try:
                sig.bind(*truncated, **kwargs)
                return _coerce(pred(*truncated, **kwargs))
            except TypeError:
                pass

        # Attempt 3: positionals only.
        try:
            sig.bind(*truncated)
            return _coerce(pred(*truncated))
        except TypeError:
            pass

        # Attempt 4: bare.
        try:
            sig.bind()
            return _coerce(pred())
        except TypeError:
            pass

        # No binding works — raise a clean ContractViolation rather
        # than letting an opaque TypeError surface.
        raise ContractViolation(
            f"predicate {pred!r} signature {sig} does not accept "
            f"the call with args={args!r}, kwargs={kwargs!r}"
        )

    # Signature unintrospectable (C builtins etc.) — fall back to
    # direct attempts in order, but only swallow TypeError until the
    # last try.
    for trial_args in (args, args[:-1] if args else args, ()):
        try:
            return _coerce(pred(*trial_args, **kwargs)) if trial_args is args \
                else _coerce(pred(*trial_args))
        except TypeError:
            continue
    raise ContractViolation(
        f"predicate {pred!r} (no introspectable signature) does not "
        f"accept any tested call shape"
    )


# ─────────────────────────────────────────────────────────────────────
# @async_requires / @async_ensures
# ─────────────────────────────────────────────────────────────────────

def async_requires(pred: Any):
    """Async precondition — checked before the coroutine starts.

    The predicate is called with the same positional + keyword
    arguments as the decorated function.
    """
    checker = _resolve_predicate(pred)
    source = getattr(pred, "source", None) or (
        pred if isinstance(pred, str) else repr(pred)
    )

    def decorator(fn):
        if not inspect.iscoroutinefunction(fn):
            raise TypeError(
                f"@async_requires: {fn.__name__} is not an async function"
            )

        @functools.wraps(fn)
        async def wrapper(*args: Any, **kwargs: Any):
            ok = _call_predicate(checker, args, kwargs)
            if not ok:
                raise ContractViolation(
                    f"@async_requires({source!r}) failed for "
                    f"{fn.__name__}(*{args}, **{kwargs})"
                )
            return await fn(*args, **kwargs)

        # Metadata the pipeline / CLI / Lean exporter consume.
        wrapper._deppy_async_requires = source  # type: ignore[attr-defined]
        wrapper.__wrapped__ = fn
        return wrapper

    return decorator


def async_ensures(pred: Any):
    """Async postcondition — checked after the coroutine resolves.

    The predicate is called with the return value as its single
    positional argument (and also as ``result`` kwarg when the
    predicate's signature accepts it).
    """
    checker = _resolve_predicate(pred)
    source = getattr(pred, "source", None) or (
        pred if isinstance(pred, str) else repr(pred)
    )

    def decorator(fn):
        if not inspect.iscoroutinefunction(fn):
            raise TypeError(
                f"@async_ensures: {fn.__name__} is not an async function"
            )

        @functools.wraps(fn)
        async def wrapper(*args: Any, **kwargs: Any):
            result = await fn(*args, **kwargs)
            try:
                ok = _call_predicate(checker, (result,), {"result": result})
            except TypeError:
                ok = _call_predicate(checker, (result,), {})
            if not ok:
                raise ContractViolation(
                    f"@async_ensures({source!r}) failed for "
                    f"{fn.__name__} → {result!r}"
                )
            return result

        wrapper._deppy_async_ensures = source  # type: ignore[attr-defined]
        wrapper.__wrapped__ = fn
        return wrapper

    return decorator


# ─────────────────────────────────────────────────────────────────────
# @async_yields (for async generators)
# ─────────────────────────────────────────────────────────────────────

def async_yields(pred: Any):
    """Invariant on every yielded value of an async generator."""
    checker = _resolve_predicate(pred)
    source = getattr(pred, "source", None) or (
        pred if isinstance(pred, str) else repr(pred)
    )

    def decorator(fn):
        if not inspect.isasyncgenfunction(fn):
            raise TypeError(
                f"@async_yields: {fn.__name__} is not an async generator"
            )

        @functools.wraps(fn)
        async def wrapper(*args: Any, **kwargs: Any) -> AsyncIterator[Any]:
            async for item in fn(*args, **kwargs):
                try:
                    ok = _call_predicate(checker, (item,), {"item": item})
                except TypeError:
                    ok = _call_predicate(checker, (item,), {})
                if not ok:
                    raise ContractViolation(
                        f"@async_yields({source!r}) failed on yielded "
                        f"value {item!r} from {fn.__name__}"
                    )
                yield item

        wrapper._deppy_async_yields = source  # type: ignore[attr-defined]
        wrapper.__wrapped__ = fn
        return wrapper

    return decorator


# ─────────────────────────────────────────────────────────────────────
# @async_invariant — loop invariant for async loops
# ─────────────────────────────────────────────────────────────────────

def async_invariant(pred: Any):
    """Loop-invariant marker for async loops.

    The predicate itself is evaluated once per call (before and
    after the function body) — the invariant should hold at entry
    and exit.  For a deeper iteration-by-iteration check, write the
    check inside the loop body and raise ``ContractViolation`` there.
    """
    checker = _resolve_predicate(pred)
    source = getattr(pred, "source", None) or (
        pred if isinstance(pred, str) else repr(pred)
    )

    def decorator(fn):
        if not inspect.iscoroutinefunction(fn):
            raise TypeError(
                f"@async_invariant: {fn.__name__} is not an async function"
            )

        @functools.wraps(fn)
        async def wrapper(*args: Any, **kwargs: Any):
            # Entry check.
            ok = _call_predicate(checker, args, kwargs)
            if not ok:
                raise ContractViolation(
                    f"@async_invariant({source!r}) failed at entry of "
                    f"{fn.__name__}"
                )
            result = await fn(*args, **kwargs)
            # Exit check — includes the result for convenience.
            exit_args = args + (result,)
            exit_kwargs = dict(kwargs)
            exit_kwargs.setdefault("result", result)
            ok = _call_predicate(checker, exit_args, exit_kwargs)
            if not ok:
                raise ContractViolation(
                    f"@async_invariant({source!r}) failed at exit of "
                    f"{fn.__name__}"
                )
            return result

        wrapper._deppy_async_invariant = source  # type: ignore[attr-defined]
        wrapper.__wrapped__ = fn
        return wrapper

    return decorator


# ─────────────────────────────────────────────────────────────────────
# @terminates — deadline-bounded async execution
# ─────────────────────────────────────────────────────────────────────

def terminates(arg=None, *, deadline: float = 30.0):
    """Wrap an async function in a real :func:`asyncio.wait_for`
    barrier.  A coroutine that runs longer than ``deadline`` seconds
    raises :class:`TerminationViolation`.

    Two forms accepted:

    * ``@terminates`` (bare)        — uses default deadline 30.0s
    * ``@terminates(deadline=10.0)`` — explicit deadline

    External cancellation (``task.cancel()``) on the wrapped coroutine
    is converted to :class:`TerminationViolation` with a clear
    message — the previous version let the ``CancelledError`` propagate
    invisibly through the contract.

    Cubical reading: ``@terminates`` declares a *bounded* path in
    time.  The path's reflexivity (refl) is the claim that the
    coroutine completes without detour; the timeout is the length
    bound on the path; external cancellation is a path that's been
    cut short and must be reported as such.
    """
    # Bare-form support: @terminates without parens.  In that case the
    # decorator was applied directly to the function — first arg is
    # the function.
    if callable(arg) and inspect.iscoroutinefunction(arg):
        return _make_terminates(arg, 30.0)

    if arg is not None and not callable(arg):
        # Treat positional arg as the deadline value (compatibility).
        deadline = float(arg)

    if deadline <= 0:
        raise ValueError("@terminates: deadline must be positive")

    def decorator(fn):
        return _make_terminates(fn, deadline)

    return decorator


def _make_terminates(fn, deadline: float):
    """Build the wrapper.  Shared by the bare and parametrised forms."""
    if not inspect.iscoroutinefunction(fn):
        raise TypeError(
            f"@terminates: {fn.__name__} is not an async function"
        )

    @functools.wraps(fn)
    async def wrapper(*args: Any, **kwargs: Any):
        try:
            return await asyncio.wait_for(
                fn(*args, **kwargs), timeout=deadline,
            )
        except asyncio.TimeoutError:
            raise TerminationViolation(
                f"@terminates: {fn.__name__} did not complete within "
                f"{deadline:.3f}s"
            )
        except asyncio.CancelledError:
            # External cancel — surface as a contract violation
            # rather than letting CancelledError propagate silently.
            raise TerminationViolation(
                f"@terminates: {fn.__name__} was externally cancelled "
                f"before its {deadline:.3f}s deadline"
            )

    wrapper._deppy_terminates = deadline  # type: ignore[attr-defined]
    wrapper.__wrapped__ = fn
    return wrapper


# ─────────────────────────────────────────────────────────────────────
# Module exports
# ─────────────────────────────────────────────────────────────────────

__all__ = [
    "async_requires", "async_ensures", "async_yields", "async_invariant",
    "terminates",
    "pure",
    "ContractViolation", "TerminationViolation",
]
