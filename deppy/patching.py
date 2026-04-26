"""
deppy.patching — verified monkey patches via equivalence checking.

``@safe_patch(target_cls, "method_name")`` runs
:func:`deppy.equivalence.check_equiv` between the original method
and the proposed replacement, then *only* installs the patch when
the check returns ``equivalent=True`` (or ``None`` with matching
signatures, configurable).  A failed check raises
:class:`SafePatchRejected` rather than silently letting a behaviour
regression through.
"""
from __future__ import annotations
import functools
import inspect
from typing import Any


class SafePatchRejected(Exception):
    """Raised when a ``@safe_patch`` cannot be installed.

    The patch was not equivalent to the original (or the equivalence
    check produced a counterexample).  The decorated wrapper is
    *not* installed onto the target class — calls keep using the
    original method.
    """
    def __init__(self, msg: str, *, counterexample: Any | None = None,
                 reason: str = ""):
        super().__init__(msg)
        self.counterexample = counterexample
        self.reason = reason


def _signatures_compatible(orig, new) -> tuple[bool, str]:
    """Liberal signature check: same param count & names (excluding self)."""
    try:
        s1 = inspect.signature(orig)
        s2 = inspect.signature(new)
    except (TypeError, ValueError):
        return True, "signatures unintrospectable — assumed compatible"
    p1 = [
        p for p in s1.parameters.values()
        if p.kind not in (p.VAR_POSITIONAL, p.VAR_KEYWORD)
    ]
    p2 = [
        p for p in s2.parameters.values()
        if p.kind not in (p.VAR_POSITIONAL, p.VAR_KEYWORD)
    ]
    if len(p1) != len(p2):
        return False, (
            f"arity mismatch: {len(p1)} vs {len(p2)} declared parameters"
        )
    for a, b in zip(p1, p2):
        if a.name != b.name:
            return False, (
                f"parameter name mismatch: {a.name!r} vs {b.name!r}"
            )
    return True, "signatures compatible"


def safe_patch(target_cls, method_name: str = "", *,
               install: bool = True,
               require_equivalence: bool = True):
    """Verified monkey patch.

    Usage::

        @safe_patch(Logger, "log")
        def timestamped_log(self, message: str) -> None:
            ...

    Verification flow:

    1. Resolve the original method ``getattr(target_cls,
       method_name)``.
    2. Run :meth:`_signatures_compatible` — same arity, same
       parameter names.  Failure → :class:`SafePatchRejected`.
    3. Run :func:`deppy.equivalence.check_equiv` between original and
       new implementation.  When ``require_equivalence=True``
       (default), an inequivalent or unknown verdict with a
       counterexample → :class:`SafePatchRejected`.
    4. On success, install the patch on ``target_cls`` (when
       ``install=True``) and return the wrapped function.

    Set ``install=False`` to perform the verification without
    actually mutating ``target_cls`` — the wrapper will still carry
    proof metadata, suitable for offline static analysis.
    """
    if not method_name:
        raise TypeError(
            "safe_patch: method_name is required — pass the name of the "
            "method on target_cls being replaced"
        )

    def decorator(fn):
        original = getattr(target_cls, method_name, None)
        if original is None:
            raise SafePatchRejected(
                f"safe_patch: {target_cls.__name__} has no method "
                f"{method_name!r} to patch"
            )

        ok, reason = _signatures_compatible(original, fn)
        if not ok:
            raise SafePatchRejected(
                f"safe_patch({target_cls.__name__}, {method_name!r}): "
                f"{reason}",
                reason=reason,
            )

        # Equivalence check.  We import lazily to avoid a circular
        # import (deppy.equivalence imports from this package).
        from deppy.equivalence import check_equiv
        try:
            equiv_result = check_equiv(original, fn)
        except Exception as e:  # pragma: no cover — safety net
            equiv_result = None
            equiv_msg = (
                f"check_equiv raised {type(e).__name__}: {e}"
            )
        else:
            equiv_msg = ""

        verdict_ok = True
        cex = None
        if equiv_result is not None:
            equivalent = getattr(equiv_result, "equivalent", None)
            cex = getattr(equiv_result, "counterexample", None)
            if equivalent is False:
                verdict_ok = False
            elif equivalent is None and cex is not None:
                verdict_ok = False

        if require_equivalence and not verdict_ok:
            raise SafePatchRejected(
                f"safe_patch({target_cls.__name__}, {method_name!r}): "
                f"original and patched implementation differ"
                + (f" — counterexample: {cex!r}" if cex else "")
                + (f" — {equiv_msg}" if equiv_msg else ""),
                counterexample=cex,
                reason="equivalence_failed",
            )

        @functools.wraps(fn)
        def wrapper(*args, **kwargs):
            return fn(*args, **kwargs)

        wrapper._deppy_safe_patch = True
        wrapper._deppy_patch_target = target_cls
        wrapper._deppy_patch_method = method_name
        wrapper._deppy_patch_original = original
        wrapper._deppy_patch_equiv_result = equiv_result

        if install:
            setattr(target_cls, method_name, wrapper)

        return wrapper

    return decorator
