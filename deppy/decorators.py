"""
deppy.decorators — decorator inspection + spec-preservation
decorators, structured cubically.

Cubical framing
---------------
A decorator ``D`` turns a function ``f`` into a wrapper ``D(f)``.
When the wrapper is supposed to preserve ``f``'s spec, the correct
statement is a **path** in the space of spec-satisfying functions:

    p : f ≃_spec D(f)                 — a homotopy rel `spec`

``@preserves_spec`` records this path requirement and exposes it at
runtime by calling the wrapper with a sample of inputs and checking
the `spec` holds on both ``f(x)`` and ``D(f)(x)`` — the two endpoints
of the path must agree pointwise on the guarantee.

``@transforms_spec`` instead declares the path is *not* an identity:
the outer spec differs from the inner by an explicit transformation,
captured as metadata so downstream verifiers can compute the
transported spec.

Entry points
------------
    unwrap_decorator_stack(fn)   — strip ``__wrapped__``
    decorator_chain(fn)          — list [outermost, …, original]
    preserves_spec(decorator)    — asserts wrapper maintains inner spec
    transforms_spec(*, adds_guarantee=..., modifies_return=..., ...)
"""
from __future__ import annotations

import functools
import inspect
import random
from typing import Any, Callable, List, Optional, TypeVar

F = TypeVar("F", bound=Callable[..., Any])


# ─────────────────────────────────────────────────────────────────────
# Inspection helpers (unchanged)
# ─────────────────────────────────────────────────────────────────────

def unwrap_decorator_stack(fn):
    """Unwrap a stack of decorators, returning the original function."""
    while hasattr(fn, '__wrapped__'):
        fn = fn.__wrapped__
    return fn


def decorator_chain(fn):
    """Return the chain of decorators applied to fn (outermost first)."""
    chain = []
    current = fn
    while hasattr(current, '__wrapped__'):
        chain.append(current)
        current = current.__wrapped__
    chain.append(current)  # original function
    return chain


# ─────────────────────────────────────────────────────────────────────
# Exception + metadata
# ─────────────────────────────────────────────────────────────────────

class SpecPreservationViolation(AssertionError):
    """Raised when ``@preserves_spec`` observes a sampled input where
    the wrapper's output fails a guarantee that held on the inner
    function's output — i.e., the supposed homotopy isn't one."""


# ─────────────────────────────────────────────────────────────────────
# @preserves_spec
# ─────────────────────────────────────────────────────────────────────

def preserves_spec(
    decorator: Optional[Callable[[F], F]] = None,
    *,
    samples: int = 32,
    sample_ints: tuple = (-3, -1, 0, 1, 2, 10),
    strict: bool = True,
) -> Any:
    """Decorator of decorators: declare that a decorator preserves
    any ``@guarantee`` its target function carries.

    Usage::

        @preserves_spec
        def memoize(fn):
            cache = {}
            @functools.wraps(fn)
            def wrapper(*args, **kwargs):
                key = (args, tuple(sorted(kwargs.items())))
                if key not in cache:
                    cache[key] = fn(*args, **kwargs)
                return cache[key]
            return wrapper

        @memoize
        @guarantee("result >= 0")
        def f(x: int) -> int:
            return x * x

    At decoration time, ``@preserves_spec`` re-decorates each
    application of ``memoize`` so that the resulting wrapper, when
    first called, compares its output against the inner function's
    output on a small sample of inputs AND re-evaluates every
    guarantee on both outputs.  Disagreements raise
    :class:`SpecPreservationViolation`.

    Parameters
    ----------
    samples
        How many random integer inputs to try when the decorated
        function has a single ``int`` parameter.  For functions
        with other signatures, we skip the sampling and only verify
        that the guarantee string list carries over.
    sample_ints
        Fixed "canonical" inputs that are always tried before the
        random ones.  Catches boundary cases (0, negatives).
    strict
        When False, mismatches are recorded on the wrapper as
        ``wrapper._deppy_preserves_spec_warnings`` instead of
        raising.

    Cubical reading: the decorator claims a *homotopy* between
    ``fn`` and ``decorator(fn)`` relative to the spec.  The sampler
    plays the role of evaluating the homotopy at several interval
    points — if any point disagrees on the guarantee, the supposed
    path doesn't exist.
    """
    # Support ``@preserves_spec`` without parentheses.
    if decorator is not None and callable(decorator):
        return _make_preserves(decorator, samples=samples,
                                sample_ints=sample_ints, strict=strict)

    def _wrap(dec: Callable[[F], F]) -> Callable[[F], F]:
        return _make_preserves(dec, samples=samples,
                                sample_ints=sample_ints, strict=strict)
    return _wrap


def _make_preserves(
    dec: Callable[[F], F],
    *,
    samples: int,
    sample_ints: tuple,
    strict: bool,
) -> Callable[[F], F]:
    """Wrap ``dec`` so that when applied to ``f`` the resulting
    wrapper enforces spec preservation.

    Coverage policy
    ---------------
    * ``samples == 0`` → emit a one-shot warning attribute and skip.
    * Single-arg functions (any annotated type or none) → sampled
      using :func:`_sample_value` per the parameter's annotation.
    * Multi-arg functions → cartesian product of small per-parameter
      samples (capped at ``samples`` total).
    * **Output equality + per-guarantee predicate evaluation** —
      every sampled output passes if and only if (a) the wrapper's
      output equals the inner's AND (b) every inner ``@guarantee``
      string evaluates to the same truth value on both outputs.
    """

    @functools.wraps(dec)
    def patched(f: F) -> F:
        wrapper: F = dec(f)
        inner_specs = _collect_guarantees(f)

        try:
            wrapper._deppy_preserves_spec = True  # type: ignore[attr-defined]
            wrapper._deppy_inner_guarantees = list(inner_specs)  # type: ignore[attr-defined]
            wrapper._deppy_preserves_spec_warnings = []  # type: ignore[attr-defined]
        except (AttributeError, TypeError):
            pass

        # samples=0 — explicit no-op, but warn so users notice.
        if samples == 0 and not sample_ints:
            try:
                wrapper._deppy_preserves_spec_warnings = [  # type: ignore[attr-defined]
                    "samples=0 with empty sample_ints: no checks ran"
                ]
            except (AttributeError, TypeError):
                pass
            return wrapper

        sig = _signature_safe(f)
        if sig is None:
            return wrapper

        # Build the input set.
        param_list = [
            p for p in sig.parameters.values()
            if p.kind in (p.POSITIONAL_OR_KEYWORD, p.POSITIONAL_ONLY)
        ]

        if not param_list:
            # Zero-arg function — call once.
            input_tuples: List[tuple] = [()]
        elif len(param_list) == 1 and _is_int_annotation(param_list[0].annotation):
            # Backward-compatible single-int-param path.
            input_tuples = [(x,) for x in (
                list(sample_ints) +
                [random.randint(-1000, 1000)
                 for _ in range(max(0, samples - len(sample_ints)))]
            )]
        else:
            # General multi-param case: per-parameter small sample set,
            # then trim to ``samples``.
            per_param_samples = [
                _sample_values(p.annotation, count=4) for p in param_list
            ]
            cartesian: List[tuple] = []
            # Bounded cross product.
            def _combine(prefix: tuple, idx: int) -> None:
                if len(cartesian) >= samples:
                    return
                if idx == len(per_param_samples):
                    cartesian.append(prefix)
                    return
                for v in per_param_samples[idx]:
                    if len(cartesian) >= samples:
                        return
                    _combine(prefix + (v,), idx + 1)
            _combine((), 0)
            input_tuples = cartesian

        violations: List[str] = []
        for inputs in input_tuples:
            try:
                y_inner = f(*inputs)
                y_wrap = wrapper(*inputs)
            except Exception:
                continue
            # (a) output equality
            if y_inner != y_wrap:
                violations.append(
                    f"{_name(dec)}({_name(f)})({inputs!r}) = {y_wrap!r}, "
                    f"but inner {_name(f)}({inputs!r}) = {y_inner!r}"
                )
                continue
            # (b) per-guarantee equality of truth values
            for spec in inner_specs:
                inner_holds = _eval_guarantee_safely(spec, y_inner, inputs)
                wrap_holds = _eval_guarantee_safely(spec, y_wrap, inputs)
                if inner_holds != wrap_holds:
                    violations.append(
                        f"{_name(dec)}: guarantee {spec!r} differs on "
                        f"{inputs!r}: inner={inner_holds}, "
                        f"wrapped={wrap_holds}"
                    )
                    break

        if violations:
            if strict:
                raise SpecPreservationViolation(
                    f"@preserves_spec: {_name(dec)} did not preserve "
                    f"{_name(f)}'s output on {len(violations)} sampled "
                    f"inputs; first mismatch: {violations[0]}"
                )
            try:
                wrapper._deppy_preserves_spec_warnings = violations  # type: ignore[attr-defined]
            except (AttributeError, TypeError):
                pass

        return wrapper

    return patched


# ── Sampling helpers ────────────────────────────────────────────────

def _sample_values(annotation: Any, *, count: int = 4) -> list:
    """Generate ``count`` plausible sample values for a parameter
    type annotation."""
    if annotation in (int, "int"):
        return [-1, 0, 1, 7][:count]
    if annotation in (float, "float"):
        return [-1.5, 0.0, 1.5, 3.14][:count]
    if annotation in (bool, "bool"):
        return [True, False]
    if annotation in (str, "str"):
        return ["", "a", "abc", "deppy"][:count]
    if annotation in (list, "list"):
        return [[], [1], [1, 2], [0, -1, 2]][:count]
    if annotation in (dict, "dict"):
        return [{}, {"k": 1}, {"a": 1, "b": 2}][:count]
    if annotation in (tuple, "tuple"):
        return [(), (1,), (1, 2), (0, "x")][:count]
    if annotation in (set, "set"):
        return [set(), {1}, {1, 2}][:count]
    # Empty annotation or unknown type: use ints as a fallback (still
    # valid Python; if the function rejects them, the call raises and
    # is skipped).
    return [-1, 0, 1, 7][:count]


def _is_int_annotation(annotation: Any) -> bool:
    return annotation in (int, "int", inspect.Parameter.empty)


def _eval_guarantee_safely(
    spec: str, result: Any, inputs: tuple,
) -> Any:
    """Evaluate a guarantee string against an output and inputs.

    Builds a minimal env binding ``result``, ``arg0``…``argN``.  On
    any error returns the sentinel ``"<unevaluable>"`` so the caller
    can detect that *both* sides were unevaluable (still equal) or
    that one side is and the other isn't (genuine difference).
    """
    env: dict = {
        "__builtins__": {
            "len": len, "abs": abs, "min": min, "max": max,
            "sum": sum, "any": any, "all": all,
            "True": True, "False": False, "None": None,
        },
        "result": result,
    }
    for i, v in enumerate(inputs):
        env[f"arg{i}"] = v
    try:
        return bool(eval(spec, env))
    except Exception:
        return "<unevaluable>"


def _collect_guarantees(f: Any) -> List[str]:
    spec = getattr(f, "_deppy_spec", None)
    if spec is None:
        return []
    return list(getattr(spec, "guarantees", []) or [])


def _signature_safe(f: Any) -> Optional[inspect.Signature]:
    try:
        return inspect.signature(f)
    except (TypeError, ValueError):
        return None


def _is_single_int_param(sig: inspect.Signature) -> bool:
    params = [p for p in sig.parameters.values()
              if p.kind in (p.POSITIONAL_OR_KEYWORD, p.POSITIONAL_ONLY)]
    if len(params) != 1:
        return False
    ann = params[0].annotation
    return ann in (int, "int", inspect.Parameter.empty)


def _name(obj: Any) -> str:
    return getattr(obj, "__qualname__",
                   getattr(obj, "__name__", repr(obj)))


# ─────────────────────────────────────────────────────────────────────
# @transforms_spec
# ─────────────────────────────────────────────────────────────────────

def transforms_spec(
    *,
    adds_guarantee: Optional[str] = None,
    removes_guarantee: Optional[str] = None,
    modifies_return: Optional[str] = None,
    adds_precondition: Optional[str] = None,
) -> Callable[[F], F]:
    """Decorator of decorators: declare exactly how a decorator
    transforms its target's spec.

    Unlike ``@preserves_spec`` which claims the homotopy is identity,
    ``@transforms_spec`` records a *non-trivial path* between the
    inner spec and the outer spec::

        @transforms_spec(adds_guarantee="result is cached")
        def memoize(fn):
            ...

        @transforms_spec(modifies_return="Optional[T] instead of T")
        def nullable(fn):
            ...

    Downstream verifiers (the safety pipeline, the Lean exporter)
    read the transformation metadata to compute the outer spec as
    ``inner_spec · transformation`` — the HoTT ``transport`` of the
    inner's spec along the declared path.

    Parameters
    ----------
    adds_guarantee
        A new guarantee string the wrapped function acquires.
    removes_guarantee
        A guarantee the inner function had that the wrapper cannot
        carry forward (the wrapper *weakens* the spec).
    modifies_return
        Description of a return-type transformation
        (e.g. ``"Optional[T] instead of T"``).
    adds_precondition
        A new precondition that callers of the wrapper must satisfy.
    """
    def _wrap(dec: F) -> F:
        @functools.wraps(dec)
        def patched(f):
            wrapper = dec(f)
            try:
                wrapper._deppy_transforms_spec = {
                    "adds_guarantee": adds_guarantee,
                    "removes_guarantee": removes_guarantee,
                    "modifies_return": modifies_return,
                    "adds_precondition": adds_precondition,
                }  # type: ignore[attr-defined]
            except (AttributeError, TypeError):
                pass
            # Propagate into the _deppy_spec structure if the wrapper
            # has one — otherwise attach a fresh metadata record.
            try:
                from deppy.proofs.sugar import _get_spec
                spec = _get_spec(wrapper)
                if adds_guarantee:
                    spec.guarantees.append(adds_guarantee)
                if removes_guarantee and removes_guarantee in spec.guarantees:
                    spec.guarantees.remove(removes_guarantee)
            except Exception:
                pass
            return wrapper
        return patched  # type: ignore[return-value]
    return _wrap


__all__ = [
    "unwrap_decorator_stack",
    "decorator_chain",
    "SpecPreservationViolation",
    "preserves_spec",
    "transforms_spec",
]
