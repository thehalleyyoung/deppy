"""
Deppy Proofs — Sidecar Spec Validator (Gap 11)

When an LLM (or human) writes a sidecar declaration like::

    spec divide:
        exception_free: when "b != 0"

we trust that ``b != 0`` actually rules out exceptions.  But the
declaration could be wrong (the function might still raise even when
``b != 0``) or vacuously over-strong (the function might never raise
*at all*, in which case the precondition is misleading).

The ``SpecValidator`` runs the function on a sample of inputs split into
two cohorts:

    * **positive cohort** — inputs where ``exception_free_when`` holds.
      These must NOT raise (any raise is a bug or a wrong spec).
    * **negative cohort** — inputs where ``exception_free_when`` is
      violated.  At least one should raise; if none do, the spec is
      either over-strong (vacuously safe) or describes the wrong
      condition.

A ``SpecHealthReport`` records the result, with a recommended trust
adjustment that the pipeline can apply.

Public API::

    from deppy.proofs.spec_validator import validate_spec
    report = validate_spec(divide, spec, sample_inputs=[...])
    if not report.ok:
        # downgrade trust before installing
        ...
"""
from __future__ import annotations

import inspect
import random
import types
from dataclasses import dataclass, field, fields, is_dataclass
from decimal import Decimal
from typing import Any, Callable, Optional, Sequence, get_args, get_origin, Union

from deppy.core.kernel import TrustLevel
from deppy.proofs.sidecar import ExternalSpec


@dataclass
class SpecHealthReport:
    """Result of running negative tests on a sidecar spec."""

    target_name: str
    positive_passed: int = 0
    positive_raised: int = 0
    negative_raised: int = 0
    negative_silent: int = 0
    counterexamples: list[dict] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        """True when positive cohort never raised AND negative cohort
        triggered at least one exception (when both cohorts non-empty)."""
        if self.positive_raised > 0:
            return False
        if (self.negative_raised + self.negative_silent) > 0 \
                and self.negative_raised == 0:
            # Spec failed to predict failure ⇒ vacuous / over-strong.
            return False
        return True

    @property
    def recommended_trust(self) -> TrustLevel:
        if not self.ok:
            return TrustLevel.UNTRUSTED
        if self.positive_passed == 0:
            return TrustLevel.AXIOM_TRUSTED  # no evidence either way
        # We tested it and the spec held up.
        return TrustLevel.LLM_CHECKED


# ───────────────────────── Helpers ─────────────────────────────────


def _evaluate_predicate(predicate: str, env: dict) -> Optional[bool]:
    """Evaluate a Python expression *predicate* in environment *env*."""
    try:
        return bool(eval(predicate, {"__builtins__": {}}, env))
    except Exception:
        return None


def _bind_inputs(target: Callable, sample: Any) -> dict:
    """Convert a sample tuple/dict into a kwargs-style env."""
    if isinstance(sample, dict):
        return dict(sample)
    if not isinstance(sample, tuple):
        sample = (sample,)
    try:
        sig = inspect.signature(target)
        names = list(sig.parameters)
    except (TypeError, ValueError):
        names = [f"arg{i}" for i in range(len(sample))]
    env = {}
    for n, v in zip(names, sample):
        env[n] = v
    return env


def _sample_pool_for_annotation(annotation: Any) -> list[Any]:
    """Boundary-oriented sample pool for a parameter annotation."""
    if annotation is inspect._empty:
        return [-3, -1, 0, 1, 2, 5, 10, 100]
    if annotation is Any:
        return [-1, 0, 1, "", "abc", None]
    if annotation is bool:
        return [False, True]
    if annotation is int:
        return [-3, -1, 0, 1, 2, 5, 10, 100]
    if annotation is float:
        return [-3.5, -1.0, 0.0, 0.5, 1.0, 2.5, 10.0]
    if annotation is Decimal:
        return [
            Decimal("-3"), Decimal("-1"), Decimal("0"),
            Decimal("0.1"), Decimal("1"), Decimal("10"),
        ]
    if annotation is str:
        return ["", "0", "1", "-1", "abc", "3.14"]
    if annotation is bytes:
        return [b"", b"0", b"abc"]

    origin = get_origin(annotation)
    args = [a for a in get_args(annotation) if a is not type(None)]
    if origin in (Union, types.UnionType):
        pool: list[Any] = [None] if len(args) != len(get_args(annotation)) else []
        for a in args:
            pool.extend(_sample_pool_for_annotation(a)[:4])
        return pool or [None]
    if origin in (list,):
        inner = _sample_pool_for_annotation(args[0] if args else int)
        seed = inner[0] if inner else 0
        return [[], [seed], inner[:2] if len(inner) >= 2 else [seed]]
    if origin in (set,):
        inner = _sample_pool_for_annotation(args[0] if args else int)
        seed = inner[0] if inner else 0
        return [set(), {seed}]
    if origin in (tuple,):
        inners = args or (int,)
        return [tuple(p[0] for p in map(_sample_pool_for_annotation, inners))]
    if origin in (dict,):
        key_pool = _sample_pool_for_annotation(args[0] if len(args) > 0 else str)
        val_pool = _sample_pool_for_annotation(args[1] if len(args) > 1 else int)
        return [{}, {key_pool[0]: val_pool[0]}]
    if is_dataclass(annotation):
        kwargs = {}
        for f in fields(annotation):
            pool = _sample_pool_for_annotation(f.type)
            kwargs[f.name] = pool[0] if pool else None
        try:
            return [annotation(**kwargs)]
        except Exception:
            return []
    return [-3, -1, 0, 1, 2, 5, 10, 100]


def _resolved_annotations(target: Callable) -> dict[str, Any]:
    """Resolve annotations even under postponed evaluation."""
    try:
        return inspect.get_annotations(target, eval_str=True)
    except Exception:
        raw = getattr(target, "__annotations__", {}) or {}
        env = {
            "Decimal": Decimal,
            "Any": Any,
            "Optional": Optional,
            "Union": Union,
            "list": list,
            "dict": dict,
            "set": set,
            "tuple": tuple,
        }
        out: dict[str, Any] = {}
        for k, v in raw.items():
            if isinstance(v, str):
                try:
                    out[k] = eval(v, {"__builtins__": {}}, env)
                except Exception:
                    out[k] = inspect._empty
            else:
                out[k] = v
        return out


def _generate_default_samples(target: Callable, n: int = 16) -> list:
    """Generate typed boundary samples from the target signature."""
    try:
        sig = inspect.signature(target)
        anns = _resolved_annotations(target)
    except (TypeError, ValueError):
        sig = None
        anns = {}
    rng = random.Random(0xDEAD)
    out: list = []
    if sig is None:
        pool = _sample_pool_for_annotation(inspect._empty)
        for _ in range(n):
            out.append((rng.choice(pool),))
        return out

    param_pools = [
        _sample_pool_for_annotation(anns.get(p.name, p.annotation)) or [0]
        for p in sig.parameters.values()
    ]
    # Deterministic boundary coverage: all-uniform picks first.
    if param_pools:
        out.append(tuple(pool[0] for pool in param_pools))
        out.append(tuple(pool[min(1, len(pool) - 1)] for pool in param_pools))
    for _ in range(max(0, n - len(out))):
        out.append(tuple(rng.choice(pool) for pool in param_pools))
    return out


# ───────────────────────── Public API ──────────────────────────────


def validate_spec(
    target: Callable,
    spec: ExternalSpec,
    *,
    sample_inputs: Optional[Sequence[Any]] = None,
    n_samples: int = 32,
    max_counterexamples: int = 3,
) -> SpecHealthReport:
    """Empirically validate a sidecar spec by running ``target`` on inputs.

    Args:
        target:        The actual callable the spec describes.
        spec:          The ``ExternalSpec`` to validate.
        sample_inputs: Iterable of argument tuples (or dicts).  If
                       omitted, naive integer samples are synthesised.
        n_samples:     How many synthesised samples to generate.
        max_counterexamples: Cap on the number of counterexamples
                       recorded in the report.

    Returns:
        A ``SpecHealthReport`` with positive/negative counts and a
        recommended trust adjustment.
    """
    report = SpecHealthReport(
        target_name=spec.target_name or getattr(target, "__name__", "<anon>"),
    )

    predicates = list(getattr(spec, "exception_free_when", None) or [])
    if not predicates:
        report.notes.append(
            "no exception_free_when predicates — nothing to falsify"
        )
        return report

    if sample_inputs is None:
        sample_inputs = _generate_default_samples(target, n_samples)

    for sample in sample_inputs:
        env = _bind_inputs(target, sample)
        # All predicates must hold for the input to be in the positive cohort.
        evals = [_evaluate_predicate(p, env) for p in predicates]
        if any(e is None for e in evals):
            report.notes.append(f"predicate uneval'd on {sample}")
            continue
        in_positive = all(evals)
        try:
            target(**env) if isinstance(sample, dict) else target(*(
                sample if isinstance(sample, tuple) else (sample,)))
            raised = False
        except Exception as exc:
            raised = True
            if len(report.counterexamples) < max_counterexamples:
                report.counterexamples.append({
                    "input": sample,
                    "in_positive_cohort": in_positive,
                    "exception": type(exc).__name__,
                    "message": str(exc),
                })

        if in_positive:
            if raised:
                report.positive_raised += 1
            else:
                report.positive_passed += 1
        else:
            if raised:
                report.negative_raised += 1
            else:
                report.negative_silent += 1
    return report


__all__ = ["SpecHealthReport", "validate_spec"]
