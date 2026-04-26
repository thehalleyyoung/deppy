"""Verdict-visible assert-narrowing dependence tracking.

Audit fix #12
=============

Python's ``assert`` statement is *removed* by the bytecode compiler
when run with ``-O`` / ``PYTHONOPTIMIZE``.  When the deppy pipeline
uses an ``assert P`` to narrow the path-sensitive guard set, every
discharge that relies on that narrowing becomes silently unsound
under ``-O`` — the asserts simply don't run, the predicate holds
vacuously, and the runtime exception is no longer prevented.

Before this module the safety pipeline emitted a *warning note* but
still set ``is_safe=True`` on the function verdict.  A consumer that
read only the boolean (e.g. a CI gate) approved the function for
deployment, including under ``-O``.

This module makes the assert dependence *verdict-visible*:

  * ``FunctionVerdict`` carries an ``assert_narrowing_dependent``
    boolean and an ``assert_dependent_sources`` list of source IDs
    whose discharge actually relied on assert-derived guards.
  * ``SafetyVerdict`` aggregates with an
    ``assert_narrowing_dependent`` boolean (any function depended)
    and an ``assert_dependent_functions`` list.
  * The pipeline accepts an ``allow_assert_narrowing`` parameter:

      - ``False`` (default): a function whose discharges depend on
        an assert is forced to ``is_safe=False`` with trust
        downgraded to ``UNTRUSTED``.  This is the safe default.

      - ``True``: the verdict is preserved (``is_safe=True`` stays
        true), but the dependence flag is still set so consumers
        can see it.  Callers opt in only when they're confident
        the deployed code does NOT use ``-O``.

Public API
----------

::

    deps = AssertDependenceTracker.empty()
    deps = deps.with_function(fn_name, sources)
    deps.dependent_functions   # list[str]
    deps.dependent_sources(fn) # list[str]
    deps.is_dependent(fn)      # bool
    deps.any_dependent()       # bool

    apply_assert_dependence_gate(verdict, deps,
                                 allow=allow_assert_narrowing)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Optional


# ─────────────────────────────────────────────────────────────────────
#  Tracker
# ─────────────────────────────────────────────────────────────────────


@dataclass
class AssertDependenceTracker:
    """Per-function record of which discharges depended on
    assert-derived guards.

    The tracker is built up during the discharge phase: whenever a
    source is discharged using a guard that was added by an
    ``assert`` statement, the source ID is recorded against its
    function.  The tracker is then handed to
    :func:`apply_assert_dependence_gate` which downgrades the
    verdict if the user did not opt in via ``allow_assert_narrowing``.
    """

    by_function: dict[str, list[str]] = field(default_factory=dict)

    @classmethod
    def empty(cls) -> "AssertDependenceTracker":
        return cls()

    def with_function(
        self, fn_name: str, sources: Iterable[str],
    ) -> "AssertDependenceTracker":
        new_by_function = {k: list(v) for k, v in self.by_function.items()}
        new_by_function.setdefault(fn_name, []).extend(sources)
        return AssertDependenceTracker(by_function=new_by_function)

    def add(self, fn_name: str, source_id: str) -> None:
        self.by_function.setdefault(fn_name, []).append(source_id)

    @property
    def dependent_functions(self) -> list[str]:
        return sorted(
            n for n, sources in self.by_function.items() if sources
        )

    def dependent_sources(self, fn_name: str) -> list[str]:
        return list(self.by_function.get(fn_name, []))

    def is_dependent(self, fn_name: str) -> bool:
        return bool(self.by_function.get(fn_name))

    def any_dependent(self) -> bool:
        return any(v for v in self.by_function.values())

    def merge(
        self, other: "AssertDependenceTracker",
    ) -> "AssertDependenceTracker":
        merged: dict[str, list[str]] = {
            k: list(v) for k, v in self.by_function.items()
        }
        for k, v in other.by_function.items():
            merged.setdefault(k, []).extend(v)
        return AssertDependenceTracker(by_function=merged)


# ─────────────────────────────────────────────────────────────────────
#  Discharge classifier — does this discharge depend on an assert?
# ─────────────────────────────────────────────────────────────────────


def discharge_depends_on_assert(
    discharge, refinement_map,
) -> bool:
    """Return True iff ``discharge`` relied on a guard added by an
    ``assert`` statement.

    The current discharge model is coarse: the
    :class:`~deppy.pipeline.refinement_inference.RefinementMap`
    carries a function-wide ``used_assert_narrowing`` flag.  When
    that flag is set, *any* path-sensitive discharge in that
    function is suspect.  We err on the side of conservative —
    if the flag is set and the discharge used a path-sensitive
    mechanism (z3-arithmetic / z3-syntactic / co-located-peer),
    we treat it as assert-dependent.

    This mirrors the existing safety-pipeline check that emitted
    only a warning; we now turn it into a structured decision so
    the verdict can be downgraded.
    """
    if refinement_map is None:
        return False
    if not getattr(refinement_map, "used_assert_narrowing", False):
        return False
    inner = getattr(discharge, "inner", None)
    if inner is None:
        return False
    inner_name = type(inner).__name__
    # ``Assume`` doesn't claim a discharge — there's no dependence.
    if inner_name == "Assume":
        return False
    return True


def collect_assert_dependences(
    fn_name: str,  # noqa: ARG001 — kept for symmetric per-function API
    discharges: Iterable,
    refinement_map,
) -> list[str]:
    """Return the list of source IDs in ``discharges`` whose
    discharge depended on assert-derived guards.

    The ``fn_name`` parameter is currently unused but is kept in
    the signature so callers can pass it without contortions; future
    iterations may use it to scope per-function refinement maps.
    """
    del fn_name  # explicit acknowledgement
    out: list[str] = []
    for d in discharges:
        if discharge_depends_on_assert(d, refinement_map):
            sid = getattr(d, "source_id", None)
            if sid is not None:
                out.append(str(sid))
    return out


# ─────────────────────────────────────────────────────────────────────
#  Verdict gate
# ─────────────────────────────────────────────────────────────────────


def apply_assert_dependence_gate(
    fn_verdict, dependence_sources: list[str], *,
    allow: bool,
) -> None:
    """Mutate ``fn_verdict`` in place to record assert dependence
    and (when ``allow=False``) force ``is_safe=False``.

    ``fn_verdict`` is expected to be a
    :class:`~deppy.pipeline.safety_pipeline.FunctionVerdict`-shaped
    object.  We use ``setattr`` rather than dataclass replacement
    so this gate works even if the verdict has been wrapped or
    extended by callers.
    """
    setattr(
        fn_verdict, "assert_narrowing_dependent",
        bool(dependence_sources),
    )
    setattr(
        fn_verdict, "assert_dependent_sources",
        list(dependence_sources),
    )
    if dependence_sources and not allow:
        # Force the verdict to be unsafe — assert-dependent
        # discharges are unsound under -O without an explicit opt-in.
        try:
            from deppy.pipeline.safety_pipeline import TrustLevel
            fn_verdict.trust = TrustLevel.UNTRUSTED
        except Exception:
            pass
        fn_verdict.is_safe = False


def apply_assert_gate_module_level(
    module_verdict, tracker: AssertDependenceTracker, *,
    allow: bool,
) -> None:
    """Aggregate the per-function dependence into the module verdict.

    Mutates ``module_verdict`` to set:

      * ``assert_narrowing_dependent``: True if any function depended.
      * ``assert_dependent_functions``: list of function names.

    When ``allow=False`` the module-level ``is_safe`` is forced
    False if any function was downgraded.  We re-derive ``is_safe``
    from the per-function flags rather than overwriting it, so
    independent reasons for unsafety (e.g. unaddressed sources)
    aren't masked.
    """
    setattr(
        module_verdict, "assert_narrowing_dependent",
        tracker.any_dependent(),
    )
    setattr(
        module_verdict, "assert_dependent_functions",
        tracker.dependent_functions,
    )
    if not allow and tracker.any_dependent():
        # Re-derive: module is_safe = all functions safe.
        try:
            module_verdict.is_safe = all(
                getattr(fv, "is_safe", False)
                for fv in module_verdict.functions.values()
            )
        except Exception:
            pass


# ─────────────────────────────────────────────────────────────────────
#  Helper for callers to render a friendly warning note
# ─────────────────────────────────────────────────────────────────────


def render_dependence_note(
    tracker: AssertDependenceTracker, *, allow: bool,
) -> Optional[str]:
    """Return a one-line summary string for inclusion in
    ``SafetyVerdict.notes``, or ``None`` if no dependence was
    recorded."""
    fns = tracker.dependent_functions
    if not fns:
        return None
    sample_fn = fns[0]
    sources = tracker.dependent_sources(sample_fn)
    fns_str = ", ".join(fns)
    if allow:
        prefix = "WARN: assert-narrowing dependence permitted by caller"
        body = (
            f" — {fns_str} would be unsound under `python -O`. "
            f"Caller opted in via allow_assert_narrowing=True."
        )
    else:
        prefix = "ERROR: verdict downgraded due to assert-narrowing dependence"
        body = (
            f" — {fns_str} relied on `assert P` for path narrowing. "
            f"asserts are stripped under `python -O`, so the discharge "
            f"would silently no-op.  Replace with `if not P: raise "
            f"AssertionError(...)` for PYTHONOPTIMIZE-safe verification, "
            f"or pass allow_assert_narrowing=True to opt in."
        )
    detail = ""
    if sources:
        detail = f"  First-affected sources in `{sample_fn}`: {sources[:3]}"
        if len(sources) > 3:
            detail += f" (+{len(sources) - 3} more)"
    return prefix + body + ("\n" + detail if detail else "")


__all__ = [
    "AssertDependenceTracker",
    "apply_assert_dependence_gate",
    "apply_assert_gate_module_level",
    "collect_assert_dependences",
    "discharge_depends_on_assert",
    "render_dependence_note",
]
