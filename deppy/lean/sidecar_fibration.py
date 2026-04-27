"""Run deppy's :class:`FibrationVerifier` on linked sidecar methods
whose body branches on ``isinstance``.

This module connects sidecar code-proofs to deppy's existing
fibration-descent infrastructure (``deppy.core.path_engine``).  For
each linked method whose source has the type-dispatch shape
``if isinstance(x, T): ... else: ...``, we:

  1. Call :meth:`FibrationVerifier.extract_fibration` on the
     dedented source text — this is the existing extractor that
     finds isinstance branches and returns a
     :class:`FibrationData` with one :class:`FiberData` per branch.

  2. For each axiom whose claim is a *predicate* over the method
     (``method(...) ≥ 0``, ``contains(...)``, ``is_collinear(...)``
     etc.), call :meth:`FibrationVerifier.verify_per_fiber` with
     the predicate as the fibre's spec.  The kernel then checks one
     :class:`Judgment` per fibre and returns a
     :class:`FibrationResult`.

The fibration result tells us — per type fibre — whether the spec
holds.  When all fibres pass, the function-level claim is verified
*by descent* (this is exactly the deppy view: a function dispatching
on isinstance is a fibration; verification over fibres lifts to a
proof on the total space).

Honest acknowledgement: ``FibrationVerifier.verify_per_fiber``
internally constructs a ``_PathProof`` (from ``path_engine``) for
each fibre — those go through the kernel's path-proof verifiers
and return ``VerificationResult`` per fibre.  The aggregate
``FibrationResult.success`` is True iff every fibre succeeded.  We
record both for transparency.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Optional


@dataclass
class FibrationOutcome:
    """Result of running FibrationVerifier on one (axiom, method) pair."""
    axiom_name: str
    target_qualified: str
    fibre_count: int = 0
    fibres_verified: int = 0
    success: bool = False
    fibre_types: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


@dataclass
class FibrationLinkReport:
    outcomes: list[FibrationOutcome] = field(default_factory=list)

    @property
    def success_count(self) -> int:
        return sum(1 for o in self.outcomes if o.success)

    @property
    def total(self) -> int:
        return len(self.outcomes)


def link_fibration(
    sidecar_module,
    audit_report,
    body_link_report,
    *,
    kernel,
) -> FibrationLinkReport:
    """For every grounded axiom whose target body branches on
    ``isinstance``, run :class:`FibrationVerifier` and record the
    per-fibre verification result.

    ``kernel`` is the same :class:`ProofKernel` already populated
    with the sidecar's foundations by
    :func:`sidecar_code_proof.attempt_all`.
    """
    if sidecar_module is None or body_link_report is None:
        return FibrationLinkReport()

    from deppy.core.path_engine import FibrationVerifier
    from deppy.lean.sidecar_source_audit import AxiomGrounding

    axioms = getattr(sidecar_module, "axioms", {}) or {}
    grounding_by_name = {
        r.name: r.grounding for r in audit_report.results
    }
    by_qualified = body_link_report.by_qualified()
    fv = FibrationVerifier()

    method_call_re = re.compile(
        r"\b([A-Z][A-Za-z0-9_]*)\.([a-z_][A-Za-z0-9_]*)\s*\("
    )

    outcomes: list[FibrationOutcome] = []
    for ax_name, ax in axioms.items():
        if grounding_by_name.get(ax_name) != AxiomGrounding.GROUNDED:
            continue
        statement = getattr(ax, "statement", "") or ""
        m = method_call_re.search(statement)
        if not m:
            continue
        cls, meth = m.group(1), m.group(2)
        target_qualified = f"{cls}_{meth}"
        body_link = by_qualified.get(target_qualified)
        if body_link is None or not body_link.source:
            continue

        try:
            fib = fv.extract_fibration(body_link.source)
        except Exception as e:
            outcomes.append(FibrationOutcome(
                axiom_name=ax_name,
                target_qualified=target_qualified,
                notes=[f"extract_fibration failed: {e}"],
            ))
            continue

        if not fib.fibers:
            # No isinstance dispatch — fibration is trivial; skip.
            continue

        try:
            result = fv.verify_per_fiber(fib, statement, kernel)
        except Exception as e:
            outcomes.append(FibrationOutcome(
                axiom_name=ax_name,
                target_qualified=target_qualified,
                fibre_count=len(fib.fibers),
                fibre_types=[repr(f.type_) for f in fib.fibers],
                notes=[f"verify_per_fiber failed: {e}"],
            ))
            continue

        verified = sum(1 for _, r in result.fiber_results if r.success)
        outcomes.append(FibrationOutcome(
            axiom_name=ax_name,
            target_qualified=target_qualified,
            fibre_count=len(fib.fibers),
            fibres_verified=verified,
            success=result.success,
            fibre_types=[repr(f.type_) for f in fib.fibers],
            notes=[
                f"{verified}/{len(fib.fibers)} fibres verified by kernel",
            ],
        ))

    return FibrationLinkReport(outcomes=outcomes)


__all__ = [
    "FibrationOutcome",
    "FibrationLinkReport",
    "link_fibration",
]
