"""
Deppy Pipeline — Abstract Interp → Proof Bridge (Gap 5)

Adapter that converts ``FunctionAbstractTrace`` queries into kernel
``SafetyObligation`` proof terms.  Each query that the abstract
interpreter answers positively becomes a ``SafetyObligation`` whose
inner proof is a ``Structural`` term (since the soundness of the
abstract domain is structural, not Z3-checkable).

This lets safety-relevant facts established by abstract interpretation
flow into the same composition machinery as Z3-discharged facts and
Čech-glued local proofs.

Public API::

    from deppy.pipeline.abstract_evidence import AbstractEvidenceBridge
    bridge = AbstractEvidenceBridge(trace)
    obl = bridge.nonzero_obligation("b", lineno=42)
    if obl is not None:
        # obl.trust is STRUCTURAL_CHAIN by default
        kernel.verify(judgment, obl, ctx)
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from deppy.core.kernel import (
    SafetyObligation,
    Structural,
    TrustLevel,
)
from deppy.pipeline.abstract_interp import FunctionAbstractTrace


@dataclass
class AbstractEvidenceBridge:
    """Convert abstract-interpretation queries into proof obligations.

    The caller selects which property to prove at which program point;
    on success, a ``SafetyObligation`` carrying a ``Structural`` proof
    is returned.  The bridge does *not* fabricate facts — it only
    forwards positive answers from the underlying trace.
    """

    trace: FunctionAbstractTrace
    function_qualname: str = ""

    # ── individual queries ─────────────────────────────────────────

    def nonzero_obligation(self, var: str, lineno: int) -> Optional[SafetyObligation]:
        """Obligation: ``var != 0`` at ``lineno`` (for division safety)."""
        if not self.trace.can_prove_nonzero_at(var, lineno):
            return None
        return self._build(
            kind="nonzero",
            var=var,
            cond=f"{var} != 0",
            lineno=lineno,
            failure_kind="ZeroDivisionError",
        )

    def nonneg_obligation(self, var: str, lineno: int) -> Optional[SafetyObligation]:
        """Obligation: ``var >= 0`` at ``lineno`` (sqrt, log, etc.)."""
        if not self.trace.can_prove_nonneg_at(var, lineno):
            return None
        return self._build(
            kind="nonneg",
            var=var,
            cond=f"{var} >= 0",
            lineno=lineno,
            failure_kind="ValueError",
        )

    def nonnull_obligation(self, var: str, lineno: int) -> Optional[SafetyObligation]:
        """Obligation: ``var is not None`` at ``lineno`` (attribute access)."""
        if not self.trace.can_prove_nonnull_at(var, lineno):
            return None
        return self._build(
            kind="nonnull",
            var=var,
            cond=f"{var} is not None",
            lineno=lineno,
            failure_kind="AttributeError",
        )

    def nonempty_obligation(self, var: str, lineno: int) -> Optional[SafetyObligation]:
        """Obligation: ``len(var) > 0`` at ``lineno`` (pop, [0], etc.)."""
        if not self.trace.can_prove_nonempty_at(var, lineno):
            return None
        return self._build(
            kind="nonempty",
            var=var,
            cond=f"len({var}) > 0",
            lineno=lineno,
            failure_kind="IndexError",
        )

    def in_bounds_obligation(self, collection: str, index: str,
                             lineno: int) -> Optional[SafetyObligation]:
        """Obligation: ``0 <= index < len(collection)`` at ``lineno``."""
        if not self.trace.can_prove_in_bounds_at(collection, index, lineno):
            return None
        return self._build(
            kind="in_bounds",
            var=f"{collection}[{index}]",
            cond=f"0 <= {index} < len({collection})",
            lineno=lineno,
            failure_kind="IndexError",
        )

    # ── batch helper ───────────────────────────────────────────────

    def collect_evidence(self, queries: list[tuple[str, ...]]) -> list[SafetyObligation]:
        """Run a batch of queries; return successfully-discharged obligations.

        Each query is a tuple ``(kind, *args, lineno)``::

            ("nonzero", "b", 42)
            ("in_bounds", "xs", "i", 17)
        """
        out: list[SafetyObligation] = []
        for q in queries:
            kind = q[0]
            lineno = int(q[-1])
            args = q[1:-1]
            obl = None
            if kind == "nonzero" and len(args) == 1:
                obl = self.nonzero_obligation(args[0], lineno)
            elif kind == "nonneg" and len(args) == 1:
                obl = self.nonneg_obligation(args[0], lineno)
            elif kind == "nonnull" and len(args) == 1:
                obl = self.nonnull_obligation(args[0], lineno)
            elif kind == "nonempty" and len(args) == 1:
                obl = self.nonempty_obligation(args[0], lineno)
            elif kind == "in_bounds" and len(args) == 2:
                obl = self.in_bounds_obligation(args[0], args[1], lineno)
            if obl is not None:
                out.append(obl)
        return out

    # ── internal ───────────────────────────────────────────────────

    def _build(self, *, kind: str, var: str, cond: str,
               lineno: int, failure_kind: str) -> SafetyObligation:
        qual = self.function_qualname or self.trace.function_name or "<anon>"
        oid = f"{qual}:L{lineno}:{kind}:{var}"
        proof = Structural(
            description=(
                f"abstract-interp: {cond} provable at L{lineno} "
                f"(domain evidence)"
            )
        )
        return SafetyObligation(
            obligation_id=oid,
            safety_condition=cond,
            proof=proof,
            failure_kind=failure_kind,
            lineno=lineno,
        )


__all__ = ["AbstractEvidenceBridge"]
