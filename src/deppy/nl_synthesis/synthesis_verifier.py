
from __future__ import annotations

from deppy.solver import SolverStatus, quick_check

from .models import NLConstraint, VerificationSummary


def verify_synthesized_constraints(constraints: tuple[NLConstraint, ...]) -> tuple[VerificationSummary, ...]:
    verdicts = []
    for constraint in constraints:
        if constraint.predicate is None:
            verdicts.append(VerificationSummary(True, 'metadata-only constraint', 'skipped'))
            continue
        result = quick_check(constraint.predicate, timeout_ms=500)
        verdicts.append(
            VerificationSummary(
                verified=result.status in {SolverStatus.SAT, SolverStatus.UNSAT},
                reason=result.explanation or result.status.value,
                solver_status=result.status.value,
            )
        )
    return tuple(verdicts)
