"""Run deppy's counterexample finder over sidecar foundations.

For each foundation that ``sidecar_foundation_discharge`` could not
verify via Z3, the finder *negates* the property and asks Z3 for a
satisfying model — a concrete counterexample.  When one is found
the foundation is *false* and the certificate must reject it.
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class CounterexampleOutcome:
    foundation: str
    found: bool = False
    inputs: dict = field(default_factory=dict)
    explanation: str = ""


@dataclass
class CounterexampleReport:
    outcomes: list[CounterexampleOutcome] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.outcomes)

    @property
    def counterexamples_found(self) -> int:
        return sum(1 for o in self.outcomes if o.found)


def run_counterexample_search(
    sidecar_module,
    foundation_discharge_report,
) -> CounterexampleReport:
    """For every foundation that didn't verify via Z3, search for
    a counterexample.  When found, the foundation is provably false
    (against Z3's model) and should not be admitted.
    """
    if sidecar_module is None or foundation_discharge_report is None:
        return CounterexampleReport()

    try:
        from deppy.pipeline.counterexample import CounterexampleFinder
        from deppy.core.types import (
            Context, Judgment, JudgmentKind, Var, PyObjType,
            RefinementType, PyBoolType,
        )
    except ImportError:
        return CounterexampleReport()

    finder = CounterexampleFinder()
    outcomes: list[CounterexampleOutcome] = []

    for d in foundation_discharge_report.discharges:
        # Only chase foundations Z3 attempted but couldn't verify.
        if not d.z3_attempted or d.z3_verified:
            continue
        ctx = Context()
        # Build a refinement-typed Judgment whose predicate is the
        # foundation's formula — that's what CounterexampleFinder
        # expects to extract.
        try:
            goal = Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=Var("foundation_check"),
                type_=RefinementType(
                    base_type=PyBoolType(),
                    predicate=d.z3_formula or d.statement,
                ),
            )
            result = finder.find(goal, timeout_ms=2000)
            outcomes.append(CounterexampleOutcome(
                foundation=d.name,
                found=result.found,
                inputs=dict(getattr(result, "inputs", {}) or {}),
                explanation=result.explanation or "",
            ))
        except Exception as e:
            outcomes.append(CounterexampleOutcome(
                foundation=d.name,
                found=False,
                explanation=f"finder error: {e}",
            ))
    return CounterexampleReport(outcomes=outcomes)


__all__ = ["CounterexampleOutcome", "CounterexampleReport", "run_counterexample_search"]
