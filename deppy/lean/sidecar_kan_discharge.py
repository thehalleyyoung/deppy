"""Discharge cubical Kan-fill obligations through deppy's kernel.

Per linked sympy method, deppy.pipeline.cubical_ast.build_cubical_set
identifies a cubical structure of the function's control flow.
:func:`deppy.pipeline.cubical_obligations.cubical_set_to_obligations`
turns Kan-fillable cells into kernel-checkable proof terms
(:class:`KanFill`).  This module then runs every obligation through
:meth:`ProofKernel.verify` and reports how many discharged.

The cubical analysis already runs in :mod:`sidecar_cubical_link` —
this module is the *kernel-discharge* step that closes the loop.
Without it, ``cubical_obligations_total`` is reported but
``cubical_obligations_verified`` is always zero.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field


@dataclass
class KanDischargeOutcome:
    method: str                          # qualified Class_method
    cells_total: int = 0
    kan_candidates: int = 0
    obligations_total: int = 0
    obligations_verified: int = 0
    obligations_failed: int = 0
    trust_levels: list[str] = field(default_factory=list)


@dataclass
class KanDischargeReport:
    outcomes: list[KanDischargeOutcome] = field(default_factory=list)

    @property
    def total_obligations(self) -> int:
        return sum(o.obligations_total for o in self.outcomes)

    @property
    def verified_obligations(self) -> int:
        return sum(o.obligations_verified for o in self.outcomes)


def discharge_kan_obligations(body_link_report) -> KanDischargeReport:
    """Run kernel.verify on every Kan-fill obligation derived from
    every linked method's cubical structure."""
    if body_link_report is None or not body_link_report.results:
        return KanDischargeReport()

    from deppy.pipeline.cubical_ast import build_cubical_set
    from deppy.pipeline.cubical_obligations import (
        cubical_set_to_obligations,
    )
    from deppy.core.kernel import ProofKernel
    from deppy.core.types import (
        Context, Judgment, JudgmentKind, Var, PyObjType,
    )

    kernel = ProofKernel()
    outcomes: list[KanDischargeOutcome] = []

    for r in body_link_report.results:
        if r.error or not r.source:
            continue
        try:
            mod = ast.parse(r.source)
        except SyntaxError:
            continue
        fn_node = next(
            (n for n in mod.body
             if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))),
            None,
        )
        if fn_node is None:
            continue

        try:
            cset = build_cubical_set(fn_node)
        except Exception:
            continue

        kan = cset.find_kan_fillable()
        try:
            obligations = cubical_set_to_obligations(cset)
        except Exception:
            obligations = []

        outcome = KanDischargeOutcome(
            method=r.qualified,
            cells_total=sum(len(c) for c in cset.cells_by_dim.values()),
            kan_candidates=len(kan),
            obligations_total=len(obligations),
        )

        for ob in obligations:
            ctx = Context()
            goal = Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=Var(f"kan_{ob.cell_id}"),
                type_=PyObjType(),
            )
            try:
                result = kernel.verify(ctx, goal, ob.proof_term)
                if result.success:
                    outcome.obligations_verified += 1
                    outcome.trust_levels.append(result.trust_level.name)
                else:
                    outcome.obligations_failed += 1
            except Exception:
                outcome.obligations_failed += 1

        outcomes.append(outcome)

    return KanDischargeReport(outcomes=outcomes)


__all__ = [
    "KanDischargeOutcome",
    "KanDischargeReport",
    "discharge_kan_obligations",
]
