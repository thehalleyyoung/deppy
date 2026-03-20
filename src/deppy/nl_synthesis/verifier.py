from __future__ import annotations

from dataclasses import replace
from typing import List, Optional, Sequence, Tuple

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.predicates import And
from deppy.solver import SolverObligation, SolverStatus, generate_certificate, quick_check

from deppy.nl_synthesis.models import (
    DocstringFragment,
    DocstringSynthesisConfig,
    SynthesizedConstraint,
    SynthesisEvidence,
)
from deppy.nl_synthesis.template_registry import TemplateRegistry, default_template_registry


class DocstringConstraintVerifier:
    """Lower fragments to constraints and check consistency with solver APIs."""

    def __init__(
        self,
        *,
        config: Optional[DocstringSynthesisConfig] = None,
        registry: Optional[TemplateRegistry] = None,
    ) -> None:
        self._config = config or DocstringSynthesisConfig()
        self._registry = registry or default_template_registry()

    def synthesize(
        self,
        fragments: Sequence[DocstringFragment],
        params: Sequence[str],
    ) -> Tuple[SynthesizedConstraint, ...]:
        accepted_predicates: List[object] = []
        constraints: List[SynthesizedConstraint] = []
        for fragment in fragments:
            if fragment.kind not in self._config.include_sections:
                continue
            template = self._registry.select(fragment)
            lowered = template.lower(fragment, params)
            if not lowered:
                constraints.append(
                    self._unsupported(fragment, template.name, "No matching template output")
                )
                continue
            for normalized_clause, spec in lowered:
                dependencies = (
                    tuple(sorted(spec.predicate.free_variables()))
                    if getattr(spec, "predicate", None) is not None
                    else ()
                )
                predicate_text = (
                    spec.predicate.pretty()
                    if getattr(spec, "predicate", None) is not None
                    else normalized_clause
                )
                evidence = SynthesisEvidence(
                    template_name=template.name,
                    normalized_clause=normalized_clause,
                )
                constraint = SynthesizedConstraint(
                    kind=fragment.kind,
                    target=fragment.target or ("result" if fragment.kind == "ensures" else None),
                    description=spec.description,
                    predicate_text=predicate_text,
                    template_name=template.name,
                    verification_status="pending",
                    dependencies=dependencies,
                    evidence=evidence,
                    predicate=getattr(spec, "predicate", None),
                )
                verified = self._verify_constraint(constraint, accepted_predicates)
                constraints.append(verified)
                if verified.verification_status == "accepted" and verified.predicate is not None:
                    accepted_predicates.append(verified.predicate)
        return tuple(constraints)

    def _verify_constraint(
        self,
        constraint: SynthesizedConstraint,
        accepted_predicates: Sequence[object],
    ) -> SynthesizedConstraint:
        predicate = constraint.predicate
        if predicate is None:
            return replace(
                constraint,
                verification_status="abstained_unverified",
                warnings=("Constraint could not be lowered to a formal predicate.",),
                evidence=replace(constraint.evidence, warnings=("uninterpreted fragment",)),
            )

        try:
            candidate_result = quick_check(predicate, timeout_ms=self._config.timeout_ms)
        except Exception as exc:  # pragma: no cover - defensive wrapper
            return replace(
                constraint,
                verification_status="abstained_unverified",
                warnings=(f"Solver check failed: {exc}",),
                evidence=replace(constraint.evidence, solver_status="error", explanation=str(exc)),
            )

        if candidate_result.status == SolverStatus.UNSAT:
            cert = generate_certificate(candidate_result, _obligation(predicate, "candidate-unsat"))
            return replace(
                constraint,
                verification_status="abstained_contradictory",
                trust=TrustLevel.RESIDUAL,
                warnings=("Constraint is internally contradictory.",),
                evidence=replace(
                    constraint.evidence,
                    solver_status=candidate_result.status.value,
                    explanation=candidate_result.explanation or "Unsatisfiable candidate constraint",
                    proof_certificate_hash=cert.certificate_hash,
                ),
            )

        if candidate_result.status in {
            SolverStatus.UNKNOWN,
            SolverStatus.TIMEOUT,
            SolverStatus.ERROR,
        }:
            return replace(
                constraint,
                verification_status="abstained_unverified",
                trust=TrustLevel.RESIDUAL,
                warnings=(f"Constraint could not be verified ({candidate_result.status.value}).",),
                evidence=replace(
                    constraint.evidence,
                    solver_status=candidate_result.status.value,
                    explanation=candidate_result.explanation,
                ),
            )

        if accepted_predicates:
            combined = And([*accepted_predicates, predicate])
            combined_result = quick_check(combined, timeout_ms=self._config.timeout_ms)
            if combined_result.status == SolverStatus.UNSAT:
                cert = generate_certificate(combined_result, _obligation(combined, "combined-unsat"))
                return replace(
                    constraint,
                    verification_status="abstained_contradictory",
                    trust=TrustLevel.RESIDUAL,
                    warnings=("Constraint contradicts earlier accepted constraints.",),
                    evidence=replace(
                        constraint.evidence,
                        solver_status=combined_result.status.value,
                        explanation=combined_result.explanation
                        or "Unsatisfiable with prior constraints",
                        proof_certificate_hash=cert.certificate_hash,
                    ),
                )
            if (
                combined_result.status
                in {SolverStatus.UNKNOWN, SolverStatus.TIMEOUT, SolverStatus.ERROR}
                and not self._config.accept_unverified
            ):
                return replace(
                    constraint,
                    verification_status="abstained_unverified",
                    trust=TrustLevel.RESIDUAL,
                    warnings=("Combined constraint set could not be verified.",),
                    evidence=replace(
                        constraint.evidence,
                        solver_status=combined_result.status.value,
                        explanation=combined_result.explanation,
                    ),
                )

        return replace(
            constraint,
            verification_status="accepted",
            trust=TrustLevel.BOUNDED_AUTO,
            evidence=replace(
                constraint.evidence,
                solver_status=candidate_result.status.value,
                explanation=candidate_result.explanation,
            ),
        )

    def _unsupported(
        self,
        fragment: DocstringFragment,
        template_name: str,
        reason: str,
    ) -> SynthesizedConstraint:
        return SynthesizedConstraint(
            kind=fragment.kind,
            target=fragment.target,
            description=fragment.text,
            predicate_text=fragment.normalized_text,
            template_name=template_name,
            verification_status="abstained_unverified",
            trust=TrustLevel.RESIDUAL,
            warnings=(reason,),
            evidence=SynthesisEvidence(
                template_name=template_name,
                normalized_clause=fragment.normalized_text,
                warnings=(reason,),
            ),
        )


def _obligation(predicate: object, name: str) -> SolverObligation:
    return SolverObligation(
        site_id=SiteId(kind=SiteKind.PROOF, name=name),
        formula=predicate,
        trust_level=TrustLevel.BOUNDED_AUTO,
    )


def verify_synthesized_constraints(
    fragments: Sequence[DocstringFragment],
    params: Sequence[str],
    *,
    config: Optional[DocstringSynthesisConfig] = None,
    registry: Optional[TemplateRegistry] = None,
) -> Tuple[SynthesizedConstraint, ...]:
    return DocstringConstraintVerifier(config=config, registry=registry).synthesize(
        fragments,
        params,
    )
