from __future__ import annotations

from dataclasses import replace
from typing import Any, Dict, Optional, Sequence

from deppy.render.proof_carrying import DescentCertificate
from deppy.proof_decorators.models import DecoratedProofArtifact, InvariantCheckResult
from deppy.solver.proof_certificate import ProofCertificate, verify_certificate


def artifact_from_solver_result(certificate: Optional[ProofCertificate]) -> Optional[Dict[str, Any]]:
    if certificate is None:
        return None
    return {
        "certificate_type": certificate.certificate_type.value,
        "formula": certificate.formula,
        "trust_level": certificate.trust_level.value,
        "certificate_hash": certificate.certificate_hash,
        "is_complete": certificate.is_complete,
        "is_structurally_valid": verify_certificate(certificate),
        "step_count": certificate.step_count,
        "unsat_core": list(certificate.unsat_core),
    }


def build_decorator_artifact(
    artifact: DecoratedProofArtifact,
    *,
    checks: Optional[Sequence[InvariantCheckResult]] = None,
    warnings: Optional[Sequence[str]] = None,
    status: Optional[str] = None,
    from_cache: Optional[bool] = None,
    descent_certificate: Optional[DescentCertificate] = None,
) -> DecoratedProofArtifact:
    return replace(
        artifact,
        checks=tuple(checks) if checks is not None else artifact.checks,
        warnings=tuple(warnings) if warnings is not None else artifact.warnings,
        status=status or artifact.status,
        from_cache=artifact.from_cache if from_cache is None else from_cache,
        descent_certificate=(
            _descent_dict(descent_certificate)
            if descent_certificate is not None
            else artifact.descent_certificate
        ),
    )


def _descent_dict(certificate: DescentCertificate) -> Dict[str, Any]:
    return {
        "function_name": certificate.function_name,
        "spec_name": certificate.spec_name,
        "verdict": certificate.verdict,
        "certificate_hash": certificate.certificate_hash,
    }
