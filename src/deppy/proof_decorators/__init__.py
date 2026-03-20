from __future__ import annotations

from deppy.proof_decorators.certificate_bridge import artifact_from_solver_result, build_decorator_artifact
from deppy.proof_decorators.decorator import prove
from deppy.proof_decorators.invariant_compiler import CompiledInvariant, compile_invariant
from deppy.proof_decorators.models import (
    DecoratedProofArtifact,
    DecoratorProofConfig,
    InvariantCheckResult,
    ProofDecoratorConfigurationError,
    ProofEmbeddingMode,
    VerificationError,
)

__all__ = [
    "CompiledInvariant",
    "DecoratedProofArtifact",
    "DecoratorProofConfig",
    "InvariantCheckResult",
    "ProofDecoratorConfigurationError",
    "ProofEmbeddingMode",
    "VerificationError",
    "artifact_from_solver_result",
    "build_decorator_artifact",
    "compile_invariant",
    "prove",
]
