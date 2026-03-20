from __future__ import annotations

import enum
from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple


class ProofDecoratorError(Exception):
    """Base error for proof decorators."""


class ProofDecoratorConfigurationError(ProofDecoratorError):
    """Raised when a decorator invariant cannot be compiled."""


class VerificationError(ProofDecoratorError):
    """Raised when strict proof checking rejects a runtime call."""


class ProofEmbeddingMode(enum.Enum):
    ANNOTATIONS = "annotations"


@dataclass(frozen=True)
class DecoratorProofConfig:
    timeout_ms: float = 200.0
    strict: bool = False
    eager: bool = True
    cache_by_source_hash: bool = True
    embedding_mode: ProofEmbeddingMode = ProofEmbeddingMode.ANNOTATIONS

    def to_dict(self) -> Dict[str, Any]:
        return {
            "timeout_ms": self.timeout_ms,
            "strict": self.strict,
            "eager": self.eager,
            "cache_by_source_hash": self.cache_by_source_hash,
            "embedding_mode": self.embedding_mode.value,
        }


@dataclass(frozen=True)
class InvariantCheckResult:
    phase: str
    source: str
    status: str
    predicate_text: str = ""
    detail: str = ""
    elapsed_ms: float = 0.0
    proof_certificate: Optional[Dict[str, Any]] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "phase": self.phase,
            "source": self.source,
            "status": self.status,
            "predicate_text": self.predicate_text,
            "detail": self.detail,
            "elapsed_ms": self.elapsed_ms,
            "proof_certificate": self.proof_certificate,
        }


@dataclass(frozen=True)
class DecoratedProofArtifact:
    function_name: str
    source_hash: str
    status: str
    config: DecoratorProofConfig
    invariants: Tuple[str, ...] = ()
    checks: Tuple[InvariantCheckResult, ...] = ()
    warnings: Tuple[str, ...] = ()
    from_cache: bool = False
    descent_certificate: Optional[Dict[str, Any]] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "function_name": self.function_name,
            "source_hash": self.source_hash,
            "status": self.status,
            "config": self.config.to_dict(),
            "invariants": list(self.invariants),
            "checks": [check.to_dict() for check in self.checks],
            "warnings": list(self.warnings),
            "from_cache": self.from_cache,
            "descent_certificate": self.descent_certificate,
        }
