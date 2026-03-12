"""Kernel protocols: solver interface, proof boundary, forcing, topos semantics."""

from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Protocol, Set, Tuple, runtime_checkable

from deppy.core._protocols import (
    LocalSection, SiteId, TrustLevel, ObstructionData,
)


class VerificationStatus(enum.Enum):
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"
    TIMEOUT = "timeout"


@dataclass
class Obligation:
    """A verification obligation to be discharged by a solver or prover."""
    proposition: Any
    site_id: SiteId
    context: Dict[str, Any] = field(default_factory=dict)
    source_location: Optional[Tuple[str, int, int]] = None
    trust_required: TrustLevel = TrustLevel.TRUSTED_AUTO


@dataclass
class VerificationResult:
    """Result of checking an obligation."""
    status: VerificationStatus
    obligation: Obligation
    model: Optional[Dict[str, Any]] = None
    unsat_core: Optional[List[Any]] = None
    proof_term: Optional[Any] = None
    elapsed_ms: float = 0.0


@runtime_checkable
class SolverInterface(Protocol):
    """Abstract solver backend."""
    def check(self, obligation: Obligation) -> VerificationResult: ...
    def push(self) -> None: ...
    def pop(self) -> None: ...


class ProofBoundaryClassification(enum.Enum):
    """How a section coordinate crosses the proof boundary."""
    TRUSTED_AUTO = "trusted_auto"
    BOUNDED_AUTO = "bounded_auto"
    RESIDUAL = "residual"


class TheoryId(enum.Enum):
    """SMT theory fragments for decidable kernels."""
    QF_LIA = "QF_LIA"
    QF_LRA = "QF_LRA"
    QF_BV = "QF_BV"
    QF_AX = "QF_AX"
    QF_UF = "QF_UF"
    COMBINED = "combined"


@runtime_checkable
class ForcingRelation(Protocol):
    """s forces phi (s ||- phi) in the internal logic of the type topos."""
    def forces(self, site: SiteId, proposition: Any) -> bool: ...


@runtime_checkable
class SubobjectClassifier(Protocol):
    """Omega(s) = sieves on s. Propositions are local truth values."""
    def classify(self, site: SiteId, predicate: Any) -> Any: ...
    def sieve_at(self, site: SiteId) -> Set[SiteId]: ...


@runtime_checkable
class VerificationBackend(Protocol):
    """Backend for proof verification (Z3, Lean4, Coq, Dafny)."""
    def verify(self, obligation: Obligation) -> VerificationResult: ...
    def supported_theories(self) -> Set[TheoryId]: ...
