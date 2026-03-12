"""Proof protocols: proof terms, obligations, tactics, proof engine."""

from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Protocol, Sequence, runtime_checkable

from deppy.core._protocols import SiteId, LocalSection


class ProofTermKind(enum.Enum):
    """The 15 proof term constructors from Part IV."""
    REFL = "refl"
    SYMM = "symm"
    TRANS = "trans"
    CONG = "cong"
    SUBST = "subst"
    MP = "mp"             # modus ponens
    INTRO = "intro"
    ELIM = "elim"
    AND_INTRO = "and_intro"
    FST = "fst"
    SND = "snd"
    INL = "inl"           # left injection
    INR = "inr"           # right injection
    CASES = "cases"
    ABSURD = "absurd"
    AUTO = "auto"         # solver discharge
    BY_ASSUMPTION = "by_assumption"


@dataclass
class ProofTerm:
    """A proof term constructed from the 15 constructors."""
    kind: ProofTermKind
    children: List["ProofTerm"] = field(default_factory=list)
    payload: Any = None
    proposition: Any = None


class ObligationStatus(enum.Enum):
    """Proof obligation lifecycle stages."""
    GENERATED = "generated"
    SOLVER_ATTEMPTED = "solver_attempted"
    DISCHARGED = "discharged"
    TRIAGED = "triaged"
    PROOF_PROVIDED = "proof_provided"
    VERIFIED = "verified"
    EXPORTED = "exported"
    RESIDUAL = "residual"


@dataclass
class ProofObligation:
    """A proof obligation with lifecycle tracking."""
    prop: Any
    site_id: SiteId
    context: Dict[str, Any] = field(default_factory=dict)
    status: ObligationStatus = ObligationStatus.GENERATED
    proof: Optional[ProofTerm] = None
    source_location: Optional[str] = None


@dataclass
class ProofContext:
    """Scoped proof context with assumptions and known facts."""
    scopes: List[Dict[str, Any]] = field(default_factory=list)

    def push_scope(self, bindings: Optional[Dict[str, Any]] = None) -> None:
        self.scopes.append(bindings or {})

    def pop_scope(self) -> Dict[str, Any]:
        return self.scopes.pop() if self.scopes else {}

    def lookup(self, name: str) -> Optional[Any]:
        for scope in reversed(self.scopes):
            if name in scope:
                return scope[name]
        return None


class AnnotationLevel(enum.Enum):
    """The 6 annotation levels from Part IV."""
    ZERO = 0       # Plain Python, system infers everything
    CONTRACTS = 1  # @requires/@ensures decorators
    INVARIANTS = 2 # Loop/class invariants, checked inductively
    LEMMAS = 3     # Programmer states lemmas, system proves
    SKETCHES = 4   # Intermediate assertions guide solver
    FULL = 5       # Complete Agda-style proofs


@runtime_checkable
class ProofEngine(Protocol):
    """5-pass proof engine: infer -> integrate -> discharge -> enrich -> re_infer."""
    def infer(self, cover: Any) -> List[ProofObligation]: ...
    def integrate(self, obligations: List[ProofObligation]) -> List[ProofObligation]: ...
    def discharge(self, obligations: List[ProofObligation]) -> List[ProofObligation]: ...
    def enrich(self, discharged: List[ProofObligation], cover: Any) -> Any: ...
    def re_infer(self, enriched: Any) -> List[ProofObligation]: ...
