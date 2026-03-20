from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Optional, Tuple

from deppy.core._protocols import TrustLevel


class NLSynthesisError(Exception):
    """Base error for the NL synthesis package."""


class NLSynthesisConfigurationError(NLSynthesisError):
    """Raised when the caller provides an invalid NL synthesis configuration."""


@dataclass(frozen=True)
class DocstringFragment:
    """A normalized constraint-bearing fragment extracted from a docstring."""

    text: str
    normalized_text: str
    kind: str
    target: Optional[str] = None
    section: str = ""
    style: str = "plain"
    line_number: Optional[int] = None
    warnings: Tuple[str, ...] = ()

    def to_dict(self) -> Dict[str, Any]:
        return {
            "text": self.text,
            "normalized_text": self.normalized_text,
            "kind": self.kind,
            "target": self.target,
            "section": self.section,
            "style": self.style,
            "line_number": self.line_number,
            "warnings": list(self.warnings),
        }


@dataclass(frozen=True)
class SynthesisEvidence:
    """Evidence gathered while lowering and checking one synthesized constraint."""

    template_name: str
    normalized_clause: str
    solver_status: str = "not_run"
    explanation: str = ""
    proof_certificate_hash: str = ""
    warnings: Tuple[str, ...] = ()

    def to_dict(self) -> Dict[str, Any]:
        return {
            "template_name": self.template_name,
            "normalized_clause": self.normalized_clause,
            "solver_status": self.solver_status,
            "explanation": self.explanation,
            "proof_certificate_hash": self.proof_certificate_hash,
            "warnings": list(self.warnings),
        }


@dataclass(frozen=True)
class SynthesizedConstraint:
    """A structured constraint synthesized from docstring text."""

    kind: str
    target: Optional[str]
    description: str
    predicate_text: str
    template_name: str
    verification_status: str
    dependencies: Tuple[str, ...] = ()
    trust: TrustLevel = TrustLevel.BOUNDED_AUTO
    warnings: Tuple[str, ...] = ()
    evidence: SynthesisEvidence = field(
        default_factory=lambda: SynthesisEvidence(
            template_name="unmatched",
            normalized_clause="",
        )
    )
    predicate: Optional[Any] = field(default=None, compare=False, repr=False)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": self.kind,
            "target": self.target,
            "description": self.description,
            "predicate_text": self.predicate_text,
            "template_name": self.template_name,
            "verification_status": self.verification_status,
            "dependencies": list(self.dependencies),
            "trust": self.trust.value,
            "warnings": list(self.warnings),
            "evidence": self.evidence.to_dict(),
        }


@dataclass(frozen=True)
class DocstringSynthesisConfig:
    """Configuration for deterministic docstring synthesis."""

    timeout_ms: float = 200.0
    accept_unverified: bool = False
    include_sections: Tuple[str, ...] = ("requires", "ensures", "invariant")


@dataclass(frozen=True)
class SynthesizedAnnotationBundle:
    """Collected synthesis results for a docstring or callable."""

    fragments: Tuple[DocstringFragment, ...] = ()
    constraints: Tuple[SynthesizedConstraint, ...] = ()
    warnings: Tuple[str, ...] = ()
    source_name: str = ""

    @property
    def accepted_constraints(self) -> Tuple[SynthesizedConstraint, ...]:
        return tuple(
            constraint
            for constraint in self.constraints
            if constraint.verification_status == "accepted"
        )

    @property
    def abstained_constraints(self) -> Tuple[SynthesizedConstraint, ...]:
        return tuple(
            constraint
            for constraint in self.constraints
            if constraint.verification_status != "accepted"
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "source_name": self.source_name,
            "warnings": list(self.warnings),
            "fragments": [fragment.to_dict() for fragment in self.fragments],
            "constraints": [constraint.to_dict() for constraint in self.constraints],
        }
