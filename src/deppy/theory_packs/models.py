from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Mapping, Optional, Tuple, TYPE_CHECKING

from deppy.core._protocols import SiteKind

if TYPE_CHECKING:
    from deppy.library_theories.theory_pack_base import TheoryPackBase


@dataclass(frozen=True)
class VerificationCase:
    """Serializable runtime check description for one axiom example."""

    name: str
    operation: str
    payload: Mapping[str, Any] = field(default_factory=dict)
    expected: Mapping[str, Any] = field(default_factory=dict)
    description: str = ""

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("verification case name must be non-empty")
        if not self.operation:
            raise ValueError("verification case operation must be non-empty")
        object.__setattr__(self, "payload", dict(self.payload))
        object.__setattr__(self, "expected", dict(self.expected))


@dataclass(frozen=True)
class AxiomSpec:
    """High-level description of one library-specific semantic axiom."""

    name: str
    library: str
    version_range: str
    site_kinds: Tuple[SiteKind, ...]
    rewrite_rule: Optional[str] = None
    solver_formula: Optional[str] = None
    verification_cases: Tuple[VerificationCase, ...] = ()
    delegate_pack_names: Tuple[str, ...] = ()
    description: str = ""

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("axiom name must be non-empty")
        if not self.library:
            raise ValueError("axiom library must be non-empty")
        if not self.version_range:
            raise ValueError("axiom version_range must be non-empty")
        if not self.site_kinds:
            raise ValueError("axiom must reference at least one site kind")
        object.__setattr__(self, "site_kinds", tuple(self.site_kinds))
        object.__setattr__(self, "verification_cases", tuple(self.verification_cases))
        object.__setattr__(self, "delegate_pack_names", tuple(self.delegate_pack_names))


@dataclass(frozen=True)
class TheoryPackSpec:
    """User-facing pack metadata layered over ``deppy.library_theories``."""

    name: str
    library: str
    version_range: str
    site_kinds: Tuple[SiteKind, ...]
    delegate_pack_names: Tuple[str, ...]
    axioms: Tuple[AxiomSpec, ...]
    description: str = ""

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("pack name must be non-empty")
        if not self.library:
            raise ValueError("pack library must be non-empty")
        if not self.version_range:
            raise ValueError("pack version_range must be non-empty")
        if not self.delegate_pack_names:
            raise ValueError("pack must declare at least one delegate pack")
        object.__setattr__(self, "site_kinds", tuple(self.site_kinds))
        object.__setattr__(self, "delegate_pack_names", tuple(self.delegate_pack_names))
        object.__setattr__(self, "axioms", tuple(self.axioms))

    @property
    def axiom_names(self) -> Tuple[str, ...]:
        return tuple(axiom.name for axiom in self.axioms)


@dataclass(frozen=True)
class AxiomVerificationResult:
    """Runtime verification outcome for one axiom case."""

    axiom_name: str
    case_name: str
    status: str
    message: str = ""

    @property
    def verified(self) -> bool:
        return self.status == "verified"

    @property
    def skipped(self) -> bool:
        return self.status == "skipped"


@dataclass(frozen=True)
class VerificationReport:
    """Summary of runtime verification for a theory-pack spec."""

    pack_name: str
    library: str
    available: bool
    library_version: Optional[str]
    axiom_results: Tuple[AxiomVerificationResult, ...] = ()
    trusted_axioms: Tuple[str, ...] = ()
    warnings: Tuple[str, ...] = ()

    @property
    def verified_count(self) -> int:
        return sum(1 for result in self.axiom_results if result.status == "verified")

    @property
    def failed_count(self) -> int:
        return sum(1 for result in self.axiom_results if result.status == "failed")

    @property
    def skipped_count(self) -> int:
        return sum(1 for result in self.axiom_results if result.status == "skipped")

    @property
    def verification_status(self) -> str:
        if not self.available:
            return "unavailable"
        if self.failed_count:
            return "partial"
        if self.verified_count:
            return "verified"
        return "unverified"


@dataclass(frozen=True)
class PackLoadReport:
    """Result of loading a high-level theory pack facade."""

    spec: TheoryPackSpec
    pack: "TheoryPackBase"
    loaded: bool
    verification: VerificationReport
    warnings: Tuple[str, ...] = ()
