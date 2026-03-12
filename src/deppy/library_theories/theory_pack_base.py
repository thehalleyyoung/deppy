"""Base class for theory packs in the sheaf-descent semantic typing system.

A theory pack encapsulates the domain-specific logic for one or more site
families. It provides:
  - site constructors: build observation sites from AST nodes
  - local solvers: refine local sections at sites
  - forward refinement: propagate type info along morphisms
  - backward pullback: infer preconditions from error sites
  - viability predicates: determine when error sites are safe
  - proof-boundary classifiers: classify section trust levels

TheoryPackBase is the abstract base from which all 12 theory families derive.
"""

from __future__ import annotations

import copy
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Type,
    Union,
)

from deppy.core._protocols import (
    Cover,
    LocalSection,
    Morphism,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite
from deppy.types.base import TypeBase, ANY_TYPE, NEVER_TYPE, type_join, type_meet


# ═══════════════════════════════════════════════════════════════════════════════
# Solver result
# ═══════════════════════════════════════════════════════════════════════════════


class SolverStatus(Enum):
    """Outcome of a local solve operation."""
    SOLVED = auto()
    REFINED = auto()
    UNCHANGED = auto()
    UNSATISFIABLE = auto()
    UNKNOWN = auto()


@dataclass
class SolverResult:
    """Result returned by a local solver invocation.

    Attributes:
        status: The outcome of the solve.
        section: The refined local section (or original if unchanged).
        constraints_remaining: Constraints that could not be resolved locally.
        explanation: Human-readable explanation of what the solver did.
        trust_upgrade: If the solver upgraded trust, what the new level is.
        proof_obligations: Proof terms the caller must still discharge.
    """
    status: SolverStatus
    section: LocalSection
    constraints_remaining: List[str] = field(default_factory=list)
    explanation: str = ""
    trust_upgrade: Optional[TrustLevel] = None
    proof_obligations: List[str] = field(default_factory=list)

    @property
    def is_success(self) -> bool:
        """True when the solver made progress or solved fully."""
        return self.status in (SolverStatus.SOLVED, SolverStatus.REFINED)

    @property
    def is_failure(self) -> bool:
        """True when the section is unsatisfiable."""
        return self.status == SolverStatus.UNSATISFIABLE

    def with_explanation(self, text: str) -> SolverResult:
        """Return a copy with updated explanation."""
        return SolverResult(
            status=self.status,
            section=self.section,
            constraints_remaining=self.constraints_remaining,
            explanation=text,
            trust_upgrade=self.trust_upgrade,
            proof_obligations=self.proof_obligations,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Proof boundary classification
# ═══════════════════════════════════════════════════════════════════════════════


class BoundaryClassification(Enum):
    """How a section at a boundary is classified for proof purposes."""
    FULLY_PROVEN = "fully_proven"
    CONDITIONALLY_PROVEN = "conditionally_proven"
    ASSUMED = "assumed"
    RUNTIME_GUARDED = "runtime_guarded"
    REQUIRES_PROOF = "requires_proof"
    INCONSISTENT = "inconsistent"


# ═══════════════════════════════════════════════════════════════════════════════
# Section manipulation helpers
# ═══════════════════════════════════════════════════════════════════════════════


def make_section(
    site_id: SiteId,
    carrier_type: Any = None,
    refinements: Optional[Dict[str, Any]] = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
    provenance: Optional[str] = None,
    witnesses: Optional[Dict[str, Any]] = None,
) -> LocalSection:
    """Convenience constructor for LocalSection with defaults."""
    return LocalSection(
        site_id=site_id,
        carrier_type=carrier_type if carrier_type is not None else ANY_TYPE,
        refinements=refinements if refinements is not None else {},
        trust=trust,
        provenance=provenance,
        witnesses=witnesses if witnesses is not None else {},
    )


def merge_refinements(
    base: Dict[str, Any],
    overlay: Dict[str, Any],
    strategy: str = "meet",
) -> Dict[str, Any]:
    """Merge two refinement dictionaries.

    Args:
        base: The existing refinements.
        overlay: The new refinements to merge in.
        strategy: 'meet' takes the intersection/tightest constraints,
                  'join' takes the union/loosest constraints,
                  'override' replaces base values with overlay values.

    Returns:
        A new merged refinements dictionary.
    """
    result = dict(base)
    for key, value in overlay.items():
        if key not in result:
            result[key] = value
            continue
        existing = result[key]
        if strategy == "override":
            result[key] = value
        elif strategy == "meet":
            result[key] = _meet_refinement_value(key, existing, value)
        elif strategy == "join":
            result[key] = _join_refinement_value(key, existing, value)
        else:
            result[key] = value
    return result


def _meet_refinement_value(key: str, a: Any, b: Any) -> Any:
    """Compute the meet (tightest) of two refinement values."""
    if key in ("lower_bound", "min"):
        if isinstance(a, (int, float)) and isinstance(b, (int, float)):
            return max(a, b)
    elif key in ("upper_bound", "max"):
        if isinstance(a, (int, float)) and isinstance(b, (int, float)):
            return min(a, b)
    elif key in ("non_null", "non_empty", "positive", "non_negative"):
        return a or b
    elif key == "length":
        if isinstance(a, (int, float)) and isinstance(b, (int, float)):
            if a == b:
                return a
            return None
    elif key == "dtype":
        if a == b:
            return a
        return None
    elif key == "device":
        if a == b:
            return a
        return None
    elif key == "shape":
        if a == b:
            return a
        return _meet_shapes(a, b)
    if a == b:
        return a
    return a


def _join_refinement_value(key: str, a: Any, b: Any) -> Any:
    """Compute the join (loosest) of two refinement values."""
    if key in ("lower_bound", "min"):
        if isinstance(a, (int, float)) and isinstance(b, (int, float)):
            return min(a, b)
    elif key in ("upper_bound", "max"):
        if isinstance(a, (int, float)) and isinstance(b, (int, float)):
            return max(a, b)
    elif key in ("non_null", "non_empty", "positive", "non_negative"):
        return a and b
    if a == b:
        return a
    return None


def _meet_shapes(a: Any, b: Any) -> Any:
    """Compute the meet of two shape tuples."""
    if not isinstance(a, tuple) or not isinstance(b, tuple):
        return None
    if len(a) != len(b):
        return None
    result = []
    for da, db in zip(a, b):
        if da == db:
            result.append(da)
        elif isinstance(da, str):
            result.append(db)
        elif isinstance(db, str):
            result.append(da)
        else:
            return None
    return tuple(result)


def narrow_section(
    section: LocalSection,
    new_refinements: Dict[str, Any],
    provenance: Optional[str] = None,
    trust: Optional[TrustLevel] = None,
) -> LocalSection:
    """Return a section with additional refinements applied (narrowing)."""
    merged = merge_refinements(section.refinements, new_refinements, strategy="meet")
    return LocalSection(
        site_id=section.site_id,
        carrier_type=section.carrier_type,
        refinements=merged,
        trust=trust if trust is not None else section.trust,
        provenance=provenance if provenance is not None else section.provenance,
        witnesses=dict(section.witnesses),
    )


def widen_section(
    section: LocalSection,
    keys_to_drop: Optional[Set[str]] = None,
    provenance: Optional[str] = None,
) -> LocalSection:
    """Return a section with some refinements dropped (widening)."""
    if keys_to_drop is None:
        new_refs: Dict[str, Any] = {}
    else:
        new_refs = {k: v for k, v in section.refinements.items() if k not in keys_to_drop}
    return LocalSection(
        site_id=section.site_id,
        carrier_type=section.carrier_type,
        refinements=new_refs,
        trust=section.trust,
        provenance=provenance if provenance is not None else section.provenance,
        witnesses=dict(section.witnesses),
    )


def replace_carrier(
    section: LocalSection,
    new_carrier: Any,
    provenance: Optional[str] = None,
) -> LocalSection:
    """Return a section with a different carrier type."""
    return LocalSection(
        site_id=section.site_id,
        carrier_type=new_carrier,
        refinements=dict(section.refinements),
        trust=section.trust,
        provenance=provenance if provenance is not None else section.provenance,
        witnesses=dict(section.witnesses),
    )


def upgrade_trust(
    section: LocalSection,
    new_trust: TrustLevel,
    provenance: Optional[str] = None,
) -> LocalSection:
    """Return a section with upgraded trust level."""
    _trust_order = {
        TrustLevel.ASSUMED: 0,
        TrustLevel.RESIDUAL: 1,
        TrustLevel.TRACE_BACKED: 2,
        TrustLevel.BOUNDED_AUTO: 3,
        TrustLevel.TRUSTED_AUTO: 4,
        TrustLevel.PROOF_BACKED: 5,
    }
    if _trust_order.get(new_trust, 0) <= _trust_order.get(section.trust, 0):
        return section
    return LocalSection(
        site_id=section.site_id,
        carrier_type=section.carrier_type,
        refinements=dict(section.refinements),
        trust=new_trust,
        provenance=provenance if provenance is not None else section.provenance,
        witnesses=dict(section.witnesses),
    )


def section_with_witness(
    section: LocalSection,
    witness_key: str,
    witness_value: Any,
) -> LocalSection:
    """Return a section with a witness entry added."""
    new_witnesses = dict(section.witnesses)
    new_witnesses[witness_key] = witness_value
    return LocalSection(
        site_id=section.site_id,
        carrier_type=section.carrier_type,
        refinements=dict(section.refinements),
        trust=section.trust,
        provenance=section.provenance,
        witnesses=new_witnesses,
    )


def sections_compatible(a: LocalSection, b: LocalSection) -> bool:
    """Check if two sections have compatible refinements on overlapping keys."""
    shared = set(a.refinements.keys()) & set(b.refinements.keys())
    for key in shared:
        va, vb = a.refinements[key], b.refinements[key]
        if va is not None and vb is not None and va != vb:
            if key in ("lower_bound", "min"):
                continue
            if key in ("upper_bound", "max"):
                continue
            return False
    return True


def make_error_site_id(name: str, location: Optional[Tuple[str, int, int]] = None) -> SiteId:
    """Create a SiteId for an error site."""
    return SiteId(kind=SiteKind.ERROR, name=name, source_location=location)


def make_guard_site_id(name: str, location: Optional[Tuple[str, int, int]] = None) -> SiteId:
    """Create a SiteId for a branch guard site."""
    return SiteId(kind=SiteKind.BRANCH_GUARD, name=name, source_location=location)


# ═══════════════════════════════════════════════════════════════════════════════
# TheoryPackBase abstract class
# ═══════════════════════════════════════════════════════════════════════════════


class TheoryPackBase(ABC):
    """Abstract base class for all theory packs.

    Each theory pack is responsible for a set of site kinds and implements
    the six core operations: site construction, local solving, forward
    refinement, backward pullback, viability predicates, and proof-boundary
    classification.

    Subclasses MUST implement all abstract methods and set the `pack_name`
    and `pack_priority` attributes.
    """

    pack_name: str = "base"
    pack_priority: int = 100

    def __init__(self) -> None:
        self._viability_cache: Dict[SiteId, str] = {}
        self._solver_cache: Dict[Tuple[SiteId, int], SolverResult] = {}

    # ── Abstract interface ────────────────────────────────────────────────

    @abstractmethod
    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        """Return the set of site kinds this pack handles."""
        ...

    @abstractmethod
    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        """Run the pack's local solver on a section at the given site.

        The solver may refine the section's carrier type, add refinements,
        upgrade trust, or report unsatisfiability.
        """
        ...

    @abstractmethod
    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Push refinements forward along a morphism.

        Given a section at the morphism's source, produce a refined section
        at the morphism's target. This implements the presheaf restriction
        with domain-specific knowledge.
        """
        ...

    @abstractmethod
    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Pull requirements backward along a morphism.

        Given requirements at the morphism's target (typically an error site
        or output boundary), compute the preconditions needed at the source.
        """
        ...

    @abstractmethod
    def viability_predicate(self, error_site: SiteId) -> str:
        """Return a human-readable viability predicate for an error site.

        The predicate describes the conditions under which the operation
        at this error site is safe (will not raise an exception).
        """
        ...

    @abstractmethod
    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        """Classify a section for proof-boundary purposes.

        Determines whether the section is fully proven, assumed, requires
        further proof, etc.
        """
        ...

    # ── Concrete helpers ──────────────────────────────────────────────────

    def handles_site(self, site_id: SiteId) -> bool:
        """Check whether this pack handles the given site's kind."""
        return site_id.kind in self.applicable_site_kinds()

    def handles_kind(self, kind: SiteKind) -> bool:
        """Check whether this pack handles the given site kind."""
        return kind in self.applicable_site_kinds()

    def solve_with_cache(self, site: SiteId, section: LocalSection) -> SolverResult:
        """Cached version of solve_local."""
        cache_key = (site, id(section))
        if cache_key in self._solver_cache:
            return self._solver_cache[cache_key]
        result = self.solve_local(site, section)
        self._solver_cache[cache_key] = result
        return result

    def clear_cache(self) -> None:
        """Clear internal caches."""
        self._viability_cache.clear()
        self._solver_cache.clear()

    def construct_site(
        self,
        name: str,
        kind: SiteKind,
        carrier_schema: Any = None,
        metadata: Optional[Dict[str, Any]] = None,
        location: Optional[Tuple[str, int, int]] = None,
    ) -> ConcreteSite:
        """Convenience method to build a ConcreteSite."""
        site_id = SiteId(kind=kind, name=name, source_location=location)
        return ConcreteSite(
            _site_id=site_id,
            _carrier_schema=carrier_schema,
            _metadata=metadata,
        )

    def construct_morphism(
        self,
        source: SiteId,
        target: SiteId,
        projection: Optional[Dict[str, str]] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> ConcreteMorphism:
        """Convenience method to build a ConcreteMorphism."""
        return ConcreteMorphism(
            _source=source,
            _target=target,
            projection=projection,
            _metadata=metadata,
        )

    def make_section(
        self,
        site_id: SiteId,
        carrier_type: Any = None,
        refinements: Optional[Dict[str, Any]] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: Optional[str] = None,
    ) -> LocalSection:
        """Convenience wrapper around module-level make_section."""
        return make_section(
            site_id=site_id,
            carrier_type=carrier_type,
            refinements=refinements,
            trust=trust,
            provenance=provenance or f"from {self.pack_name}",
        )

    def identity_forward(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Default forward: just restrict along the morphism."""
        return morphism.restrict(section)

    def identity_backward(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Default backward: project refinements back to source."""
        new_refs: Dict[str, Any] = {}
        if morphism.projection:
            for tgt_key, src_key in morphism.projection.items():
                if tgt_key in section.refinements:
                    new_refs[src_key] = section.refinements[tgt_key]
        else:
            new_refs = dict(section.refinements)
        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=new_refs,
            trust=section.trust,
            provenance=f"pullback from {section.site_id}",
        )

    def make_solver_result(
        self,
        section: LocalSection,
        status: SolverStatus = SolverStatus.SOLVED,
        explanation: str = "",
    ) -> SolverResult:
        """Build a SolverResult with defaults."""
        return SolverResult(
            status=status,
            section=section,
            explanation=explanation or f"solved by {self.pack_name}",
        )

    def check_refinement_consistency(self, section: LocalSection) -> bool:
        """Validate that a section's refinements are internally consistent.

        For example, lower_bound <= upper_bound.
        """
        refs = section.refinements
        lo = refs.get("lower_bound", refs.get("min"))
        hi = refs.get("upper_bound", refs.get("max"))
        if lo is not None and hi is not None:
            if isinstance(lo, (int, float)) and isinstance(hi, (int, float)):
                if lo > hi:
                    return False
        non_neg = refs.get("non_negative", False)
        neg = refs.get("negative", False)
        if non_neg and neg:
            return False
        return True

    def __repr__(self) -> str:
        kinds = ", ".join(k.value for k in self.applicable_site_kinds())
        return f"TheoryPack({self.pack_name}, kinds=[{kinds}])"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, TheoryPackBase):
            return NotImplemented
        return self.pack_name == other.pack_name

    def __hash__(self) -> int:
        return hash(self.pack_name)
