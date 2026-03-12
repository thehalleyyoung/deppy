"""Core protocols for the sheaf-descent semantic typing system.

Every package in DepPy imports from these protocols. They define the
observation site category S, semantic presheaf Sem: S^op -> Poset,
boundary sections, descent data, cohomology, obstructions, and frontiers.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import (
    Any, Dict, FrozenSet, Iterable, List, Mapping, Optional,
    Protocol, Sequence, Set, Tuple, TypeVar, Union, runtime_checkable,
)


class TrustLevel(enum.Enum):
    """How a local section coordinate was established."""
    TRUSTED_AUTO = "trusted_auto"
    BOUNDED_AUTO = "bounded_auto"
    PROOF_BACKED = "proof_backed"
    TRACE_BACKED = "trace_backed"
    RESIDUAL = "residual"
    ASSUMED = "assumed"


class SiteKind(enum.Enum):
    """The 14 site families from the site-family catalogue."""
    ARGUMENT_BOUNDARY = "argument_boundary"
    RETURN_OUTPUT_BOUNDARY = "return_output_boundary"
    SSA_VALUE = "ssa_value"
    BRANCH_GUARD = "branch_guard"
    CALL_RESULT = "call_result"
    TENSOR_SHAPE = "tensor_shape"
    TENSOR_ORDER = "tensor_order"
    TENSOR_INDEXING = "tensor_indexing"
    HEAP_PROTOCOL = "heap_protocol"
    PROOF = "proof"
    TRACE = "trace"
    ERROR = "error"
    LOOP_HEADER_INVARIANT = "loop_header_invariant"
    MODULE_SUMMARY = "module_summary"


@dataclass(frozen=True)
class SiteId:
    """Unique identifier for an observation site."""
    kind: SiteKind
    name: str
    source_location: Optional[Tuple[str, int, int]] = None

    def __str__(self) -> str:
        return f"{self.kind.value}:{self.name}"


@runtime_checkable
class Site(Protocol):
    """An object in the observation site category S."""
    @property
    def site_id(self) -> SiteId: ...
    @property
    def kind(self) -> SiteKind: ...
    @property
    def carrier_schema(self) -> Any: ...


@runtime_checkable
class Morphism(Protocol):
    """A morphism in S -- restriction or reindexing map."""
    @property
    def source(self) -> SiteId: ...
    @property
    def target(self) -> SiteId: ...
    def restrict(self, section: "LocalSection") -> "LocalSection": ...


@dataclass
class Cover:
    """A cover {u_i -> s} in the Grothendieck topology.
    The durable artifact emitted by Stage 1 (Cover synthesis).
    """
    sites: Dict[SiteId, Site] = field(default_factory=dict)
    morphisms: List[Morphism] = field(default_factory=list)
    overlaps: List[Tuple[SiteId, SiteId]] = field(default_factory=list)
    error_sites: Set[SiteId] = field(default_factory=set)
    input_boundary: Set[SiteId] = field(default_factory=set)
    output_boundary: Set[SiteId] = field(default_factory=set)

    def site_ids(self) -> FrozenSet[SiteId]:
        return frozenset(self.sites.keys())


@runtime_checkable
class GrothendieckTopology(Protocol):
    """Axioms: identity, stability under pullback, transitivity."""
    def covers(self, site: SiteId) -> Iterable[Cover]: ...
    def is_cover(self, candidate: Cover, site: SiteId) -> bool: ...


@dataclass
class LocalSection:
    """A section of the semantic presheaf at a single site.
    Contains carrier type, refinements, provenance, trust, witnesses.
    """
    site_id: SiteId
    carrier_type: Any = None
    refinements: Dict[str, Any] = field(default_factory=dict)
    trust: TrustLevel = TrustLevel.RESIDUAL
    provenance: Optional[str] = None
    witnesses: Dict[str, Any] = field(default_factory=dict)

    def __repr__(self) -> str:
        return f"LocalSection({self.site_id}, trust={self.trust.value})"


@dataclass
class BoundarySection:
    """Section restricted to a boundary (input or output)."""
    boundary_sites: Dict[SiteId, LocalSection] = field(default_factory=dict)
    is_input: bool = True

    @property
    def site_ids(self) -> FrozenSet[SiteId]:
        return frozenset(self.boundary_sites.keys())


@dataclass
class GlobalSection:
    """A compatible family of local sections satisfying the sheaf condition.
    H^0(U, T) = ker(delta^0) -- global sections are valid type assignments.
    """
    local_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    input_section: Optional[BoundarySection] = None
    output_section: Optional[BoundarySection] = None

    def at(self, site_id: SiteId) -> Optional[LocalSection]:
        return self.local_sections.get(site_id)


@runtime_checkable
class SemanticPresheaf(Protocol):
    """Functor Sem: S^op -> Poset."""
    def sections_at(self, site: SiteId) -> Iterable[LocalSection]: ...
    def restrict(self, section: LocalSection, morphism: Morphism) -> LocalSection: ...


@dataclass
class DescentDatum:
    """Descent datum ({sigma_i}, {phi_ij}) with cocycle condition."""
    sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    transition_isos: Dict[Tuple[SiteId, SiteId], Any] = field(default_factory=dict)

    def cocycle_condition_holds(self) -> bool:
        return True  # Implemented in core/descent.py


@dataclass
class CechCochainData:
    """Raw data for a Cech n-cochain."""
    degree: int
    values: Dict[Tuple[SiteId, ...], Any] = field(default_factory=dict)


@dataclass
class CohomologyClass:
    """Element of H^n(U, T). H^0=global sections, H^1=type errors, H^2=higher."""
    degree: int
    representative: CechCochainData
    is_trivial: bool = False


@dataclass
class ObstructionData:
    """Obstruction class [alpha] in H^1(U, T). Represents a type error."""
    cohomology_class: Optional[CohomologyClass] = None
    conflicting_overlaps: List[Tuple[SiteId, SiteId]] = field(default_factory=list)
    explanation: str = ""

    @property
    def is_trivial(self) -> bool:
        return len(self.conflicting_overlaps) == 0


@dataclass
class RepairSuggestion:
    """Repair beta in C^0 such that alpha\' = alpha - delta*beta has smaller support."""
    sites_to_adjust: Dict[SiteId, Any] = field(default_factory=dict)
    obstructions_resolved: int = 0
    locality_score: float = 0.0
    plausibility_score: float = 0.0


@dataclass
class FrontierPoint:
    """A point on the Pareto frontier. Lexicographic objective:
    1. min residual errors, 2. min input cost, 3. max output info,
    4. max local coverage, 5. min proof debt, 6. min explanation complexity.
    """
    input_section: BoundarySection
    output_section: BoundarySection
    global_section: GlobalSection
    residual_errors: Set[SiteId] = field(default_factory=set)
    proof_debt: int = 0
    information_score: float = 0.0


@dataclass
class FrontierSummary:
    """Collection of frontier points representing the analysis result."""
    points: List[FrontierPoint] = field(default_factory=list)
    obstructions: List[ObstructionData] = field(default_factory=list)
    repairs: List[RepairSuggestion] = field(default_factory=list)


@runtime_checkable
class InformationOrder(Protocol):
    """Partial order on sections by information content."""
    def leq(self, a: LocalSection, b: LocalSection) -> bool: ...
    def join(self, a: LocalSection, b: LocalSection) -> LocalSection: ...
    def meet(self, a: LocalSection, b: LocalSection) -> LocalSection: ...


@dataclass
class BidirectionalResult:
    """Result of the bidirectional refinement problem."""
    input_section: BoundarySection
    output_section: BoundarySection
    global_section: GlobalSection
    obstructions: List[ObstructionData] = field(default_factory=list)
    error_viability: Dict[SiteId, bool] = field(default_factory=dict)
    converged: bool = False


# ═══════════════════════════════════════════════════════════════════════════════
# Phase 4 protocols: cover synthesis, error registry, provenance
# ═══════════════════════════════════════════════════════════════════════════════


@runtime_checkable
class SiteCoverProtocol(Protocol):
    """Protocol for cover synthesis from source or AST.

    Implementors take a function's AST or source string and produce a
    complete Cover with all 14 site families populated.
    """

    def synthesize(self, source_or_ast: Any) -> Cover:
        """Synthesize a Cover from source code or AST node."""
        ...


@runtime_checkable
class ErrorRegistryProtocol(Protocol):
    """Protocol for error-site registries.

    Implementors maintain a mapping from error types to viability predicates
    and provide lookup by site-id and operation kind.
    """

    def get_viability(self, site_id: SiteId) -> str:
        """Get the viability description for an error site."""
        ...

    def get_error_sites_for_operation(self, op_kind: Any) -> List[SiteId]:
        """Get error sites triggered by a given operation kind."""
        ...

    def is_registered(self, site_id: SiteId) -> bool:
        """Check whether a site is registered as an error site."""
        ...


@runtime_checkable
class ProvenanceProtocol(Protocol):
    """Protocol for provenance tracking during cover synthesis.

    Implementors record how sites were created and provide lookup
    from site-id to provenance records and from AST nodes to sites.
    """

    def record_site_creation(
        self, site_id: SiteId, source_node: Any, reason: Any,
        description: str = "", **kwargs: Any,
    ) -> Any:
        """Record the creation of a site."""
        ...

    def get_provenance(self, site_id: SiteId) -> Any:
        """Look up the provenance record for a site."""
        ...

    def get_sites_from_node(self, ast_node: Any) -> List[SiteId]:
        """Get all sites created from a given AST node."""
        ...


@runtime_checkable
class OverlapProtocol(Protocol):
    """Protocol for overlap computation between sites.

    Implementors analyze site structure and morphisms to produce
    overlap edges.
    """

    def build_overlaps(
        self, sites: Mapping[SiteId, Any], morphisms: Sequence[Any],
    ) -> List[Tuple[SiteId, SiteId]]:
        """Compute overlap pairs from sites and morphisms."""
        ...


@runtime_checkable
class BoundarySynthesisProtocol(Protocol):
    """Protocol for boundary site synthesis.

    Implementors identify input boundary (parameters) and output boundary
    (return/raise/yield) from a function AST.
    """

    def synthesize_input_boundary(self, func_ast: Any) -> Set[SiteId]:
        """Synthesize input boundary SiteIds."""
        ...

    def synthesize_output_boundary(self, func_ast: Any) -> Set[SiteId]:
        """Synthesize output boundary SiteIds."""
        ...
