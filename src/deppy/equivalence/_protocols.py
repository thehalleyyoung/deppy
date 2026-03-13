"""Core protocols and data structures for sheaf-theoretic equivalence checking.

Models equivalence of two programs f, g as an isomorphism of their semantic
presheaves Sem_f ≅ Sem_g over a common refinement cover.  Every data
structure here is expressed in terms of the existing sheaf machinery
(LocalSection, Cover, DescentDatum, CohomologyClass) and the refinement
predicate language (Predicate, RefinementType, IdentityType).

Mathematical summary
--------------------
Given programs f, g with semantic presheaves Sem_f, Sem_g : S^op → Poset,
we construct:

1.  A **common refinement cover** U = {U_i} refining both the f-cover and
    the g-cover.
2.  A **fiber-product presheaf** Sem_f ×_S Sem_g whose sections at U_i are
    pairs (σ_f, σ_g) satisfying an equalizer condition encoded as a
    RefinementType predicate.
3.  A **natural transformation** η : Sem_f ⇒ Sem_g whose components η_{U_i}
    are verified as type equivalences (mutual subtyping).
4.  **Descent data** for the paired cover, with transition isomorphisms
    that must be equivalences.  Obstructions live in H¹(U, Iso(Sem_f, Sem_g)).

The verdict is ``EQUIVALENT`` when η is a natural isomorphism (H¹ trivial),
``REFINED`` when one direction holds (sub-presheaf), and ``INEQUIVALENT``
when H¹ is nontrivial — with the cohomology class providing a precise
obstruction basis localised to specific sites.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Protocol,
    Sequence,
    Set,
    Tuple,
    Union,
    runtime_checkable,
)

from deppy.core._protocols import (
    BoundarySection,
    CechCochainData,
    CohomologyClass,
    Cover,
    DescentDatum,
    GlobalSection,
    LocalSection,
    Morphism,
    ObstructionData,
    RepairSuggestion,
    SiteId,
    SiteKind,
    TrustLevel,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Equivalence-specific enums
# ═══════════════════════════════════════════════════════════════════════════════


class EquivalenceVerdict(enum.Enum):
    """Outcome of an equivalence check between two programs / sections."""

    EQUIVALENT = "equivalent"
    """Sem_f ≅ Sem_g — full natural isomorphism, H¹ trivial."""

    REFINED = "refined"
    """Sem_f ⊆ Sem_g or Sem_g ⊆ Sem_f — one direction holds."""

    INEQUIVALENT = "inequivalent"
    """H¹ nontrivial — with obstruction basis localising disagreements."""

    UNKNOWN = "unknown"
    """Solver timed out or analysis is incomplete."""


class EquivalenceStrength(enum.Enum):
    """How strong an equivalence claim is."""

    OBSERVATIONAL = "observational"
    """Same observable behaviour on all inputs (∀x. f(x) = g(x))."""

    DENOTATIONAL = "denotational"
    """Same denotation in the semantic domain (presheaf isomorphism)."""

    BISIMULATION = "bisimulation"
    """Bisimulation equivalence (preserves step-by-step structure)."""

    REFINEMENT = "refinement"
    """One-directional: f refines g (Sem_f ⊆ Sem_g)."""

    CONTEXTUAL = "contextual"
    """Equivalent under all program contexts C[·]."""


class EquivalenceSiteKind(enum.Enum):
    """Extended site kinds for paired / fiber-product sites."""

    PAIRED_ARGUMENT = "paired_argument"
    PAIRED_RETURN = "paired_return"
    PAIRED_SSA = "paired_ssa"
    PAIRED_BRANCH = "paired_branch"
    PAIRED_CALL = "paired_call"
    FIBER_PRODUCT = "fiber_product"
    EQUALIZER = "equalizer"
    COMMON_REFINEMENT = "common_refinement"


class MorphismDirection(enum.Enum):
    """Direction of a sheaf morphism component."""

    FORWARD = "forward"    # Sem_f → Sem_g
    BACKWARD = "backward"  # Sem_g → Sem_f


# ═══════════════════════════════════════════════════════════════════════════════
# Section pairs and fiber products
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ProgramId:
    """Identifies one of the two programs being compared."""

    name: str
    source_path: Optional[str] = None
    function_name: Optional[str] = None

    def __str__(self) -> str:
        parts = [self.name]
        if self.function_name:
            parts.append(f"::{self.function_name}")
        return "".join(parts)


@dataclass
class SectionPair:
    """A pair of local sections (σ_f, σ_g) at a common site.

    This is the basic unit of comparison: at each site U_i in the common
    refinement cover, we have one section from each program's presheaf.
    """

    site_id: SiteId
    section_f: LocalSection
    section_g: LocalSection
    agreement_predicate: Optional[Any] = None  # Predicate encoding σ_f ≡ σ_g
    is_compatible: Optional[bool] = None

    @property
    def carrier_types_match(self) -> bool:
        if self.section_f.carrier_type is None or self.section_g.carrier_type is None:
            return True
        return self.section_f.carrier_type == self.section_g.carrier_type


@dataclass
class FiberProductSection:
    """A section of the fiber product presheaf Sem_f ×_S Sem_g at a site.

    The fiber product at U_i is the equalizer:
        (Sem_f ×_S Sem_g)(U_i) = { (σ_f, σ_g) | σ_f and σ_g agree on the
                                     equalizer condition }

    Encoded as a RefinementType {v : τ_f × τ_g | φ_eq(v)} where
    φ_eq asserts the components are equivalent.
    """

    site_id: SiteId
    pair: SectionPair
    equalizer_type: Optional[Any] = None  # RefinementType
    is_inhabited: bool = False
    witness: Optional[Any] = None  # ProofTerm witnessing inhabitance


@dataclass
class SiteCorrespondence:
    """Maps sites between two covers.

    For common refinement construction, we need to know how sites in Cover_f
    relate to sites in Cover_g.  A correspondence is a span:

        Cover_f ← CommonRefinement → Cover_g
    """

    f_site: SiteId
    g_site: SiteId
    common_site: SiteId
    morphism_from_f: Optional[Morphism] = None
    morphism_from_g: Optional[Morphism] = None
    alignment_score: float = 1.0


# ═══════════════════════════════════════════════════════════════════════════════
# Sheaf morphisms and natural transformations
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class SheafMorphismComponent:
    """A single component η_{U_i} : Sem_f(U_i) → Sem_g(U_i).

    Each component is encoded as a pair of verification conditions:
    - forward_vc: ∀x. φ_f(x) ⟹ φ_g(η(x))
    - backward_vc: ∀y. φ_g(y) ⟹ φ_f(η⁻¹(y))  (for isomorphism)

    When both hold, the component is an isomorphism.
    """

    site_id: SiteId
    direction: MorphismDirection
    source_section: LocalSection
    target_section: LocalSection
    forward_vc: Optional[Any] = None   # Predicate
    backward_vc: Optional[Any] = None  # Predicate
    is_isomorphism: Optional[bool] = None
    proof: Optional[Any] = None  # ProofTerm


@dataclass
class NaturalTransformation:
    """A natural transformation η : Sem_f ⇒ Sem_g.

    Naturality square at each morphism m : U_i → U_j:

        Sem_f(U_i) --η_{U_i}--> Sem_g(U_i)
            |                         |
        ρ_f(m)                    ρ_g(m)
            |                         |
            v                         v
        Sem_f(U_j) --η_{U_j}--> Sem_g(U_j)

    Naturality: ρ_g(m) ∘ η_{U_i} = η_{U_j} ∘ ρ_f(m) at every morphism.
    """

    components: Dict[SiteId, SheafMorphismComponent] = field(default_factory=dict)
    naturality_checks: Dict[Tuple[SiteId, SiteId], bool] = field(
        default_factory=dict
    )
    is_natural: Optional[bool] = None
    is_isomorphism: Optional[bool] = None

    @property
    def component_sites(self) -> FrozenSet[SiteId]:
        return frozenset(self.components.keys())

    def naturality_failures(self) -> List[Tuple[SiteId, SiteId]]:
        """Return morphisms where the naturality square fails to commute."""
        return [
            edge
            for edge, ok in self.naturality_checks.items()
            if not ok
        ]


@dataclass
class IsomorphismWitness:
    """Witness that η is an isomorphism of sheaves.

    Consists of:
    - The forward natural transformation η : Sem_f ⇒ Sem_g
    - The inverse η⁻¹ : Sem_g ⇒ Sem_f
    - Proofs that η⁻¹ ∘ η = id and η ∘ η⁻¹ = id (up to IdentityType)
    """

    forward: NaturalTransformation
    inverse: NaturalTransformation
    roundtrip_fg: Dict[SiteId, Any] = field(default_factory=dict)  # ProofTerms
    roundtrip_gf: Dict[SiteId, Any] = field(default_factory=dict)
    strength: EquivalenceStrength = EquivalenceStrength.DENOTATIONAL


# ═══════════════════════════════════════════════════════════════════════════════
# Equivalence obligations and judgments
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class EquivalenceObligation:
    """A verification obligation arising from the equivalence check.

    Extends the solver-obligation concept with paired predicates.
    An equivalence obligation at site U_i asserts:

        ∀x : τ_common. φ_f(x) ⟺ φ_g(x)

    decomposed into:
        forward:  φ_f(x) ⟹ φ_g(x)
        backward: φ_g(x) ⟹ φ_f(x)
    """

    site_id: SiteId
    description: str
    forward_predicate: Optional[Any] = None   # ImplicationPred: φ_f ⟹ φ_g
    backward_predicate: Optional[Any] = None  # ImplicationPred: φ_g ⟹ φ_f
    carrier_type_f: Optional[Any] = None
    carrier_type_g: Optional[Any] = None
    refinement_type_f: Optional[Any] = None   # RefinementType
    refinement_type_g: Optional[Any] = None   # RefinementType
    strength: EquivalenceStrength = EquivalenceStrength.DENOTATIONAL

    @property
    def is_bidirectional(self) -> bool:
        return self.forward_predicate is not None and self.backward_predicate is not None


@dataclass
class LocalEquivalenceJudgment:
    """Result of checking equivalence at a single site.

    Contains the verdict, proof term (if equivalent), and counterexample
    (if not).
    """

    site_id: SiteId
    verdict: EquivalenceVerdict
    obligation: EquivalenceObligation
    forward_holds: Optional[bool] = None
    backward_holds: Optional[bool] = None
    proof: Optional[Any] = None  # ProofTerm
    counterexample: Optional[Dict[str, Any]] = None
    explanation: str = ""

    @property
    def is_equivalent(self) -> bool:
        return self.verdict == EquivalenceVerdict.EQUIVALENT

    @property
    def is_refined(self) -> bool:
        return self.verdict == EquivalenceVerdict.REFINED


@dataclass
class EquivalenceJudgment:
    """Global equivalence judgment across all sites in the common refinement.

    This is the top-level result.  It aggregates per-site local judgments,
    the natural transformation (if one exists), and the obstruction data
    (if equivalence fails).
    """

    verdict: EquivalenceVerdict
    program_f: ProgramId
    program_g: ProgramId
    strength: EquivalenceStrength = EquivalenceStrength.DENOTATIONAL

    # Per-site results
    local_judgments: Dict[SiteId, LocalEquivalenceJudgment] = field(
        default_factory=dict
    )

    # Sheaf-morphism data
    natural_transformation: Optional[NaturalTransformation] = None
    isomorphism_witness: Optional[IsomorphismWitness] = None

    # Fiber product and descent data
    fiber_product_sections: Dict[SiteId, FiberProductSection] = field(
        default_factory=dict
    )
    descent_datum: Optional[DescentDatum] = None

    # Obstruction data (when inequivalent)
    obstructions: List[ObstructionData] = field(default_factory=list)
    cohomology_class: Optional[CohomologyClass] = None
    counterexamples: List[Dict[str, Any]] = field(default_factory=list)

    # Repair suggestions
    repairs: List[RepairSuggestion] = field(default_factory=list)

    # Common refinement cover
    common_cover: Optional[Cover] = None

    @property
    def is_equivalent(self) -> bool:
        return self.verdict == EquivalenceVerdict.EQUIVALENT

    @property
    def sites_equivalent(self) -> FrozenSet[SiteId]:
        return frozenset(
            sid
            for sid, j in self.local_judgments.items()
            if j.is_equivalent
        )

    @property
    def sites_inequivalent(self) -> FrozenSet[SiteId]:
        return frozenset(
            sid
            for sid, j in self.local_judgments.items()
            if j.verdict == EquivalenceVerdict.INEQUIVALENT
        )

    def summary(self) -> str:
        """One-line summary of the equivalence judgment."""
        total = len(self.local_judgments)
        eq = len(self.sites_equivalent)
        ineq = len(self.sites_inequivalent)
        return (
            f"{self.verdict.value}: {eq}/{total} sites equivalent, "
            f"{ineq} inequivalent, {len(self.obstructions)} obstructions"
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Descent data for equivalence
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class EquivalenceDescentDatum:
    """Descent datum for the equivalence problem.

    Extends DescentDatum with the requirement that transition isomorphisms
    φ_{ij} : σ_f|_{U_i ∩ U_j} ≅ σ_g|_{U_i ∩ U_j} are themselves equivalences.

    The cocycle condition becomes:
        φ_{ij} ∘ φ_{jk} = φ_{ik}  on triple overlaps U_i ∩ U_j ∩ U_k

    where each φ is an equivalence witness.
    """

    # Standard descent data for each program
    descent_f: DescentDatum = field(default_factory=DescentDatum)
    descent_g: DescentDatum = field(default_factory=DescentDatum)

    # Cross-program transition isomorphisms: at each overlap (i, j),
    # an equivalence between the f-section and g-section
    cross_transitions: Dict[Tuple[SiteId, SiteId], Any] = field(
        default_factory=dict
    )  # Maps to IsomorphismWitness or ProofTerm

    # Cocycle checks
    cocycle_checks: Dict[Tuple[SiteId, SiteId, SiteId], bool] = field(
        default_factory=dict
    )

    def cocycle_condition_holds(self) -> bool:
        """Check the cocycle condition on all triple overlaps."""
        if not self.cocycle_checks:
            return True
        return all(self.cocycle_checks.values())

    @property
    def nontrivial_transitions(self) -> Dict[Tuple[SiteId, SiteId], Any]:
        """Return transitions that are not the identity."""
        return {
            k: v for k, v in self.cross_transitions.items()
            if v is not None
        }


# ═══════════════════════════════════════════════════════════════════════════════
# Čech cohomology for equivalence
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class EquivalenceCochainData:
    """Čech cochain data enriched with equivalence information.

    A degree-0 cochain assigns an equivalence judgment to each site.
    A degree-1 cochain assigns an equivalence witness to each overlap.
    """

    degree: int
    values: Dict[Tuple[SiteId, ...], Any] = field(default_factory=dict)
    predicate_values: Dict[Tuple[SiteId, ...], Any] = field(
        default_factory=dict
    )  # Predicate at each simplex


@dataclass
class EquivalenceCohomologyClass:
    """Element of H^n(U, Iso(Sem_f, Sem_g)).

    H^0 = global isomorphisms (the equivalence we seek).
    H^1 = obstructions to gluing local equivalences into a global one.
    """

    degree: int
    representative: EquivalenceCochainData
    is_trivial: bool = False
    obstruction_description: str = ""

    @property
    def witnesses_equivalence(self) -> bool:
        """H⁰ nontrivial means there exists a global equivalence."""
        return self.degree == 0 and not self.is_trivial

    @property
    def witnesses_obstruction(self) -> bool:
        """H¹ nontrivial means equivalence cannot be glued globally."""
        return self.degree == 1 and not self.is_trivial


# ═══════════════════════════════════════════════════════════════════════════════
# Equivalence-specific obstruction data
# ═══════════════════════════════════════════════════════════════════════════════


class EquivalenceObstructionKind(enum.Enum):
    """Classification of why two programs differ at a site."""

    CARRIER_TYPE_MISMATCH = "carrier_type_mismatch"
    """The base types differ: int vs str, etc."""

    PREDICATE_GAP = "predicate_gap"
    """Base types match but refinement predicates are not bi-implied."""

    FORWARD_ONLY = "forward_only"
    """φ_f ⟹ φ_g holds but φ_g ⟹ φ_f does not (f refines g)."""

    BACKWARD_ONLY = "backward_only"
    """φ_g ⟹ φ_f holds but φ_f ⟹ φ_g does not (g refines f)."""

    BOUNDARY_DISAGREEMENT = "boundary_disagreement"
    """Input or output boundaries have incompatible sections."""

    NATURALITY_FAILURE = "naturality_failure"
    """The morphism components don't satisfy the naturality square."""

    COCYCLE_FAILURE = "cocycle_failure"
    """Transition isomorphisms violate the cocycle condition."""

    DEPENDENT_TYPE_MISMATCH = "dependent_type_mismatch"
    """Pi/Sigma/Forall/Exists types differ in structure."""

    WITNESS_MISSING = "witness_missing"
    """Could not construct the required proof term."""

    SOLVER_TIMEOUT = "solver_timeout"
    """The SMT solver timed out on the verification condition."""


@dataclass
class EquivalenceObstruction:
    """An enriched obstruction localised to specific sites with classification.

    Each obstruction pinpoints:
    - which sites disagree
    - what kind of disagreement
    - the predicate gap (what additional constraint would close it)
    - a counterexample (if the solver produced one)
    """

    kind: EquivalenceObstructionKind
    sites: List[SiteId] = field(default_factory=list)
    description: str = ""
    predicate_gap: Optional[Any] = None  # Predicate
    counterexample: Optional[Dict[str, Any]] = None
    severity: str = "high"
    repair_hint: Optional[str] = None

    # Link to the underlying ObstructionData
    underlying: Optional[ObstructionData] = None

    def to_obstruction_data(self) -> ObstructionData:
        """Convert to the base ObstructionData for integration."""
        return ObstructionData(
            conflicting_overlaps=[(s, s) for s in self.sites],
            explanation=f"[{self.kind.value}] {self.description}",
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Protocols
# ═══════════════════════════════════════════════════════════════════════════════


@runtime_checkable
class EquivalenceChecker(Protocol):
    """Protocol for checking equivalence between two programs."""

    def check(
        self,
        program_f: ProgramId,
        program_g: ProgramId,
        cover_f: Cover,
        cover_g: Cover,
        sections_f: Dict[SiteId, LocalSection],
        sections_g: Dict[SiteId, LocalSection],
        strength: EquivalenceStrength = EquivalenceStrength.DENOTATIONAL,
    ) -> EquivalenceJudgment:
        """Check whether programs f and g are equivalent."""
        ...


@runtime_checkable
class LocalEquivalenceCheckerProtocol(Protocol):
    """Protocol for checking equivalence at a single site."""

    def check_local(
        self,
        pair: SectionPair,
        strength: EquivalenceStrength,
    ) -> LocalEquivalenceJudgment:
        """Check equivalence of two sections at a single site."""
        ...


@runtime_checkable
class FiberProductBuilder(Protocol):
    """Protocol for constructing the fiber product presheaf."""

    def build(
        self,
        cover: Cover,
        sections_f: Dict[SiteId, LocalSection],
        sections_g: Dict[SiteId, LocalSection],
        correspondences: List[SiteCorrespondence],
    ) -> Dict[SiteId, FiberProductSection]:
        """Build fiber product sections at each site."""
        ...
