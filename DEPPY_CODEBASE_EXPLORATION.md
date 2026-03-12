# DepPy Codebase Exploration Report
## For Building the Normalize Package

Generated: 2025-03-11
Project Root: `/Users/halleyyoung/Documents/div/mathdivergence/deppy`

---

## EXECUTIVE SUMMARY

The DepPy codebase follows a **sheaf-descent semantic typing** architecture where:
- **Core**: Foundational protocols for observation sites, sections, presheaves, and descent (1186 LOC)
- **Proof**: Proof term constructors and obligation tracking (101 LOC)
- **Predicates**: Empty stub (to be implemented)
- **Types**: Empty stub (to be implemented)
- **Contracts**: Empty stub (to be implemented)

**Key Finding**: The predicates, types, and contracts directories are EMPTY stubs that YOU need to fill with the normalize package implementation.

---

## 1. CORE MODULES (~/deppy/src/deppy/core/)

### Module Hierarchy
```
deppy.core/
├── _protocols.py         (7,505 lines) - Foundational protocols & dataclasses
├── boundary.py           (4,604 lines) - Boundary extraction
├── grothendieck.py       (4,918 lines) - Grothendieck topology
├── presheaf.py           (6,325 lines) - Semantic presheaf & sheaf condition
├── section.py            (7,789 lines) - Section construction & merging
└── site.py               (8,745 lines) - Site category & cover builders
TOTAL: 1,186 LOC
```

### Key Types & Classes from `deppy.core._protocols`

**Import Path**: `from deppy.core._protocols import ...`

#### Enums
```python
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
```

#### Core Dataclasses

**1. SiteId** (frozen)
```python
@dataclass(frozen=True)
class SiteId:
    kind: SiteKind
    name: str
    source_location: Optional[Tuple[str, int, int]] = None
    
    def __str__(self) -> str: ...
```
**Used for**: Unique identifier for observation sites.

**2. LocalSection**
```python
@dataclass
class LocalSection:
    site_id: SiteId
    carrier_type: Any = None
    refinements: Dict[str, Any] = field(default_factory=dict)
    trust: TrustLevel = TrustLevel.RESIDUAL
    provenance: Optional[str] = None
    witnesses: Dict[str, Any] = field(default_factory=dict)
```
**Used for**: Section of semantic presheaf at a single site. Core semantic value.

**3. BoundarySection**
```python
@dataclass
class BoundarySection:
    boundary_sites: Dict[SiteId, LocalSection] = field(default_factory=dict)
    is_input: bool = True
    
    @property
    def site_ids(self) -> FrozenSet[SiteId]: ...
```
**Used for**: Input or output boundary of a covered region.

**4. GlobalSection**
```python
@dataclass
class GlobalSection:
    """Compatible family of local sections satisfying sheaf condition."""
    local_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    input_section: Optional[BoundarySection] = None
    output_section: Optional[BoundarySection] = None
    
    def at(self, site_id: SiteId) -> Optional[LocalSection]: ...
```
**Used for**: Global type assignment over entire covered region.

**5. Cover**
```python
@dataclass
class Cover:
    """A cover {u_i -> s} in the Grothendieck topology."""
    sites: Dict[SiteId, Site] = field(default_factory=dict)
    morphisms: List[Morphism] = field(default_factory=list)
    overlaps: List[Tuple[SiteId, SiteId]] = field(default_factory=list)
    error_sites: Set[SiteId] = field(default_factory=set)
    input_boundary: Set[SiteId] = field(default_factory=set)
    output_boundary: Set[SiteId] = field(default_factory=set)
    
    def site_ids(self) -> FrozenSet[SiteId]: ...
```
**Used for**: Durable artifact emitted by Stage 1 (Cover synthesis).

**6. DescentDatum**
```python
@dataclass
class DescentDatum:
    """Descent datum ({sigma_i}, {phi_ij}) with cocycle condition."""
    sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    transition_isos: Dict[Tuple[SiteId, SiteId], Any] = field(default_factory=dict)
    
    def cocycle_condition_holds(self) -> bool: ...
```
**Used for**: Descent data for gluing sections along covers.

**7. CohomologyClass**
```python
@dataclass
class CohomologyClass:
    """Element of H^n(U, T). H^0=global sections, H^1=type errors, H^2=higher."""
    degree: int
    representative: CechCochainData
    is_trivial: bool = False
```
**Used for**: Cohomology computation for obstruction theory.

**8. ObstructionData**
```python
@dataclass
class ObstructionData:
    """Obstruction class [alpha] in H^1(U, T). Represents a type error."""
    cohomology_class: Optional[CohomologyClass] = None
    conflicting_overlaps: List[Tuple[SiteId, SiteId]] = field(default_factory=list)
    explanation: str = ""
    
    @property
    def is_trivial(self) -> bool: ...
```
**Used for**: Type errors as obstructions in cohomology.

**9. FrontierPoint**
```python
@dataclass
class FrontierPoint:
    """A point on Pareto frontier. Lexicographic objective."""
    input_section: BoundarySection
    output_section: BoundarySection
    global_section: GlobalSection
    residual_errors: Set[SiteId] = field(default_factory=set)
    proof_debt: int = 0
    information_score: float = 0.0
```
**Used for**: Optimal type refinements on frontier.

**10. BidirectionalResult**
```python
@dataclass
class BidirectionalResult:
    """Result of bidirectional refinement problem."""
    input_section: BoundarySection
    output_section: BoundarySection
    global_section: GlobalSection
    obstructions: List[ObstructionData] = field(default_factory=list)
    error_viability: Dict[SiteId, bool] = field(default_factory=dict)
    converged: bool = False
```
**Used for**: Final bidirectional result.

#### Protocols (Runtime Checkable)

```python
@runtime_checkable
class Site(Protocol):
    @property
    def site_id(self) -> SiteId: ...
    @property
    def kind(self) -> SiteKind: ...
    @property
    def carrier_schema(self) -> Any: ...

@runtime_checkable
class Morphism(Protocol):
    @property
    def source(self) -> SiteId: ...
    @property
    def target(self) -> SiteId: ...
    def restrict(self, section: "LocalSection") -> "LocalSection": ...

@runtime_checkable
class GrothendieckTopology(Protocol):
    def covers(self, site: SiteId) -> Iterable[Cover]: ...
    def is_cover(self, candidate: Cover, site: SiteId) -> bool: ...

@runtime_checkable
class SemanticPresheaf(Protocol):
    def sections_at(self, site: SiteId) -> Iterable[LocalSection]: ...
    def restrict(self, section: LocalSection, morphism: Morphism) -> LocalSection: ...

@runtime_checkable
class InformationOrder(Protocol):
    def leq(self, a: LocalSection, b: LocalSection) -> bool: ...
    def join(self, a: LocalSection, b: LocalSection) -> LocalSection: ...
    def meet(self, a: LocalSection, b: LocalSection) -> LocalSection: ...
```

---

### Key Classes from `deppy.core.site`

**Import Path**: `from deppy.core.site import ...`

#### ConcreteSite
```python
@dataclass(frozen=True)
class ConcreteSite:
    """Object in the observation site category S."""
    _site_id: SiteId
    _carrier_schema: Any = None
    
    @property
    def site_id(self) -> SiteId: ...
    @property
    def kind(self) -> SiteKind: ...
    @property
    def carrier_schema(self) -> Any: ...
```

#### ConcreteMorphism
```python
@dataclass(frozen=True)
class ConcreteMorphism:
    """Morphism in S — restriction or reindexing map."""
    _source: SiteId
    _target: SiteId
    projection: Optional[Dict[str, str]] = None
    
    @property
    def source(self) -> SiteId: ...
    @property
    def target(self) -> SiteId: ...
    
    def restrict(self, section: LocalSection) -> LocalSection: ...
```

#### SiteCategory
```python
class SiteCategory:
    """Manages sites and morphisms; supports path-finding and overlap detection."""
    
    def add_site(self, site: Site) -> None: ...
    def add_morphism(self, morphism: ConcreteMorphism) -> None: ...
    def get_site(self, site_id: SiteId) -> Optional[Site]: ...
    
    @property
    def sites(self) -> Dict[SiteId, Site]: ...
    @property
    def morphisms(self) -> List[ConcreteMorphism]: ...
    
    def outgoing(self, site_id: SiteId) -> List[ConcreteMorphism]: ...
    def find_path(self, start: SiteId, end: SiteId) -> Optional[List[ConcreteMorphism]]: ...
    def find_overlaps(self, sites: FrozenSet[SiteId]) -> List[Tuple[SiteId, SiteId]]: ...
```

#### CoverBuilder
```python
class CoverBuilder:
    """Fluent API for constructing Cover objects."""
    
    def add_site(self, site: Site) -> CoverBuilder: ...
    def add_morphism(self, morphism: Morphism) -> CoverBuilder: ...
    def add_overlap(self, a: SiteId, b: SiteId) -> CoverBuilder: ...
    def mark_error(self, site_id: SiteId) -> CoverBuilder: ...
    def mark_input(self, site_id: SiteId) -> CoverBuilder: ...
    def mark_output(self, site_id: SiteId) -> CoverBuilder: ...
    def build(self) -> Cover: ...
```

---

### Key Classes from `deppy.core.section`

**Import Path**: `from deppy.core.section import ...`

#### SectionFactory
```python
class SectionFactory:
    @staticmethod
    def create(
        site_id: SiteId,
        carrier_type: Any = None,
        refinements: Optional[Dict[str, Any]] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: Optional[str] = None,
        witnesses: Optional[Dict[str, Any]] = None,
    ) -> LocalSection: ...
```

#### SectionMerger
```python
class SectionMerger:
    @staticmethod
    def merge(
        a: LocalSection,
        b: LocalSection,
        merged_site_id: Optional[SiteId] = None,
    ) -> LocalSection: ...
    
    @staticmethod
    def are_compatible(a: LocalSection, b: LocalSection) -> bool: ...
    
    _TRUST_ORDER: List[TrustLevel] = [
        TrustLevel.RESIDUAL,
        TrustLevel.ASSUMED,
        TrustLevel.TRACE_BACKED,
        TrustLevel.BOUNDED_AUTO,
        TrustLevel.TRUSTED_AUTO,
        TrustLevel.PROOF_BACKED,
    ]
```

#### GlobalSectionBuilder
```python
class GlobalSectionBuilder:
    def __init__(self) -> None: ...
    def add_section(self, section: LocalSection) -> GlobalSectionBuilder: ...
    def mark_input(self, site_id: SiteId) -> GlobalSectionBuilder: ...
    def mark_output(self, site_id: SiteId) -> GlobalSectionBuilder: ...
    def check_compatibility(
        self, overlaps: List[Tuple[SiteId, SiteId]]
    ) -> List[Tuple[SiteId, SiteId]]: ...
    def build(
        self, overlaps: Optional[List[Tuple[SiteId, SiteId]]] = None
    ) -> Tuple[GlobalSection, List[Tuple[SiteId, SiteId]]]: ...
```

---

### Key Classes from `deppy.core.presheaf`

**Import Path**: `from deppy.core.presheaf import ...`

#### ConcretePresheaf
```python
@dataclass
class ConcretePresheaf:
    """Functor Sem: S^op -> Poset."""
    _sections: Dict[SiteId, List[LocalSection]] = field(default_factory=dict)
    _morphisms: Dict[Tuple[SiteId, SiteId], Morphism] = field(default_factory=dict)
    name: str = ""
    
    def sections_at(self, site: SiteId) -> Iterable[LocalSection]: ...
    def restrict(self, section: LocalSection, morphism: Morphism) -> LocalSection: ...
    def add_section(self, section: LocalSection) -> None: ...
    def add_morphism(self, morphism: Morphism) -> None: ...
    def get_morphism(self, source: SiteId, target: SiteId) -> Optional[Morphism]: ...
    def site_ids(self) -> Set[SiteId]: ...
```

#### SheafConditionChecker
```python
class SheafConditionChecker:
    @staticmethod
    def check_agreement(
        sections: Dict[SiteId, LocalSection],
        overlaps: List[Tuple[SiteId, SiteId]],
    ) -> List[Tuple[SiteId, SiteId]]: ...
    
    @staticmethod
    def attempt_gluing(
        sections: Dict[SiteId, LocalSection],
        overlaps: List[Tuple[SiteId, SiteId]],
    ) -> GluingResult: ...
    
    @staticmethod
    def verify_uniqueness(
        global_section: GlobalSection,
        sections: Dict[SiteId, LocalSection],
    ) -> bool: ...
```

---

### Key Classes from `deppy.core.boundary`

**Import Path**: `from deppy.core.boundary import ...`

#### InputBoundaryBuilder
```python
class InputBoundaryBuilder:
    INPUT_KINDS: Set[SiteKind] = {
        SiteKind.ARGUMENT_BOUNDARY,
        SiteKind.LOOP_HEADER_INVARIANT,
    }
    
    @staticmethod
    def extract(cover: Cover) -> Set[SiteId]: ...
    
    @staticmethod
    def build_section(
        cover: Cover, sections: Dict[SiteId, LocalSection]
    ) -> BoundarySection: ...
```

#### OutputBoundaryBuilder
```python
class OutputBoundaryBuilder:
    OUTPUT_KINDS: Set[SiteKind] = {
        SiteKind.RETURN_OUTPUT_BOUNDARY,
        SiteKind.ERROR,
        SiteKind.MODULE_SUMMARY,
    }
    
    @staticmethod
    def extract(cover: Cover) -> Set[SiteId]: ...
    
    @staticmethod
    def build_section(
        cover: Cover, sections: Dict[SiteId, LocalSection]
    ) -> BoundarySection: ...
```

#### BoundarySectionFactory
```python
class BoundarySectionFactory:
    @staticmethod
    def create(
        sections: Dict[SiteId, LocalSection],
        boundary_ids: Optional[Set[SiteId]] = None,
        is_input: bool = True,
    ) -> BoundarySection: ...
    
    @staticmethod
    def from_cover(
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
        is_input: bool = True,
    ) -> BoundarySection: ...
```

---

### Key Classes from `deppy.core.grothendieck`

**Import Path**: `from deppy.core.grothendieck import ...`

#### ConcreteTopolgy (note: typo in original code)
```python
@dataclass
class ConcreteTopolgy:
    """A Grothendieck topology on the site category S."""
    _covers: Dict[SiteId, List[Cover]] = field(default_factory=dict)
    _all_site_ids: Set[SiteId] = field(default_factory=set)
    
    def add_cover(self, cover: Cover, site: SiteId) -> None: ...
    def covers(self, site: SiteId) -> Iterable[Cover]: ...
    def is_cover(self, candidate: Cover, site: SiteId) -> bool: ...
    def all_sites(self) -> Set[SiteId]: ...
    
    # Internal axiom checkers
    def _check_identity(self, candidate: Cover, site: SiteId) -> bool: ...
    def _check_stability(self, candidate: Cover, _site: SiteId) -> bool: ...
    def _check_registered(self, candidate: Cover, site: SiteId) -> bool: ...
    def _check_transitivity(self, candidate: Cover, site: SiteId) -> bool: ...
```

---

## 2. PROOF MODULES (~/deppy/src/deppy/proof/)

### Module Structure
```
deppy.proof/
├── _protocols.py        (101 lines) - Proof term types & proof engine protocol
└── __init__.py          (27 lines)
TOTAL: 101 LOC
```

### Key Types from `deppy.proof._protocols`

**Import Path**: `from deppy.proof._protocols import ...`

#### Enums

```python
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

class AnnotationLevel(enum.Enum):
    """The 6 annotation levels from Part IV."""
    ZERO = 0       # Plain Python, system infers everything
    CONTRACTS = 1  # @requires/@ensures decorators
    INVARIANTS = 2 # Loop/class invariants, checked inductively
    LEMMAS = 3     # Programmer states lemmas, system proves
    SKETCHES = 4   # Intermediate assertions guide solver
    FULL = 5       # Complete Agda-style proofs
```

#### Dataclasses

```python
@dataclass
class ProofTerm:
    """A proof term constructed from the 15 constructors."""
    kind: ProofTermKind
    children: List["ProofTerm"] = field(default_factory=list)
    payload: Any = None
    proposition: Any = None

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
    
    def push_scope(self, bindings: Optional[Dict[str, Any]] = None) -> None: ...
    def pop_scope(self) -> Dict[str, Any]: ...
    def lookup(self, name: str) -> Optional[Any]: ...
```

#### Protocol

```python
@runtime_checkable
class ProofEngine(Protocol):
    """5-pass proof engine: infer -> integrate -> discharge -> enrich -> re_infer."""
    def infer(self, cover: Any) -> List[ProofObligation]: ...
    def integrate(self, obligations: List[ProofObligation]) -> List[ProofObligation]: ...
    def discharge(self, obligations: List[ProofObligation]) -> List[ProofObligation]: ...
    def enrich(self, discharged: List[ProofObligation], cover: Any) -> Any: ...
    def re_infer(self, enriched: Any) -> List[ProofObligation]: ...
```

---

## 3. EMPTY STUBS (To be Implemented)

### Predicates Module
**Path**: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/src/deppy/predicates/`
**Status**: Empty stub with only `__init__.py`

**According to PACKAGE_STRUCTURE.md, should contain**:
- `predicate.py` - Canonical predicate representation (adapt from guard_extractor.py)
- `kinds.py` - PredicateKind enum
- `provenance.py` - Source tracking
- `templates.py` - Predicate templates
- `matching.py` - Pattern matching
- `lattice.py` - Predicate lattice structure
- `normalization.py` - Simplify & normalize predicates

### Types Module
**Path**: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/src/deppy/types/`
**Status**: Empty stub with only `__init__.py`

**According to PACKAGE_STRUCTURE.md, should contain**:
- `base_type.py` - BaseType hierarchy
- `variables.py` - TypeVariable, RowVariable
- `refinement_type.py` - {v: τ | φ}
- `dependent_type.py` - Π(x:τ₁).τ₂
- `sigma_type.py` - Σ(x:τ₁).τ₂
- `contract.py` - Pre/post conditions
- `object_protocol.py` - Obj{φ} structural types
- `subtyping.py` - Subtype checker
- `unification.py` - Type unification
- `environment.py` - Type environment (Γ)

### Contracts Module
**Path**: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/src/deppy/contracts/`
**Status**: Empty stub with only `__init__.py`

**According to PACKAGE_STRUCTURE.md, should contain**:
- Contract types and structures (pre/post conditions, decorators, etc.)

### Normalize Module
**Path**: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/src/deppy/normalize/`
**Status**: Empty stub with only `__init__.py`

**According to PACKAGE_STRUCTURE.md, should contain**:
- `normalizer.py` - Norm: Pred ↝ Core
- `fragment_classifier.py` - Fragment classification
- `symbol_elimination.py` - Variable elimination
- `arithmetic_classifier.py` - Classify arithmetic
- `finite_domain_encoder.py` - Encode finite domains
- `outside_kernel.py` - Handle non-decidable predicates

---

## 4. RECOMMENDED IMPORTS FOR TYPE CHECKING

For your normalize package, use these TYPE_CHECKING imports:

```python
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from deppy.core._protocols import (
        SiteId,
        SiteKind,
        LocalSection,
        BoundarySection,
        GlobalSection,
        Cover,
        Site,
        Morphism,
        GrothendieckTopology,
        SemanticPresheaf,
        DescentDatum,
        CohomologyClass,
        ObstructionData,
        FrontierPoint,
        BidirectionalResult,
    )
    from deppy.core.site import (
        ConcreteSite,
        ConcreteMorphism,
        SiteCategory,
        CoverBuilder,
    )
    from deppy.core.section import (
        SectionFactory,
        SectionMerger,
        GlobalSectionBuilder,
    )
    from deppy.core.presheaf import (
        ConcretePresheaf,
        SheafConditionChecker,
    )
    from deppy.core.boundary import (
        InputBoundaryBuilder,
        OutputBoundaryBuilder,
        BoundarySectionFactory,
    )
    from deppy.core.grothendieck import ConcreteTopolgy
    from deppy.proof._protocols import (
        ProofTermKind,
        ProofTerm,
        ProofObligation,
        ProofContext,
        ObligationStatus,
        AnnotationLevel,
        ProofEngine,
    )
```

**Runtime imports** (use in actual code):
```python
from deppy.core._protocols import (
    SiteId,
    SiteKind,
    LocalSection,
    TrustLevel,
)
from deppy.core.site import CoverBuilder
from deppy.core.section import SectionFactory, SectionMerger
```

---

## 5. KEY ARCHITECTURAL PRINCIPLES

### Sheaf-Descent Model
- **Sites** (S): Observation points (arguments, SSA values, returns, etc.)
- **Morphisms**: Restriction/reindexing between sites
- **Local Sections**: Type info at one site
- **Global Sections**: Compatible families (H^0 cohomology)
- **Covers**: Collections of sites with morphisms
- **Presheaves**: Functor S^op → Poset (assignment of types to sites)

### Trust Levels (in order of certainty)
1. RESIDUAL (lowest - assumed)
2. ASSUMED
3. TRACE_BACKED
4. BOUNDED_AUTO
5. TRUSTED_AUTO
6. PROOF_BACKED (highest)

### Site Families (14 total)
- Input: ARGUMENT_BOUNDARY, LOOP_HEADER_INVARIANT
- Computation: SSA_VALUE, BRANCH_GUARD, CALL_RESULT
- Tensor: TENSOR_SHAPE, TENSOR_ORDER, TENSOR_INDEXING
- Heap: HEAP_PROTOCOL
- Meta: PROOF, TRACE, ERROR, MODULE_SUMMARY

### Proof Obligations
- 15 constructors: REFL, SYMM, TRANS, CONG, SUBST, MP, INTRO, ELIM, AND_INTRO, FST, SND, INL, INR, CASES, ABSURD, AUTO, BY_ASSUMPTION
- Lifecycle: GENERATED → SOLVER_ATTEMPTED → DISCHARGED → TRIAGED → PROOF_PROVIDED → VERIFIED → EXPORTED or RESIDUAL

### 6 Annotation Levels
- ZERO: Plain Python (full inference)
- CONTRACTS: @requires/@ensures
- INVARIANTS: Inductive checking
- LEMMAS: Programmer-stated
- SKETCHES: Intermediate assertions
- FULL: Complete Agda-style

---

## 6. USAGE EXAMPLES

### Creating a Site and LocalSection
```python
from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.core.site import ConcreteSite
from deppy.core.section import SectionFactory

# Create site ID
arg_site = SiteId(
    kind=SiteKind.ARGUMENT_BOUNDARY,
    name="x",
    source_location=("file.py", 10, 5)
)

# Create concrete site
concrete_site = ConcreteSite(_site_id=arg_site, _carrier_schema="int")

# Create local section
section = SectionFactory.create(
    site_id=arg_site,
    carrier_type="int",
    refinements={"constraint_1": "x > 0"},
    trust=TrustLevel.BOUNDED_AUTO,
    provenance="inferred from guard"
)
```

### Building a Cover
```python
from deppy.core.site import CoverBuilder, ConcreteSite, ConcreteMorphism
from deppy.core._protocols import SiteId, SiteKind

builder = CoverBuilder()
builder.add_site(site_a)
builder.add_site(site_b)
builder.add_morphism(morphism_ab)
builder.add_overlap(site_a_id, site_b_id)
builder.mark_error(error_site_id)
builder.mark_input(input_site_id)
builder.mark_output(output_site_id)

cover = builder.build()
```

### Merging Sections
```python
from deppy.core.section import SectionMerger

merged = SectionMerger.merge(section_a, section_b)
compatible = SectionMerger.are_compatible(section_a, section_b)
```

### Building Global Sections
```python
from deppy.core.section import GlobalSectionBuilder

builder = GlobalSectionBuilder()
builder.add_section(section_1)
builder.add_section(section_2)
builder.mark_input(site_1_id)
builder.mark_output(site_2_id)
global_section, conflicts = builder.build(overlaps=[(site_1_id, site_2_id)])
```

---

## 7. NORMALIZE PACKAGE DESIGN HINTS

Based on the codebase structure, your normalize package should:

1. **Accept**: Predicates + LocalSections + GlobalSections
2. **Transform**: High-level logical predicates → SMT solver inputs
3. **Handle**: Fragment classification (decidable vs NP-hard)
4. **Produce**:
   - Normalized verification conditions
   - Symbol elimination results
   - Arithmetic classification
   - Finite domain encodings
   - Outside-kernel classifications

**Core responsibilities**:
- `normalizer.py`: Main orchestrator
- `fragment_classifier.py`: Decidability analysis
- `symbol_elimination.py`: Variable elimination (Fourier-Motzkin, etc.)
- `arithmetic_classifier.py`: Linear vs nonlinear
- `finite_domain_encoder.py`: Bit-vector encoding
- `outside_kernel.py`: Graceful degradation for non-decidable

**Key integration points**:
- **Input from predicates module**: Predicate objects
- **Input from types module**: Type constraints
- **Output to solver module**: Normalized VC in Z3-friendly format
- **Logging to proof module**: Proof obligations

---

## SUMMARY TABLE

| Module | Location | Status | LOC | Key Classes |
|--------|----------|--------|-----|-------------|
| core._protocols | deppy/src/deppy/core/ | ✅ Done | 233 | SiteId, LocalSection, GlobalSection, Cover, DescentDatum, ... |
| core.site | deppy/src/deppy/core/ | ✅ Done | 262 | ConcreteSite, ConcreteMorphism, SiteCategory, CoverBuilder |
| core.section | deppy/src/deppy/core/ | ✅ Done | 236 | SectionFactory, SectionMerger, GlobalSectionBuilder |
| core.presheaf | deppy/src/deppy/core/ | ✅ Done | 188 | ConcretePresheaf, SheafConditionChecker, GluingResult |
| core.boundary | deppy/src/deppy/core/ | ✅ Done | 145 | InputBoundaryBuilder, OutputBoundaryBuilder, BoundarySectionFactory |
| core.grothendieck | deppy/src/deppy/core/ | ✅ Done | 127 | ConcreteTopolgy |
| proof._protocols | deppy/src/deppy/proof/ | ✅ Done | 101 | ProofTermKind, ProofTerm, ProofObligation, ProofContext |
| predicates | deppy/src/deppy/predicates/ | ❌ Stub | 0 | To implement |
| types | deppy/src/deppy/types/ | ❌ Stub | 0 | To implement |
| contracts | deppy/src/deppy/contracts/ | ❌ Stub | 0 | To implement |
| normalize | deppy/src/deppy/normalize/ | ❌ Stub | 0 | To implement |

