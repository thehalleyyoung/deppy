"""deppy.equivalence -- Sheaf-theoretic two-program equivalence checker.

This package turns deppy from a single-program type-error detector into
a two-program equivalence checker, maximally leveraging the sheaf-theoretic
machinery of the core framework.

Central idea:
    Two programs f, g are equivalent iff their semantic presheaves
    Sem_f, Sem_g are isomorphic as sheaves over a common refinement cover.

Architecture overview:

    _protocols      Core data structures (EquivalenceJudgment, etc.)
    predicates      Equivalence-specific Predicate subclasses
    topos           Genuine categorical constructions (pullback, equaliser,
                    subobject classifier, internal hom, pushout)
    stalk           Stalk computation, germs, stalk-level equivalence
    cohomology      Proper Cech cohomology (C^0 -> C^1 -> C^2, H^0, H^1)
    fiber_product   Fiber product presheaf via pullback construction
    site_alignment  Common refinement via sieve pullback
    local_checker   Per-site equivalence checking with equaliser integration
    global_checker  Global equivalence via sheaf gluing + descent
    sheaf_morphism  Natural transformations with verified naturality squares
    descent         Descent data and cohomological gluing obstruction
    solver_bridge   Z3/SMT encoding bridge for equivalence VCs
    obstruction     Obstruction classification and repair suggestion
    pipeline        Equivalence checking pipeline orchestrator
    render          Diagnostic rendering (terminal, JSON, SARIF)
    cli             CLI command: deppy equiv file1.py file2.py
    contracts       @equiv, @refines decorators for specification
"""

# --- Core protocols ---
from deppy.equivalence._protocols import (
    EquivalenceVerdict,
    EquivalenceStrength,
    EquivalenceSiteKind,
    EquivalenceObstructionKind,
    MorphismDirection,
    ProgramId,
    SectionPair,
    FiberProductSection,
    SiteCorrespondence,
    SheafMorphismComponent,
    NaturalTransformation,
    IsomorphismWitness,
    EquivalenceObligation,
    LocalEquivalenceJudgment,
    EquivalenceJudgment,
    EquivalenceDescentDatum,
    EquivalenceCochainData,
    EquivalenceCohomologyClass,
    EquivalenceObstruction,
)

# --- Predicates ---
from deppy.equivalence.predicates import (
    BiimplicationPred,
    EquivalencePred,
    RefinementEquivalencePred,
    BehavioralEquivalencePred,
    SectionAgreementPred,
    TransportPred,
    FiberProductPred,
    build_equivalence_predicate,
    build_fiber_product_predicate,
)

# --- Topos (categorical constructions) ---
from deppy.equivalence.topos import (
    PresheafMorphism,
    SectionTransformComponent,
)

# --- Stalk ---
from deppy.equivalence.stalk import (
    Germ,
    Stalk,
    StalkFunctor,
    GermMorphism,
    StalkEquivalenceChecker,
    PointStalkResult,
    StalkEquivalenceResult,
)

# --- Cohomology ---
from deppy.equivalence.cohomology import (
    CochainElement,
    CochainGroup,
    CoboundaryOperator,
    CechCohomologyComputer,
    CechCohomologyResult,
    extract_obstructions_from_h1,
)

# --- Fiber product ---
from deppy.equivalence.fiber_product import (
    FiberSection,
    FiberProjection,
    FiberProductBuilder,
    FiberProduct,
)

# --- Site alignment ---
from deppy.equivalence.site_alignment import (
    SiteMatcher,
    Sieve,
    SieveComputer,
    CommonRefinementBuilder,
    CommonRefinement,
)

# --- Local checker ---
from deppy.equivalence.local_checker import (
    LocalEquivalenceChecker,
    EqualiserLocalChecker,
    check_local_equivalences,
)

# --- Sheaf morphism ---
from deppy.equivalence.sheaf_morphism import (
    NaturalityVerdict,
    NaturalitySquare,
    MorphismComponent,
    SheafMorphismBuilder,
    SheafMorphism,
    IsomorphismChecker,
    IsomorphismResult,
)

# --- Global checker ---
from deppy.equivalence.global_checker import (
    GlobalEquivalenceChecker,
    GlobalEquivalenceResult,
    GluingResult,
)

# --- Descent ---
from deppy.equivalence.descent import (
    TransitionFunction,
    TransitionFunctionBuilder,
    DescentDatumBuilder,
    EquivalenceDescentChecker,
    DescentResult,
    CocycleConditionChecker,
    CocycleResult,
    quick_descent_check,
)

# --- Solver bridge ---
from deppy.equivalence.solver_bridge import (
    EquivalenceEncoder,
    CounterexampleExtractor,
)

# --- Obstruction ---
from deppy.equivalence.obstruction import (
    ObstructionClassifier,
    RepairSuggester,
)

# --- Pipeline ---
from deppy.equivalence.pipeline import (
    EquivalencePipeline,
    EquivalencePipelineResult,
)

# --- Render ---
from deppy.equivalence.render import (
    EquivalenceTerminalRenderer,
    EquivalenceJsonRenderer,
    EquivalenceSarifRenderer,
    EquivalenceSummaryRenderer,
)

# --- CLI ---
from deppy.equivalence.cli import (
    EquivCommand,
)

# --- Predicate equivalence (computational core) ---
from deppy.equivalence.predicate_eq import (
    PredicateRelation,
    PredicateEquivalenceResult,
    predicates_equivalent,
    compose_predicates,
    check_cocycle_identity,
)

# --- Contracts ---
from deppy.equivalence.contracts import (
    equiv,
    refines,
)


__all__ = [
    # Protocols
    "EquivalenceVerdict",
    "EquivalenceStrength",
    "EquivalenceSiteKind",
    "EquivalenceObstructionKind",
    "MorphismDirection",
    "ProgramId",
    "SectionPair",
    "FiberProductSection",
    "SiteCorrespondence",
    "SheafMorphismComponent",
    "NaturalTransformation",
    "IsomorphismWitness",
    "EquivalenceObligation",
    "LocalEquivalenceJudgment",
    "EquivalenceJudgment",
    "EquivalenceDescentDatum",
    "EquivalenceCochainData",
    "EquivalenceCohomologyClass",
    "EquivalenceObstruction",
    # Predicates
    "BiimplicationPred",
    "EquivalencePred",
    "RefinementEquivalencePred",
    "BehavioralEquivalencePred",
    "SectionAgreementPred",
    "TransportPred",
    "FiberProductPred",
    "build_equivalence_predicate",
    "build_fiber_product_predicate",
    # Predicate equivalence
    "PredicateRelation",
    "PredicateEquivalenceResult",
    "predicates_equivalent",
    "compose_predicates",
    "check_cocycle_identity",
    # Topos
    "PresheafMorphism",
    "SectionTransformComponent",
    # Stalk
    "Germ",
    "Stalk",
    "StalkFunctor",
    "GermMorphism",
    "StalkEquivalenceChecker",
    "PointStalkResult",
    "StalkEquivalenceResult",
    # Cohomology
    "CochainElement",
    "CochainGroup",
    "CoboundaryOperator",
    "CechCohomologyComputer",
    "CechCohomologyResult",
    "extract_obstructions_from_h1",
    # Fiber product
    "FiberSection",
    "FiberProjection",
    "FiberProductBuilder",
    "FiberProduct",
    # Site alignment
    "SiteMatcher",
    "Sieve",
    "SieveComputer",
    "CommonRefinementBuilder",
    "CommonRefinement",
    # Local checker
    "LocalEquivalenceChecker",
    "EqualiserLocalChecker",
    "check_local_equivalences",
    # Sheaf morphism
    "NaturalityVerdict",
    "NaturalitySquare",
    "MorphismComponent",
    "SheafMorphismBuilder",
    "SheafMorphism",
    "IsomorphismChecker",
    "IsomorphismResult",
    # Global checker
    "GlobalEquivalenceChecker",
    "GlobalEquivalenceResult",
    "GluingResult",
    # Descent
    "TransitionFunction",
    "TransitionFunctionBuilder",
    "DescentDatumBuilder",
    "EquivalenceDescentChecker",
    "DescentResult",
    "CocycleConditionChecker",
    "CocycleResult",
    "quick_descent_check",
    # Solver bridge
    "EquivalenceEncoder",
    "CounterexampleExtractor",
    # Obstruction
    "ObstructionClassifier",
    "RepairSuggester",
    # Pipeline
    "EquivalencePipeline",
    "EquivalencePipelineResult",
    # Render
    "EquivalenceTerminalRenderer",
    "EquivalenceJsonRenderer",
    "EquivalenceSarifRenderer",
    "EquivalenceSummaryRenderer",
    # CLI
    "EquivCommand",
    # Contracts
    "equiv",
    "refines",
]
