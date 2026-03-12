"""Kernel -- Core typing engine for the sheaf-descent semantic typing system.

The kernel implements the central algorithms of DepPy:

- **Algorithm 2** (:mod:`local_solver_dispatch`): Dispatch each site in a
  cover to the appropriate local theory-pack solver.

- **Algorithm 3** (:mod:`backward_synthesis`): Backward safe-input synthesis
  from error sites to the input boundary.

- **Algorithm 4** (:mod:`forward_synthesis`): Forward output synthesis from
  input boundary seeds to the output boundary.

- **Algorithm 5** (:mod:`obstruction_extractor`): Extract disagreeing
  overlaps and compute the obstruction basis (H^1 cohomology).

- **Fixed-point engine** (:mod:`fixed_point`): Iterate the above algorithms
  until the section assignment converges.

Supporting modules:

- :mod:`trust_classifier`: Classify sections by trust level.
- :mod:`section_propagator`: Push/pull sections along morphisms.
- :mod:`phi_merge`: Merge sections at control-flow join points.
- :mod:`viability_checker`: Check error-site viability predicates.
- :mod:`obligation_generator`: Generate verification conditions.
- :mod:`_protocols`: Kernel-internal protocols (Obligation, VerificationResult).
"""

from __future__ import annotations

# ---------------------------------------------------------------------------
# Internal protocols
# ---------------------------------------------------------------------------

from deppy.kernel._protocols import (
    Obligation,
    VerificationResult,
    VerificationStatus,
    TheoryId,
    ProofBoundaryClassification,
    SolverInterface,
    ForcingRelation,
    SubobjectClassifier,
    VerificationBackend,
)

# ---------------------------------------------------------------------------
# Trust classifier
# ---------------------------------------------------------------------------

from deppy.kernel.trust_classifier import (
    TrustClassifier,
    TrustClassification,
    ProvenanceTag,
    ProvenanceChain,
    trust_rank,
    trust_leq,
    trust_meet,
    trust_join,
    restriction_ceiling,
)

# ---------------------------------------------------------------------------
# Section propagator
# ---------------------------------------------------------------------------

from deppy.kernel.section_propagator import (
    SectionPropagator,
    PropagationResult,
    ChainPropagationResult,
)

# ---------------------------------------------------------------------------
# Phi-node merge
# ---------------------------------------------------------------------------

from deppy.kernel.phi_merge import (
    PhiMerger,
    PhiMergeResult,
)

# ---------------------------------------------------------------------------
# Algorithm 2: Local solver dispatch
# ---------------------------------------------------------------------------

from deppy.kernel.local_solver_dispatch import (
    LocalSolverDispatch,
    SolverResult,
    SolverStatus,
    LocalSolveResult,
    TheoryPack,
    DefaultTheoryPack,
    SSAValuePack,
    BranchGuardPack,
    ArgumentBoundaryPack,
    ReturnBoundaryPack,
    ErrorSitePack,
    CallResultPack,
    TensorPack,
    LoopInvariantPack,
    ProofSitePack,
    HeapProtocolPack,
)

# ---------------------------------------------------------------------------
# Algorithm 3: Backward synthesis
# ---------------------------------------------------------------------------

from deppy.kernel.backward_synthesis import (
    BackwardSynthesizer,
    BackwardSynthesisResult,
    BackwardStatus,
    ViabilityPrecondition,
)

# ---------------------------------------------------------------------------
# Algorithm 4: Forward synthesis
# ---------------------------------------------------------------------------

from deppy.kernel.forward_synthesis import (
    ForwardSynthesizer,
    ForwardSynthesisResult,
    ForwardStatus,
)

# ---------------------------------------------------------------------------
# Algorithm 5: Obstruction extraction
# ---------------------------------------------------------------------------

from deppy.kernel.obstruction_extractor import (
    ObstructionExtractor,
    ExtractionResult,
    RankedObstruction,
    ObstructionSeverity,
)

# ---------------------------------------------------------------------------
# Viability checker
# ---------------------------------------------------------------------------

from deppy.kernel.viability_checker import (
    ViabilityChecker,
    ViabilityResult,
    ViabilitySummary,
    ViabilityStatus,
)

# ---------------------------------------------------------------------------
# Obligation generator
# ---------------------------------------------------------------------------

from deppy.kernel.obligation_generator import (
    ObligationGenerator,
    EnrichedObligation,
    GenerationResult,
    ObligationKind,
)

# ---------------------------------------------------------------------------
# Fixed-point engine
# ---------------------------------------------------------------------------

from deppy.kernel.fixed_point import (
    FixedPointEngine,
    FixedPointResult,
    ConvergenceStatus,
    IterationSnapshot,
)

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

__all__ = [
    # Protocols
    "Obligation",
    "VerificationResult",
    "VerificationStatus",
    "TheoryId",
    "ProofBoundaryClassification",
    "SolverInterface",
    "ForcingRelation",
    "SubobjectClassifier",
    "VerificationBackend",
    # Trust
    "TrustClassifier",
    "TrustClassification",
    "ProvenanceTag",
    "ProvenanceChain",
    "trust_rank",
    "trust_leq",
    "trust_meet",
    "trust_join",
    "restriction_ceiling",
    # Section propagation
    "SectionPropagator",
    "PropagationResult",
    "ChainPropagationResult",
    # Phi merge
    "PhiMerger",
    "PhiMergeResult",
    # Algorithm 2
    "LocalSolverDispatch",
    "SolverResult",
    "SolverStatus",
    "LocalSolveResult",
    "TheoryPack",
    "DefaultTheoryPack",
    "SSAValuePack",
    "BranchGuardPack",
    "ArgumentBoundaryPack",
    "ReturnBoundaryPack",
    "ErrorSitePack",
    "CallResultPack",
    "TensorPack",
    "LoopInvariantPack",
    "ProofSitePack",
    "HeapProtocolPack",
    # Algorithm 3
    "BackwardSynthesizer",
    "BackwardSynthesisResult",
    "BackwardStatus",
    "ViabilityPrecondition",
    # Algorithm 4
    "ForwardSynthesizer",
    "ForwardSynthesisResult",
    "ForwardStatus",
    # Algorithm 5
    "ObstructionExtractor",
    "ExtractionResult",
    "RankedObstruction",
    "ObstructionSeverity",
    # Viability
    "ViabilityChecker",
    "ViabilityResult",
    "ViabilitySummary",
    "ViabilityStatus",
    # Obligations
    "ObligationGenerator",
    "EnrichedObligation",
    "GenerationResult",
    "ObligationKind",
    # Fixed-point
    "FixedPointEngine",
    "FixedPointResult",
    "ConvergenceStatus",
    "IterationSnapshot",
]
