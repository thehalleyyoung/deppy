"""deppy.proof -- Proof system for sheaf-descent semantic typing.

This package implements the proof infrastructure for DepPy's dependent
typing system, including proof checking, elaboration, transport compilation,
witness combinators, theorem registries, goal management, termination
checking, and proof rendering.

Modules:
    _protocols        -- Core proof protocols (ProofTerm, ProofObligation, etc.)
    proof_checker     -- Verify proof terms against obligations.
    proof_elaborator  -- Elaborate theorem decorators into proof sites.
    transport_compiler-- Compile @transport declarations into morphisms.
    witness_combinators-- Compose witness / proof terms.
    theorem_registry  -- Registry of available theorems and lemmas.
    proof_goal_manager-- Track open proof goals and discharge them.
    decreases_checker -- Check well-founded decreases annotations.
    proof_renderer    -- Render proof goals as human-readable text.
"""

# ---------------------------------------------------------------------------
# Protocol-level types (_protocols.py)
# ---------------------------------------------------------------------------
from deppy.proof._protocols import (
    ProofTermKind,
    ProofTerm as ProtocolProofTerm,
    ObligationStatus,
    ProofObligation,
    ProofContext,
    AnnotationLevel,
    ProofEngine,
)

# ---------------------------------------------------------------------------
# Proof checker (proof_checker.py)
# ---------------------------------------------------------------------------
from deppy.proof.proof_checker import (
    CheckVerdict,
    Counterexample,
    CheckResult,
    PropositionKind,
    Proposition,
    ProofEnvironment,
    ProofChecker,
)

# ---------------------------------------------------------------------------
# Proof elaborator (proof_elaborator.py)
# ---------------------------------------------------------------------------
from deppy.proof.proof_elaborator import (
    DecoratorKind,
    ParsedDecorator,
    ElaborationResult,
    ProofElaborator,
)

# ---------------------------------------------------------------------------
# Transport compiler (transport_compiler.py)
# ---------------------------------------------------------------------------
from deppy.proof.transport_compiler import (
    TransportKind,
    TransportDeclaration,
    TransportCompilationResult,
    TransportCompiler,
)

# ---------------------------------------------------------------------------
# Witness combinators (witness_combinators.py)
# ---------------------------------------------------------------------------
from deppy.proof.witness_combinators import (
    TransitivityWitness,
    SymmetryWitness,
    CongruenceWitness,
    ExistentialPackWitness,
    UniversalWitness,
    PairWitness,
    ProjectionWitness,
    ModusPonensWitness,
    LeftInjectionWitness,
    RightInjectionWitness,
    CaseAnalysisWitness,
    AbsurdityWitness,
    TransportProofWitness,
    compose_transitivity,
    compose_symmetry,
    lift_congruence,
    lift_congruence_multi,
    pack_witness,
    unpack_witness,
    make_modus_ponens,
    make_universal,
    make_existential,
    make_case_analysis,
    make_absurdity,
    make_transport,
    make_left_injection,
    make_right_injection,
    simplify_proof,
    proof_size,
)

# ---------------------------------------------------------------------------
# Theorem registry (theorem_registry.py)
# ---------------------------------------------------------------------------
from deppy.proof.theorem_registry import (
    TheoremKind,
    TheoremHypothesis,
    TheoremConclusion,
    TheoremInfo,
    TheoremMatch,
    TheoremRegistry,
    create_default_registry,
)

# ---------------------------------------------------------------------------
# Proof goal manager (proof_goal_manager.py)
# ---------------------------------------------------------------------------
from deppy.proof.proof_goal_manager import (
    GoalStatus,
    GoalPriority,
    ProofGoal,
    DischargedGoal,
    ProofProgress,
    ProofGoalManager,
)

# ---------------------------------------------------------------------------
# Decreases checker (decreases_checker.py)
# ---------------------------------------------------------------------------
from deppy.proof.decreases_checker import (
    DecreasesVerdict,
    MeasureKind,
    RecursiveCallInfo,
    LoopIterationInfo,
    MeasureDecreaseEvidence,
    DecreasesResult,
    DecreasesChecker,
)

# ---------------------------------------------------------------------------
# Proof renderer (proof_renderer.py)
# ---------------------------------------------------------------------------
from deppy.proof.proof_renderer import (
    RenderConfig,
    ProofRenderer,
)

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
__all__ = [
    # _protocols
    "ProofTermKind",
    "ProtocolProofTerm",
    "ObligationStatus",
    "ProofObligation",
    "ProofContext",
    "AnnotationLevel",
    "ProofEngine",
    # proof_checker
    "CheckVerdict",
    "Counterexample",
    "CheckResult",
    "PropositionKind",
    "Proposition",
    "ProofEnvironment",
    "ProofChecker",
    # proof_elaborator
    "DecoratorKind",
    "ParsedDecorator",
    "ElaborationResult",
    "ProofElaborator",
    # transport_compiler
    "TransportKind",
    "TransportDeclaration",
    "TransportCompilationResult",
    "TransportCompiler",
    # witness_combinators
    "TransitivityWitness",
    "SymmetryWitness",
    "CongruenceWitness",
    "ExistentialPackWitness",
    "UniversalWitness",
    "PairWitness",
    "ProjectionWitness",
    "ModusPonensWitness",
    "LeftInjectionWitness",
    "RightInjectionWitness",
    "CaseAnalysisWitness",
    "AbsurdityWitness",
    "TransportProofWitness",
    "compose_transitivity",
    "compose_symmetry",
    "lift_congruence",
    "lift_congruence_multi",
    "pack_witness",
    "unpack_witness",
    "make_modus_ponens",
    "make_universal",
    "make_existential",
    "make_case_analysis",
    "make_absurdity",
    "make_transport",
    "make_left_injection",
    "make_right_injection",
    "simplify_proof",
    "proof_size",
    # theorem_registry
    "TheoremKind",
    "TheoremHypothesis",
    "TheoremConclusion",
    "TheoremInfo",
    "TheoremMatch",
    "TheoremRegistry",
    "create_default_registry",
    # proof_goal_manager
    "GoalStatus",
    "GoalPriority",
    "ProofGoal",
    "DischargedGoal",
    "ProofProgress",
    "ProofGoalManager",
    # decreases_checker
    "DecreasesVerdict",
    "MeasureKind",
    "RecursiveCallInfo",
    "LoopIterationInfo",
    "MeasureDecreaseEvidence",
    "DecreasesResult",
    "DecreasesChecker",
    # proof_renderer
    "RenderConfig",
    "ProofRenderer",
]
