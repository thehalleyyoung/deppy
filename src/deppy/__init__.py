"""DepPy: sheaf-cohomological program analysis via refinement types.

DepPy provides automatic refinement type synthesis and verification
for Python programs, from zero annotation to full specification.

Core API (unified refinement type engine):
    refine(source)              — synthesize refinement types + find bugs
    verify(fn_or_source)        — verify against specs via refinement types
    check_equiv(src_f, src_g)   — equivalence via refinement type comparison
    synthesize_refinements(src) — extract refinement types from code
    requires(predicate)         — precondition decorator
    ensures(predicate)          — postcondition decorator

Legacy API (still supported):
    Workspace                   — incremental project analysis
    prove                       — lightweight proof decorator
    load_theory_pack            — library-specific axiom packs
    synthesize_types_from_docstring — NL → type synthesis
"""

# ── Unified refinement type API (canonical) ──
try:
    from deppy.refinement_engine import (
        DeppyEngine,
        CandidateReport,
        FleetResult,
        GeneratedModule,
        IdeationResult,
        ProjectScaffold,
        refine,
        verify,
        check_equiv,
        generate,
        ideate,
        run_fleet,
        scaffold,
        synthesize_refinements,
        requires,
        ensures,
        invariant,
        decreases,
        RefinementAnalysis,
        VerificationResult,
        EquivalenceResult,
        VerificationLevel,
        SynthesizedRefinement,
    )
except ModuleNotFoundError:
    pass  # deppy2 not installed; refinement engine API unavailable

# ── Legacy API (backward compatible) ──
from deppy.incremental import Workspace
from deppy.nl_synthesis import synthesize_types_from_docstring
from deppy.proof_decorators import prove
from deppy.theory_packs import load_theory_pack

__version__ = "3.0.0"

__all__ = [
    "__version__",
    # Unified refinement type API
    "refine",
    "verify",
    "check_equiv",
    "generate",
    "ideate",
    "run_fleet",
    "scaffold",
    "synthesize_refinements",
    "requires",
    "ensures",
    "invariant",
    "decreases",
    "DeppyEngine",
    "CandidateReport",
    "FleetResult",
    "GeneratedModule",
    "IdeationResult",
    "ProjectScaffold",
    "RefinementAnalysis",
    "VerificationResult",
    "EquivalenceResult",
    "VerificationLevel",
    "SynthesizedRefinement",
    # Legacy API
    "Workspace",
    "load_theory_pack",
    "prove",
    "synthesize_types_from_docstring",
]
