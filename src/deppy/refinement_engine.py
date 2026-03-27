"""Compatibility facade over the top-level deppy2 implementation."""

import importlib
from pathlib import Path
import sys

try:
    from deppy2.api.decorators import decreases, ensures, invariant, requires
    from deppy2.api.engine import (
        DeppyEngine,
        check_equiv,
        generate,
        ideate,
        refine,
        run_fleet,
        scaffold,
        synthesize_refinements,
        verify,
    )
    from deppy2.api.public_types import (
        CandidateReport,
        EquivalenceResult,
        FleetResult,
        GeneratedModule,
        IdeationResult,
        ProjectScaffold,
        RefinementAnalysis,
        RefinementObstruction,
        SynthesizedRefinement,
        VerificationCondition,
        VerificationLevel,
        VerificationResult,
    )
except ModuleNotFoundError as exc:
    if exc.name is None or not exc.name.startswith("deppy2"):
        raise
    repo_deppy2_src = Path(__file__).resolve().parents[3] / "deppy2" / "src"
    if repo_deppy2_src.exists():
        sys.path.insert(0, str(repo_deppy2_src))
        sys.modules.pop("deppy2", None)
        importlib.invalidate_caches()
    from deppy2.api.decorators import decreases, ensures, invariant, requires
    from deppy2.api.engine import (
        DeppyEngine,
        check_equiv,
        generate,
        ideate,
        refine,
        run_fleet,
        scaffold,
        synthesize_refinements,
        verify,
    )
    from deppy2.api.public_types import (
        CandidateReport,
        EquivalenceResult,
        FleetResult,
        GeneratedModule,
        IdeationResult,
        ProjectScaffold,
        RefinementAnalysis,
        RefinementObstruction,
        SynthesizedRefinement,
        VerificationCondition,
        VerificationLevel,
        VerificationResult,
    )

__all__ = [
    'CandidateReport',
    'DeppyEngine',
    'EquivalenceResult',
    'FleetResult',
    'GeneratedModule',
    'IdeationResult',
    'ProjectScaffold',
    'RefinementAnalysis',
    'RefinementObstruction',
    'SynthesizedRefinement',
    'VerificationCondition',
    'VerificationLevel',
    'VerificationResult',
    'check_equiv',
    'decreases',
    'ensures',
    'generate',
    'ideate',
    'invariant',
    'refine',
    'requires',
    'run_fleet',
    'scaffold',
    'synthesize_refinements',
    'verify',
]
