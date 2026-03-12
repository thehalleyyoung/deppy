"""deppy.pipeline.stages -- Individual pipeline stage implementations.

Each stage represents a phase of the sheaf-descent analysis:
  parse -> harvest -> cover -> solve -> synthesis -> render
"""

from deppy.pipeline.stages.parse_stage import (
    AnnotationInfo,
    IRModule,
    ParameterInfo,
    ParseResult,
    ParseStage,
    ScopeInfo,
    SourceInfo,
)
from deppy.pipeline.stages.harvest_stage import (
    GuardKind,
    HarvestResult,
    HarvestStage,
    HarvestedGuard,
)
from deppy.pipeline.stages.cover_stage import (
    CoverResult,
    CoverStage,
)
from deppy.pipeline.stages.solve_stage import (
    ArithmeticSolver,
    CollectionSolver,
    NoneSolver,
    SiteSolveRecord,
    SolveResult,
    SolveStage,
    StringSolver,
    TensorSolver,
    TheorySolver,
)
from deppy.pipeline.stages.synthesis_stage import (
    ConvergenceInfo,
    PropagationRecord,
    SynthesisResult,
    SynthesisStage,
)
from deppy.pipeline.stages.render_stage import (
    ContractAnnotation,
    Diagnostic,
    DiagnosticLocation,
    DiagnosticSeverity,
    RenderResult,
    RenderStage,
)

__all__ = [
    # parse
    "AnnotationInfo",
    "IRModule",
    "ParameterInfo",
    "ParseResult",
    "ParseStage",
    "ScopeInfo",
    "SourceInfo",
    # harvest
    "GuardKind",
    "HarvestResult",
    "HarvestStage",
    "HarvestedGuard",
    # cover
    "CoverResult",
    "CoverStage",
    # solve
    "ArithmeticSolver",
    "CollectionSolver",
    "NoneSolver",
    "SiteSolveRecord",
    "SolveResult",
    "SolveStage",
    "StringSolver",
    "TensorSolver",
    "TheorySolver",
    # synthesis
    "ConvergenceInfo",
    "PropagationRecord",
    "SynthesisResult",
    "SynthesisStage",
    # render
    "ContractAnnotation",
    "Diagnostic",
    "DiagnosticLocation",
    "DiagnosticSeverity",
    "RenderResult",
    "RenderStage",
]
