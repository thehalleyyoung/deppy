"""deppy.pipeline -- Analysis pipeline for sheaf-descent semantic typing.

The pipeline orchestrates six stages:
  parse -> harvest -> cover -> solve -> synthesis -> render

Usage::

    from deppy.pipeline import AnalysisPipeline, PipelineConfig

    pipeline = AnalysisPipeline()
    result = pipeline.run("myfile.py")
    print(result.summary())
"""

from deppy.pipeline.pipeline_config import (
    IncrementalConfig,
    IncrementalStrategy,
    NormalizationConfig,
    OutputFormat,
    PipelineConfig,
    SolverConfig,
    StageFilterConfig,
    TheoryPack,
    TimeoutConfig,
    Verbosity,
)
from deppy.pipeline.stage_registry import (
    Stage,
    StageMetadata,
    StageRegistry,
    StageStatus,
    StageTiming,
)
from deppy.pipeline.pipeline import (
    AnalysisPipeline,
    PipelineHooks,
    PipelineResult,
    PipelineTiming,
    analyze_file,
    analyze_source,
)

__all__ = [
    # config
    "IncrementalConfig",
    "IncrementalStrategy",
    "NormalizationConfig",
    "OutputFormat",
    "PipelineConfig",
    "SolverConfig",
    "StageFilterConfig",
    "TheoryPack",
    "TimeoutConfig",
    "Verbosity",
    # stage registry
    "Stage",
    "StageMetadata",
    "StageRegistry",
    "StageStatus",
    "StageTiming",
    # pipeline
    "AnalysisPipeline",
    "PipelineHooks",
    "PipelineResult",
    "PipelineTiming",
    "analyze_file",
    "analyze_source",
]
