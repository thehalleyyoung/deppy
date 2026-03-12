"""Main analysis pipeline orchestrator for sheaf-descent semantic typing.

The AnalysisPipeline is the top-level entry point for running the full
analysis.  It orchestrates the six stages:

    parse -> harvest -> cover_synthesis -> local_solve ->
    backward_synth + forward_synth -> obstruction_extract -> render

and supports incremental mode for efficient re-analysis.
"""

from __future__ import annotations

import hashlib
import os
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import (
    Cover,
    LocalSection,
    ObstructionData,
    SiteId,
    TrustLevel,
)
from deppy.pipeline.pipeline_config import PipelineConfig
from deppy.pipeline.stage_registry import (
    Stage,
    StageMetadata,
    StageRegistry,
    StageStatus,
    StageTiming,
)
from deppy.pipeline.stages.parse_stage import IRModule, ParseResult, ParseStage
from deppy.pipeline.stages.harvest_stage import HarvestResult, HarvestStage
from deppy.pipeline.stages.cover_stage import CoverResult, CoverStage
from deppy.pipeline.stages.solve_stage import SolveResult, SolveStage
from deppy.pipeline.stages.synthesis_stage import (
    ConvergenceInfo,
    SynthesisResult,
    SynthesisStage,
)
from deppy.pipeline.stages.render_stage import (
    ContractAnnotation,
    Diagnostic,
    DiagnosticSeverity,
    RenderResult,
    RenderStage,
)


# ===================================================================
#  Pipeline timing
# ===================================================================


@dataclass(frozen=True)
class PipelineTiming:
    """Timing data for the entire pipeline run."""

    _total_elapsed: float
    _stage_timings: Tuple[StageTiming, ...]
    _start_timestamp: float
    _end_timestamp: float

    @property
    def total_elapsed(self) -> float:
        return self._total_elapsed

    @property
    def stage_timings(self) -> Tuple[StageTiming, ...]:
        return self._stage_timings

    @property
    def start_timestamp(self) -> float:
        return self._start_timestamp

    @property
    def end_timestamp(self) -> float:
        return self._end_timestamp

    def stage_elapsed(self, stage_name: str) -> float:
        """Get elapsed time for a specific stage."""
        for t in self._stage_timings:
            if t.stage_name == stage_name:
                return t.elapsed_seconds
        return 0.0

    def summary(self) -> str:
        lines: List[str] = [f"Pipeline: {self._total_elapsed:.3f}s total"]
        for t in self._stage_timings:
            lines.append(f"  {t.stage_name}: {t.elapsed_seconds:.3f}s ({t.status.value})")
        return "\n".join(lines)


# ===================================================================
#  Pipeline result
# ===================================================================


@dataclass(frozen=True)
class PipelineResult:
    """Complete result from a pipeline run.

    Aggregates all stage results: cover, sections, obstructions,
    diagnostics, contracts, and timing information.
    """

    _cover: Optional[Cover] = None
    _sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    _obstructions: Tuple[ObstructionData, ...] = ()
    _diagnostics: Tuple[Diagnostic, ...] = ()
    _contracts: Tuple[ContractAnnotation, ...] = ()
    _timing: Optional[PipelineTiming] = None
    _convergence: Optional[ConvergenceInfo] = None
    _ir_module: Optional[IRModule] = None
    _success: bool = True
    _errors: Tuple[str, ...] = ()
    _warnings: Tuple[str, ...] = ()

    @property
    def cover(self) -> Optional[Cover]:
        return self._cover

    @property
    def sections(self) -> Dict[SiteId, LocalSection]:
        return dict(self._sections)

    @property
    def obstructions(self) -> Tuple[ObstructionData, ...]:
        return self._obstructions

    @property
    def diagnostics(self) -> Tuple[Diagnostic, ...]:
        return self._diagnostics

    @property
    def contracts(self) -> Tuple[ContractAnnotation, ...]:
        return self._contracts

    @property
    def timing(self) -> Optional[PipelineTiming]:
        return self._timing

    @property
    def convergence(self) -> Optional[ConvergenceInfo]:
        return self._convergence

    @property
    def ir_module(self) -> Optional[IRModule]:
        return self._ir_module

    @property
    def success(self) -> bool:
        return self._success

    @property
    def errors(self) -> Tuple[str, ...]:
        return self._errors

    @property
    def warnings(self) -> Tuple[str, ...]:
        return self._warnings

    @property
    def has_errors(self) -> bool:
        return len(self._errors) > 0 or any(
            d.severity == DiagnosticSeverity.ERROR for d in self._diagnostics
        )

    @property
    def error_count(self) -> int:
        return sum(
            1 for d in self._diagnostics
            if d.severity == DiagnosticSeverity.ERROR
        )

    @property
    def warning_count(self) -> int:
        return sum(
            1 for d in self._diagnostics
            if d.severity == DiagnosticSeverity.WARNING
        )

    @property
    def site_count(self) -> int:
        if self._cover:
            return len(self._cover.sites)
        return 0

    @property
    def obstruction_count(self) -> int:
        return len(self._obstructions)

    def summary(self) -> str:
        """Human-readable summary of the pipeline result."""
        lines: List[str] = []
        lines.append(f"Pipeline result: {'SUCCESS' if self._success else 'FAILURE'}")
        lines.append(f"  Sites: {self.site_count}")
        lines.append(f"  Sections: {len(self._sections)}")
        lines.append(f"  Obstructions: {self.obstruction_count}")
        lines.append(f"  Diagnostics: {len(self._diagnostics)} "
                      f"({self.error_count} errors, {self.warning_count} warnings)")
        lines.append(f"  Contracts: {len(self._contracts)}")
        if self._timing:
            lines.append(f"  Time: {self._timing.total_elapsed:.3f}s")
        if self._convergence:
            lines.append(f"  Converged: {self._convergence.converged} "
                          f"({self._convergence.iterations_used} iterations)")
        return "\n".join(lines)


# ===================================================================
#  Incremental cache
# ===================================================================


class _IncrementalCache:
    """Simple hash-based cache for incremental mode."""

    def __init__(self) -> None:
        self._cache: Dict[str, PipelineResult] = {}
        self._hashes: Dict[str, str] = {}

    def get(self, key: str, source_hash: str) -> Optional[PipelineResult]:
        """Return cached result if the hash matches."""
        if key in self._cache and self._hashes.get(key) == source_hash:
            return self._cache[key]
        return None

    def put(self, key: str, source_hash: str, result: PipelineResult) -> None:
        """Store a result in the cache."""
        self._cache[key] = result
        self._hashes[key] = source_hash

    def invalidate(self, key: str) -> None:
        """Remove a cached entry."""
        self._cache.pop(key, None)
        self._hashes.pop(key, None)

    def clear(self) -> None:
        """Clear the entire cache."""
        self._cache.clear()
        self._hashes.clear()

    @property
    def size(self) -> int:
        return len(self._cache)


# ===================================================================
#  Pipeline hooks
# ===================================================================


@dataclass(frozen=True)
class PipelineHooks:
    """Callback hooks for pipeline lifecycle events."""

    _on_stage_start: Optional[Callable[[str], None]] = None
    _on_stage_complete: Optional[Callable[[str, float], None]] = None
    _on_stage_error: Optional[Callable[[str, Exception], None]] = None
    _on_diagnostic: Optional[Callable[[Diagnostic], None]] = None
    _on_complete: Optional[Callable[[PipelineResult], None]] = None

    @property
    def on_stage_start(self) -> Optional[Callable[[str], None]]:
        return self._on_stage_start

    @property
    def on_stage_complete(self) -> Optional[Callable[[str, float], None]]:
        return self._on_stage_complete

    @property
    def on_stage_error(self) -> Optional[Callable[[str, Exception], None]]:
        return self._on_stage_error

    @property
    def on_diagnostic(self) -> Optional[Callable[[Diagnostic], None]]:
        return self._on_diagnostic

    @property
    def on_complete(self) -> Optional[Callable[[PipelineResult], None]]:
        return self._on_complete


# ===================================================================
#  AnalysisPipeline
# ===================================================================


class AnalysisPipeline:
    """Main orchestrator for the sheaf-descent analysis pipeline.

    Usage::

        pipeline = AnalysisPipeline(config)
        result = pipeline.run("path/to/file.py")
        # or
        result = pipeline.run_source("def f(x: int) -> int: return x + 1")

    The pipeline registers default stages and executes them in order.
    Custom stages can be added or existing ones replaced.
    """

    def __init__(
        self,
        config: Optional[PipelineConfig] = None,
        hooks: Optional[PipelineHooks] = None,
    ) -> None:
        self._config = config or PipelineConfig.default()
        self._hooks = hooks or PipelineHooks()
        self._registry = StageRegistry()
        self._cache = _IncrementalCache()
        self._register_default_stages()

    @property
    def config(self) -> PipelineConfig:
        return self._config

    @property
    def registry(self) -> StageRegistry:
        return self._registry

    # -- Stage registration -----------------------------------------------

    def _register_default_stages(self) -> None:
        """Register the six default pipeline stages."""
        self._registry.register(ParseStage())
        self._registry.register(HarvestStage())
        self._registry.register(CoverStage())
        self._registry.register(SolveStage())
        self._registry.register(SynthesisStage())
        self._registry.register(RenderStage())

    def register_stage(self, stage: Stage) -> None:
        """Register a custom stage.

        If a stage with the same name exists, it is replaced.
        """
        meta = stage.metadata()
        if self._registry.has_stage(meta.name):
            self._registry.unregister(meta.name)
        self._registry.register(stage)

    # -- Public entry points ----------------------------------------------

    def run(self, source_path: str) -> PipelineResult:
        """Run the full pipeline on a source file.

        Parameters
        ----------
        source_path : str
            Path to the Python source file to analyze.

        Returns
        -------
        PipelineResult
            The complete analysis result.
        """
        # Check incremental cache
        if self._config.incremental.enabled:
            source_hash = self._compute_file_hash(source_path)
            cached = self._cache.get(source_path, source_hash)
            if cached is not None:
                return cached

        context: Dict[str, Any] = {"source_path": source_path}
        result = self._execute_pipeline(context)

        # Cache result for incremental mode
        if self._config.incremental.enabled:
            source_hash = self._compute_file_hash(source_path)
            self._cache.put(source_path, source_hash, result)

        return result

    def run_source(self, source_text: str) -> PipelineResult:
        """Run the full pipeline on a source string.

        Parameters
        ----------
        source_text : str
            Python source code to analyze.

        Returns
        -------
        PipelineResult
            The complete analysis result.
        """
        context: Dict[str, Any] = {"source_text": source_text}
        return self._execute_pipeline(context)

    def run_incremental(
        self,
        source_path: str,
        changed_lines: Optional[Set[int]] = None,
    ) -> PipelineResult:
        """Run the pipeline in incremental mode.

        Re-analyzes only the portions affected by changes.
        """
        source_hash = self._compute_file_hash(source_path)

        # Check cache
        cached = self._cache.get(source_path, source_hash)
        if cached is not None:
            return cached

        # Full re-analysis with change hints
        context: Dict[str, Any] = {
            "source_path": source_path,
            "changed_lines": changed_lines,
        }
        result = self._execute_pipeline(context)
        self._cache.put(source_path, source_hash, result)
        return result

    # -- Pipeline execution -----------------------------------------------

    def _execute_pipeline(self, initial_context: Dict[str, Any]) -> PipelineResult:
        """Execute the pipeline stages in order."""
        start_time = time.monotonic()
        start_timestamp = time.time()
        errors: List[str] = []
        warnings: List[str] = []

        # Notify stage starts via hooks
        context = dict(initial_context)
        stage_timings: List[StageTiming] = []

        stages = self._registry.get_stages()

        for stage in stages:
            meta = stage.metadata()

            if not self._config.stage_filter.should_run(meta.name):
                stage_timings.append(StageTiming(
                    _stage_name=meta.name,
                    _start_time=time.monotonic(),
                    _end_time=time.monotonic(),
                    _status=StageStatus.SKIPPED,
                ))
                continue

            if self._hooks.on_stage_start:
                self._hooks.on_stage_start(meta.name)

            stage_start = time.monotonic()
            try:
                result = stage.run(context, self._config)
                context[meta.name] = result
                stage_elapsed = time.monotonic() - stage_start

                stage_timings.append(StageTiming(
                    _stage_name=meta.name,
                    _start_time=stage_start,
                    _end_time=time.monotonic(),
                    _status=StageStatus.COMPLETED,
                ))

                if self._hooks.on_stage_complete:
                    self._hooks.on_stage_complete(meta.name, stage_elapsed)

                # Collect per-stage warnings
                stage_warnings = getattr(result, "warnings", ())
                if stage_warnings:
                    warnings.extend(stage_warnings)

            except Exception as exc:
                stage_timings.append(StageTiming(
                    _stage_name=meta.name,
                    _start_time=stage_start,
                    _end_time=time.monotonic(),
                    _status=StageStatus.FAILED,
                ))

                if self._hooks.on_stage_error:
                    self._hooks.on_stage_error(meta.name, exc)

                errors.append(f"Stage '{meta.name}' failed: {exc}")

                if self._config.strict_mode:
                    break

        # Assemble the final PipelineResult from context
        end_time = time.monotonic()
        end_timestamp = time.time()

        pipeline_timing = PipelineTiming(
            _total_elapsed=end_time - start_time,
            _stage_timings=tuple(stage_timings),
            _start_timestamp=start_timestamp,
            _end_timestamp=end_timestamp,
        )

        return self._assemble_result(context, pipeline_timing, errors, warnings)

    def _assemble_result(
        self,
        context: Dict[str, Any],
        timing: PipelineTiming,
        errors: List[str],
        warnings: List[str],
    ) -> PipelineResult:
        """Assemble a PipelineResult from the accumulated context."""
        # Extract parse result
        parse_result: Optional[ParseResult] = context.get("parse")
        ir_module = parse_result.ir_module if parse_result else None
        if parse_result and parse_result.errors:
            errors.extend(parse_result.errors)

        # Extract cover result
        cover_result: Optional[CoverResult] = context.get("cover")
        cover = cover_result.cover if cover_result else None

        # Extract synthesis result
        synthesis_result: Optional[SynthesisResult] = context.get("synthesis")
        sections: Dict[SiteId, LocalSection] = {}
        obstructions: Tuple[ObstructionData, ...] = ()
        convergence: Optional[ConvergenceInfo] = None
        if synthesis_result:
            sections = synthesis_result.sections
            obstructions = synthesis_result.obstructions
            convergence = synthesis_result.convergence

        # Extract render result
        render_result: Optional[RenderResult] = context.get("render")
        diagnostics: Tuple[Diagnostic, ...] = ()
        contracts: Tuple[ContractAnnotation, ...] = ()
        if render_result:
            diagnostics = render_result.diagnostics
            contracts = render_result.contracts

        # Notify hooks for each diagnostic
        if self._hooks.on_diagnostic:
            for diag in diagnostics:
                self._hooks.on_diagnostic(diag)

        success = len(errors) == 0 and not any(
            d.severity == DiagnosticSeverity.ERROR for d in diagnostics
        )

        result = PipelineResult(
            _cover=cover,
            _sections=sections,
            _obstructions=obstructions,
            _diagnostics=diagnostics,
            _contracts=contracts,
            _timing=timing,
            _convergence=convergence,
            _ir_module=ir_module,
            _success=success,
            _errors=tuple(errors),
            _warnings=tuple(warnings),
        )

        if self._hooks.on_complete:
            self._hooks.on_complete(result)

        return result

    # -- Utilities --------------------------------------------------------

    @staticmethod
    def _compute_file_hash(file_path: str) -> str:
        """Compute a SHA-256 hash of a file's contents."""
        try:
            content = Path(file_path).read_bytes()
            return hashlib.sha256(content).hexdigest()[:16]
        except (OSError, FileNotFoundError):
            return ""

    def invalidate_cache(self, source_path: Optional[str] = None) -> None:
        """Invalidate the incremental cache."""
        if source_path:
            self._cache.invalidate(source_path)
        else:
            self._cache.clear()

    def stage_names(self) -> List[str]:
        """Return the names of all registered stages in execution order."""
        return self._registry.get_stage_names()

    def __repr__(self) -> str:
        return (
            f"AnalysisPipeline(stages={self.stage_names()}, "
            f"config={self._config!r})"
        )


# ===================================================================
#  Convenience functions
# ===================================================================


def analyze_file(
    source_path: str,
    config: Optional[PipelineConfig] = None,
) -> PipelineResult:
    """Convenience function to analyze a single file."""
    pipeline = AnalysisPipeline(config)
    return pipeline.run(source_path)


def analyze_source(
    source_text: str,
    config: Optional[PipelineConfig] = None,
) -> PipelineResult:
    """Convenience function to analyze a source string."""
    pipeline = AnalysisPipeline(config)
    return pipeline.run_source(source_text)
