"""Pipeline configuration for the sheaf-descent semantic typing system.

Centralizes all knobs controlling how the analysis pipeline runs:
theory-pack selection, iteration limits, timeouts, trust thresholds,
output format, incremental mode, and verbosity.
"""

from __future__ import annotations

import enum
import os
from dataclasses import dataclass, field
from pathlib import Path
from typing import (
    Any,
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

from deppy.core._protocols import TrustLevel


# ===================================================================
#  Enumerations
# ===================================================================


class OutputFormat(enum.Enum):
    """Supported output formats for pipeline results."""

    TERMINAL = "terminal"
    PLAIN = "plain"
    JSON = "json"
    SARIF = "sarif"


class Verbosity(enum.Enum):
    """Verbosity levels for pipeline logging."""

    QUIET = 0
    NORMAL = 1
    VERBOSE = 2
    DEBUG = 3


class TheoryPack(enum.Enum):
    """Available theory packs for local solving."""

    BUILTIN_ARITHMETIC = "builtin_arithmetic"
    BUILTIN_STRING = "builtin_string"
    BUILTIN_COLLECTION = "builtin_collection"
    BUILTIN_NONE = "builtin_none"
    TENSOR_SHAPE = "tensor_shape"
    HEAP_PROTOCOL = "heap_protocol"
    CUSTOM = "custom"


class IncrementalStrategy(enum.Enum):
    """Strategy for incremental re-analysis."""

    NONE = "none"
    FILE_LEVEL = "file_level"
    FUNCTION_LEVEL = "function_level"
    SITE_LEVEL = "site_level"


# ===================================================================
#  Timeout configuration
# ===================================================================


@dataclass(frozen=True)
class TimeoutConfig:
    """Timeout configuration for various pipeline phases.

    All timeouts are in seconds.  A value of zero means no timeout.
    """

    _per_site: float = 5.0
    _per_stage: float = 30.0
    _total: float = 120.0
    _solver: float = 10.0

    @property
    def per_site(self) -> float:
        return self._per_site

    @property
    def per_stage(self) -> float:
        return self._per_stage

    @property
    def total(self) -> float:
        return self._total

    @property
    def solver(self) -> float:
        return self._solver

    def with_per_site(self, seconds: float) -> TimeoutConfig:
        return TimeoutConfig(
            _per_site=seconds,
            _per_stage=self._per_stage,
            _total=self._total,
            _solver=self._solver,
        )

    def with_total(self, seconds: float) -> TimeoutConfig:
        return TimeoutConfig(
            _per_site=self._per_site,
            _per_stage=self._per_stage,
            _total=seconds,
            _solver=self._solver,
        )

    def scale(self, factor: float) -> TimeoutConfig:
        """Scale all timeouts by *factor*."""
        return TimeoutConfig(
            _per_site=self._per_site * factor,
            _per_stage=self._per_stage * factor,
            _total=self._total * factor,
            _solver=self._solver * factor,
        )


# ===================================================================
#  Solver configuration
# ===================================================================


@dataclass(frozen=True)
class SolverConfig:
    """Configuration for the local theory solver."""

    _max_iterations: int = 50
    _convergence_threshold: float = 1e-8
    _enable_caching: bool = True
    _cache_capacity: int = 10000
    _parallel_sites: bool = False

    @property
    def max_iterations(self) -> int:
        return self._max_iterations

    @property
    def convergence_threshold(self) -> float:
        return self._convergence_threshold

    @property
    def enable_caching(self) -> bool:
        return self._enable_caching

    @property
    def cache_capacity(self) -> int:
        return self._cache_capacity

    @property
    def parallel_sites(self) -> bool:
        return self._parallel_sites


# ===================================================================
#  Normalization configuration
# ===================================================================


@dataclass(frozen=True)
class NormalizationConfig:
    """Configuration for the normalization passes."""

    _enable_expression_normalization: bool = True
    _enable_predicate_normalization: bool = True
    _enable_contract_normalization: bool = True
    _enable_fragment_classification: bool = True
    _enable_symbol_elimination: bool = True
    _enable_section_normalization: bool = True
    _prenex_conversion: bool = False

    @property
    def enable_expression_normalization(self) -> bool:
        return self._enable_expression_normalization

    @property
    def enable_predicate_normalization(self) -> bool:
        return self._enable_predicate_normalization

    @property
    def enable_contract_normalization(self) -> bool:
        return self._enable_contract_normalization

    @property
    def enable_fragment_classification(self) -> bool:
        return self._enable_fragment_classification

    @property
    def enable_symbol_elimination(self) -> bool:
        return self._enable_symbol_elimination

    @property
    def enable_section_normalization(self) -> bool:
        return self._enable_section_normalization

    @property
    def prenex_conversion(self) -> bool:
        return self._prenex_conversion


# ===================================================================
#  Incremental configuration
# ===================================================================


@dataclass(frozen=True)
class IncrementalConfig:
    """Configuration for incremental re-analysis."""

    _strategy: IncrementalStrategy = IncrementalStrategy.NONE
    _cache_dir: Optional[str] = None
    _max_cache_entries: int = 5000
    _invalidation_granularity: str = "function"
    _persist_between_runs: bool = False

    @property
    def strategy(self) -> IncrementalStrategy:
        return self._strategy

    @property
    def cache_dir(self) -> Optional[str]:
        return self._cache_dir

    @property
    def max_cache_entries(self) -> int:
        return self._max_cache_entries

    @property
    def invalidation_granularity(self) -> str:
        return self._invalidation_granularity

    @property
    def persist_between_runs(self) -> bool:
        return self._persist_between_runs

    @property
    def enabled(self) -> bool:
        return self._strategy is not IncrementalStrategy.NONE

    def effective_cache_dir(self) -> Path:
        if self._cache_dir is not None:
            return Path(self._cache_dir)
        return Path.cwd() / ".deppy_cache"


# ===================================================================
#  Stage filter configuration
# ===================================================================


@dataclass(frozen=True)
class StageFilterConfig:
    """Controls which stages run and in what order."""

    _skip_stages: FrozenSet[str] = frozenset()
    _only_stages: Optional[FrozenSet[str]] = None
    _custom_order: Optional[Tuple[str, ...]] = None

    @property
    def skip_stages(self) -> FrozenSet[str]:
        return self._skip_stages

    @property
    def only_stages(self) -> Optional[FrozenSet[str]]:
        return self._only_stages

    @property
    def custom_order(self) -> Optional[Tuple[str, ...]]:
        return self._custom_order

    def should_run(self, stage_name: str) -> bool:
        """Check if a stage should run given the filter configuration."""
        if stage_name in self._skip_stages:
            return False
        if self._only_stages is not None:
            return stage_name in self._only_stages
        return True


# ===================================================================
#  Main PipelineConfig
# ===================================================================


@dataclass(frozen=True)
class PipelineConfig:
    """Master configuration for the analysis pipeline.

    Aggregates theory-pack selection, iteration bounds, timeout policy,
    trust thresholds, output formatting, incremental mode, and verbosity.
    Immutable by design -- create new configs via ``with_*`` methods or
    ``replace()``.
    """

    _theory_packs: Tuple[TheoryPack, ...] = (
        TheoryPack.BUILTIN_ARITHMETIC,
        TheoryPack.BUILTIN_STRING,
        TheoryPack.BUILTIN_COLLECTION,
        TheoryPack.BUILTIN_NONE,
    )
    _max_iterations: int = 20
    _trust_threshold: TrustLevel = TrustLevel.RESIDUAL
    _output_format: OutputFormat = OutputFormat.TERMINAL
    _verbosity: Verbosity = Verbosity.NORMAL
    _timeout: TimeoutConfig = field(default_factory=TimeoutConfig)
    _solver: SolverConfig = field(default_factory=SolverConfig)
    _normalization: NormalizationConfig = field(default_factory=NormalizationConfig)
    _incremental: IncrementalConfig = field(default_factory=IncrementalConfig)
    _stage_filter: StageFilterConfig = field(default_factory=StageFilterConfig)
    _source_roots: Tuple[str, ...] = ()
    _target_files: Tuple[str, ...] = ()
    _exclude_patterns: Tuple[str, ...] = ("__pycache__", ".git", "*.pyc")
    _emit_contracts: bool = True
    _emit_diagnostics: bool = True
    _strict_mode: bool = False
    _color_output: bool = True
    _extra: Dict[str, Any] = field(default_factory=dict)

    # -- property accessors -----------------------------------------------

    @property
    def theory_packs(self) -> Tuple[TheoryPack, ...]:
        return self._theory_packs

    @property
    def max_iterations(self) -> int:
        return self._max_iterations

    @property
    def trust_threshold(self) -> TrustLevel:
        return self._trust_threshold

    @property
    def output_format(self) -> OutputFormat:
        return self._output_format

    @property
    def verbosity(self) -> Verbosity:
        return self._verbosity

    @property
    def timeout(self) -> TimeoutConfig:
        return self._timeout

    @property
    def solver(self) -> SolverConfig:
        return self._solver

    @property
    def normalization(self) -> NormalizationConfig:
        return self._normalization

    @property
    def incremental(self) -> IncrementalConfig:
        return self._incremental

    @property
    def stage_filter(self) -> StageFilterConfig:
        return self._stage_filter

    @property
    def source_roots(self) -> Tuple[str, ...]:
        return self._source_roots

    @property
    def target_files(self) -> Tuple[str, ...]:
        return self._target_files

    @property
    def exclude_patterns(self) -> Tuple[str, ...]:
        return self._exclude_patterns

    @property
    def emit_contracts(self) -> bool:
        return self._emit_contracts

    @property
    def emit_diagnostics(self) -> bool:
        return self._emit_diagnostics

    @property
    def strict_mode(self) -> bool:
        return self._strict_mode

    @property
    def color_output(self) -> bool:
        return self._color_output

    @property
    def extra(self) -> Dict[str, Any]:
        return dict(self._extra)

    @property
    def verbose(self) -> bool:
        return self._verbosity.value >= Verbosity.VERBOSE.value

    # -- builder methods --------------------------------------------------

    def with_theory_packs(self, packs: Sequence[TheoryPack]) -> PipelineConfig:
        return PipelineConfig(
            _theory_packs=tuple(packs),
            _max_iterations=self._max_iterations,
            _trust_threshold=self._trust_threshold,
            _output_format=self._output_format,
            _verbosity=self._verbosity,
            _timeout=self._timeout,
            _solver=self._solver,
            _normalization=self._normalization,
            _incremental=self._incremental,
            _stage_filter=self._stage_filter,
            _source_roots=self._source_roots,
            _target_files=self._target_files,
            _exclude_patterns=self._exclude_patterns,
            _emit_contracts=self._emit_contracts,
            _emit_diagnostics=self._emit_diagnostics,
            _strict_mode=self._strict_mode,
            _color_output=self._color_output,
            _extra=self._extra,
        )

    def with_max_iterations(self, n: int) -> PipelineConfig:
        return PipelineConfig(
            _theory_packs=self._theory_packs,
            _max_iterations=n,
            _trust_threshold=self._trust_threshold,
            _output_format=self._output_format,
            _verbosity=self._verbosity,
            _timeout=self._timeout,
            _solver=self._solver,
            _normalization=self._normalization,
            _incremental=self._incremental,
            _stage_filter=self._stage_filter,
            _source_roots=self._source_roots,
            _target_files=self._target_files,
            _exclude_patterns=self._exclude_patterns,
            _emit_contracts=self._emit_contracts,
            _emit_diagnostics=self._emit_diagnostics,
            _strict_mode=self._strict_mode,
            _color_output=self._color_output,
            _extra=self._extra,
        )

    def with_output_format(self, fmt: OutputFormat) -> PipelineConfig:
        return PipelineConfig(
            _theory_packs=self._theory_packs,
            _max_iterations=self._max_iterations,
            _trust_threshold=self._trust_threshold,
            _output_format=fmt,
            _verbosity=self._verbosity,
            _timeout=self._timeout,
            _solver=self._solver,
            _normalization=self._normalization,
            _incremental=self._incremental,
            _stage_filter=self._stage_filter,
            _source_roots=self._source_roots,
            _target_files=self._target_files,
            _exclude_patterns=self._exclude_patterns,
            _emit_contracts=self._emit_contracts,
            _emit_diagnostics=self._emit_diagnostics,
            _strict_mode=self._strict_mode,
            _color_output=self._color_output,
            _extra=self._extra,
        )

    def with_verbosity(self, v: Verbosity) -> PipelineConfig:
        return PipelineConfig(
            _theory_packs=self._theory_packs,
            _max_iterations=self._max_iterations,
            _trust_threshold=self._trust_threshold,
            _output_format=self._output_format,
            _verbosity=v,
            _timeout=self._timeout,
            _solver=self._solver,
            _normalization=self._normalization,
            _incremental=self._incremental,
            _stage_filter=self._stage_filter,
            _source_roots=self._source_roots,
            _target_files=self._target_files,
            _exclude_patterns=self._exclude_patterns,
            _emit_contracts=self._emit_contracts,
            _emit_diagnostics=self._emit_diagnostics,
            _strict_mode=self._strict_mode,
            _color_output=self._color_output,
            _extra=self._extra,
        )

    def with_strict_mode(self, strict: bool) -> PipelineConfig:
        return PipelineConfig(
            _theory_packs=self._theory_packs,
            _max_iterations=self._max_iterations,
            _trust_threshold=self._trust_threshold,
            _output_format=self._output_format,
            _verbosity=self._verbosity,
            _timeout=self._timeout,
            _solver=self._solver,
            _normalization=self._normalization,
            _incremental=self._incremental,
            _stage_filter=self._stage_filter,
            _source_roots=self._source_roots,
            _target_files=self._target_files,
            _exclude_patterns=self._exclude_patterns,
            _emit_contracts=self._emit_contracts,
            _emit_diagnostics=self._emit_diagnostics,
            _strict_mode=strict,
            _color_output=self._color_output,
            _extra=self._extra,
        )

    def with_source_roots(self, roots: Sequence[str]) -> PipelineConfig:
        return PipelineConfig(
            _theory_packs=self._theory_packs,
            _max_iterations=self._max_iterations,
            _trust_threshold=self._trust_threshold,
            _output_format=self._output_format,
            _verbosity=self._verbosity,
            _timeout=self._timeout,
            _solver=self._solver,
            _normalization=self._normalization,
            _incremental=self._incremental,
            _stage_filter=self._stage_filter,
            _source_roots=tuple(roots),
            _target_files=self._target_files,
            _exclude_patterns=self._exclude_patterns,
            _emit_contracts=self._emit_contracts,
            _emit_diagnostics=self._emit_diagnostics,
            _strict_mode=self._strict_mode,
            _color_output=self._color_output,
            _extra=self._extra,
        )

    def with_target_files(self, files: Sequence[str]) -> PipelineConfig:
        return PipelineConfig(
            _theory_packs=self._theory_packs,
            _max_iterations=self._max_iterations,
            _trust_threshold=self._trust_threshold,
            _output_format=self._output_format,
            _verbosity=self._verbosity,
            _timeout=self._timeout,
            _solver=self._solver,
            _normalization=self._normalization,
            _incremental=self._incremental,
            _stage_filter=self._stage_filter,
            _source_roots=self._source_roots,
            _target_files=tuple(files),
            _exclude_patterns=self._exclude_patterns,
            _emit_contracts=self._emit_contracts,
            _emit_diagnostics=self._emit_diagnostics,
            _strict_mode=self._strict_mode,
            _color_output=self._color_output,
            _extra=self._extra,
        )

    # -- factories --------------------------------------------------------

    @classmethod
    def default(cls) -> PipelineConfig:
        """Return a sensible default configuration."""
        return cls()

    @classmethod
    def strict(cls) -> PipelineConfig:
        """Return a strict-mode configuration for CI use."""
        return cls(
            _strict_mode=True,
            _trust_threshold=TrustLevel.TRUSTED_AUTO,
            _output_format=OutputFormat.JSON,
            _color_output=False,
            _verbosity=Verbosity.QUIET,
        )

    @classmethod
    def development(cls) -> PipelineConfig:
        """Return a development-friendly configuration."""
        return cls(
            _verbosity=Verbosity.VERBOSE,
            _strict_mode=False,
            _color_output=True,
            _incremental=IncrementalConfig(
                _strategy=IncrementalStrategy.FUNCTION_LEVEL,
            ),
        )

    @classmethod
    def from_dict(cls, data: Mapping[str, Any]) -> PipelineConfig:
        """Build a PipelineConfig from a flat dictionary.

        Keys correspond to parameter names without the leading underscore.
        """
        theory_packs_raw = data.get("theory_packs", None)
        theory_packs: Optional[Tuple[TheoryPack, ...]] = None
        if theory_packs_raw is not None:
            theory_packs = tuple(
                TheoryPack(t) if isinstance(t, str) else t
                for t in theory_packs_raw
            )

        output_fmt_raw = data.get("output_format", None)
        output_fmt: Optional[OutputFormat] = None
        if output_fmt_raw is not None:
            output_fmt = OutputFormat(output_fmt_raw) if isinstance(output_fmt_raw, str) else output_fmt_raw

        verbosity_raw = data.get("verbosity", None)
        verbosity: Optional[Verbosity] = None
        if verbosity_raw is not None:
            if isinstance(verbosity_raw, int):
                verbosity = Verbosity(verbosity_raw)
            elif isinstance(verbosity_raw, str):
                verbosity = Verbosity[verbosity_raw.upper()]
            else:
                verbosity = verbosity_raw

        trust_raw = data.get("trust_threshold", None)
        trust: Optional[TrustLevel] = None
        if trust_raw is not None:
            trust = TrustLevel(trust_raw) if isinstance(trust_raw, str) else trust_raw

        timeout_data = data.get("timeout", {})
        timeout_config = TimeoutConfig(
            _per_site=timeout_data.get("per_site", 5.0),
            _per_stage=timeout_data.get("per_stage", 30.0),
            _total=timeout_data.get("total", 120.0),
            _solver=timeout_data.get("solver", 10.0),
        )

        incremental_data = data.get("incremental", {})
        strategy_raw = incremental_data.get("strategy", "none")
        incremental_config = IncrementalConfig(
            _strategy=IncrementalStrategy(strategy_raw) if isinstance(strategy_raw, str) else strategy_raw,
            _cache_dir=incremental_data.get("cache_dir", None),
            _max_cache_entries=incremental_data.get("max_cache_entries", 5000),
            _persist_between_runs=incremental_data.get("persist_between_runs", False),
        )

        return cls(
            _theory_packs=theory_packs or cls._theory_packs,
            _max_iterations=data.get("max_iterations", 20),
            _trust_threshold=trust or TrustLevel.RESIDUAL,
            _output_format=output_fmt or OutputFormat.TERMINAL,
            _verbosity=verbosity or Verbosity.NORMAL,
            _timeout=timeout_config,
            _incremental=incremental_config,
            _source_roots=tuple(data.get("source_roots", ())),
            _target_files=tuple(data.get("target_files", ())),
            _exclude_patterns=tuple(data.get("exclude_patterns", ("__pycache__", ".git", "*.pyc"))),
            _emit_contracts=data.get("emit_contracts", True),
            _emit_diagnostics=data.get("emit_diagnostics", True),
            _strict_mode=data.get("strict_mode", False),
            _color_output=data.get("color_output", True),
            _extra=dict(data.get("extra", {})),
        )

    def to_dict(self) -> Dict[str, Any]:
        """Serialize configuration to a flat dictionary."""
        return {
            "theory_packs": [tp.value for tp in self._theory_packs],
            "max_iterations": self._max_iterations,
            "trust_threshold": self._trust_threshold.value,
            "output_format": self._output_format.value,
            "verbosity": self._verbosity.value,
            "timeout": {
                "per_site": self._timeout.per_site,
                "per_stage": self._timeout.per_stage,
                "total": self._timeout.total,
                "solver": self._timeout.solver,
            },
            "incremental": {
                "strategy": self._incremental.strategy.value,
                "cache_dir": self._incremental.cache_dir,
                "max_cache_entries": self._incremental.max_cache_entries,
                "persist_between_runs": self._incremental.persist_between_runs,
            },
            "source_roots": list(self._source_roots),
            "target_files": list(self._target_files),
            "exclude_patterns": list(self._exclude_patterns),
            "emit_contracts": self._emit_contracts,
            "emit_diagnostics": self._emit_diagnostics,
            "strict_mode": self._strict_mode,
            "color_output": self._color_output,
            "extra": dict(self._extra),
        }

    def __repr__(self) -> str:
        return (
            f"PipelineConfig(packs={len(self._theory_packs)}, "
            f"iter={self._max_iterations}, "
            f"strict={self._strict_mode}, "
            f"format={self._output_format.value})"
        )
