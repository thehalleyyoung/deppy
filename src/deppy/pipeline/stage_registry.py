"""Stage registration and ordering for the analysis pipeline.

The StageRegistry manages the lifecycle of pipeline stages: registration,
dependency ordering, topological sorting, and selective execution based
on PipelineConfig filters.
"""

from __future__ import annotations

import enum
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
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
    Type,
)

from deppy.pipeline.pipeline_config import PipelineConfig


# ===================================================================
#  Stage protocol
# ===================================================================


class StageStatus(enum.Enum):
    """Execution status of a pipeline stage."""

    PENDING = "pending"
    RUNNING = "running"
    COMPLETED = "completed"
    SKIPPED = "skipped"
    FAILED = "failed"


@dataclass(frozen=True)
class StageTiming:
    """Timing information for a completed stage."""

    _stage_name: str
    _start_time: float
    _end_time: float
    _status: StageStatus

    @property
    def stage_name(self) -> str:
        return self._stage_name

    @property
    def start_time(self) -> float:
        return self._start_time

    @property
    def end_time(self) -> float:
        return self._end_time

    @property
    def status(self) -> StageStatus:
        return self._status

    @property
    def elapsed_seconds(self) -> float:
        return self._end_time - self._start_time

    def __repr__(self) -> str:
        return (
            f"StageTiming({self._stage_name}, "
            f"{self.elapsed_seconds:.3f}s, "
            f"{self._status.value})"
        )


@dataclass(frozen=True)
class StageMetadata:
    """Metadata describing a pipeline stage."""

    _name: str
    _description: str
    _dependencies: FrozenSet[str]
    _optional: bool = False
    _order_hint: int = 0

    @property
    def name(self) -> str:
        return self._name

    @property
    def description(self) -> str:
        return self._description

    @property
    def dependencies(self) -> FrozenSet[str]:
        return self._dependencies

    @property
    def optional(self) -> bool:
        return self._optional

    @property
    def order_hint(self) -> int:
        return self._order_hint


class Stage(ABC):
    """Abstract base for all pipeline stages.

    Each stage declares its name, dependencies, and provides a ``run``
    method that accepts the pipeline context and returns a result.
    """

    @abstractmethod
    def metadata(self) -> StageMetadata:
        """Return metadata for this stage."""
        ...

    @abstractmethod
    def run(self, context: Dict[str, Any], config: PipelineConfig) -> Any:
        """Execute the stage given accumulated context from prior stages.

        Parameters
        ----------
        context : dict
            Mutable dictionary carrying results from earlier stages.
            Each stage may read from and write to this context.
        config : PipelineConfig
            The pipeline configuration.

        Returns
        -------
        Any
            The stage-specific result, also stored in ``context``.
        """
        ...


# ===================================================================
#  StageRegistry
# ===================================================================


class StageRegistry:
    """Registry managing pipeline stage registration and ordering.

    Stages are registered with their metadata (name, dependencies, etc.)
    and the registry provides topologically sorted execution plans.
    """

    def __init__(self) -> None:
        self._stages: Dict[str, Stage] = {}
        self._metadata: Dict[str, StageMetadata] = {}
        self._custom_order: Optional[List[str]] = None
        self._timings: List[StageTiming] = []

    # -- registration -----------------------------------------------------

    def register(self, stage: Stage) -> None:
        """Register a stage with the registry.

        Raises ValueError if a stage with the same name already exists.
        """
        meta = stage.metadata()
        if meta.name in self._stages:
            raise ValueError(
                f"Stage '{meta.name}' is already registered"
            )
        self._stages[meta.name] = stage
        self._metadata[meta.name] = meta

    def unregister(self, name: str) -> None:
        """Remove a stage from the registry."""
        self._stages.pop(name, None)
        self._metadata.pop(name, None)

    def has_stage(self, name: str) -> bool:
        """Check if a stage is registered."""
        return name in self._stages

    def get_stage(self, name: str) -> Optional[Stage]:
        """Look up a stage by name."""
        return self._stages.get(name)

    def get_metadata(self, name: str) -> Optional[StageMetadata]:
        """Look up stage metadata by name."""
        return self._metadata.get(name)

    # -- ordering ---------------------------------------------------------

    def get_stages(self) -> List[Stage]:
        """Return stages in topologically sorted execution order.

        If a custom order was set via ``reorder()``, use that instead.
        Falls back to topological sort based on declared dependencies.
        """
        if self._custom_order is not None:
            result: List[Stage] = []
            for name in self._custom_order:
                stage = self._stages.get(name)
                if stage is not None:
                    result.append(stage)
            return result
        return self._topological_sort()

    def get_stage_names(self) -> List[str]:
        """Return stage names in execution order."""
        return [s.metadata().name for s in self.get_stages()]

    def reorder(self, stage_names: Sequence[str]) -> None:
        """Override the default topological order with a custom sequence.

        Only stages present in *stage_names* will be included in the
        execution plan. To reset to topological order, call
        ``reset_order()``.
        """
        for name in stage_names:
            if name not in self._stages:
                raise ValueError(
                    f"Unknown stage '{name}'. "
                    f"Registered stages: {sorted(self._stages.keys())}"
                )
        self._custom_order = list(stage_names)

    def reset_order(self) -> None:
        """Reset to default topological ordering."""
        self._custom_order = None

    def _topological_sort(self) -> List[Stage]:
        """Kahn's algorithm for topological sort based on dependencies."""
        in_degree: Dict[str, int] = {name: 0 for name in self._stages}
        adjacency: Dict[str, List[str]] = {name: [] for name in self._stages}

        for name, meta in self._metadata.items():
            for dep in meta.dependencies:
                if dep in self._stages:
                    adjacency[dep].append(name)
                    in_degree[name] += 1

        # Break ties using order_hint for deterministic output
        queue: List[str] = sorted(
            [n for n, d in in_degree.items() if d == 0],
            key=lambda n: self._metadata[n].order_hint,
        )
        result: List[str] = []

        while queue:
            current = queue.pop(0)
            result.append(current)
            for neighbor in sorted(adjacency[current]):
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    # Insert sorted by order_hint to maintain determinism
                    inserted = False
                    hint = self._metadata[neighbor].order_hint
                    for i, q_item in enumerate(queue):
                        if self._metadata[q_item].order_hint > hint:
                            queue.insert(i, neighbor)
                            inserted = True
                            break
                    if not inserted:
                        queue.append(neighbor)

        if len(result) != len(self._stages):
            missing = set(self._stages.keys()) - set(result)
            raise ValueError(
                f"Dependency cycle detected involving stages: {missing}"
            )

        return [self._stages[name] for name in result]

    # -- execution --------------------------------------------------------

    def execute_all(
        self,
        config: PipelineConfig,
        initial_context: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        """Execute all stages in order, threading context between them.

        Returns the final accumulated context dictionary.
        """
        context = dict(initial_context) if initial_context else {}
        self._timings = []

        for stage in self.get_stages():
            meta = stage.metadata()

            if not config.stage_filter.should_run(meta.name):
                self._timings.append(StageTiming(
                    _stage_name=meta.name,
                    _start_time=time.monotonic(),
                    _end_time=time.monotonic(),
                    _status=StageStatus.SKIPPED,
                ))
                continue

            start = time.monotonic()
            status = StageStatus.RUNNING
            try:
                result = stage.run(context, config)
                context[meta.name] = result
                status = StageStatus.COMPLETED
            except Exception as exc:
                context[f"{meta.name}_error"] = str(exc)
                status = StageStatus.FAILED
                if config.strict_mode:
                    raise
            finally:
                end = time.monotonic()
                self._timings.append(StageTiming(
                    _stage_name=meta.name,
                    _start_time=start,
                    _end_time=end,
                    _status=status,
                ))

        return context

    # -- inspection -------------------------------------------------------

    @property
    def timings(self) -> List[StageTiming]:
        """Timing data from the most recent ``execute_all`` run."""
        return list(self._timings)

    @property
    def total_elapsed(self) -> float:
        """Total wall-clock time across all stages."""
        if not self._timings:
            return 0.0
        return sum(t.elapsed_seconds for t in self._timings)

    def dependency_graph(self) -> Dict[str, FrozenSet[str]]:
        """Return the dependency graph as {stage_name: frozenset(deps)}."""
        return {
            name: meta.dependencies
            for name, meta in self._metadata.items()
        }

    def validate(self) -> List[str]:
        """Validate the registry configuration.

        Returns a list of warnings/errors (empty if valid).
        """
        issues: List[str] = []

        for name, meta in self._metadata.items():
            for dep in meta.dependencies:
                if dep not in self._stages:
                    issues.append(
                        f"Stage '{name}' depends on unregistered stage '{dep}'"
                    )

        # Check for cycles
        try:
            self._topological_sort()
        except ValueError as exc:
            issues.append(str(exc))

        return issues

    def summary(self) -> str:
        """Return a human-readable summary of the registry."""
        lines: List[str] = ["StageRegistry:"]
        for stage in self.get_stages():
            meta = stage.metadata()
            deps = ", ".join(sorted(meta.dependencies)) if meta.dependencies else "none"
            lines.append(f"  [{meta.order_hint:02d}] {meta.name} (deps: {deps})")
        if self._timings:
            lines.append(f"  Last run: {self.total_elapsed:.3f}s total")
        return "\n".join(lines)

    def __repr__(self) -> str:
        return f"StageRegistry(stages={sorted(self._stages.keys())})"

    def __len__(self) -> int:
        return len(self._stages)
