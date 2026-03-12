"""Select representative traces for maximal coverage.

Given a collection of :class:`ParsedTrace` objects from multiple runs,
this module selects a minimal subset that covers the full range of
observed behaviours.  The goal is to retain enough traces to back
:class:`LocalSection` objects with high confidence while discarding
redundant runs.

Coverage criteria
-----------------
1. **Type diversity** -- every observed type must appear in at least
   one selected trace.
2. **Branch coverage** -- every observed branch polarity (true/false)
   must be represented.
3. **Shape diversity** -- every observed tensor shape must appear.
4. **Exception coverage** -- every observed exception type must be
   represented.
5. **Parameter variation** -- distinct parameter type combinations
   should be covered.

The selection algorithm is a greedy set-cover: repeatedly pick the
trace that covers the most uncovered criteria until all are met.
"""

from __future__ import annotations

import enum
from collections import defaultdict
from dataclasses import dataclass, field
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
)

from deppy.observe.trace_parser import (
    BranchObservation,
    ExceptionObservation,
    FunctionObservation,
    ObservedType,
    ParsedTrace,
    VariableObservation,
)


# ---------------------------------------------------------------------------
# Coverage criteria
# ---------------------------------------------------------------------------

class CriterionKind(enum.Enum):
    """Classification of coverage criteria."""
    TYPE = "type"
    SHAPE = "shape"
    BRANCH_TRUE = "branch_true"
    BRANCH_FALSE = "branch_false"
    EXCEPTION = "exception"
    DTYPE = "dtype"
    LENGTH = "length"
    PARAMETER_COMBO = "parameter_combo"
    RETURN_TYPE = "return_type"


@dataclass(frozen=True)
class CoverageCriterion:
    """A single coverage requirement.

    Attributes
    ----------
    kind : CriterionKind
        What aspect of behaviour this criterion represents.
    key : str
        A unique identifier within its kind (e.g. type name, branch id).
    description : str
        Human-readable explanation.
    weight : float
        Relative importance (higher = more important to cover).
    """

    kind: CriterionKind
    key: str
    description: str = ""
    weight: float = 1.0

    def __hash__(self) -> int:
        return hash((self.kind, self.key))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CoverageCriterion):
            return NotImplemented
        return self.kind == other.kind and self.key == other.key


# ---------------------------------------------------------------------------
# Coverage extraction
# ---------------------------------------------------------------------------

def _extract_criteria(trace: ParsedTrace) -> FrozenSet[CoverageCriterion]:
    """Extract all coverage criteria satisfied by a single trace."""
    criteria: Set[CoverageCriterion] = set()

    for fo in trace.function_observations:
        # Type diversity
        for vo in fo.variables:
            for ot in vo.observed_types:
                criteria.add(CoverageCriterion(
                    kind=CriterionKind.TYPE,
                    key=f"{fo.function}:{vo.variable}:{ot.type_name}",
                    description=f"type {ot.type_name} for {vo.variable} in {fo.function}",
                ))
                # Shape diversity
                for shape in ot.shapes:
                    criteria.add(CoverageCriterion(
                        kind=CriterionKind.SHAPE,
                        key=f"{fo.function}:{vo.variable}:{shape}",
                        description=f"shape {shape} for {vo.variable} in {fo.function}",
                        weight=1.5,
                    ))
                # Dtype diversity
                for dtype in ot.dtypes:
                    criteria.add(CoverageCriterion(
                        kind=CriterionKind.DTYPE,
                        key=f"{fo.function}:{vo.variable}:{dtype}",
                        description=f"dtype {dtype} for {vo.variable}",
                    ))
                # Length diversity
                for length in ot.lengths:
                    criteria.add(CoverageCriterion(
                        kind=CriterionKind.LENGTH,
                        key=f"{fo.function}:{vo.variable}:len={length}",
                        description=f"length {length} for {vo.variable}",
                        weight=0.5,
                    ))

        # Parameter type combinations
        if fo.parameter_observations:
            param_types = tuple(
                (po.variable, po.dominant_type.type_name if po.dominant_type else "Any")
                for po in fo.parameter_observations
            )
            combo_key = f"{fo.function}:params:{param_types}"
            criteria.add(CoverageCriterion(
                kind=CriterionKind.PARAMETER_COMBO,
                key=combo_key,
                description=f"parameter combo for {fo.function}",
                weight=2.0,
            ))

        # Return type
        if fo.return_observation and fo.return_observation.dominant_type:
            criteria.add(CoverageCriterion(
                kind=CriterionKind.RETURN_TYPE,
                key=f"{fo.function}:return:{fo.return_observation.dominant_type.type_name}",
                description=f"return type for {fo.function}",
                weight=1.5,
            ))

        # Branch coverage
        for bo in fo.branches:
            loc_key = f"{bo.location[0]}:{bo.location[1]}:{bo.location[2]}"
            if bo.true_count > 0:
                criteria.add(CoverageCriterion(
                    kind=CriterionKind.BRANCH_TRUE,
                    key=f"{fo.function}:branch_true:{loc_key}",
                    description=f"branch true at {loc_key} in {fo.function}",
                    weight=2.0,
                ))
            if bo.false_count > 0:
                criteria.add(CoverageCriterion(
                    kind=CriterionKind.BRANCH_FALSE,
                    key=f"{fo.function}:branch_false:{loc_key}",
                    description=f"branch false at {loc_key} in {fo.function}",
                    weight=2.0,
                ))

        # Exception coverage
        for eo in fo.exceptions:
            criteria.add(CoverageCriterion(
                kind=CriterionKind.EXCEPTION,
                key=f"{fo.function}:exc:{eo.exception_type}",
                description=f"exception {eo.exception_type} in {fo.function}",
                weight=3.0,
            ))

    return frozenset(criteria)


# ---------------------------------------------------------------------------
# Coverage report
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CoverageReport:
    """Summary of coverage achieved by a set of traces.

    Attributes
    ----------
    total_criteria : int
        Total number of coverage criteria identified.
    covered_criteria : int
        Number of criteria covered by the selected traces.
    uncovered : FrozenSet[CoverageCriterion]
        Criteria that remain uncovered.
    coverage_ratio : float
        ``covered / total`` (0.0 -- 1.0).
    criteria_by_kind : Dict[CriterionKind, int]
        Count of criteria per kind.
    covered_by_kind : Dict[CriterionKind, int]
        Count of covered criteria per kind.
    selected_count : int
        Number of traces selected.
    original_count : int
        Number of traces in the input pool.
    """

    total_criteria: int = 0
    covered_criteria: int = 0
    uncovered: FrozenSet[CoverageCriterion] = frozenset()
    coverage_ratio: float = 0.0
    criteria_by_kind: Tuple[Tuple[str, int], ...] = ()
    covered_by_kind: Tuple[Tuple[str, int], ...] = ()
    selected_count: int = 0
    original_count: int = 0

    @property
    def is_complete(self) -> bool:
        return self.coverage_ratio >= 1.0

    @property
    def criteria_by_kind_dict(self) -> Dict[str, int]:
        return dict(self.criteria_by_kind)

    @property
    def covered_by_kind_dict(self) -> Dict[str, int]:
        return dict(self.covered_by_kind)


# ---------------------------------------------------------------------------
# SelectionResult
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SelectionResult:
    """Result of representative selection.

    Attributes
    ----------
    selected : Tuple[ParsedTrace, ...]
        The selected representative traces.
    report : CoverageReport
        Coverage statistics.
    selection_order : Tuple[int, ...]
        Indices into the original trace list, in the order they were selected.
    per_trace_criteria : Tuple[Tuple[int, int], ...]
        ``(trace_index, criteria_covered)`` for each selected trace.
    """

    selected: Tuple[ParsedTrace, ...] = ()
    report: CoverageReport = field(default_factory=CoverageReport)
    selection_order: Tuple[int, ...] = ()
    per_trace_criteria: Tuple[Tuple[int, int], ...] = ()


# ---------------------------------------------------------------------------
# RepresentativeSelector
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SelectionConfig:
    """Configuration for the representative selector.

    Attributes
    ----------
    max_representatives : int
        Upper bound on how many traces to select.
    min_coverage : float
        Stop early if this coverage ratio is reached (0.0 -- 1.0).
    include_failing : bool
        Whether to include traces that raised exceptions.
    weight_branches : float
        Multiplier for branch coverage criteria weights.
    weight_shapes : float
        Multiplier for shape coverage criteria weights.
    weight_types : float
        Multiplier for type coverage criteria weights.
    weight_exceptions : float
        Multiplier for exception coverage criteria weights.
    """

    max_representatives: int = 20
    min_coverage: float = 1.0
    include_failing: bool = True
    weight_branches: float = 1.0
    weight_shapes: float = 1.0
    weight_types: float = 1.0
    weight_exceptions: float = 1.0


_DEFAULT_SELECTION_CONFIG = SelectionConfig()


class RepresentativeSelector:
    """Selects a minimal set of traces covering all observed behaviours.

    Uses a weighted greedy set-cover algorithm.

    Parameters
    ----------
    config : SelectionConfig
        Configuration controlling the selection process.
    """

    def __init__(
        self,
        config: SelectionConfig = _DEFAULT_SELECTION_CONFIG,
    ) -> None:
        self._config = config

    @property
    def config(self) -> SelectionConfig:
        return self._config

    def select(
        self,
        traces: Sequence[ParsedTrace],
    ) -> SelectionResult:
        """Select representative traces from the pool.

        Parameters
        ----------
        traces : Sequence[ParsedTrace]
            The full pool of parsed traces.

        Returns
        -------
        SelectionResult
            The selected subset with coverage report.
        """
        if not traces:
            return SelectionResult()

        # Filter out failing traces if configured
        candidates: List[Tuple[int, ParsedTrace]] = []
        for i, trace in enumerate(traces):
            if not self._config.include_failing and not trace.succeeded:
                continue
            candidates.append((i, trace))

        if not candidates:
            return SelectionResult()

        # Extract criteria for each candidate
        criteria_map: Dict[int, FrozenSet[CoverageCriterion]] = {}
        all_criteria: Set[CoverageCriterion] = set()
        for idx, trace in candidates:
            criteria = _extract_criteria(trace)
            # Apply weight multipliers
            adjusted: Set[CoverageCriterion] = set()
            for c in criteria:
                weight = c.weight
                if c.kind in (CriterionKind.BRANCH_TRUE, CriterionKind.BRANCH_FALSE):
                    weight *= self._config.weight_branches
                elif c.kind == CriterionKind.SHAPE:
                    weight *= self._config.weight_shapes
                elif c.kind == CriterionKind.TYPE:
                    weight *= self._config.weight_types
                elif c.kind == CriterionKind.EXCEPTION:
                    weight *= self._config.weight_exceptions
                adjusted.add(CoverageCriterion(
                    kind=c.kind,
                    key=c.key,
                    description=c.description,
                    weight=weight,
                ))
            criteria_map[idx] = frozenset(adjusted)
            all_criteria.update(adjusted)

        if not all_criteria:
            # No criteria to cover -- just return the first trace
            return SelectionResult(
                selected=(candidates[0][1],),
                report=CoverageReport(
                    total_criteria=0,
                    covered_criteria=0,
                    coverage_ratio=1.0,
                    selected_count=1,
                    original_count=len(traces),
                ),
                selection_order=(candidates[0][0],),
                per_trace_criteria=((candidates[0][0], 0),),
            )

        # Greedy set-cover
        uncovered = set(all_criteria)
        selected_indices: List[int] = []
        per_trace: List[Tuple[int, int]] = []

        remaining = set(criteria_map.keys())
        while uncovered and len(selected_indices) < self._config.max_representatives and remaining:
            # Pick the candidate covering the most weighted uncovered criteria
            best_idx = -1
            best_score = -1.0
            best_newly_covered = 0

            for idx in remaining:
                crit = criteria_map[idx]
                newly_covered = crit & uncovered
                score = sum(c.weight for c in newly_covered)
                if score > best_score:
                    best_score = score
                    best_idx = idx
                    best_newly_covered = len(newly_covered)

            if best_idx < 0 or best_score <= 0:
                break

            selected_indices.append(best_idx)
            per_trace.append((best_idx, best_newly_covered))
            uncovered -= criteria_map[best_idx]
            remaining.discard(best_idx)

            # Check early stopping
            covered_count = len(all_criteria) - len(uncovered)
            ratio = covered_count / len(all_criteria) if all_criteria else 1.0
            if ratio >= self._config.min_coverage:
                break

        # Build report
        covered_count = len(all_criteria) - len(uncovered)
        ratio = covered_count / len(all_criteria) if all_criteria else 1.0

        criteria_by_kind: Dict[str, int] = {}
        covered_by_kind: Dict[str, int] = {}
        for c in all_criteria:
            k = c.kind.value
            criteria_by_kind[k] = criteria_by_kind.get(k, 0) + 1
        covered_criteria_set = all_criteria - uncovered
        for c in covered_criteria_set:
            k = c.kind.value
            covered_by_kind[k] = covered_by_kind.get(k, 0) + 1

        report = CoverageReport(
            total_criteria=len(all_criteria),
            covered_criteria=covered_count,
            uncovered=frozenset(uncovered),
            coverage_ratio=ratio,
            criteria_by_kind=tuple(sorted(criteria_by_kind.items())),
            covered_by_kind=tuple(sorted(covered_by_kind.items())),
            selected_count=len(selected_indices),
            original_count=len(traces),
        )

        # Resolve selected traces
        idx_to_trace = dict(candidates)
        selected_traces = tuple(
            idx_to_trace[idx] for idx in selected_indices
        )

        return SelectionResult(
            selected=selected_traces,
            report=report,
            selection_order=tuple(selected_indices),
            per_trace_criteria=tuple(per_trace),
        )


# ---------------------------------------------------------------------------
# Convenience function
# ---------------------------------------------------------------------------

def select_representatives(
    traces: Sequence[ParsedTrace],
    *,
    max_representatives: int = 20,
    min_coverage: float = 1.0,
    include_failing: bool = True,
) -> List[ParsedTrace]:
    """Select a minimal set of representative traces.

    This is a convenience wrapper around :class:`RepresentativeSelector`.

    Parameters
    ----------
    traces : Sequence[ParsedTrace]
        Pool of parsed traces.
    max_representatives : int
        Maximum traces to select.
    min_coverage : float
        Early-stop coverage threshold.
    include_failing : bool
        Whether to include failing traces.

    Returns
    -------
    List[ParsedTrace]
        The selected representatives.
    """
    config = SelectionConfig(
        max_representatives=max_representatives,
        min_coverage=min_coverage,
        include_failing=include_failing,
    )
    selector = RepresentativeSelector(config)
    result = selector.select(traces)
    return list(result.selected)


# ---------------------------------------------------------------------------
# Coverage analysis utilities
# ---------------------------------------------------------------------------

def compute_coverage(
    traces: Sequence[ParsedTrace],
) -> CoverageReport:
    """Compute coverage for a set of traces without selecting.

    Parameters
    ----------
    traces : Sequence[ParsedTrace]
        Traces to analyse.

    Returns
    -------
    CoverageReport
        The coverage statistics.
    """
    all_criteria: Set[CoverageCriterion] = set()
    for trace in traces:
        all_criteria.update(_extract_criteria(trace))

    if not all_criteria:
        return CoverageReport(
            coverage_ratio=1.0,
            original_count=len(traces),
        )

    criteria_by_kind: Dict[str, int] = {}
    for c in all_criteria:
        k = c.kind.value
        criteria_by_kind[k] = criteria_by_kind.get(k, 0) + 1

    return CoverageReport(
        total_criteria=len(all_criteria),
        covered_criteria=len(all_criteria),
        coverage_ratio=1.0,
        criteria_by_kind=tuple(sorted(criteria_by_kind.items())),
        covered_by_kind=tuple(sorted(criteria_by_kind.items())),
        selected_count=len(traces),
        original_count=len(traces),
    )


def find_coverage_gaps(
    traces: Sequence[ParsedTrace],
    reference_criteria: FrozenSet[CoverageCriterion],
) -> FrozenSet[CoverageCriterion]:
    """Identify criteria in *reference_criteria* not covered by *traces*.

    Parameters
    ----------
    traces : Sequence[ParsedTrace]
        Traces to check.
    reference_criteria : FrozenSet[CoverageCriterion]
        The full set of criteria to be covered.

    Returns
    -------
    FrozenSet[CoverageCriterion]
        Uncovered criteria.
    """
    covered: Set[CoverageCriterion] = set()
    for trace in traces:
        covered.update(_extract_criteria(trace))
    return frozenset(reference_criteria - covered)


def suggest_additional_inputs(
    gaps: FrozenSet[CoverageCriterion],
) -> List[Dict[str, Any]]:
    """Suggest input characteristics that would cover the given gaps.

    Returns a list of dicts describing what kind of input might fill
    each gap.  This is heuristic and intended for human guidance.

    Parameters
    ----------
    gaps : FrozenSet[CoverageCriterion]
        Uncovered criteria.

    Returns
    -------
    List[Dict[str, Any]]
        Suggestions for additional test inputs.
    """
    suggestions: List[Dict[str, Any]] = []
    for gap in sorted(gaps, key=lambda c: (-c.weight, c.key)):
        suggestion: Dict[str, Any] = {
            "criterion_kind": gap.kind.value,
            "criterion_key": gap.key,
            "description": gap.description,
            "priority": gap.weight,
        }
        if gap.kind == CriterionKind.BRANCH_TRUE:
            suggestion["hint"] = "Provide input that makes this branch condition True"
        elif gap.kind == CriterionKind.BRANCH_FALSE:
            suggestion["hint"] = "Provide input that makes this branch condition False"
        elif gap.kind == CriterionKind.SHAPE:
            suggestion["hint"] = "Provide a tensor/array with this specific shape"
        elif gap.kind == CriterionKind.TYPE:
            suggestion["hint"] = "Provide a value of this specific type"
        elif gap.kind == CriterionKind.EXCEPTION:
            suggestion["hint"] = "Provide input that triggers this exception"
        elif gap.kind == CriterionKind.PARAMETER_COMBO:
            suggestion["hint"] = "Provide this combination of parameter types"
        else:
            suggestion["hint"] = "Provide input exercising this behaviour"
        suggestions.append(suggestion)
    return suggestions
