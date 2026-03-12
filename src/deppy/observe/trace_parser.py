"""Parse trace logs into structured trace sections.

This module sits between the raw :class:`TraceLog` produced by
:mod:`deppy.observe.trace_recorder` and the sheaf-section converter
in :mod:`deppy.observe.trace_to_section`.  Its job is to organise
chronologically-ordered events into grouped, deduplicated, and
well-ordered data structures that downstream consumers can work with
efficiently.

The primary entry-point is :func:`parse_trace_log`.
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

from deppy.core._protocols import SiteId, SiteKind
from deppy.static_analysis.observation_sites import SourceSpan

from deppy.observe.trace_recorder import (
    EventKind,
    TraceEvent,
    TraceLog,
)


# ---------------------------------------------------------------------------
# Type-observation summary
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ObservedType:
    """Summary of a single observed Python type.

    Attributes
    ----------
    type_name : str
        Fully-qualified type name (e.g. ``"numpy.ndarray"``).
    count : int
        How many times this type was observed.
    shapes : Tuple[Tuple[int, ...], ...]
        Distinct tensor/array shapes seen for this type.
    dtypes : Tuple[str, ...]
        Distinct element dtypes seen.
    lengths : Tuple[int, ...]
        Distinct container lengths seen.
    sample_reprs : Tuple[str, ...]
        Up to 5 representative ``repr`` strings.
    """

    type_name: str
    count: int = 1
    shapes: Tuple[Tuple[int, ...], ...] = ()
    dtypes: Tuple[str, ...] = ()
    lengths: Tuple[int, ...] = ()
    sample_reprs: Tuple[str, ...] = ()

    @property
    def has_shape(self) -> bool:
        return len(self.shapes) > 0

    @property
    def is_tensor_like(self) -> bool:
        return self.has_shape or any(
            kw in self.type_name.lower()
            for kw in ("tensor", "ndarray", "array")
        )

    @property
    def unique_shape_count(self) -> int:
        return len(set(self.shapes))


# ---------------------------------------------------------------------------
# Variable observation
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class VariableObservation:
    """All observations for a single variable within a single function.

    Attributes
    ----------
    function : str
        Qualified function name.
    variable : str
        Variable name.
    observed_types : Tuple[ObservedType, ...]
        Distinct types observed for this variable.
    assignment_count : int
        Total number of assignment events.
    first_location : Optional[Tuple[str, int, int]]
        Source location of the first observation.
    last_location : Optional[Tuple[str, int, int]]
        Source location of the last observation.
    is_parameter : bool
        Whether this variable is a function parameter.
    is_return : bool
        Whether this captures return-value observations.
    sample_values : Tuple[str, ...]
        Up to 10 representative value reprs.
    """

    function: str
    variable: str
    observed_types: Tuple[ObservedType, ...] = ()
    assignment_count: int = 0
    first_location: Optional[Tuple[str, int, int]] = None
    last_location: Optional[Tuple[str, int, int]] = None
    is_parameter: bool = False
    is_return: bool = False
    sample_values: Tuple[str, ...] = ()

    @property
    def dominant_type(self) -> Optional[ObservedType]:
        """Return the most frequently observed type, or ``None``."""
        if not self.observed_types:
            return None
        return max(self.observed_types, key=lambda t: t.count)

    @property
    def is_monomorphic(self) -> bool:
        """True when exactly one type was observed."""
        return len(self.observed_types) == 1

    @property
    def is_polymorphic(self) -> bool:
        """True when more than one type was observed."""
        return len(self.observed_types) > 1

    @property
    def type_names(self) -> FrozenSet[str]:
        return frozenset(t.type_name for t in self.observed_types)

    @property
    def all_shapes(self) -> Tuple[Tuple[int, ...], ...]:
        shapes: List[Tuple[int, ...]] = []
        for t in self.observed_types:
            shapes.extend(t.shapes)
        return tuple(shapes)

    @property
    def source_span(self) -> Optional[SourceSpan]:
        if self.first_location is None:
            return None
        f, line, col = self.first_location
        return SourceSpan(file=f, start_line=line, start_col=col)


# ---------------------------------------------------------------------------
# Branch observation
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class BranchObservation:
    """Summary of a branch (if/elif/assert) observed at a location.

    Attributes
    ----------
    function : str
        Qualified function name.
    location : Tuple[str, int, int]
        Source location of the branch.
    true_count : int
        How many times the branch was taken (True).
    false_count : int
        How many times the branch was not taken (False).
    guard_repr : str
        Representative repr of the guard expression.
    """

    function: str
    location: Tuple[str, int, int]
    true_count: int = 0
    false_count: int = 0
    guard_repr: str = ""

    @property
    def total(self) -> int:
        return self.true_count + self.false_count

    @property
    def always_true(self) -> bool:
        return self.true_count > 0 and self.false_count == 0

    @property
    def always_false(self) -> bool:
        return self.false_count > 0 and self.true_count == 0

    @property
    def both_taken(self) -> bool:
        return self.true_count > 0 and self.false_count > 0


# ---------------------------------------------------------------------------
# Exception observation
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ExceptionObservation:
    """Summary of exceptions observed in a function.

    Attributes
    ----------
    function : str
        Qualified function name.
    exception_type : str
        Fully-qualified exception type name.
    count : int
        How many times this exception was raised.
    locations : Tuple[Tuple[str, int, int], ...]
        Source locations where the exception was observed.
    sample_messages : Tuple[str, ...]
        Up to 5 representative exception messages.
    """

    function: str
    exception_type: str
    count: int = 1
    locations: Tuple[Tuple[str, int, int], ...] = ()
    sample_messages: Tuple[str, ...] = ()


# ---------------------------------------------------------------------------
# Function observation
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class FunctionObservation:
    """All observations for a single function across the trace.

    Attributes
    ----------
    function : str
        Qualified function name.
    call_count : int
        How many times the function was called.
    variables : Tuple[VariableObservation, ...]
        Per-variable observations.
    branches : Tuple[BranchObservation, ...]
        Per-branch observations.
    exceptions : Tuple[ExceptionObservation, ...]
        Per-exception-type observations.
    return_observation : Optional[VariableObservation]
        Observation of return values.
    parameter_observations : Tuple[VariableObservation, ...]
        Observations of function parameters.
    max_depth : int
        Maximum call depth at which this function was observed.
    locations : Tuple[Tuple[str, int, int], ...]
        Source locations of call events.
    """

    function: str
    call_count: int = 0
    variables: Tuple[VariableObservation, ...] = ()
    branches: Tuple[BranchObservation, ...] = ()
    exceptions: Tuple[ExceptionObservation, ...] = ()
    return_observation: Optional[VariableObservation] = None
    parameter_observations: Tuple[VariableObservation, ...] = ()
    max_depth: int = 0
    locations: Tuple[Tuple[str, int, int], ...] = ()

    @property
    def variable_names(self) -> FrozenSet[str]:
        return frozenset(v.variable for v in self.variables)

    @property
    def parameter_names(self) -> FrozenSet[str]:
        return frozenset(v.variable for v in self.parameter_observations)

    @property
    def exception_types(self) -> FrozenSet[str]:
        return frozenset(e.exception_type for e in self.exceptions)

    @property
    def has_exceptions(self) -> bool:
        return len(self.exceptions) > 0

    @property
    def total_variable_assignments(self) -> int:
        return sum(v.assignment_count for v in self.variables)


# ---------------------------------------------------------------------------
# ParsedTrace -- the top-level result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ParsedTrace:
    """Structured, grouped, and deduplicated representation of a trace.

    This is the primary output of :func:`parse_trace_log`.

    Attributes
    ----------
    trace_id : str
        Inherited from the source :class:`TraceLog`.
    target_function : str
        The outermost function that was traced.
    function_observations : Tuple[FunctionObservation, ...]
        Per-function grouped observations.
    all_variables : Tuple[VariableObservation, ...]
        Flattened list of all variable observations.
    all_branches : Tuple[BranchObservation, ...]
        Flattened list of all branch observations.
    all_exceptions : Tuple[ExceptionObservation, ...]
        Flattened list of all exception observations.
    unique_types : FrozenSet[str]
        All distinct type names observed.
    unique_shapes : FrozenSet[Tuple[int, ...]]
        All distinct tensor/array shapes observed.
    duration : float
        Wall-clock duration of the trace.
    succeeded : bool
        Whether the trace completed without exception.
    event_count : int
        Total number of events in the source log.
    """

    trace_id: str
    target_function: str
    function_observations: Tuple[FunctionObservation, ...] = ()
    all_variables: Tuple[VariableObservation, ...] = ()
    all_branches: Tuple[BranchObservation, ...] = ()
    all_exceptions: Tuple[ExceptionObservation, ...] = ()
    unique_types: FrozenSet[str] = frozenset()
    unique_shapes: FrozenSet[Tuple[int, ...]] = frozenset()
    duration: float = 0.0
    succeeded: bool = True
    event_count: int = 0

    # Convenience ---------------------------------------------------------

    def observation_for_function(self, name: str) -> Optional[FunctionObservation]:
        """Look up a function observation by name (suffix match)."""
        for fo in self.function_observations:
            if fo.function == name or fo.function.endswith(f".{name}"):
                return fo
        return None

    def variable_observation(
        self, function: str, variable: str
    ) -> Optional[VariableObservation]:
        """Look up a specific variable observation."""
        fo = self.observation_for_function(function)
        if fo is None:
            return None
        for vo in fo.variables:
            if vo.variable == variable:
                return vo
        return None

    @property
    def function_names(self) -> FrozenSet[str]:
        return frozenset(fo.function for fo in self.function_observations)

    @property
    def total_call_count(self) -> int:
        return sum(fo.call_count for fo in self.function_observations)

    @property
    def total_branch_count(self) -> int:
        return sum(b.total for b in self.all_branches)

    @property
    def covered_branch_count(self) -> int:
        """Branches where both true and false were observed."""
        return sum(1 for b in self.all_branches if b.both_taken)


# ---------------------------------------------------------------------------
# Internal builder helpers
# ---------------------------------------------------------------------------

class _ObservedTypeBuilder:
    """Mutable accumulator for building an :class:`ObservedType`."""

    __slots__ = ("type_name", "count", "shapes", "dtypes", "lengths", "reprs")

    def __init__(self, type_name: str) -> None:
        self.type_name = type_name
        self.count = 0
        self.shapes: Set[Tuple[int, ...]] = set()
        self.dtypes: Set[str] = set()
        self.lengths: Set[int] = set()
        self.reprs: List[str] = []

    def add(self, event: TraceEvent) -> None:
        self.count += 1
        if event.shape is not None:
            self.shapes.add(event.shape)
        if event.dtype is not None:
            self.dtypes.add(event.dtype)
        if event.length is not None:
            self.lengths.add(event.length)
        if len(self.reprs) < 5:
            self.reprs.append(event.value_repr)

    def build(self) -> ObservedType:
        return ObservedType(
            type_name=self.type_name,
            count=self.count,
            shapes=tuple(sorted(self.shapes)),
            dtypes=tuple(sorted(self.dtypes)),
            lengths=tuple(sorted(self.lengths)),
            sample_reprs=tuple(self.reprs),
        )


class _VariableBuilder:
    """Mutable accumulator for building a :class:`VariableObservation`."""

    __slots__ = (
        "function", "variable", "type_builders", "count",
        "first_loc", "last_loc", "is_param", "is_return", "reprs",
    )

    def __init__(self, function: str, variable: str) -> None:
        self.function = function
        self.variable = variable
        self.type_builders: Dict[str, _ObservedTypeBuilder] = {}
        self.count = 0
        self.first_loc: Optional[Tuple[str, int, int]] = None
        self.last_loc: Optional[Tuple[str, int, int]] = None
        self.is_param = False
        self.is_return = False
        self.reprs: List[str] = []

    def add(self, event: TraceEvent) -> None:
        self.count += 1
        tname = event.value_type
        if tname not in self.type_builders:
            self.type_builders[tname] = _ObservedTypeBuilder(tname)
        self.type_builders[tname].add(event)
        if event.location is not None:
            if self.first_loc is None:
                self.first_loc = event.location
            self.last_loc = event.location
        if len(self.reprs) < 10:
            self.reprs.append(event.value_repr)

    def build(self) -> VariableObservation:
        return VariableObservation(
            function=self.function,
            variable=self.variable,
            observed_types=tuple(
                tb.build() for tb in sorted(
                    self.type_builders.values(),
                    key=lambda b: -b.count,
                )
            ),
            assignment_count=self.count,
            first_location=self.first_loc,
            last_location=self.last_loc,
            is_parameter=self.is_param,
            is_return=self.is_return,
            sample_values=tuple(self.reprs),
        )


# ---------------------------------------------------------------------------
# parse_trace_log
# ---------------------------------------------------------------------------

def parse_trace_log(trace_log: TraceLog) -> ParsedTrace:
    """Parse a :class:`TraceLog` into a :class:`ParsedTrace`.

    This performs:

    1. **Grouping** -- events are grouped by function name.
    2. **Variable aggregation** -- per-variable observations are assembled
       with type, shape, and dtype statistics.
    3. **Branch aggregation** -- branch events are grouped by location.
    4. **Exception aggregation** -- exception events are grouped by type.
    5. **Deduplication** -- redundant observations are collapsed.
    6. **Ordering** -- results are sorted by frequency and source location.

    Parameters
    ----------
    trace_log : TraceLog
        The raw trace log to parse.

    Returns
    -------
    ParsedTrace
        The structured, grouped trace.
    """
    # Group events by function
    func_events: Dict[str, List[TraceEvent]] = defaultdict(list)
    for event in trace_log.events:
        func_events[event.function].append(event)

    # Build per-function observations
    function_observations: List[FunctionObservation] = []
    all_variables: List[VariableObservation] = []
    all_branches: List[BranchObservation] = []
    all_exceptions: List[ExceptionObservation] = []
    all_types: Set[str] = set()
    all_shapes: Set[Tuple[int, ...]] = set()

    for func_name, events in func_events.items():
        fo = _build_function_observation(func_name, events)
        function_observations.append(fo)
        all_variables.extend(fo.variables)
        if fo.return_observation is not None:
            all_variables.append(fo.return_observation)
        all_variables.extend(fo.parameter_observations)
        all_branches.extend(fo.branches)
        all_exceptions.extend(fo.exceptions)
        for vo in fo.variables:
            for ot in vo.observed_types:
                all_types.add(ot.type_name)
                all_shapes.update(ot.shapes)

    # Sort function observations by call count (descending)
    function_observations.sort(key=lambda fo: -fo.call_count)

    return ParsedTrace(
        trace_id=trace_log.trace_id,
        target_function=trace_log.target_function,
        function_observations=tuple(function_observations),
        all_variables=tuple(all_variables),
        all_branches=tuple(all_branches),
        all_exceptions=tuple(all_exceptions),
        unique_types=frozenset(all_types),
        unique_shapes=frozenset(all_shapes),
        duration=trace_log.duration,
        succeeded=trace_log.succeeded,
        event_count=trace_log.event_count,
    )


def _build_function_observation(
    func_name: str,
    events: List[TraceEvent],
) -> FunctionObservation:
    """Build a :class:`FunctionObservation` from a list of events."""

    # Variable builders
    var_builders: Dict[str, _VariableBuilder] = {}
    return_builder: Optional[_VariableBuilder] = None
    param_builders: Dict[str, _VariableBuilder] = {}

    # Branch accumulators: keyed by location tuple
    branch_acc: Dict[Tuple[str, int, int], Dict[str, int]] = {}

    # Exception accumulators: keyed by exception type
    exc_acc: Dict[str, Dict[str, Any]] = {}

    call_count = 0
    max_depth = 0
    locations: List[Tuple[str, int, int]] = []

    for event in events:
        all_shapes_set: Set[Tuple[int, ...]] = set()

        if event.call_depth > max_depth:
            max_depth = event.call_depth

        if event.kind == EventKind.CALL:
            call_count += 1
            if event.location is not None:
                locations.append(event.location)
            if event.variable:
                # This is a parameter observation
                key = event.variable
                if key not in param_builders:
                    pb = _VariableBuilder(func_name, key)
                    pb.is_param = True
                    param_builders[key] = pb
                param_builders[key].add(event)

        elif event.kind == EventKind.RETURN:
            if return_builder is None:
                return_builder = _VariableBuilder(func_name, "<return>")
                return_builder.is_return = True
            return_builder.add(event)

        elif event.kind == EventKind.LOCAL_ASSIGN:
            key = event.variable
            if key not in var_builders:
                var_builders[key] = _VariableBuilder(func_name, key)
            var_builders[key].add(event)

        elif event.kind == EventKind.BRANCH_TAKEN:
            loc = event.location or ("<unknown>", 0, 0)
            if loc not in branch_acc:
                branch_acc[loc] = {
                    "true": 0,
                    "false": 0,
                    "guard": event.value_repr,
                }
            # Determine polarity from the value_repr
            if event.value_repr.lower() in ("true", "1"):
                branch_acc[loc]["true"] += 1
            else:
                branch_acc[loc]["false"] += 1

        elif event.kind == EventKind.EXCEPTION:
            exc_type = event.variable or event.value_type
            if exc_type not in exc_acc:
                exc_acc[exc_type] = {
                    "count": 0,
                    "locations": [],
                    "messages": [],
                }
            exc_acc[exc_type]["count"] += 1
            if event.location is not None:
                exc_acc[exc_type]["locations"].append(event.location)
            if len(exc_acc[exc_type]["messages"]) < 5:
                exc_acc[exc_type]["messages"].append(event.value_repr)

        elif event.kind in (
            EventKind.ATTRIBUTE_ACCESS,
            EventKind.SUBSCRIPT,
            EventKind.ITERATION,
        ):
            key = event.variable
            if key and key not in var_builders:
                var_builders[key] = _VariableBuilder(func_name, key)
            if key:
                var_builders[key].add(event)

    # Ensure at least 1 call count
    if call_count == 0:
        call_count = 1

    # Build variable observations
    variables = tuple(
        vb.build()
        for vb in sorted(var_builders.values(), key=lambda b: -b.count)
    )

    # Build branch observations
    branches = tuple(
        BranchObservation(
            function=func_name,
            location=loc,
            true_count=acc["true"],
            false_count=acc["false"],
            guard_repr=acc.get("guard", ""),
        )
        for loc, acc in sorted(branch_acc.items())
    )

    # Build exception observations
    exceptions = tuple(
        ExceptionObservation(
            function=func_name,
            exception_type=exc_type,
            count=data["count"],
            locations=tuple(data["locations"]),
            sample_messages=tuple(data["messages"]),
        )
        for exc_type, data in sorted(
            exc_acc.items(), key=lambda kv: -kv[1]["count"]
        )
    )

    # Deduplicate locations
    seen_locs: Set[Tuple[str, int, int]] = set()
    deduped_locs: List[Tuple[str, int, int]] = []
    for loc in locations:
        if loc not in seen_locs:
            seen_locs.add(loc)
            deduped_locs.append(loc)

    return FunctionObservation(
        function=func_name,
        call_count=call_count,
        variables=variables,
        branches=branches,
        exceptions=exceptions,
        return_observation=return_builder.build() if return_builder else None,
        parameter_observations=tuple(
            pb.build()
            for pb in sorted(param_builders.values(), key=lambda b: -b.count)
        ),
        max_depth=max_depth,
        locations=tuple(deduped_locs),
    )


# ---------------------------------------------------------------------------
# Merge multiple parsed traces
# ---------------------------------------------------------------------------

def merge_parsed_traces(traces: Sequence[ParsedTrace]) -> ParsedTrace:
    """Merge multiple :class:`ParsedTrace` objects into a unified view.

    Variables with the same ``(function, variable)`` key are combined.
    This is useful for building a combined picture from multiple runs
    before feeding into :mod:`trace_to_section`.

    Parameters
    ----------
    traces : Sequence[ParsedTrace]
        Parsed traces to merge.

    Returns
    -------
    ParsedTrace
        A single merged parsed trace.
    """
    if not traces:
        return ParsedTrace(
            trace_id="<empty>",
            target_function="<merged>",
        )
    if len(traces) == 1:
        return traces[0]

    # Collect all function observations by function name
    func_obs_map: Dict[str, List[FunctionObservation]] = defaultdict(list)
    for pt in traces:
        for fo in pt.function_observations:
            func_obs_map[fo.function].append(fo)

    merged_func_obs: List[FunctionObservation] = []
    for func_name, obs_list in func_obs_map.items():
        merged_func_obs.append(_merge_function_observations(func_name, obs_list))

    all_vars: List[VariableObservation] = []
    all_branches: List[BranchObservation] = []
    all_exceptions: List[ExceptionObservation] = []
    all_types: Set[str] = set()
    all_shapes: Set[Tuple[int, ...]] = set()

    for fo in merged_func_obs:
        all_vars.extend(fo.variables)
        if fo.return_observation:
            all_vars.append(fo.return_observation)
        all_vars.extend(fo.parameter_observations)
        all_branches.extend(fo.branches)
        all_exceptions.extend(fo.exceptions)

    for pt in traces:
        all_types.update(pt.unique_types)
        all_shapes.update(pt.unique_shapes)

    return ParsedTrace(
        trace_id=traces[0].trace_id,
        target_function=traces[0].target_function,
        function_observations=tuple(merged_func_obs),
        all_variables=tuple(all_vars),
        all_branches=tuple(all_branches),
        all_exceptions=tuple(all_exceptions),
        unique_types=frozenset(all_types),
        unique_shapes=frozenset(all_shapes),
        duration=sum(pt.duration for pt in traces),
        succeeded=all(pt.succeeded for pt in traces),
        event_count=sum(pt.event_count for pt in traces),
    )


def _merge_function_observations(
    func_name: str,
    obs_list: List[FunctionObservation],
) -> FunctionObservation:
    """Merge multiple :class:`FunctionObservation` for the same function."""
    total_calls = sum(fo.call_count for fo in obs_list)
    max_depth = max(fo.max_depth for fo in obs_list)

    # Merge variables by name
    var_map: Dict[str, List[VariableObservation]] = defaultdict(list)
    for fo in obs_list:
        for vo in fo.variables:
            var_map[vo.variable].append(vo)

    merged_vars = tuple(
        _merge_variable_observations(func_name, vname, vos)
        for vname, vos in sorted(var_map.items())
    )

    # Merge parameters
    param_map: Dict[str, List[VariableObservation]] = defaultdict(list)
    for fo in obs_list:
        for po in fo.parameter_observations:
            param_map[po.variable].append(po)
    merged_params = tuple(
        _merge_variable_observations(func_name, pname, pos)
        for pname, pos in sorted(param_map.items())
    )

    # Merge return observations
    return_obs: List[VariableObservation] = [
        fo.return_observation for fo in obs_list if fo.return_observation
    ]
    merged_return: Optional[VariableObservation] = None
    if return_obs:
        merged_return = _merge_variable_observations(
            func_name, "<return>", return_obs
        )

    # Collect branches and exceptions (simple concatenation with dedup later)
    all_branches: List[BranchObservation] = []
    for fo in obs_list:
        all_branches.extend(fo.branches)
    all_exceptions: List[ExceptionObservation] = []
    for fo in obs_list:
        all_exceptions.extend(fo.exceptions)

    all_locs: List[Tuple[str, int, int]] = []
    for fo in obs_list:
        all_locs.extend(fo.locations)

    return FunctionObservation(
        function=func_name,
        call_count=total_calls,
        variables=merged_vars,
        branches=tuple(all_branches),
        exceptions=tuple(all_exceptions),
        return_observation=merged_return,
        parameter_observations=merged_params,
        max_depth=max_depth,
        locations=tuple(dict.fromkeys(all_locs)),
    )


def _merge_variable_observations(
    func_name: str,
    var_name: str,
    obs_list: List[VariableObservation],
) -> VariableObservation:
    """Merge multiple observations for the same variable."""
    type_map: Dict[str, List[ObservedType]] = defaultdict(list)
    for vo in obs_list:
        for ot in vo.observed_types:
            type_map[ot.type_name].append(ot)

    merged_types: List[ObservedType] = []
    for tname, ots in type_map.items():
        total_count = sum(o.count for o in ots)
        all_shapes: Set[Tuple[int, ...]] = set()
        all_dtypes: Set[str] = set()
        all_lengths: Set[int] = set()
        all_reprs: List[str] = []
        for o in ots:
            all_shapes.update(o.shapes)
            all_dtypes.update(o.dtypes)
            all_lengths.update(o.lengths)
            all_reprs.extend(o.sample_reprs)
        merged_types.append(ObservedType(
            type_name=tname,
            count=total_count,
            shapes=tuple(sorted(all_shapes)),
            dtypes=tuple(sorted(all_dtypes)),
            lengths=tuple(sorted(all_lengths)),
            sample_reprs=tuple(all_reprs[:5]),
        ))

    merged_types.sort(key=lambda t: -t.count)
    total_assigns = sum(vo.assignment_count for vo in obs_list)
    first_loc = next(
        (vo.first_location for vo in obs_list if vo.first_location), None
    )
    last_loc = next(
        (vo.last_location for vo in reversed(obs_list) if vo.last_location),
        None,
    )
    all_sample_vals: List[str] = []
    for vo in obs_list:
        all_sample_vals.extend(vo.sample_values)

    return VariableObservation(
        function=func_name,
        variable=var_name,
        observed_types=tuple(merged_types),
        assignment_count=total_assigns,
        first_location=first_loc,
        last_location=last_loc,
        is_parameter=any(vo.is_parameter for vo in obs_list),
        is_return=any(vo.is_return for vo in obs_list),
        sample_values=tuple(all_sample_vals[:10]),
    )
