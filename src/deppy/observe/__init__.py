"""deppy.observe -- dynamic trace ingestion for sheaf-descent typing.

This package converts runtime observations into local sections with
``TrustLevel.TRACE_BACKED``.  The pipeline is:

1. **trace_recorder** -- instrument and execute functions, capturing
   :class:`TraceEvent` objects into a :class:`TraceLog`.
2. **trace_parser** -- group, deduplicate, and structure events into
   a :class:`ParsedTrace`.
3. **trace_to_section** -- convert parsed traces into :class:`LocalSection`
   objects with ``trust=TrustLevel.TRACE_BACKED``.
4. **representative_selector** -- select a minimal subset of traces
   that covers all observed behaviours.
5. **dynamic_viability** -- infer error-site viability from traces.
"""

from __future__ import annotations

from deppy.observe.trace_recorder import (
    EventKind,
    InstrumentationConfig,
    TraceEvent,
    TraceInput,
    TraceLog,
    TraceRecorder,
    TraceSummary,
    filter_events,
    instrument,
    merge_trace_logs,
    record_trace,
    record_traces_batch,
    summarize_trace,
)
from deppy.observe.trace_parser import (
    BranchObservation,
    ExceptionObservation,
    FunctionObservation,
    ObservedType,
    ParsedTrace,
    VariableObservation,
    merge_parsed_traces,
    parse_trace_log,
)
from deppy.observe.trace_to_section import (
    InferredRefinements,
    SectionEnrichment,
    branch_to_local_section,
    enrich_section,
    exception_to_local_section,
    function_to_local_sections,
    merge_trace_sections,
    section_agrees_with_static,
    trace_to_local_section,
    trace_to_sections,
    variable_to_local_section,
)
from deppy.observe.representative_selector import (
    CoverageCriterion,
    CoverageReport,
    CriterionKind,
    RepresentativeSelector,
    SelectionConfig,
    SelectionResult,
    compute_coverage,
    find_coverage_gaps,
    select_representatives,
    suggest_additional_inputs,
)
from deppy.observe.dynamic_viability import (
    SiteViability,
    ViabilityConfig,
    ViabilityInference,
    ViabilityLevel,
    ViabilityResult,
    infer_viability,
    viability_to_sections,
)

__all__ = [
    # trace_recorder
    "EventKind",
    "InstrumentationConfig",
    "TraceEvent",
    "TraceInput",
    "TraceLog",
    "TraceRecorder",
    "TraceSummary",
    "filter_events",
    "instrument",
    "merge_trace_logs",
    "record_trace",
    "record_traces_batch",
    "summarize_trace",
    # trace_parser
    "BranchObservation",
    "ExceptionObservation",
    "FunctionObservation",
    "ObservedType",
    "ParsedTrace",
    "VariableObservation",
    "merge_parsed_traces",
    "parse_trace_log",
    # trace_to_section
    "InferredRefinements",
    "SectionEnrichment",
    "branch_to_local_section",
    "enrich_section",
    "exception_to_local_section",
    "function_to_local_sections",
    "merge_trace_sections",
    "section_agrees_with_static",
    "trace_to_local_section",
    "trace_to_sections",
    "variable_to_local_section",
    # representative_selector
    "CoverageCriterion",
    "CoverageReport",
    "CriterionKind",
    "RepresentativeSelector",
    "SelectionConfig",
    "SelectionResult",
    "compute_coverage",
    "find_coverage_gaps",
    "select_representatives",
    "suggest_additional_inputs",
    # dynamic_viability
    "SiteViability",
    "ViabilityConfig",
    "ViabilityInference",
    "ViabilityLevel",
    "ViabilityResult",
    "infer_viability",
    "viability_to_sections",
]
