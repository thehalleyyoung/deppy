"""Interprocedural analysis for the sheaf-descent semantic typing system.

This package provides call-graph construction, summary propagation,
section transport, error viability pushback, wrapper analysis, and
context-sensitive analysis for DepPy's interprocedural phase.

Modules
-------
call_graph
    Call graph construction from AST with topological ordering and SCC detection.
summary_propagation
    Propagate boundary sections across function call boundaries.
section_transport
    Import callee sections at call sites via actual-to-formal reindexing.
error_viability_pushback
    Push error viability requirements backward through call chains.
wrapper_analysis
    Analyze wrapper chains for transparency.
context_sensitivity
    Context-sensitive summaries using k-CFA.
"""

from deppy.interprocedural.call_graph import (
    CallEdge,
    CallGraph,
    CallTarget,
)

from deppy.interprocedural.summary_propagation import (
    FunctionSummary,
    PropagationResult,
    SummaryPropagator,
)

from deppy.interprocedural.section_transport import (
    ParameterMapping,
    SectionTransporter,
    TransportResult,
)

from deppy.interprocedural.error_viability_pushback import (
    ErrorViabilityPushback,
    PushbackResult,
    ViabilityRequirement,
)

from deppy.interprocedural.wrapper_analysis import (
    TransparencyChainResult,
    WrapperAnalyzer,
    WrapperPattern,
)

from deppy.interprocedural.context_sensitivity import (
    CallContext,
    ContextSensitiveAnalyzer,
    ContextualSections,
)

from deppy.interprocedural._protocols import (
    CallSiteSummary,
    KanExtensionResult,
    Profunctor,
    SectionTransport,
)

__all__ = [
    # call_graph
    "CallEdge",
    "CallGraph",
    "CallTarget",
    # summary_propagation
    "FunctionSummary",
    "PropagationResult",
    "SummaryPropagator",
    # section_transport
    "ParameterMapping",
    "SectionTransporter",
    "TransportResult",
    # error_viability_pushback
    "ErrorViabilityPushback",
    "PushbackResult",
    "ViabilityRequirement",
    # wrapper_analysis
    "TransparencyChainResult",
    "WrapperAnalyzer",
    "WrapperPattern",
    # context_sensitivity
    "CallContext",
    "ContextSensitiveAnalyzer",
    "ContextualSections",
    # _protocols
    "CallSiteSummary",
    "KanExtensionResult",
    "Profunctor",
    "SectionTransport",
]
