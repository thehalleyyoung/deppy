"""Context-sensitive interprocedural analysis (k-CFA).

Standard interprocedural analysis merges all call contexts for a function
into a single summary.  Context-sensitive analysis maintains separate
summaries for different calling contexts, improving precision.

In the sheaf-descent framework, context sensitivity means maintaining
multiple covers for the same function, one per calling context.  Each
cover may have different boundary sections depending on which arguments
the caller provided.

This module implements k-CFA context sensitivity, where a context is
the last k call sites on the call stack.
"""

from __future__ import annotations

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

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.interprocedural.call_graph import CallEdge, CallGraph


# ---------------------------------------------------------------------------
# Call context
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CallContext:
    """A calling context for context-sensitive analysis.

    A context is a sequence of call sites representing the last k
    entries on the call stack.  The empty context () represents
    context-insensitive analysis.

    Attributes:
        _call_chain: Tuple of (caller, call_site) pairs, most recent last.
        _k: The sensitivity level (length of the chain).
    """

    _call_chain: Tuple[Tuple[str, Optional[SiteId]], ...] = ()
    _k: int = 0

    @property
    def call_chain(self) -> Tuple[Tuple[str, Optional[SiteId]], ...]:
        return self._call_chain

    @property
    def k(self) -> int:
        return self._k

    @property
    def depth(self) -> int:
        """Number of context entries."""
        return len(self._call_chain)

    @property
    def is_empty(self) -> bool:
        return len(self._call_chain) == 0

    @property
    def caller(self) -> Optional[str]:
        """The most recent caller, or None for empty context."""
        if self._call_chain:
            return self._call_chain[-1][0]
        return None

    @property
    def call_site(self) -> Optional[SiteId]:
        """The most recent call site, or None for empty context."""
        if self._call_chain:
            return self._call_chain[-1][1]
        return None

    def extend(
        self,
        caller: str,
        call_site: Optional[SiteId],
    ) -> CallContext:
        """Extend this context with a new call.

        If the chain exceeds k, truncate from the front (oldest entries).
        """
        new_chain = self._call_chain + ((caller, call_site),)
        if self._k > 0 and len(new_chain) > self._k:
            new_chain = new_chain[-self._k:]
        return CallContext(_call_chain=new_chain, _k=self._k)

    def truncate(self, new_k: int) -> CallContext:
        """Truncate the context to a shorter sensitivity level."""
        if new_k >= len(self._call_chain):
            return CallContext(_call_chain=self._call_chain, _k=new_k)
        return CallContext(
            _call_chain=self._call_chain[-new_k:],
            _k=new_k,
        )

    @classmethod
    def empty(cls, k: int = 0) -> CallContext:
        """Create an empty context with the given sensitivity level."""
        return cls(_call_chain=(), _k=k)

    @classmethod
    def from_edge(cls, edge: CallEdge, k: int = 1) -> CallContext:
        """Create a context from a single call edge."""
        return cls(
            _call_chain=((edge.caller, edge.call_site_id),),
            _k=k,
        )

    def __repr__(self) -> str:
        if not self._call_chain:
            return "CallContext([])"
        parts = [
            f"{caller}@{site}" for caller, site in self._call_chain
        ]
        return f"CallContext([{' -> '.join(parts)}])"


# ---------------------------------------------------------------------------
# Context-sensitive section store
# ---------------------------------------------------------------------------

@dataclass
class ContextualSections:
    """Sections for a function, partitioned by calling context.

    Attributes:
        _func_name: The function these sections belong to.
        _sections_by_context: Maps context to site->section dict.
    """

    _func_name: str
    _sections_by_context: Dict[CallContext, Dict[SiteId, LocalSection]] = field(
        default_factory=dict
    )

    @property
    def func_name(self) -> str:
        return self._func_name

    @property
    def contexts(self) -> FrozenSet[CallContext]:
        return frozenset(self._sections_by_context.keys())

    def get_sections(
        self, context: CallContext
    ) -> Dict[SiteId, LocalSection]:
        """Get sections for a specific context."""
        return dict(self._sections_by_context.get(context, {}))

    def set_sections(
        self,
        context: CallContext,
        sections: Dict[SiteId, LocalSection],
    ) -> None:
        """Set sections for a specific context."""
        self._sections_by_context[context] = dict(sections)

    def update_section(
        self,
        context: CallContext,
        site_id: SiteId,
        section: LocalSection,
    ) -> None:
        """Update a single section in a specific context."""
        if context not in self._sections_by_context:
            self._sections_by_context[context] = {}
        self._sections_by_context[context][site_id] = section

    def all_sections_flat(self) -> Dict[SiteId, LocalSection]:
        """Merge all contexts into a single section dict (join)."""
        merged: Dict[SiteId, LocalSection] = {}
        for sections in self._sections_by_context.values():
            for site_id, section in sections.items():
                if site_id not in merged:
                    merged[site_id] = section
                else:
                    merged[site_id] = _join_sections(merged[site_id], section)
        return merged


def _join_sections(a: LocalSection, b: LocalSection) -> LocalSection:
    """Join two sections at the same site (take weaker information).

    Merges refinements as the union of keys, and takes the weaker trust.
    """
    merged_refs: Dict[str, Any] = {}
    # Intersection of refinements (conservative)
    common_keys = set(a.refinements.keys()) & set(b.refinements.keys())
    for key in common_keys:
        if a.refinements[key] == b.refinements[key]:
            merged_refs[key] = a.refinements[key]

    # Weaker trust
    trust_order = [
        TrustLevel.RESIDUAL,
        TrustLevel.ASSUMED,
        TrustLevel.TRACE_BACKED,
        TrustLevel.BOUNDED_AUTO,
        TrustLevel.TRUSTED_AUTO,
        TrustLevel.PROOF_BACKED,
    ]
    a_rank = trust_order.index(a.trust) if a.trust in trust_order else 0
    b_rank = trust_order.index(b.trust) if b.trust in trust_order else 0
    merged_trust = trust_order[min(a_rank, b_rank)]

    return LocalSection(
        site_id=a.site_id,
        carrier_type=a.carrier_type,
        refinements=merged_refs,
        trust=merged_trust,
        provenance=f"joined({a.provenance}, {b.provenance})",
    )


# ---------------------------------------------------------------------------
# ContextSensitiveAnalyzer
# ---------------------------------------------------------------------------

class ContextSensitiveAnalyzer:
    """Context-sensitive interprocedural analysis using k-CFA.

    Maintains separate section summaries for each calling context up to
    depth k.  At k=0, this degenerates to context-insensitive analysis.
    At k=1, each call site gets its own summary.

    The analyzer:
    1. Builds context-sensitive call chains from the call graph.
    2. For each (function, context) pair, computes sections.
    3. Merges contexts when k-sensitivity is exceeded.
    """

    def __init__(self, k: int = 1) -> None:
        """Initialize with sensitivity level k.

        Args:
            k: Context sensitivity depth. 0 = insensitive, 1 = 1-CFA, etc.
        """
        self._k = k
        self._contextual_stores: Dict[str, ContextualSections] = {}

    @property
    def k(self) -> int:
        return self._k

    @property
    def stores(self) -> Dict[str, ContextualSections]:
        return dict(self._contextual_stores)

    # -- Analysis -----------------------------------------------------------

    def analyze(
        self,
        call_graph: CallGraph,
        covers: Dict[str, Cover],
        k: Optional[int] = None,
    ) -> Dict[CallContext, Dict[SiteId, LocalSection]]:
        """Perform context-sensitive analysis over the call graph.

        Args:
            call_graph: The module's call graph.
            covers: Function covers from intraprocedural analysis.
            k: Override sensitivity level (uses self._k if None).

        Returns:
            Mapping from (function, context) -> sections, encoded as
            context -> sections where context identifies the function.
        """
        sensitivity = k if k is not None else self._k
        result: Dict[CallContext, Dict[SiteId, LocalSection]] = {}

        # Initialize stores for all functions
        for func_name in call_graph.nodes:
            if func_name not in self._contextual_stores:
                self._contextual_stores[func_name] = ContextualSections(
                    _func_name=func_name
                )

        # Process in topological order (callees first)
        topo_order = call_graph.topological_order()

        for func_name in topo_order:
            cover = covers.get(func_name)
            if cover is None:
                continue

            store = self._contextual_stores[func_name]

            # Determine all calling contexts for this function
            contexts = self._compute_contexts(
                func_name, call_graph, sensitivity
            )

            if not contexts:
                # Root function: use empty context
                ctx = CallContext.empty(sensitivity)
                contexts = [ctx]

            for ctx in contexts:
                # Compute sections for this (func, context) pair
                sections = self._analyze_in_context(
                    func_name, ctx, call_graph, covers
                )
                store.set_sections(ctx, sections)
                result[ctx] = sections

        return result

    def merge_contexts(
        self,
        contexts: Dict[CallContext, Dict[SiteId, LocalSection]],
    ) -> Dict[SiteId, LocalSection]:
        """Merge all context-specific sections into a single summary.

        Takes the join (weakest information) across all contexts.
        Used when context sensitivity needs to be abandoned (e.g., for
        recursive functions or when the analysis budget is exceeded).
        """
        merged: Dict[SiteId, LocalSection] = {}

        for ctx_sections in contexts.values():
            for site_id, section in ctx_sections.items():
                if site_id not in merged:
                    merged[site_id] = section
                else:
                    merged[site_id] = _join_sections(merged[site_id], section)

        return merged

    def get_context_count(self, func_name: str) -> int:
        """Return the number of distinct contexts for a function."""
        store = self._contextual_stores.get(func_name)
        if store is None:
            return 0
        return len(store.contexts)

    def get_sections_for_context(
        self,
        func_name: str,
        context: CallContext,
    ) -> Dict[SiteId, LocalSection]:
        """Get sections for a specific function and context."""
        store = self._contextual_stores.get(func_name)
        if store is None:
            return {}
        return store.get_sections(context)

    def get_merged_sections(
        self, func_name: str
    ) -> Dict[SiteId, LocalSection]:
        """Get the merged (context-insensitive) sections for a function."""
        store = self._contextual_stores.get(func_name)
        if store is None:
            return {}
        return store.all_sections_flat()

    # -- Internal helpers ---------------------------------------------------

    def _compute_contexts(
        self,
        func_name: str,
        call_graph: CallGraph,
        k: int,
    ) -> List[CallContext]:
        """Compute all calling contexts for a function.

        Traverses the call graph backward up to depth k to enumerate
        all distinct call chains that lead to this function.
        """
        if k == 0:
            return [CallContext.empty(0)]

        # Collect all call edges targeting this function
        caller_edges = call_graph.get_callers(func_name)
        if not caller_edges:
            return [CallContext.empty(k)]

        contexts: List[CallContext] = []

        if k == 1:
            # Simple case: one context per direct caller
            for edge in caller_edges:
                ctx = CallContext.from_edge(edge, k=1)
                contexts.append(ctx)
            return contexts

        # General case: enumerate chains of length up to k
        # Use BFS backward from each caller edge
        for edge in caller_edges:
            base_ctx = CallContext.from_edge(edge, k=k)
            chain_contexts = self._extend_context_backward(
                base_ctx, edge.caller, call_graph, k - 1
            )
            contexts.extend(chain_contexts)

        # Deduplicate
        seen: Set[Tuple[Tuple[str, Optional[SiteId]], ...]] = set()
        unique: List[CallContext] = []
        for ctx in contexts:
            key = ctx.call_chain
            if key not in seen:
                seen.add(key)
                unique.append(ctx)

        return unique if unique else [CallContext.empty(k)]

    def _extend_context_backward(
        self,
        current_ctx: CallContext,
        func_name: str,
        call_graph: CallGraph,
        remaining_depth: int,
    ) -> List[CallContext]:
        """Extend a context backward through callers."""
        if remaining_depth <= 0:
            return [current_ctx]

        caller_edges = call_graph.get_callers(func_name)
        if not caller_edges:
            return [current_ctx]

        extended: List[CallContext] = []
        for edge in caller_edges:
            new_ctx = CallContext(
                _call_chain=(
                    (edge.caller, edge.call_site_id),
                ) + current_ctx.call_chain,
                _k=current_ctx.k,
            )
            # Truncate to k
            if new_ctx.depth > current_ctx.k:
                new_ctx = new_ctx.truncate(current_ctx.k)

            sub_contexts = self._extend_context_backward(
                new_ctx, edge.caller, call_graph, remaining_depth - 1
            )
            extended.extend(sub_contexts)

        return extended

    def _analyze_in_context(
        self,
        func_name: str,
        context: CallContext,
        call_graph: CallGraph,
        covers: Dict[str, Cover],
    ) -> Dict[SiteId, LocalSection]:
        """Compute sections for a function in a specific context.

        Uses the caller's sections (from the context) to initialize
        the function's input boundary, then propagates forward.
        """
        cover = covers.get(func_name)
        if cover is None:
            return {}

        sections: Dict[SiteId, LocalSection] = {}

        # Initialize input boundary sections
        for site_id in cover.input_boundary:
            # Try to get caller-specific information from context
            caller_section = self._lookup_caller_section(
                site_id, context, covers
            )
            if caller_section is not None:
                sections[site_id] = LocalSection(
                    site_id=site_id,
                    carrier_type=caller_section.carrier_type,
                    refinements=dict(caller_section.refinements),
                    trust=caller_section.trust,
                    provenance=(
                        f"context-sensitive from {context.caller}"
                        if context.caller
                        else "context-insensitive"
                    ),
                )
            else:
                sections[site_id] = LocalSection(
                    site_id=site_id,
                    trust=TrustLevel.RESIDUAL,
                    provenance="no context info",
                )

        # Initialize output boundary from cover
        for site_id in cover.output_boundary:
            sections[site_id] = LocalSection(
                site_id=site_id,
                trust=TrustLevel.RESIDUAL,
            )

        # Import callee summaries (context-sensitive)
        for edge in call_graph.get_callees(func_name):
            callee_name = edge.callee
            callee_store = self._contextual_stores.get(callee_name)
            if callee_store is None:
                continue

            # Find the callee context from this call
            callee_ctx = context.extend(func_name, edge.call_site_id)
            callee_sections = callee_store.get_sections(callee_ctx)

            if not callee_sections:
                # Fall back to merged sections
                callee_sections = callee_store.all_sections_flat()

            # Import callee output sections at call-result sites
            call_result_id = edge.call_site_id
            if call_result_id is None:
                call_result_id = SiteId(
                    kind=SiteKind.CALL_RESULT,
                    name=f"{func_name}.call_{callee_name}",
                )

            for site_id, section in callee_sections.items():
                if site_id.kind == SiteKind.RETURN_OUTPUT_BOUNDARY:
                    sections[call_result_id] = LocalSection(
                        site_id=call_result_id,
                        carrier_type=section.carrier_type,
                        refinements=dict(section.refinements),
                        trust=section.trust,
                        provenance=f"imported from {callee_name} ctx={callee_ctx}",
                    )

        return sections

    def _lookup_caller_section(
        self,
        callee_input_site: SiteId,
        context: CallContext,
        covers: Dict[str, Cover],
    ) -> Optional[LocalSection]:
        """Look up a caller section for a callee input site."""
        if context.is_empty:
            return None

        caller_name = context.caller
        if caller_name is None:
            return None

        caller_store = self._contextual_stores.get(caller_name)
        if caller_store is None:
            return None

        # Get the caller's sections in its context
        # Pop the last entry from context to get the caller's own context
        if len(context.call_chain) > 1:
            caller_ctx = CallContext(
                _call_chain=context.call_chain[:-1],
                _k=context.k,
            )
        else:
            caller_ctx = CallContext.empty(context.k)

        caller_sections = caller_store.get_sections(caller_ctx)
        if not caller_sections:
            caller_sections = caller_store.all_sections_flat()

        # Find matching section by parameter name
        param_name = callee_input_site.name.split(".")[-1]
        for site_id, section in caller_sections.items():
            s_name = site_id.name.split(".")[-1]
            if s_name == param_name:
                return section

        return None

    def clear(self) -> None:
        """Clear all stored analysis results."""
        self._contextual_stores.clear()
