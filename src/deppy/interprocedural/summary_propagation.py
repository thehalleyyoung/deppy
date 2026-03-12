"""Propagate boundary sections across function call boundaries.

In sheaf-descent semantics, each function has a cover whose input and output
boundaries carry local sections.  When function F calls function G:

1. F's actual-argument sections are transported to G's input boundary
   (actual -> formal reindexing).
2. G's analysis produces output boundary sections (the callee summary).
3. G's output boundary sections are imported into F's call-result sites
   (return -> caller reindexing).

This module implements the SummaryPropagator that orchestrates this
interprocedural section transport for an entire call graph.
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
    BoundarySection,
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism

from deppy.interprocedural.call_graph import CallEdge, CallGraph


# ---------------------------------------------------------------------------
# Summary data structures
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class FunctionSummary:
    """Boundary sections summarizing a function's behavior.

    Attributes:
        _func_name: Name of the summarized function.
        _input_sections: Sections at input boundary sites (formal params).
        _output_sections: Sections at output boundary sites (returns).
        _error_sections: Sections at error sites with viability info.
        _is_recursive: Whether this function participates in recursion.
        _iteration_count: Number of fixpoint iterations (for recursive fns).
    """

    _func_name: str
    _input_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    _output_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    _error_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    _is_recursive: bool = False
    _iteration_count: int = 0

    @property
    def func_name(self) -> str:
        return self._func_name

    @property
    def input_sections(self) -> Dict[SiteId, LocalSection]:
        return dict(self._input_sections)

    @property
    def output_sections(self) -> Dict[SiteId, LocalSection]:
        return dict(self._output_sections)

    @property
    def error_sections(self) -> Dict[SiteId, LocalSection]:
        return dict(self._error_sections)

    @property
    def is_recursive(self) -> bool:
        return self._is_recursive

    @property
    def iteration_count(self) -> int:
        return self._iteration_count


@dataclass(frozen=True)
class PropagationResult:
    """Result of propagating a callee summary into a caller's cover.

    Attributes:
        _caller: Name of the caller function.
        _callee: Name of the callee function.
        _imported_sections: Sections imported at caller's call-result sites.
        _transported_refinements: Refinements carried from callee to caller.
        _trust_level: Trust level of the imported sections.
        _morphisms_created: Morphisms created for section transport.
    """

    _caller: str
    _callee: str
    _imported_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    _transported_refinements: Dict[str, Any] = field(default_factory=dict)
    _trust_level: TrustLevel = TrustLevel.BOUNDED_AUTO
    _morphisms_created: List[ConcreteMorphism] = field(default_factory=list)

    @property
    def caller(self) -> str:
        return self._caller

    @property
    def callee(self) -> str:
        return self._callee

    @property
    def imported_sections(self) -> Dict[SiteId, LocalSection]:
        return dict(self._imported_sections)

    @property
    def trust_level(self) -> TrustLevel:
        return self._trust_level


# ---------------------------------------------------------------------------
# Section merger for overlap
# ---------------------------------------------------------------------------

def _merge_sections(
    existing: LocalSection,
    incoming: LocalSection,
) -> LocalSection:
    """Merge an incoming section with an existing one at the same site.

    Takes the intersection of refinements (conservative merge) and
    uses the weaker trust level.
    """
    # Merge refinements: keep keys present in both, prefer existing values
    merged_refs: Dict[str, Any] = {}
    for key in set(existing.refinements.keys()) | set(incoming.refinements.keys()):
        if key in existing.refinements and key in incoming.refinements:
            # Both have it -- prefer existing
            merged_refs[key] = existing.refinements[key]
        elif key in existing.refinements:
            merged_refs[key] = existing.refinements[key]
        else:
            merged_refs[key] = incoming.refinements[key]

    # Merge witnesses
    merged_witnesses: Dict[str, Any] = {}
    merged_witnesses.update(existing.witnesses)
    merged_witnesses.update(incoming.witnesses)

    # Choose weaker trust
    trust_order = [
        TrustLevel.RESIDUAL,
        TrustLevel.ASSUMED,
        TrustLevel.TRACE_BACKED,
        TrustLevel.BOUNDED_AUTO,
        TrustLevel.TRUSTED_AUTO,
        TrustLevel.PROOF_BACKED,
    ]
    existing_rank = (
        trust_order.index(existing.trust)
        if existing.trust in trust_order
        else 0
    )
    incoming_rank = (
        trust_order.index(incoming.trust)
        if incoming.trust in trust_order
        else 0
    )
    merged_trust = trust_order[min(existing_rank, incoming_rank)]

    return LocalSection(
        site_id=existing.site_id,
        carrier_type=existing.carrier_type,
        refinements=merged_refs,
        trust=merged_trust,
        provenance=f"merged({existing.provenance}, {incoming.provenance})",
        witnesses=merged_witnesses,
    )


# ---------------------------------------------------------------------------
# Argument mapping
# ---------------------------------------------------------------------------

def _build_arg_mapping(
    call_edge: CallEdge,
    callee_cover: Cover,
) -> Dict[SiteId, SiteId]:
    """Build a mapping from callee input boundary sites to caller sites.

    Maps each callee formal parameter site to the caller's actual
    argument site (or a synthetic site if needed).
    """
    mapping: Dict[SiteId, SiteId] = {}

    callee_name = call_edge.callee
    caller_name = call_edge.caller

    # Find callee input boundary sites by matching parameter names
    for site_id in callee_cover.input_boundary:
        if site_id.kind == SiteKind.ARGUMENT_BOUNDARY:
            # Extract param name from site name: "callee.param_name"
            parts = site_id.name.split(".")
            if len(parts) >= 2:
                param_name = parts[-1]
            else:
                param_name = site_id.name

            # Find matching argument in call edge
            # The call_edge.arguments contains positional arg names
            # We match by position based on parameter order
            # Since SiteId includes source_location, we build a
            # caller-side site id for the matching argument

            caller_site_id = SiteId(
                kind=SiteKind.ARGUMENT_BOUNDARY,
                name=f"{caller_name}.actual_{param_name}",
                source_location=call_edge.call_site_id.source_location
                if call_edge.call_site_id
                else None,
            )
            mapping[site_id] = caller_site_id

    return mapping


def _build_return_mapping(
    call_edge: CallEdge,
    callee_cover: Cover,
) -> Dict[SiteId, SiteId]:
    """Build a mapping from callee output boundary sites to caller sites.

    Maps each callee return site to the caller's call-result site.
    """
    mapping: Dict[SiteId, SiteId] = {}

    # Use the call_site_id from the edge as the target
    call_result_id = call_edge.call_site_id
    if call_result_id is None:
        call_result_id = SiteId(
            kind=SiteKind.CALL_RESULT,
            name=f"{call_edge.caller}.call_{call_edge.callee}",
        )

    for site_id in callee_cover.output_boundary:
        if site_id.kind == SiteKind.RETURN_OUTPUT_BOUNDARY:
            mapping[site_id] = call_result_id

    return mapping


# ---------------------------------------------------------------------------
# SummaryPropagator
# ---------------------------------------------------------------------------

class SummaryPropagator:
    """Propagate boundary sections across call boundaries.

    Orchestrates interprocedural section transport for an entire call graph.
    Processes functions in topological order (callees before callers) and
    applies fixpoint iteration for recursive function groups.

    The propagator supports:
    - Forward propagation: actual args -> formal params
    - Backward propagation: callee returns -> caller call-result sites
    - Error viability transport: callee errors -> caller input requirements
    - Fixpoint iteration for mutually recursive SCCs
    """

    def __init__(
        self,
        *,
        max_iterations: int = 10,
        trust_downgrade_on_transport: bool = True,
    ) -> None:
        self._max_iterations = max_iterations
        self._trust_downgrade = trust_downgrade_on_transport
        self._summaries: Dict[str, FunctionSummary] = {}
        self._propagation_log: List[PropagationResult] = []

    @property
    def summaries(self) -> Dict[str, FunctionSummary]:
        """All computed function summaries."""
        return dict(self._summaries)

    @property
    def propagation_log(self) -> List[PropagationResult]:
        """Log of all propagation steps."""
        return list(self._propagation_log)

    # -- Core propagation ---------------------------------------------------

    def propagate_callee_summary(
        self,
        caller_cover: Cover,
        callee_cover: Cover,
        call_edge: CallEdge,
    ) -> Dict[SiteId, LocalSection]:
        """Propagate a callee's summary into the caller's cover.

        1. Transport callee output boundary sections to caller call-result sites.
        2. Reindex refinements from callee naming to caller naming.
        3. Downgrade trust if configured to do so.

        Returns a dict of new/updated sections for the caller's cover.
        """
        updated_sections: Dict[SiteId, LocalSection] = {}

        # Build return mapping: callee output -> caller call-result
        return_mapping = _build_return_mapping(call_edge, callee_cover)

        # Transport each callee output section to the caller
        for callee_site_id, caller_site_id in return_mapping.items():
            # Find the callee's section at this output site
            callee_section = self._find_section_at(
                callee_cover, callee_site_id
            )
            if callee_section is None:
                continue

            # Reindex refinements
            reindexed_refs = self._reindex_refinements_to_caller(
                callee_section.refinements,
                call_edge,
            )

            # Choose trust level
            trust = callee_section.trust
            if self._trust_downgrade:
                if trust == TrustLevel.PROOF_BACKED:
                    trust = TrustLevel.TRUSTED_AUTO
                elif trust == TrustLevel.TRUSTED_AUTO:
                    trust = TrustLevel.BOUNDED_AUTO

            imported = LocalSection(
                site_id=caller_site_id,
                carrier_type=callee_section.carrier_type,
                refinements=reindexed_refs,
                trust=trust,
                provenance=(
                    f"imported from {call_edge.callee} "
                    f"at {call_edge.caller}:{call_edge.line}"
                ),
                witnesses=dict(callee_section.witnesses),
            )

            # Merge with existing section if present
            existing = self._find_caller_section(
                caller_cover, caller_site_id, updated_sections
            )
            if existing is not None:
                imported = _merge_sections(existing, imported)

            updated_sections[caller_site_id] = imported

        # Log the propagation
        result = PropagationResult(
            _caller=call_edge.caller,
            _callee=call_edge.callee,
            _imported_sections=dict(updated_sections),
        )
        self._propagation_log.append(result)

        return updated_sections

    def propagate_actual_to_formal(
        self,
        caller_sections: Dict[SiteId, LocalSection],
        callee_cover: Cover,
        call_edge: CallEdge,
    ) -> Dict[SiteId, LocalSection]:
        """Transport actual argument sections to callee formal parameters.

        For each argument at the call site, find the matching callee
        parameter and transport the caller's section there.

        Returns updated sections for the callee's input boundary.
        """
        updated: Dict[SiteId, LocalSection] = {}

        arg_mapping = _build_arg_mapping(call_edge, callee_cover)

        # Reverse the mapping: callee formal -> caller actual
        # arg_mapping maps callee_input -> caller_actual
        # We need to find caller sections that match caller_actual sites

        for callee_site_id, caller_actual_id in arg_mapping.items():
            # Find a caller section that provides info for this argument
            caller_section = self._find_best_matching_section(
                caller_sections, caller_actual_id, call_edge
            )
            if caller_section is None:
                continue

            # Reindex from caller naming to callee naming
            reindexed_refs = self._reindex_refinements_to_callee(
                caller_section.refinements,
                call_edge,
                callee_site_id,
            )

            formal_section = LocalSection(
                site_id=callee_site_id,
                carrier_type=caller_section.carrier_type,
                refinements=reindexed_refs,
                trust=caller_section.trust,
                provenance=(
                    f"transported from {call_edge.caller} "
                    f"actual arg to {call_edge.callee} formal"
                ),
                witnesses=dict(caller_section.witnesses),
            )
            updated[callee_site_id] = formal_section

        return updated

    def propagate_all(
        self,
        call_graph: CallGraph,
        covers: Dict[str, Cover],
    ) -> Dict[str, Dict[SiteId, LocalSection]]:
        """Propagate summaries across the entire call graph.

        Processes functions in topological order (callees first).
        For recursive SCCs, applies fixpoint iteration.

        Returns a mapping from function name to updated sections.
        """
        all_updates: Dict[str, Dict[SiteId, LocalSection]] = defaultdict(dict)

        # Get topological order
        topo_order = call_graph.topological_order()

        # Process SCCs for fixpoint handling
        sccs = call_graph.strongly_connected_components()
        scc_map: Dict[str, FrozenSet[str]] = {}
        for scc in sccs:
            for func in scc:
                scc_map[func] = scc

        processed: Set[str] = set()

        for func_name in topo_order:
            if func_name in processed:
                continue

            scc = scc_map.get(func_name, frozenset({func_name}))

            if len(scc) > 1:
                # Mutually recursive SCC: fixpoint iteration
                scc_updates = self._propagate_scc(
                    scc, call_graph, covers, all_updates
                )
                for fn, sections in scc_updates.items():
                    all_updates[fn].update(sections)
                processed.update(scc)
            else:
                # Non-recursive: single pass
                if func_name not in covers:
                    processed.add(func_name)
                    continue

                func_cover = covers[func_name]
                updates = self._propagate_single(
                    func_name, call_graph, covers, all_updates
                )
                all_updates[func_name].update(updates)

                # Build summary for this function
                self._build_summary(func_name, func_cover, all_updates)
                processed.add(func_name)

        return dict(all_updates)

    # -- Internal helpers ---------------------------------------------------

    def _propagate_single(
        self,
        func_name: str,
        call_graph: CallGraph,
        covers: Dict[str, Cover],
        existing_updates: Dict[str, Dict[SiteId, LocalSection]],
    ) -> Dict[SiteId, LocalSection]:
        """Propagate summaries for a single non-recursive function."""
        updates: Dict[SiteId, LocalSection] = {}

        if func_name not in covers:
            return updates

        caller_cover = covers[func_name]

        # For each callee of this function
        for edge in call_graph.get_callees(func_name):
            callee_name = edge.callee
            if callee_name not in covers:
                continue

            callee_cover = covers[callee_name]

            # Forward: transport actual args to callee formals
            caller_sections = dict(existing_updates.get(func_name, {}))
            # Also include sections from the caller's cover
            for site_id in caller_cover.input_boundary:
                if site_id not in caller_sections:
                    caller_sections[site_id] = LocalSection(
                        site_id=site_id,
                        trust=TrustLevel.RESIDUAL,
                    )

            formal_updates = self.propagate_actual_to_formal(
                caller_sections, callee_cover, edge
            )

            # Backward: import callee summary into caller
            imported = self.propagate_callee_summary(
                caller_cover, callee_cover, edge
            )
            updates.update(imported)

        return updates

    def _propagate_scc(
        self,
        scc: FrozenSet[str],
        call_graph: CallGraph,
        covers: Dict[str, Cover],
        existing_updates: Dict[str, Dict[SiteId, LocalSection]],
    ) -> Dict[str, Dict[SiteId, LocalSection]]:
        """Apply fixpoint iteration for a mutually recursive SCC."""
        scc_updates: Dict[str, Dict[SiteId, LocalSection]] = {
            fn: {} for fn in scc
        }

        for iteration in range(self._max_iterations):
            changed = False

            for func_name in sorted(scc):
                if func_name not in covers:
                    continue

                old_sections = dict(scc_updates.get(func_name, {}))

                # Propagate within the SCC
                new_sections = self._propagate_single(
                    func_name, call_graph, covers, {
                        **existing_updates,
                        **scc_updates,
                    }
                )

                # Check for changes
                for site_id, section in new_sections.items():
                    if site_id not in old_sections:
                        changed = True
                    elif (
                        old_sections[site_id].refinements
                        != section.refinements
                    ):
                        changed = True

                scc_updates[func_name].update(new_sections)

            if not changed:
                break

        # Build summaries for all SCC members
        for func_name in scc:
            if func_name in covers:
                self._build_summary(
                    func_name,
                    covers[func_name],
                    {**existing_updates, **scc_updates},
                    is_recursive=True,
                    iteration_count=iteration + 1,
                )

        return scc_updates

    def _build_summary(
        self,
        func_name: str,
        cover: Cover,
        all_updates: Dict[str, Dict[SiteId, LocalSection]],
        *,
        is_recursive: bool = False,
        iteration_count: int = 0,
    ) -> None:
        """Build a FunctionSummary from a cover and updates."""
        updates = all_updates.get(func_name, {})

        input_sections: Dict[SiteId, LocalSection] = {}
        output_sections: Dict[SiteId, LocalSection] = {}
        error_sections: Dict[SiteId, LocalSection] = {}

        for site_id in cover.input_boundary:
            if site_id in updates:
                input_sections[site_id] = updates[site_id]
            else:
                input_sections[site_id] = LocalSection(
                    site_id=site_id, trust=TrustLevel.RESIDUAL
                )

        for site_id in cover.output_boundary:
            if site_id in updates:
                output_sections[site_id] = updates[site_id]
            else:
                output_sections[site_id] = LocalSection(
                    site_id=site_id, trust=TrustLevel.RESIDUAL
                )

        for site_id in cover.error_sites:
            if site_id in updates:
                error_sections[site_id] = updates[site_id]

        summary = FunctionSummary(
            _func_name=func_name,
            _input_sections=input_sections,
            _output_sections=output_sections,
            _error_sections=error_sections,
            _is_recursive=is_recursive,
            _iteration_count=iteration_count,
        )
        self._summaries[func_name] = summary

    def _find_section_at(
        self,
        cover: Cover,
        site_id: SiteId,
    ) -> Optional[LocalSection]:
        """Find a section in a cover's sites or synthesize a minimal one."""
        # Check if any site in the cover matches
        if site_id in cover.sites:
            return LocalSection(
                site_id=site_id,
                trust=TrustLevel.RESIDUAL,
            )
        return None

    def _find_caller_section(
        self,
        caller_cover: Cover,
        site_id: SiteId,
        updates: Dict[SiteId, LocalSection],
    ) -> Optional[LocalSection]:
        """Find a section for a site, checking updates first."""
        if site_id in updates:
            return updates[site_id]
        if site_id in caller_cover.sites:
            return LocalSection(
                site_id=site_id, trust=TrustLevel.RESIDUAL
            )
        return None

    def _find_best_matching_section(
        self,
        sections: Dict[SiteId, LocalSection],
        target_site_id: SiteId,
        call_edge: CallEdge,
    ) -> Optional[LocalSection]:
        """Find the best section matching a target site.

        Tries exact match first, then name-based matching.
        """
        # Exact match
        if target_site_id in sections:
            return sections[target_site_id]

        # Name-based matching: look for sections whose name
        # contains the target parameter name
        target_param = target_site_id.name.split(".")[-1]
        if target_param.startswith("actual_"):
            target_param = target_param[len("actual_"):]

        for site_id, section in sections.items():
            site_param = site_id.name.split(".")[-1]
            if site_param == target_param:
                return section

        # Match by argument position
        arg_names = call_edge.arguments
        for idx, arg_name in enumerate(arg_names):
            # Find callee's idx-th parameter section
            for site_id, section in sections.items():
                if site_id.kind == SiteKind.ARGUMENT_BOUNDARY:
                    if site_id.name.endswith(f".{arg_name}"):
                        return section

        return None

    def _reindex_refinements_to_caller(
        self,
        refinements: Dict[str, Any],
        call_edge: CallEdge,
    ) -> Dict[str, Any]:
        """Reindex refinement keys from callee naming to caller naming.

        For example, if callee has refinement "lst.non_empty" and the
        actual argument was "my_list", rename to "my_list.non_empty".
        """
        if not refinements:
            return {}

        reindexed: Dict[str, Any] = {}
        callee_name = call_edge.callee

        for key, value in refinements.items():
            # Strip callee function prefix if present
            new_key = key
            if key.startswith(f"{callee_name}."):
                suffix = key[len(callee_name) + 1:]
                new_key = f"{call_edge.caller}.{suffix}"

            reindexed[new_key] = value

        return reindexed

    def _reindex_refinements_to_callee(
        self,
        refinements: Dict[str, Any],
        call_edge: CallEdge,
        callee_site_id: SiteId,
    ) -> Dict[str, Any]:
        """Reindex refinement keys from caller naming to callee naming.

        For example, if caller has refinement "my_list.non_empty" and
        the formal parameter is "lst", rename to "lst.non_empty".
        """
        if not refinements:
            return {}

        reindexed: Dict[str, Any] = {}
        caller_name = call_edge.caller

        for key, value in refinements.items():
            new_key = key
            if key.startswith(f"{caller_name}."):
                suffix = key[len(caller_name) + 1:]
                callee_prefix = callee_site_id.name.split(".")[0]
                new_key = f"{callee_prefix}.{suffix}"

            reindexed[new_key] = value

        return reindexed

    # -- Summary queries ----------------------------------------------------

    def get_summary(self, func_name: str) -> Optional[FunctionSummary]:
        """Get the computed summary for a function."""
        return self._summaries.get(func_name)

    def has_summary(self, func_name: str) -> bool:
        """Check whether a summary exists for a function."""
        return func_name in self._summaries

    def clear(self) -> None:
        """Clear all summaries and logs."""
        self._summaries.clear()
        self._propagation_log.clear()
