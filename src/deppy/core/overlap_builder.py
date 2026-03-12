"""Build overlap edges between observation sites.

Analyzes the morphism structure and site metadata to discover four categories
of overlaps (from the monograph):

1. **Lineage overlaps** -- two sites refer to the same SSA variable lineage.
2. **Control overlaps** -- a branch guard narrows a variable whose SSA site
   already exists.
3. **Call overlaps** -- a call site's return flows into an SSA site, or an
   argument site feeds into a call.
4. **Tensor pack-transport overlaps** -- shape, order, and indexing sites for
   the same tensor.

Additionally handles:

5. **Error-path overlaps** -- an error site is viable on a path that includes
   a given SSA or call site.
6. **Loop-header overlaps** -- loop header invariant sites overlap with SSA
   sites for the loop variable.
7. **Proof/trace overlaps** -- proof and trace sites that reference the same
   underlying value.
8. **Module-boundary overlaps** -- module summary sites overlapping with
   argument/return sites.

Key class: :class:`OverlapBuilder`.
"""

from __future__ import annotations

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

from deppy.core._protocols import Cover, Morphism, SiteId, SiteKind
from deppy.core.site import ConcreteMorphism, ConcreteSite


# ═══════════════════════════════════════════════════════════════════════════════
# Overlap kind taxonomy
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class OverlapEdge:
    """An overlap between two sites, with a reason annotation.

    Attributes:
        site_a: First site in the overlap.
        site_b: Second site in the overlap.
        kind: The category of overlap.
        reason: Human-readable explanation.
        confidence: How certain we are this overlap is real (0..1).
    """

    _site_a: SiteId
    _site_b: SiteId
    _kind: str
    _reason: str = ""
    _confidence: float = 1.0

    @property
    def site_a(self) -> SiteId:
        return self._site_a

    @property
    def site_b(self) -> SiteId:
        return self._site_b

    @property
    def kind(self) -> str:
        return self._kind

    @property
    def reason(self) -> str:
        return self._reason

    @property
    def confidence(self) -> float:
        return self._confidence

    @property
    def pair(self) -> Tuple[SiteId, SiteId]:
        return (self._site_a, self._site_b)

    @property
    def canonical_pair(self) -> Tuple[SiteId, SiteId]:
        """Canonical ordering so (a, b) == (b, a)."""
        if str(self._site_a) <= str(self._site_b):
            return (self._site_a, self._site_b)
        return (self._site_b, self._site_a)

    def __repr__(self) -> str:
        return (
            f"OverlapEdge({self._site_a} <-> {self._site_b}, "
            f"kind={self._kind})"
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Helper: metadata extraction
# ═══════════════════════════════════════════════════════════════════════════════


def _get_meta(site: Any, key: str, default: Any = None) -> Any:
    """Safely extract metadata from a ConcreteSite."""
    if hasattr(site, "metadata") and site.metadata is not None:
        return site.metadata.get(key, default)
    if hasattr(site, "_metadata") and site._metadata is not None:
        return site._metadata.get(key, default)
    return default


def _get_site_kind(site_id: SiteId) -> SiteKind:
    """Extract the SiteKind from a SiteId."""
    return site_id.kind


# ═══════════════════════════════════════════════════════════════════════════════
# Overlap builder
# ═══════════════════════════════════════════════════════════════════════════════


class OverlapBuilder:
    """Analyze sites and morphisms to discover overlap edges.

    The builder examines the site graph's structure (kinds, metadata,
    morphism connectivity) to produce a complete overlap list.

    Usage::

        builder = OverlapBuilder()
        edges = builder.build_overlaps(cover.sites, cover.morphisms)
        # edges is List[Tuple[SiteId, SiteId]]
    """

    def __init__(self, confidence_threshold: float = 0.3) -> None:
        self._confidence_threshold = confidence_threshold
        self._edges: List[OverlapEdge] = []
        self._seen: Set[Tuple[SiteId, SiteId]] = set()

    # ── Main entry point ───────────────────────────────────────────────────

    def build_overlaps(
        self,
        sites: Mapping[SiteId, Any],
        morphisms: Sequence[Morphism],
    ) -> List[Tuple[SiteId, SiteId]]:
        """Compute all overlap pairs from sites and morphisms.

        Returns deduplicated list of (SiteId, SiteId) pairs.
        """
        self._edges.clear()
        self._seen.clear()

        # Run all overlap detectors
        self._lineage_overlaps(sites)
        self._control_overlaps(sites)
        self._call_overlaps(sites)
        self._tensor_pack_overlaps(sites)
        self._error_path_overlaps(sites)
        self._loop_header_overlaps(sites)
        self._proof_trace_overlaps(sites)
        self._module_boundary_overlaps(sites)
        self._morphism_induced_overlaps(sites, morphisms)

        # Filter by confidence and deduplicate
        result: List[Tuple[SiteId, SiteId]] = []
        seen_pairs: Set[Tuple[SiteId, SiteId]] = set()

        for edge in self._edges:
            if edge.confidence < self._confidence_threshold:
                continue
            canonical = edge.canonical_pair
            if canonical not in seen_pairs:
                seen_pairs.add(canonical)
                result.append(canonical)

        return result

    def build_overlaps_annotated(
        self,
        sites: Mapping[SiteId, Any],
        morphisms: Sequence[Morphism],
    ) -> List[OverlapEdge]:
        """Like build_overlaps but returns annotated OverlapEdge objects."""
        self.build_overlaps(sites, morphisms)

        # Deduplicate, keeping highest confidence
        best: Dict[Tuple[SiteId, SiteId], OverlapEdge] = {}
        for edge in self._edges:
            if edge.confidence < self._confidence_threshold:
                continue
            canonical = edge.canonical_pair
            existing = best.get(canonical)
            if existing is None or edge.confidence > existing.confidence:
                best[canonical] = edge

        return list(best.values())

    # ── Lineage overlaps ───────────────────────────────────────────────────

    def _lineage_overlaps(self, sites: Mapping[SiteId, Any]) -> None:
        """Find overlaps between SSA sites that share a variable lineage.

        Two SSA sites for the same variable name (different versions) overlap
        because they represent successive definitions of the same value.
        """
        # Group SSA sites by variable name
        var_groups: Dict[str, List[SiteId]] = {}
        for sid, site in sites.items():
            if sid.kind == SiteKind.SSA_VALUE:
                var_name = _get_meta(site, "var_name", "")
                if not var_name:
                    # Try to extract from site name (format: {var}_{version})
                    parts = sid.name.rsplit("_", 1)
                    if len(parts) == 2 and parts[1].isdigit():
                        var_name = parts[0]
                    else:
                        var_name = sid.name
                var_groups.setdefault(var_name, []).append(sid)

        # Helper to extract version from a site id
        def _version_key(s: SiteId) -> int:
            site = sites.get(s)
            v = _get_meta(site, "ssa_version", 0) if site else 0
            if v:
                return v
            parts = s.name.rsplit("_", 1)
            if len(parts) == 2 and parts[1].isdigit():
                return int(parts[1])
            return 0

        # Create lineage overlaps between consecutive versions
        for var_name, group in var_groups.items():
            if len(group) < 2:
                continue
            sorted_group = sorted(group, key=_version_key)
            for i in range(len(sorted_group) - 1):
                self._add_edge(
                    sorted_group[i],
                    sorted_group[i + 1],
                    "lineage",
                    f"SSA lineage for '{var_name}': "
                    f"v{_version_key(sorted_group[i])} -> "
                    f"v{_version_key(sorted_group[i + 1])}",
                    confidence=1.0,
                )

        # Also connect argument sites to their first SSA definition
        for sid, site in sites.items():
            if sid.kind == SiteKind.ARGUMENT_BOUNDARY:
                param_name = _get_meta(site, "param_name", "")
                if param_name and param_name in var_groups:
                    ssa_sites = var_groups[param_name]
                    if ssa_sites:
                        first_ssa = min(ssa_sites, key=_version_key)
                        self._add_edge(
                            sid,
                            first_ssa,
                            "lineage",
                            f"Argument '{param_name}' flows to SSA definition",
                            confidence=1.0,
                        )

    # ── Control overlaps ───────────────────────────────────────────────────

    def _control_overlaps(self, sites: Mapping[SiteId, Any]) -> None:
        """Find overlaps between branch guards and the variables they narrow.

        A branch guard site that narrows variable 'x' overlaps with every
        SSA site for 'x' that is in scope at the branch point.
        """
        guard_sites: List[Tuple[SiteId, Any]] = []
        ssa_by_var: Dict[str, List[SiteId]] = {}

        for sid, site in sites.items():
            if sid.kind == SiteKind.BRANCH_GUARD:
                guard_sites.append((sid, site))
            elif sid.kind == SiteKind.SSA_VALUE:
                var_name = _get_meta(site, "var_name", "")
                if not var_name:
                    parts = sid.name.rsplit("_", 1)
                    if len(parts) == 2 and parts[1].isdigit():
                        var_name = parts[0]
                    else:
                        var_name = sid.name
                ssa_by_var.setdefault(var_name, []).append(sid)

        for guard_sid, guard_site in guard_sites:
            narrowed = _get_meta(guard_site, "narrowed_vars", [])
            condition = _get_meta(guard_site, "condition_text", "")

            if isinstance(narrowed, list):
                for var_name in narrowed:
                    ssa_sites = ssa_by_var.get(var_name, [])
                    for ssa_sid in ssa_sites:
                        self._add_edge(
                            guard_sid,
                            ssa_sid,
                            "control",
                            f"Guard '{condition}' narrows '{var_name}'",
                            confidence=0.9,
                        )

            # If no explicit narrowed_vars, try to parse condition for variable names
            if not narrowed and condition:
                for var_name, ssa_sites in ssa_by_var.items():
                    if var_name in condition:
                        for ssa_sid in ssa_sites:
                            self._add_edge(
                                guard_sid,
                                ssa_sid,
                                "control",
                                f"Guard '{condition}' references '{var_name}'",
                                confidence=0.6,
                            )

    # ── Call overlaps ──────────────────────────────────────────────────────

    def _call_overlaps(self, sites: Mapping[SiteId, Any]) -> None:
        """Find overlaps between call sites and argument/SSA sites.

        A call result site overlaps with:
        - Argument sites that feed into the call
        - SSA sites that receive the call's return value
        - Other call sites in a call chain
        """
        call_sites: List[Tuple[SiteId, Any]] = []
        arg_sites: Dict[str, SiteId] = {}
        ssa_by_var: Dict[str, List[SiteId]] = {}

        for sid, site in sites.items():
            if sid.kind == SiteKind.CALL_RESULT:
                call_sites.append((sid, site))
            elif sid.kind == SiteKind.ARGUMENT_BOUNDARY:
                param_name = _get_meta(site, "param_name", "")
                if param_name:
                    arg_sites[param_name] = sid
            elif sid.kind == SiteKind.SSA_VALUE:
                var_name = _get_meta(site, "var_name", "")
                if not var_name:
                    parts = sid.name.rsplit("_", 1)
                    if len(parts) == 2 and parts[1].isdigit():
                        var_name = parts[0]
                ssa_by_var.setdefault(var_name, []).append(sid)

        # Connect call sites to return output boundary
        return_sites: List[SiteId] = [
            sid for sid in sites if sid.kind == SiteKind.RETURN_OUTPUT_BOUNDARY
        ]

        for call_sid, call_site in call_sites:
            callee = _get_meta(call_site, "callee_name", "")

            # Connect to SSA sites that might receive the call result
            # Heuristic: SSA variables named like the callee or call_idx pattern
            call_idx = _get_meta(call_site, "call_index", 0)
            possible_result_vars = [
                f"call_{callee}_{call_idx}",
                callee,
                f"result_{call_idx}",
            ]
            for var_name in possible_result_vars:
                for ssa_sid in ssa_by_var.get(var_name, []):
                    self._add_edge(
                        call_sid,
                        ssa_sid,
                        "call",
                        f"Call to '{callee}' result -> SSA '{var_name}'",
                        confidence=0.8,
                    )

        # Connect consecutive calls (call chain overlaps)
        if len(call_sites) > 1:
            # Sort by call_index
            sorted_calls = sorted(
                call_sites,
                key=lambda cs: _get_meta(cs[1], "call_index", 0) or 0,
            )
            for i in range(len(sorted_calls) - 1):
                self._add_edge(
                    sorted_calls[i][0],
                    sorted_calls[i + 1][0],
                    "call",
                    "Consecutive calls in call chain",
                    confidence=0.5,
                )

    # ── Tensor pack-transport overlaps ─────────────────────────────────────

    def _tensor_pack_overlaps(self, sites: Mapping[SiteId, Any]) -> None:
        """Find overlaps between tensor shape, order, and indexing sites.

        All three tensor site families for the same tensor name overlap
        because they describe complementary aspects of the same tensor.
        """
        # Group tensor sites by tensor name
        tensor_groups: Dict[str, Dict[SiteKind, List[SiteId]]] = {}
        tensor_kinds = {
            SiteKind.TENSOR_SHAPE,
            SiteKind.TENSOR_ORDER,
            SiteKind.TENSOR_INDEXING,
        }

        for sid, site in sites.items():
            if sid.kind in tensor_kinds:
                tensor_name = _get_meta(site, "tensor_name", "")
                if not tensor_name:
                    # Extract from site name
                    for prefix in ("shape_", "order_", "idx_"):
                        if sid.name.startswith(prefix):
                            tensor_name = sid.name[len(prefix):]
                            break
                if tensor_name:
                    group = tensor_groups.setdefault(tensor_name, {})
                    group.setdefault(sid.kind, []).append(sid)

        # Create overlaps between all tensor sites for the same tensor
        for tensor_name, kind_map in tensor_groups.items():
            all_tensor_sites: List[SiteId] = []
            for site_list in kind_map.values():
                all_tensor_sites.extend(site_list)

            for i in range(len(all_tensor_sites)):
                for j in range(i + 1, len(all_tensor_sites)):
                    a, b = all_tensor_sites[i], all_tensor_sites[j]
                    self._add_edge(
                        a,
                        b,
                        "tensor_pack",
                        f"Tensor '{tensor_name}': "
                        f"{a.kind.value} <-> {b.kind.value}",
                        confidence=1.0,
                    )

        # Also connect tensor sites to SSA sites that hold the tensor value
        ssa_sites = {
            sid: site for sid, site in sites.items()
            if sid.kind == SiteKind.SSA_VALUE
        }
        for tensor_name, kind_map in tensor_groups.items():
            for ssa_sid, ssa_site in ssa_sites.items():
                ssa_var = _get_meta(ssa_site, "var_name", "")
                if ssa_var == tensor_name:
                    for site_list in kind_map.values():
                        for tensor_sid in site_list:
                            self._add_edge(
                                ssa_sid,
                                tensor_sid,
                                "tensor_pack",
                                f"SSA '{ssa_var}' is tensor with "
                                f"{tensor_sid.kind.value} site",
                                confidence=0.9,
                            )

    # ── Error-path overlaps ────────────────────────────────────────────────

    def _error_path_overlaps(self, sites: Mapping[SiteId, Any]) -> None:
        """Find overlaps between error sites and the sites on their paths.

        An error site overlaps with:
        - SSA sites for variables involved in the error condition
        - Call sites that may raise the error
        - Guard sites that could prevent the error
        """
        error_sites: List[Tuple[SiteId, Any]] = []
        ssa_sites: Dict[str, List[SiteId]] = {}
        call_sites: List[Tuple[SiteId, Any]] = []
        guard_sites: List[Tuple[SiteId, Any]] = []

        for sid, site in sites.items():
            if sid.kind == SiteKind.ERROR:
                error_sites.append((sid, site))
            elif sid.kind == SiteKind.SSA_VALUE:
                var_name = _get_meta(site, "var_name", "")
                if not var_name:
                    parts = sid.name.rsplit("_", 1)
                    if len(parts) == 2 and parts[1].isdigit():
                        var_name = parts[0]
                ssa_sites.setdefault(var_name, []).append(sid)
            elif sid.kind == SiteKind.CALL_RESULT:
                call_sites.append((sid, site))
            elif sid.kind == SiteKind.BRANCH_GUARD:
                guard_sites.append((sid, site))

        for error_sid, error_site in error_sites:
            source_op = _get_meta(error_site, "source_op", "")
            error_kind = _get_meta(error_site, "error_kind", "")

            # Connect to SSA sites mentioned in source_op
            if source_op:
                for var_name, var_sites in ssa_sites.items():
                    if var_name in source_op:
                        for ssa_sid in var_sites:
                            self._add_edge(
                                error_sid,
                                ssa_sid,
                                "error_path",
                                f"Error '{error_kind}' involves '{var_name}'",
                                confidence=0.7,
                            )

            # Connect to call sites that might raise this error
            for call_sid, call_site in call_sites:
                callee = _get_meta(call_site, "callee_name", "")
                if callee and (callee in source_op or not source_op):
                    self._add_edge(
                        error_sid,
                        call_sid,
                        "error_path",
                        f"Error '{error_kind}' from call to '{callee}'",
                        confidence=0.5 if source_op else 0.3,
                    )

            # Connect to guard sites that might prevent the error
            guarded = _get_meta(error_site, "guarded", False)
            if guarded:
                for guard_sid, guard_site in guard_sites:
                    self._add_edge(
                        error_sid,
                        guard_sid,
                        "error_path",
                        f"Error '{error_kind}' guarded by condition",
                        confidence=0.6,
                    )

    # ── Loop-header overlaps ───────────────────────────────────────────────

    def _loop_header_overlaps(self, sites: Mapping[SiteId, Any]) -> None:
        """Find overlaps between loop header sites and related SSA/guard sites.

        A loop header invariant site overlaps with:
        - SSA sites for the loop variable
        - Branch guard sites for loop conditions
        """
        loop_sites: List[Tuple[SiteId, Any]] = []
        ssa_by_var: Dict[str, List[SiteId]] = {}
        guard_sites: List[Tuple[SiteId, Any]] = []

        for sid, site in sites.items():
            if sid.kind == SiteKind.LOOP_HEADER_INVARIANT:
                loop_sites.append((sid, site))
            elif sid.kind == SiteKind.SSA_VALUE:
                var_name = _get_meta(site, "var_name", "")
                if not var_name:
                    parts = sid.name.rsplit("_", 1)
                    if len(parts) == 2 and parts[1].isdigit():
                        var_name = parts[0]
                ssa_by_var.setdefault(var_name, []).append(sid)
            elif sid.kind == SiteKind.BRANCH_GUARD:
                guard_sites.append((sid, site))

        for loop_sid, loop_site in loop_sites:
            loop_var = _get_meta(loop_site, "loop_variable", "")
            if loop_var and loop_var in ssa_by_var:
                for ssa_sid in ssa_by_var[loop_var]:
                    self._add_edge(
                        loop_sid,
                        ssa_sid,
                        "loop_header",
                        f"Loop variable '{loop_var}' SSA definition",
                        confidence=1.0,
                    )

            # Connect to guard sites (loop condition)
            for guard_sid, guard_site in guard_sites:
                narrowed = _get_meta(guard_site, "narrowed_vars", [])
                if isinstance(narrowed, list) and loop_var in narrowed:
                    self._add_edge(
                        loop_sid,
                        guard_sid,
                        "loop_header",
                        f"Loop guard narrows loop variable '{loop_var}'",
                        confidence=0.8,
                    )

    # ── Proof/trace overlaps ───────────────────────────────────────────────

    def _proof_trace_overlaps(self, sites: Mapping[SiteId, Any]) -> None:
        """Find overlaps between proof/trace sites and the values they reference.

        Proof and trace sites overlap with SSA sites for the values they
        constrain or observe.
        """
        proof_sites: List[Tuple[SiteId, Any]] = []
        trace_sites: List[Tuple[SiteId, Any]] = []
        ssa_by_var: Dict[str, List[SiteId]] = {}

        for sid, site in sites.items():
            if sid.kind == SiteKind.PROOF:
                proof_sites.append((sid, site))
            elif sid.kind == SiteKind.TRACE:
                trace_sites.append((sid, site))
            elif sid.kind == SiteKind.SSA_VALUE:
                var_name = _get_meta(site, "var_name", "")
                if not var_name:
                    parts = sid.name.rsplit("_", 1)
                    if len(parts) == 2 and parts[1].isdigit():
                        var_name = parts[0]
                ssa_by_var.setdefault(var_name, []).append(sid)

        # Connect proof sites to SSA sites they mention
        for proof_sid, proof_site in proof_sites:
            proposition = _get_meta(proof_site, "proposition", "")
            if proposition:
                for var_name, var_sites in ssa_by_var.items():
                    if var_name in str(proposition):
                        for ssa_sid in var_sites:
                            self._add_edge(
                                proof_sid,
                                ssa_sid,
                                "proof_trace",
                                f"Proof references '{var_name}'",
                                confidence=0.7,
                            )

        # Connect trace sites to SSA sites they observe
        for trace_sid, trace_site in trace_sites:
            trace_point = _get_meta(trace_site, "trace_point", "")
            if trace_point:
                for var_name, var_sites in ssa_by_var.items():
                    if var_name in trace_point:
                        for ssa_sid in var_sites:
                            self._add_edge(
                                trace_sid,
                                ssa_sid,
                                "proof_trace",
                                f"Trace observes '{var_name}'",
                                confidence=0.6,
                            )

        # Proof and trace sites for the same variable overlap with each other
        all_evidence: List[Tuple[SiteId, str]] = []
        for proof_sid, proof_site in proof_sites:
            prop = str(_get_meta(proof_site, "proposition", ""))
            all_evidence.append((proof_sid, prop))
        for trace_sid, trace_site in trace_sites:
            tp = str(_get_meta(trace_site, "trace_point", ""))
            all_evidence.append((trace_sid, tp))

        for i in range(len(all_evidence)):
            for j in range(i + 1, len(all_evidence)):
                sid_a, text_a = all_evidence[i]
                sid_b, text_b = all_evidence[j]
                # Skip if both are the same kind and no textual connection
                if sid_a.kind == sid_b.kind:
                    continue
                # Check for shared variable references
                for var_name in ssa_by_var:
                    if var_name in text_a and var_name in text_b:
                        self._add_edge(
                            sid_a,
                            sid_b,
                            "proof_trace",
                            f"Both reference '{var_name}'",
                            confidence=0.5,
                        )
                        break

    # ── Module-boundary overlaps ───────────────────────────────────────────

    def _module_boundary_overlaps(self, sites: Mapping[SiteId, Any]) -> None:
        """Find overlaps between module summary sites and boundary sites.

        Module summary sites overlap with argument and return sites because
        the module summary describes the function's public interface.
        """
        module_sites: List[SiteId] = []
        boundary_sites: List[SiteId] = []

        for sid in sites:
            if sid.kind == SiteKind.MODULE_SUMMARY:
                module_sites.append(sid)
            elif sid.kind in (
                SiteKind.ARGUMENT_BOUNDARY,
                SiteKind.RETURN_OUTPUT_BOUNDARY,
            ):
                boundary_sites.append(sid)

        for mod_sid in module_sites:
            for bnd_sid in boundary_sites:
                self._add_edge(
                    mod_sid,
                    bnd_sid,
                    "module_boundary",
                    f"Module summary <-> {bnd_sid.kind.value}",
                    confidence=0.7,
                )

    # ── Morphism-induced overlaps ──────────────────────────────────────────

    def _morphism_induced_overlaps(
        self,
        sites: Mapping[SiteId, Any],
        morphisms: Sequence[Morphism],
    ) -> None:
        """Find overlaps induced by the morphism structure.

        Two sites overlap if there exist morphisms from both to a common
        target, or if they are directly connected by a morphism.
        """
        site_set = frozenset(sites.keys())

        # Direct morphism connections
        for m in morphisms:
            if m.source in site_set and m.target in site_set:
                self._add_edge(
                    m.source,
                    m.target,
                    "morphism",
                    "Direct morphism connection",
                    confidence=1.0,
                )

        # Common target: if A -> C and B -> C, then A and B overlap
        target_to_sources: Dict[SiteId, List[SiteId]] = {}
        for m in morphisms:
            if m.source in site_set:
                target_to_sources.setdefault(m.target, []).append(m.source)

        for target, sources in target_to_sources.items():
            if len(sources) < 2:
                continue
            for i in range(len(sources)):
                for j in range(i + 1, len(sources)):
                    self._add_edge(
                        sources[i],
                        sources[j],
                        "morphism",
                        f"Common morphism target {target}",
                        confidence=0.9,
                    )

    # ── Edge management ────────────────────────────────────────────────────

    def _add_edge(
        self,
        a: SiteId,
        b: SiteId,
        kind: str,
        reason: str,
        confidence: float = 1.0,
    ) -> None:
        """Add an overlap edge, avoiding self-loops."""
        if a == b:
            return
        edge = OverlapEdge(
            _site_a=a,
            _site_b=b,
            _kind=kind,
            _reason=reason,
            _confidence=confidence,
        )
        self._edges.append(edge)

    # ── Diagnostics ────────────────────────────────────────────────────────

    @property
    def last_edges(self) -> List[OverlapEdge]:
        """All edges from the last build_overlaps call."""
        return list(self._edges)

    def overlap_kind_histogram(self) -> Dict[str, int]:
        """Histogram of overlap kinds from the last build."""
        hist: Dict[str, int] = {}
        for edge in self._edges:
            hist[edge.kind] = hist.get(edge.kind, 0) + 1
        return hist

    def summary_report(self) -> str:
        """Generate a summary report of discovered overlaps."""
        lines: List[str] = [
            f"OverlapBuilder: {len(self._edges)} total edges"
        ]
        for kind, count in sorted(
            self.overlap_kind_histogram().items(),
            key=lambda kv: kv[1],
            reverse=True,
        ):
            lines.append(f"  {kind}: {count}")
        return "\n".join(lines)

    def __repr__(self) -> str:
        return f"OverlapBuilder({len(self._edges)} edges)"
