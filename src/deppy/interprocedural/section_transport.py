"""Import callee sections at call sites via actual-to-formal reindexing.

In the sheaf-descent framework, a function call is modeled as a span of
morphisms between the caller's cover and the callee's cover:

    caller_actual_site ---> callee_formal_site   (actual -> formal)
    callee_return_site ---> caller_result_site    (return -> caller)

This module provides SectionTransporter which creates the morphisms for
these transport steps and applies them to move sections across call
boundaries.  The morphisms carry RestrictionData with kind
ACTUAL_TO_FORMAL or FORMAL_TO_RETURN.
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

from deppy.core._protocols import (
    BoundarySection,
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    RestrictionKind,
    make_actual_to_formal_restriction,
    make_return_to_caller_restriction,
    apply_restriction,
)
from deppy.interprocedural.call_graph import CallEdge


# ---------------------------------------------------------------------------
# Transport result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TransportResult:
    """Result of transporting sections across a call boundary.

    Attributes:
        _sections: The transported sections at target sites.
        _morphisms: The morphisms used for the transport.
        _source_sites: The source sites from which sections were transported.
        _target_sites: The target sites receiving the transported sections.
    """

    _sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    _morphisms: List[ConcreteMorphism] = field(default_factory=list)
    _source_sites: Tuple[SiteId, ...] = ()
    _target_sites: Tuple[SiteId, ...] = ()

    @property
    def sections(self) -> Dict[SiteId, LocalSection]:
        return dict(self._sections)

    @property
    def morphisms(self) -> List[ConcreteMorphism]:
        return list(self._morphisms)

    @property
    def source_sites(self) -> Tuple[SiteId, ...]:
        return self._source_sites

    @property
    def target_sites(self) -> Tuple[SiteId, ...]:
        return self._target_sites

    @property
    def is_empty(self) -> bool:
        return len(self._sections) == 0


# ---------------------------------------------------------------------------
# Formal-actual parameter mapping
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ParameterMapping:
    """Mapping between actual arguments and formal parameters.

    Attributes:
        _actual_to_formal: Maps actual arg site IDs to formal param site IDs.
        _actual_names: The actual argument names in call order.
        _formal_names: The formal parameter names in definition order.
        _name_mapping: Maps actual names to formal names.
    """

    _actual_to_formal: Dict[SiteId, SiteId] = field(default_factory=dict)
    _actual_names: Tuple[str, ...] = ()
    _formal_names: Tuple[str, ...] = ()
    _name_mapping: Dict[str, str] = field(default_factory=dict)

    @property
    def actual_to_formal(self) -> Dict[SiteId, SiteId]:
        return dict(self._actual_to_formal)

    @property
    def name_mapping(self) -> Dict[str, str]:
        return dict(self._name_mapping)


def _build_parameter_mapping(
    call_edge: CallEdge,
    caller_cover: Cover,
    callee_cover: Cover,
) -> ParameterMapping:
    """Build the mapping from caller actual sites to callee formal sites.

    Matches arguments by position, falling back to name matching for
    keyword arguments.
    """
    actual_to_formal: Dict[SiteId, SiteId] = {}
    name_mapping: Dict[str, str] = {}

    # Collect callee formal parameter sites in order
    formal_sites: List[Tuple[str, SiteId]] = []
    for site_id in sorted(callee_cover.input_boundary, key=lambda s: s.name):
        if site_id.kind == SiteKind.ARGUMENT_BOUNDARY:
            parts = site_id.name.split(".")
            param_name = parts[-1] if parts else site_id.name
            formal_sites.append((param_name, site_id))

    # Skip 'self' parameter for method calls
    if call_edge.is_method_call and formal_sites:
        first_name = formal_sites[0][0]
        if first_name == "self" or first_name == "cls":
            formal_sites = formal_sites[1:]

    # Match positional arguments
    arg_names = call_edge.arguments
    for idx, arg_name in enumerate(arg_names):
        if idx >= len(formal_sites):
            break
        formal_name, formal_site_id = formal_sites[idx]

        # Build actual site ID
        actual_site_id = SiteId(
            kind=SiteKind.ARGUMENT_BOUNDARY,
            name=f"{call_edge.caller}.actual_{arg_name}",
            source_location=(
                call_edge.call_site_id.source_location
                if call_edge.call_site_id
                else None
            ),
        )

        actual_to_formal[actual_site_id] = formal_site_id
        name_mapping[arg_name] = formal_name

    # Match keyword arguments
    formal_name_map = {name: sid for name, sid in formal_sites}
    for kw_name, kw_value in call_edge.keyword_arguments:
        if kw_name == "**":
            continue  # Skip **kwargs
        if kw_name in formal_name_map:
            actual_site_id = SiteId(
                kind=SiteKind.ARGUMENT_BOUNDARY,
                name=f"{call_edge.caller}.actual_{kw_value}",
                source_location=(
                    call_edge.call_site_id.source_location
                    if call_edge.call_site_id
                    else None
                ),
            )
            actual_to_formal[actual_site_id] = formal_name_map[kw_name]
            name_mapping[kw_value] = kw_name

    return ParameterMapping(
        _actual_to_formal=actual_to_formal,
        _actual_names=arg_names,
        _formal_names=tuple(n for n, _ in formal_sites),
        _name_mapping=name_mapping,
    )


# ---------------------------------------------------------------------------
# SectionTransporter
# ---------------------------------------------------------------------------

class SectionTransporter:
    """Transport sections across call boundaries using reindexing morphisms.

    Creates ConcreteMorphism instances with ACTUAL_TO_FORMAL and
    FORMAL_TO_RETURN restriction kinds, and applies them to transport
    sections between caller and callee covers.
    """

    def __init__(
        self,
        *,
        preserve_all_refinements: bool = False,
        trust_policy: str = "downgrade",
    ) -> None:
        """Initialize the transporter.

        Args:
            preserve_all_refinements: If True, all refinement keys survive
                transport. Otherwise, only explicitly preserved keys survive.
            trust_policy: One of "downgrade" (reduce trust level on transport),
                "preserve" (keep trust level), or "residual" (set to RESIDUAL).
        """
        self._preserve_all = preserve_all_refinements
        self._trust_policy = trust_policy
        self._transport_log: List[TransportResult] = []

    @property
    def transport_log(self) -> List[TransportResult]:
        return list(self._transport_log)

    # -- Actual to formal ---------------------------------------------------

    def transport_actual_to_formal(
        self,
        actual_sections: Dict[SiteId, LocalSection],
        call_edge: CallEdge,
        callee_cover: Cover,
        caller_cover: Optional[Cover] = None,
    ) -> TransportResult:
        """Transport actual argument sections to callee formal parameters.

        For each actual argument at the call site, creates a morphism
        from the actual site to the corresponding formal parameter site,
        then applies the morphism to transport the section.

        Returns a TransportResult with the transported sections.
        """
        if caller_cover is None:
            caller_cover = Cover()

        param_mapping = _build_parameter_mapping(
            call_edge, caller_cover, callee_cover
        )

        transported: Dict[SiteId, LocalSection] = {}
        morphisms: List[ConcreteMorphism] = []
        source_sites: List[SiteId] = []
        target_sites: List[SiteId] = []

        for actual_site_id, formal_site_id in param_mapping.actual_to_formal.items():
            # Find the actual section
            actual_section = self._find_actual_section(
                actual_sections, actual_site_id, call_edge
            )
            if actual_section is None:
                continue

            # Determine preserved keys
            preserved = self._compute_preserved_keys(
                actual_section, call_edge
            )

            # Extract names for the morphism
            actual_name = actual_site_id.name.split(".")[-1]
            if actual_name.startswith("actual_"):
                actual_name = actual_name[len("actual_"):]
            formal_name = formal_site_id.name.split(".")[-1]

            # Create the transport morphism
            morphism = make_actual_to_formal_restriction(
                caller_arg_site=actual_site_id,
                callee_param_site=formal_site_id,
                actual_name=actual_name,
                formal_name=formal_name,
                preserved_keys=preserved,
            )
            morphisms.append(morphism)

            # Apply the restriction to transport the section
            formal_section = self._apply_transport(
                actual_section, morphism, formal_site_id
            )
            transported[formal_site_id] = formal_section
            source_sites.append(actual_site_id)
            target_sites.append(formal_site_id)

        result = TransportResult(
            _sections=transported,
            _morphisms=morphisms,
            _source_sites=tuple(source_sites),
            _target_sites=tuple(target_sites),
        )
        self._transport_log.append(result)
        return result

    # -- Return to caller ---------------------------------------------------

    def transport_return_to_caller(
        self,
        return_sections: Dict[SiteId, LocalSection],
        call_edge: CallEdge,
        callee_cover: Optional[Cover] = None,
    ) -> TransportResult:
        """Transport callee return sections to caller call-result sites.

        For each return site in the callee's output boundary, creates a
        morphism to the caller's call-result site and transports the section.
        """
        transported: Dict[SiteId, LocalSection] = {}
        morphisms: List[ConcreteMorphism] = []
        source_sites: List[SiteId] = []
        target_sites: List[SiteId] = []

        # Determine the caller's call-result site
        call_result_id = call_edge.call_site_id
        if call_result_id is None:
            call_result_id = SiteId(
                kind=SiteKind.CALL_RESULT,
                name=f"{call_edge.caller}.call_{call_edge.callee}",
            )

        for return_site_id, return_section in return_sections.items():
            if return_site_id.kind != SiteKind.RETURN_OUTPUT_BOUNDARY:
                continue

            preserved = self._compute_preserved_keys(
                return_section, call_edge
            )

            morphism = make_return_to_caller_restriction(
                callee_return_site=return_site_id,
                caller_result_site=call_result_id,
                preserved_keys=preserved,
            )
            morphisms.append(morphism)

            caller_section = self._apply_transport(
                return_section, morphism, call_result_id
            )
            transported[call_result_id] = caller_section
            source_sites.append(return_site_id)
            target_sites.append(call_result_id)

        result = TransportResult(
            _sections=transported,
            _morphisms=morphisms,
            _source_sites=tuple(source_sites),
            _target_sites=tuple(target_sites),
        )
        self._transport_log.append(result)
        return result

    # -- Morphism creation --------------------------------------------------

    def create_transport_morphisms(
        self,
        call_edge: CallEdge,
        caller_cover: Cover,
        callee_cover: Cover,
    ) -> List[ConcreteMorphism]:
        """Create all transport morphisms for a call edge.

        Returns both actual-to-formal and return-to-caller morphisms
        without applying them to any sections.
        """
        morphisms: List[ConcreteMorphism] = []

        # Actual-to-formal morphisms
        param_mapping = _build_parameter_mapping(
            call_edge, caller_cover, callee_cover
        )
        for actual_site_id, formal_site_id in param_mapping.actual_to_formal.items():
            actual_name = actual_site_id.name.split(".")[-1]
            if actual_name.startswith("actual_"):
                actual_name = actual_name[len("actual_"):]
            formal_name = formal_site_id.name.split(".")[-1]

            morphism = make_actual_to_formal_restriction(
                caller_arg_site=actual_site_id,
                callee_param_site=formal_site_id,
                actual_name=actual_name,
                formal_name=formal_name,
            )
            morphisms.append(morphism)

        # Return-to-caller morphisms
        call_result_id = call_edge.call_site_id
        if call_result_id is None:
            call_result_id = SiteId(
                kind=SiteKind.CALL_RESULT,
                name=f"{call_edge.caller}.call_{call_edge.callee}",
            )

        for site_id in callee_cover.output_boundary:
            if site_id.kind == SiteKind.RETURN_OUTPUT_BOUNDARY:
                morphism = make_return_to_caller_restriction(
                    callee_return_site=site_id,
                    caller_result_site=call_result_id,
                )
                morphisms.append(morphism)

        return morphisms

    # -- Batch transport ----------------------------------------------------

    def transport_boundary_pair(
        self,
        caller_cover: Cover,
        callee_cover: Cover,
        call_edge: CallEdge,
        caller_sections: Dict[SiteId, LocalSection],
        callee_return_sections: Dict[SiteId, LocalSection],
    ) -> Tuple[TransportResult, TransportResult]:
        """Perform both directions of transport for a call edge.

        Returns (forward_result, backward_result) where:
        - forward_result: actual -> formal transport
        - backward_result: return -> caller transport
        """
        forward = self.transport_actual_to_formal(
            caller_sections, call_edge, callee_cover, caller_cover
        )
        backward = self.transport_return_to_caller(
            callee_return_sections, call_edge, callee_cover
        )
        return forward, backward

    # -- Internal helpers ---------------------------------------------------

    def _find_actual_section(
        self,
        sections: Dict[SiteId, LocalSection],
        actual_site_id: SiteId,
        call_edge: CallEdge,
    ) -> Optional[LocalSection]:
        """Find the section for an actual argument.

        Tries exact match, then name-based matching.
        """
        if actual_site_id in sections:
            return sections[actual_site_id]

        # Name-based fallback
        target_name = actual_site_id.name.split(".")[-1]
        if target_name.startswith("actual_"):
            target_name = target_name[len("actual_"):]

        for site_id, section in sections.items():
            site_name = site_id.name.split(".")[-1]
            if site_name == target_name:
                return section

        # Position-based fallback
        arg_names = call_edge.arguments
        for idx, arg_name in enumerate(arg_names):
            if target_name == arg_name:
                for site_id, section in sections.items():
                    if site_id.kind == SiteKind.ARGUMENT_BOUNDARY:
                        s_name = site_id.name.split(".")[-1]
                        if s_name == arg_name:
                            return section

        return None

    def _compute_preserved_keys(
        self,
        section: LocalSection,
        call_edge: CallEdge,
    ) -> FrozenSet[str]:
        """Determine which refinement keys survive transport."""
        if self._preserve_all:
            return frozenset(section.refinements.keys())

        # Preserve keys that are position-independent
        preserved: Set[str] = set()
        for key in section.refinements:
            # Keep type-level refinements
            if any(
                key.startswith(prefix)
                for prefix in ("type_", "non_", "positive", "bounded", "len_")
            ):
                preserved.add(key)
            # Keep keys without function-specific naming
            if "." not in key:
                preserved.add(key)

        return frozenset(preserved)

    def _apply_transport(
        self,
        source_section: LocalSection,
        morphism: ConcreteMorphism,
        target_site_id: SiteId,
    ) -> LocalSection:
        """Apply a transport morphism to a section.

        Uses the restriction map's apply_restriction, then adjusts
        trust according to policy.
        """
        # Create a section with the source site ID for apply_restriction
        adapted_section = LocalSection(
            site_id=morphism.source,
            carrier_type=source_section.carrier_type,
            refinements=dict(source_section.refinements),
            trust=source_section.trust,
            provenance=source_section.provenance,
            witnesses=dict(source_section.witnesses),
        )

        transported = apply_restriction(morphism, adapted_section)

        # Adjust trust according to policy
        trust = transported.trust
        if self._trust_policy == "downgrade":
            if trust == TrustLevel.PROOF_BACKED:
                trust = TrustLevel.TRUSTED_AUTO
            elif trust == TrustLevel.TRUSTED_AUTO:
                trust = TrustLevel.BOUNDED_AUTO
        elif self._trust_policy == "residual":
            trust = TrustLevel.RESIDUAL

        return LocalSection(
            site_id=target_site_id,
            carrier_type=transported.carrier_type,
            refinements=transported.refinements,
            trust=trust,
            provenance=transported.provenance,
            witnesses=transported.witnesses,
        )

    def clear_log(self) -> None:
        """Clear the transport log."""
        self._transport_log.clear()
