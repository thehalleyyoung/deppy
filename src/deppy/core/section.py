"""Section construction, merging, restriction, and global section building.

Provides:
- SectionFactory: create LocalSection from site + type + refinements
- SectionMerger: merge two sections at an overlap
- SectionRestrictor: apply restriction map along a morphism
- GlobalSectionBuilder: collect local sections, check compatibility, produce GlobalSection
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

from deppy.core._protocols import (
    BoundarySection,
    Cover,
    GlobalSection,
    LocalSection,
    Morphism,
    SiteId,
    TrustLevel,
)


class SectionFactory:
    """Create LocalSection instances from site + type + refinement data."""

    @staticmethod
    def create(
        site_id: SiteId,
        carrier_type: Any = None,
        refinements: Optional[Dict[str, Any]] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: Optional[str] = None,
        witnesses: Optional[Dict[str, Any]] = None,
    ) -> LocalSection:
        """Create a new LocalSection.

        Args:
            site_id: The site at which this section lives.
            carrier_type: The base type (e.g. 'int', 'str', a type object).
            refinements: Predicate refinements keyed by name.
            trust: How this section was established.
            provenance: Textual provenance for debugging.
            witnesses: Proof witnesses or evidence.
        """
        return LocalSection(
            site_id=site_id,
            carrier_type=carrier_type,
            refinements=refinements or {},
            trust=trust,
            provenance=provenance,
            witnesses=witnesses or {},
        )


class SectionMerger:
    """Merge two local sections at an overlap.

    When two sites overlap, their sections must agree on the overlap.
    This merger creates a combined section that integrates information
    from both sections, taking the more informative value where they differ.
    """

    @staticmethod
    def merge(
        a: LocalSection,
        b: LocalSection,
        merged_site_id: Optional[SiteId] = None,
    ) -> LocalSection:
        """Merge two sections, combining their refinements.

        Uses the target site_id from a by default, or merged_site_id if given.
        Carrier types must match (or one must be None).
        """
        target_id = merged_site_id or a.site_id

        # Resolve carrier type
        if a.carrier_type is not None and b.carrier_type is not None:
            if a.carrier_type != b.carrier_type:
                raise ValueError(
                    f"Incompatible carrier types at merge: "
                    f"{a.carrier_type} vs {b.carrier_type}"
                )
            carrier = a.carrier_type
        else:
            carrier = a.carrier_type if a.carrier_type is not None else b.carrier_type

        # Merge refinements (a takes priority on conflicts)
        merged_refs = dict(b.refinements)
        merged_refs.update(a.refinements)

        # Merge witnesses
        merged_witnesses = dict(b.witnesses)
        merged_witnesses.update(a.witnesses)

        # Take the higher trust level
        trust = SectionMerger._max_trust(a.trust, b.trust)

        return LocalSection(
            site_id=target_id,
            carrier_type=carrier,
            refinements=merged_refs,
            trust=trust,
            provenance=f"merged({a.provenance}, {b.provenance})",
            witnesses=merged_witnesses,
        )

    @staticmethod
    def are_compatible(a: LocalSection, b: LocalSection) -> bool:
        """Check whether two sections are compatible (agree on shared refinements).

        Two sections are compatible if their carrier types match (or one is None)
        and all shared refinement keys have equal values.
        """
        if (
            a.carrier_type is not None
            and b.carrier_type is not None
            and a.carrier_type != b.carrier_type
        ):
            return False
        shared_keys = set(a.refinements) & set(b.refinements)
        for key in shared_keys:
            if a.refinements[key] != b.refinements[key]:
                return False
        return True

    _TRUST_ORDER = [
        TrustLevel.RESIDUAL,
        TrustLevel.ASSUMED,
        TrustLevel.TRACE_BACKED,
        TrustLevel.BOUNDED_AUTO,
        TrustLevel.TRUSTED_AUTO,
        TrustLevel.PROOF_BACKED,
    ]

    @staticmethod
    def _max_trust(a: TrustLevel, b: TrustLevel) -> TrustLevel:
        """Return the higher trust level."""
        order = SectionMerger._TRUST_ORDER
        ai = order.index(a) if a in order else 0
        bi = order.index(b) if b in order else 0
        return order[max(ai, bi)]


    # ── Trust-level-aware merging ─────────────────────────────────────────

    @staticmethod
    def merge_with_trust(
        a: LocalSection,
        b: LocalSection,
        merged_site_id: Optional[SiteId] = None,
        prefer_higher_trust: bool = True,
    ) -> LocalSection:
        """Merge two sections with trust-level-aware conflict resolution.

        When refinements conflict, the section with the higher trust level
        wins.  If *prefer_higher_trust* is False, the section with the
        lower trust level wins (conservative merge).

        Args:
            a: First section.
            b: Second section.
            merged_site_id: Target site id (defaults to a.site_id).
            prefer_higher_trust: If True, higher trust wins conflicts.

        Returns:
            A merged LocalSection with reconciled refinements.
        """
        target_id = merged_site_id or a.site_id

        # Resolve carrier type
        if a.carrier_type is not None and b.carrier_type is not None:
            if a.carrier_type != b.carrier_type:
                # Use trust level to break the tie
                a_rank = SectionMerger._trust_rank(a.trust)
                b_rank = SectionMerger._trust_rank(b.trust)
                if prefer_higher_trust:
                    carrier = a.carrier_type if a_rank >= b_rank else b.carrier_type
                else:
                    carrier = a.carrier_type if a_rank <= b_rank else b.carrier_type
            else:
                carrier = a.carrier_type
        else:
            carrier = a.carrier_type if a.carrier_type is not None else b.carrier_type

        # Merge refinements with trust-aware conflict resolution
        merged_refs: Dict[str, Any] = {}
        all_keys = set(a.refinements.keys()) | set(b.refinements.keys())
        a_rank = SectionMerger._trust_rank(a.trust)
        b_rank = SectionMerger._trust_rank(b.trust)

        for key in all_keys:
            in_a = key in a.refinements
            in_b = key in b.refinements
            if in_a and in_b:
                if a.refinements[key] == b.refinements[key]:
                    merged_refs[key] = a.refinements[key]
                elif prefer_higher_trust:
                    merged_refs[key] = (
                        a.refinements[key] if a_rank >= b_rank
                        else b.refinements[key]
                    )
                else:
                    merged_refs[key] = (
                        a.refinements[key] if a_rank <= b_rank
                        else b.refinements[key]
                    )
            elif in_a:
                merged_refs[key] = a.refinements[key]
            else:
                merged_refs[key] = b.refinements[key]

        # Merge witnesses (higher trust wins on conflict)
        merged_witnesses: Dict[str, Any] = {}
        all_w_keys = set(a.witnesses.keys()) | set(b.witnesses.keys())
        for key in all_w_keys:
            in_a = key in a.witnesses
            in_b = key in b.witnesses
            if in_a and in_b:
                if prefer_higher_trust:
                    merged_witnesses[key] = (
                        a.witnesses[key] if a_rank >= b_rank
                        else b.witnesses[key]
                    )
                else:
                    merged_witnesses[key] = (
                        a.witnesses[key] if a_rank <= b_rank
                        else b.witnesses[key]
                    )
            elif in_a:
                merged_witnesses[key] = a.witnesses[key]
            else:
                merged_witnesses[key] = b.witnesses[key]

        # Resulting trust is the max of both
        trust = SectionMerger._max_trust(a.trust, b.trust)

        return LocalSection(
            site_id=target_id,
            carrier_type=carrier,
            refinements=merged_refs,
            trust=trust,
            provenance=f"trust_merged({a.provenance}, {b.provenance})",
            witnesses=merged_witnesses,
        )

    @staticmethod
    def compute_trust_propagation(
        sections: List[LocalSection],
        morphisms: List[Morphism],
    ) -> Dict[SiteId, TrustLevel]:
        """Compute trust propagation through a restriction chain.

        Given a list of sections and the morphisms connecting them,
        propagate trust levels forward: each section's trust is at most
        as high as the minimum trust along any path from the boundary.

        This implements the monotonicity property of trust through
        restriction maps: if sigma_u has trust T and there is a morphism
        u -> v, then sigma_v's effective trust is min(T, sigma_v.trust).

        Args:
            sections: Local sections at various sites.
            morphisms: Morphisms forming the restriction chain.

        Returns:
            Mapping from SiteId to propagated TrustLevel.
        """
        trust_order = SectionMerger._TRUST_ORDER
        section_map = {s.site_id: s for s in sections}
        trust_map: Dict[SiteId, TrustLevel] = {
            s.site_id: s.trust for s in sections
        }

        # Build adjacency: source -> list of targets
        adj: Dict[SiteId, List[SiteId]] = {}
        for m in morphisms:
            adj.setdefault(m.source, []).append(m.target)

        # Forward propagation: each target's trust is capped by source's trust
        changed = True
        max_iterations = len(sections) + 1
        iteration = 0
        while changed and iteration < max_iterations:
            changed = False
            iteration += 1
            for m in morphisms:
                src_trust = trust_map.get(m.source)
                tgt_trust = trust_map.get(m.target)
                if src_trust is None or tgt_trust is None:
                    continue
                src_rank = SectionMerger._trust_rank(src_trust)
                tgt_rank = SectionMerger._trust_rank(tgt_trust)
                # Target trust is capped by source trust
                if tgt_rank > src_rank:
                    trust_map[m.target] = src_trust
                    changed = True

        return trust_map

    @staticmethod
    def compute_effective_trust(
        section: LocalSection,
        incoming_morphisms: List[Tuple[Morphism, LocalSection]],
    ) -> TrustLevel:
        """Compute the effective trust of a section considering incoming restrictions.

        The effective trust is the minimum of:
        - The section's own trust level
        - The trust levels of all incoming restricted sections

        Args:
            section: The section whose effective trust to compute.
            incoming_morphisms: Pairs of (morphism, source_section) for all
                morphisms targeting this section's site.

        Returns:
            The effective TrustLevel.
        """
        trust_order = SectionMerger._TRUST_ORDER
        min_rank = SectionMerger._trust_rank(section.trust)

        for morphism, source_section in incoming_morphisms:
            src_rank = SectionMerger._trust_rank(source_section.trust)
            if src_rank < min_rank:
                min_rank = src_rank

        return trust_order[min_rank] if min_rank < len(trust_order) else TrustLevel.RESIDUAL

    @staticmethod
    def _trust_rank(trust: TrustLevel) -> int:
        """Return the numeric rank of a trust level (higher = more trusted)."""
        order = SectionMerger._TRUST_ORDER
        try:
            return order.index(trust)
        except ValueError:
            return 0

    @staticmethod
    def merge_chain(
        sections: List[LocalSection],
        merged_site_id: Optional[SiteId] = None,
    ) -> LocalSection:
        """Merge a chain of sections left-to-right with trust awareness.

        Useful when assembling a global section from multiple overlapping
        local sections.  Each successive merge uses trust-aware conflict
        resolution.

        Args:
            sections: Sections to merge in order.
            merged_site_id: Optional target site id.

        Returns:
            A single merged LocalSection.

        Raises:
            ValueError: If the section list is empty.
        """
        if not sections:
            raise ValueError("Cannot merge empty section list")
        if len(sections) == 1:
            return sections[0]

        result = sections[0]
        for section in sections[1:]:
            result = SectionMerger.merge_with_trust(
                result, section, merged_site_id=merged_site_id
            )
        return result


class SectionRestrictor:
    """Apply restriction maps to sections along morphisms."""

    @staticmethod
    def restrict(section: LocalSection, morphism: Morphism) -> LocalSection:
        """Restrict a section along a morphism.

        Delegates to the morphism's restrict method.
        """
        return morphism.restrict(section)

    @staticmethod
    def restrict_with_trust_cap(
        section: LocalSection,
        morphism: Morphism,
        max_trust: TrustLevel,
    ) -> LocalSection:
        """Restrict a section along a morphism, capping the trust level.

        The restricted section's trust will be at most *max_trust*,
        implementing the monotonicity of trust through restriction.

        Args:
            section: Section to restrict.
            morphism: Morphism to restrict along.
            max_trust: Maximum trust level for the result.

        Returns:
            A restricted LocalSection with capped trust.
        """
        restricted = morphism.restrict(section)
        trust_order = SectionMerger._TRUST_ORDER
        restricted_rank = SectionMerger._trust_rank(restricted.trust)
        cap_rank = SectionMerger._trust_rank(max_trust)
        effective_rank = min(restricted_rank, cap_rank)
        effective_trust = trust_order[effective_rank] if effective_rank < len(trust_order) else TrustLevel.RESIDUAL

        if effective_trust != restricted.trust:
            return LocalSection(
                site_id=restricted.site_id,
                carrier_type=restricted.carrier_type,
                refinements=restricted.refinements,
                trust=effective_trust,
                provenance=f"trust_capped({restricted.provenance})",
                witnesses=restricted.witnesses,
            )
        return restricted

    @staticmethod
    def restrict_chain(
        section: LocalSection,
        morphisms: List[Morphism],
    ) -> LocalSection:
        """Apply a chain of restriction morphisms in sequence.

        Args:
            section: The starting section.
            morphisms: Morphisms to apply in order.

        Returns:
            The fully restricted LocalSection.
        """
        result = section
        for morphism in morphisms:
            result = morphism.restrict(result)
        return result


class GlobalSectionBuilder:
    """Collect local sections, check compatibility, produce GlobalSection.

    A global section is a compatible family of local sections: for every
    overlap (u, v), the restrictions of sigma_u and sigma_v to the
    overlap must agree.
    """

    def __init__(self) -> None:
        self._sections: Dict[SiteId, LocalSection] = {}
        self._input_sites: Set[SiteId] = set()
        self._output_sites: Set[SiteId] = set()

    def add_section(self, section: LocalSection) -> GlobalSectionBuilder:
        """Add a local section to the builder."""
        self._sections[section.site_id] = section
        return self

    def mark_input(self, site_id: SiteId) -> GlobalSectionBuilder:
        """Mark a site as part of the input boundary."""
        self._input_sites.add(site_id)
        return self

    def mark_output(self, site_id: SiteId) -> GlobalSectionBuilder:
        """Mark a site as part of the output boundary."""
        self._output_sites.add(site_id)
        return self

    def check_compatibility(
        self, overlaps: List[Tuple[SiteId, SiteId]]
    ) -> List[Tuple[SiteId, SiteId]]:
        """Check compatibility of sections on overlaps.

        Returns a list of conflicting overlap pairs.
        """
        conflicts: List[Tuple[SiteId, SiteId]] = []
        for u, v in overlaps:
            su = self._sections.get(u)
            sv = self._sections.get(v)
            if su is None or sv is None:
                continue
            if not SectionMerger.are_compatible(su, sv):
                conflicts.append((u, v))
        return conflicts

    def build(
        self, overlaps: Optional[List[Tuple[SiteId, SiteId]]] = None
    ) -> Tuple[GlobalSection, List[Tuple[SiteId, SiteId]]]:
        """Build a GlobalSection, returning it alongside any conflicts.

        If overlaps is provided, checks compatibility first.
        """
        conflicts = self.check_compatibility(overlaps) if overlaps else []

        input_section = BoundarySection(
            boundary_sites={
                sid: self._sections[sid]
                for sid in self._input_sites
                if sid in self._sections
            },
            is_input=True,
        )
        output_section = BoundarySection(
            boundary_sites={
                sid: self._sections[sid]
                for sid in self._output_sites
                if sid in self._sections
            },
            is_input=False,
        )

        gs = GlobalSection(
            local_sections=dict(self._sections),
            input_section=input_section,
            output_section=output_section,
        )
        return gs, conflicts
