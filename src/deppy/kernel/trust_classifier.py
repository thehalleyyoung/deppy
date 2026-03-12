"""Trust classifier for the sheaf-descent kernel.

Classifies sections by trust level based on their provenance chain.  Trust
degrades monotonically through certain restriction maps: a PROOF_BACKED
section restricted through an unverified morphism degrades to BOUNDED_AUTO,
and further unresolved steps degrade it to RESIDUAL.

The trust lattice is:

    PROOF_BACKED > TRUSTED_AUTO > TRACE_BACKED > BOUNDED_AUTO > RESIDUAL > ASSUMED

Classification rules:
1. Sections obtained from proof-transport morphisms get PROOF_BACKED.
2. Sections from static analysis with full coverage get TRUSTED_AUTO.
3. Sections backed by runtime trace data get TRACE_BACKED.
4. Sections with bounded-model checking evidence get BOUNDED_AUTO.
5. Sections propagated with residual obligations get RESIDUAL.
6. Sections assumed without evidence get ASSUMED.

Trust propagation through restrictions follows the weakest-link principle:
the resulting trust is the *meet* of the source trust and the restriction's
trust ceiling.
"""

from __future__ import annotations

import enum
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
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import RestrictionData, RestrictionKind


# ---------------------------------------------------------------------------
# Trust ordering
# ---------------------------------------------------------------------------

_TRUST_RANK: Dict[TrustLevel, int] = {
    TrustLevel.PROOF_BACKED: 5,
    TrustLevel.TRUSTED_AUTO: 4,
    TrustLevel.TRACE_BACKED: 3,
    TrustLevel.BOUNDED_AUTO: 2,
    TrustLevel.RESIDUAL: 1,
    TrustLevel.ASSUMED: 0,
}


def trust_rank(level: TrustLevel) -> int:
    """Return the numeric rank of a trust level (higher is stronger)."""
    return _TRUST_RANK.get(level, 0)


def trust_leq(a: TrustLevel, b: TrustLevel) -> bool:
    """Return ``True`` when trust level *a* is at most *b*."""
    return trust_rank(a) <= trust_rank(b)


def trust_meet(a: TrustLevel, b: TrustLevel) -> TrustLevel:
    """Compute the greatest lower bound (weakest-link) of two trust levels."""
    if trust_rank(a) <= trust_rank(b):
        return a
    return b


def trust_join(a: TrustLevel, b: TrustLevel) -> TrustLevel:
    """Compute the least upper bound of two trust levels."""
    if trust_rank(a) >= trust_rank(b):
        return a
    return b


# ---------------------------------------------------------------------------
# Trust ceiling for restriction kinds
# ---------------------------------------------------------------------------

_RESTRICTION_CEILING: Dict[RestrictionKind, TrustLevel] = {
    # Proof/witness transports preserve or establish proof-backed trust
    RestrictionKind.PROOF_TRANSPORT: TrustLevel.PROOF_BACKED,
    RestrictionKind.WITNESS_FLOW: TrustLevel.PROOF_BACKED,

    # Structural restrictions preserve full trust
    RestrictionKind.LINEAGE: TrustLevel.PROOF_BACKED,
    RestrictionKind.CONTROL_TRUE: TrustLevel.PROOF_BACKED,
    RestrictionKind.CONTROL_FALSE: TrustLevel.PROOF_BACKED,
    RestrictionKind.PHI_MERGE: TrustLevel.TRUSTED_AUTO,
    RestrictionKind.SCOPE_ENTRY: TrustLevel.PROOF_BACKED,

    # Interprocedural restrictions are slightly weaker
    RestrictionKind.ACTUAL_TO_FORMAL: TrustLevel.TRUSTED_AUTO,
    RestrictionKind.FORMAL_TO_RETURN: TrustLevel.TRUSTED_AUTO,
    RestrictionKind.CALLEE_ERROR_PULLBACK: TrustLevel.BOUNDED_AUTO,

    # Theory-pack transports depend on pack trustworthiness
    RestrictionKind.PACK_TRANSPORT: TrustLevel.TRUSTED_AUTO,
    RestrictionKind.SHAPE_PROPAGATION: TrustLevel.TRUSTED_AUTO,
    RestrictionKind.ORDER_PROJECTION: TrustLevel.TRUSTED_AUTO,
    RestrictionKind.INDEX_DOMAIN: TrustLevel.TRUSTED_AUTO,

    # Boundary projections preserve trust
    RestrictionKind.INPUT_PROJECTION: TrustLevel.PROOF_BACKED,
    RestrictionKind.OUTPUT_PROJECTION: TrustLevel.PROOF_BACKED,

    # Error restrictions introduce uncertainty
    RestrictionKind.ERROR_VIABILITY: TrustLevel.BOUNDED_AUTO,
    RestrictionKind.ERROR_PULLBACK: TrustLevel.BOUNDED_AUTO,

    # Heap restrictions can degrade
    RestrictionKind.FIELD_INIT: TrustLevel.TRUSTED_AUTO,
    RestrictionKind.ALIAS_CHAIN: TrustLevel.TRUSTED_AUTO,
    RestrictionKind.FRAME_RESTRICTION: TrustLevel.TRUSTED_AUTO,
}


def restriction_ceiling(kind: RestrictionKind) -> TrustLevel:
    """Return the maximum trust level a section can retain after restriction."""
    return _RESTRICTION_CEILING.get(kind, TrustLevel.BOUNDED_AUTO)


# ---------------------------------------------------------------------------
# Provenance tags
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ProvenanceTag:
    """A single step in a provenance chain.

    Records the kind of derivation step and the trust ceiling it imposes.
    """
    _step_kind: str
    _source_site: Optional[SiteId] = None
    _restriction_kind: Optional[RestrictionKind] = None
    _trust_ceiling: TrustLevel = TrustLevel.PROOF_BACKED

    @property
    def step_kind(self) -> str:
        return self._step_kind

    @property
    def source_site(self) -> Optional[SiteId]:
        return self._source_site

    @property
    def restriction_kind(self) -> Optional[RestrictionKind]:
        return self._restriction_kind

    @property
    def trust_ceiling(self) -> TrustLevel:
        return self._trust_ceiling

    def __repr__(self) -> str:
        parts = [self._step_kind]
        if self._source_site is not None:
            parts.append(f"from={self._source_site}")
        if self._restriction_kind is not None:
            parts.append(f"via={self._restriction_kind.value}")
        parts.append(f"ceil={self._trust_ceiling.value}")
        return f"ProvenanceTag({', '.join(parts)})"


@dataclass(frozen=True)
class ProvenanceChain:
    """An ordered sequence of provenance tags from origin to current site.

    The chain records how a section was derived, and the effective trust
    is the meet of all ceilings in the chain.
    """
    _tags: Tuple[ProvenanceTag, ...] = ()

    @property
    def tags(self) -> Tuple[ProvenanceTag, ...]:
        return self._tags

    @property
    def length(self) -> int:
        return len(self._tags)

    def effective_trust(self) -> TrustLevel:
        """Compute the effective trust by taking the meet of all ceilings."""
        if not self._tags:
            return TrustLevel.ASSUMED
        result = TrustLevel.PROOF_BACKED
        for tag in self._tags:
            result = trust_meet(result, tag.trust_ceiling)
        return result

    def append(self, tag: ProvenanceTag) -> ProvenanceChain:
        """Return a new chain with the given tag appended."""
        return ProvenanceChain(_tags=self._tags + (tag,))

    def weakest_link(self) -> Optional[ProvenanceTag]:
        """Return the tag with the lowest trust ceiling."""
        if not self._tags:
            return None
        return min(self._tags, key=lambda t: trust_rank(t.trust_ceiling))

    def __repr__(self) -> str:
        if not self._tags:
            return "ProvenanceChain(empty)"
        steps = " -> ".join(t.step_kind for t in self._tags)
        return f"ProvenanceChain({steps}, trust={self.effective_trust().value})"


# ---------------------------------------------------------------------------
# Trust classification result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TrustClassification:
    """Result of classifying a section's trust level."""
    _section_site: SiteId
    _assigned_trust: TrustLevel
    _provenance_chain: ProvenanceChain
    _reasoning: str = ""
    _degradation_path: Tuple[Tuple[str, TrustLevel], ...] = ()

    @property
    def section_site(self) -> SiteId:
        return self._section_site

    @property
    def assigned_trust(self) -> TrustLevel:
        return self._assigned_trust

    @property
    def provenance_chain(self) -> ProvenanceChain:
        return self._provenance_chain

    @property
    def reasoning(self) -> str:
        return self._reasoning

    @property
    def degradation_path(self) -> Tuple[Tuple[str, TrustLevel], ...]:
        return self._degradation_path

    def __repr__(self) -> str:
        return (
            f"TrustClassification({self._section_site}, "
            f"trust={self._assigned_trust.value}, "
            f"reason={self._reasoning!r})"
        )


# ---------------------------------------------------------------------------
# TrustClassifier
# ---------------------------------------------------------------------------

class TrustClassifier:
    """Classify sections by trust level based on provenance.

    The classifier examines how a section was derived and assigns a trust
    level reflecting the weakest link in its provenance chain.

    For each section, the classifier:
    1. Extracts the provenance string from the section.
    2. Builds a provenance chain from morphism metadata.
    3. Computes the effective trust as the meet of all trust ceilings.
    4. Returns a classification result with reasoning.
    """

    def __init__(
        self,
        *,
        default_trust: TrustLevel = TrustLevel.ASSUMED,
        trust_overrides: Optional[Dict[SiteKind, TrustLevel]] = None,
    ) -> None:
        self._default_trust = default_trust
        self._trust_overrides = trust_overrides or {}
        self._classification_cache: Dict[SiteId, TrustClassification] = {}

    # -- Public API --------------------------------------------------------

    def classify(
        self,
        section: LocalSection,
        provenance: Optional[ProvenanceChain] = None,
    ) -> TrustLevel:
        """Classify the trust level of a section.

        If a provenance chain is provided, the effective trust is the meet of
        the chain's ceilings.  Otherwise, the section's existing trust is used
        as a baseline, with site-kind overrides applied.
        """
        if provenance is not None and provenance.length > 0:
            chain_trust = provenance.effective_trust()
            effective = trust_meet(section.trust, chain_trust)
        else:
            effective = section.trust

        # Apply site-kind overrides (e.g., PROOF sites always get PROOF_BACKED)
        kind_override = self._trust_overrides.get(section.site_id.kind)
        if kind_override is not None:
            effective = trust_meet(effective, kind_override)

        # Proof sites get a floor of PROOF_BACKED if they carry witnesses
        if section.site_id.kind == SiteKind.PROOF and section.witnesses:
            effective = trust_join(effective, TrustLevel.PROOF_BACKED)

        # Trace sites get TRACE_BACKED if they have trace data
        if section.site_id.kind == SiteKind.TRACE:
            effective = trust_join(effective, TrustLevel.TRACE_BACKED)

        # Error sites are capped at BOUNDED_AUTO unless proven safe
        if section.site_id.kind == SiteKind.ERROR:
            if effective != TrustLevel.PROOF_BACKED:
                effective = trust_meet(effective, TrustLevel.BOUNDED_AUTO)

        # Build classification record
        chain = provenance or ProvenanceChain()
        degradation: List[Tuple[str, TrustLevel]] = []
        running = section.trust
        for tag in chain.tags:
            new_level = trust_meet(running, tag.trust_ceiling)
            if new_level != running:
                degradation.append((tag.step_kind, new_level))
                running = new_level

        classification = TrustClassification(
            _section_site=section.site_id,
            _assigned_trust=effective,
            _provenance_chain=chain,
            _reasoning=self._build_reasoning(section, effective, chain),
            _degradation_path=tuple(degradation),
        )
        self._classification_cache[section.site_id] = classification
        return effective

    def propagate_trust(
        self,
        source_trust: TrustLevel,
        kind: RestrictionKind,
    ) -> TrustLevel:
        """Compute the resulting trust after propagation through a restriction.

        The result is the meet of the source trust and the restriction's
        trust ceiling.  This implements the weakest-link principle.
        """
        ceiling = restriction_ceiling(kind)
        return trust_meet(source_trust, ceiling)

    def classify_morphism_chain(
        self,
        source_trust: TrustLevel,
        morphism_chain: Sequence[ConcreteMorphism],
    ) -> Tuple[TrustLevel, ProvenanceChain]:
        """Classify the trust level after propagating through a chain of morphisms.

        Returns the resulting trust level and the provenance chain recording
        each degradation step.
        """
        current_trust = source_trust
        chain = ProvenanceChain()

        for morphism in morphism_chain:
            rdata = _extract_restriction_data(morphism)
            if rdata is not None:
                # Apply forced trust if present
                if rdata.forced_trust is not None:
                    new_trust = rdata.forced_trust
                    tag = ProvenanceTag(
                        _step_kind=f"forced_{rdata.kind.value}",
                        _source_site=morphism.source,
                        _restriction_kind=rdata.kind,
                        _trust_ceiling=rdata.forced_trust,
                    )
                else:
                    ceiling = restriction_ceiling(rdata.kind)
                    new_trust = trust_meet(current_trust, ceiling)
                    tag = ProvenanceTag(
                        _step_kind=rdata.kind.value,
                        _source_site=morphism.source,
                        _restriction_kind=rdata.kind,
                        _trust_ceiling=ceiling,
                    )
            else:
                # No restriction data: assume structural morphism preserving trust
                new_trust = current_trust
                tag = ProvenanceTag(
                    _step_kind="structural",
                    _source_site=morphism.source,
                    _trust_ceiling=TrustLevel.PROOF_BACKED,
                )

            chain = chain.append(tag)
            current_trust = new_trust

        return current_trust, chain

    def classify_all(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, TrustClassification]:
        """Classify trust levels for all sections in a cover.

        Builds provenance chains by tracing incoming morphisms for each site
        and computes effective trust levels.
        """
        # Build reverse adjacency: target -> list of incoming morphisms
        incoming: Dict[SiteId, List[ConcreteMorphism]] = {}
        for m in cover.morphisms:
            incoming.setdefault(m.target, []).append(m)

        results: Dict[SiteId, TrustClassification] = {}

        for site_id, section in sections.items():
            # Build provenance chain from incoming morphisms
            chain = self._build_provenance_chain(
                site_id, sections, incoming, visited=set()
            )
            trust = self.classify(section, chain)
            results[site_id] = self._classification_cache.get(
                site_id,
                TrustClassification(
                    _section_site=site_id,
                    _assigned_trust=trust,
                    _provenance_chain=chain,
                ),
            )

        return results

    def get_cached_classification(
        self, site_id: SiteId
    ) -> Optional[TrustClassification]:
        """Retrieve a previously computed classification from the cache."""
        return self._classification_cache.get(site_id)

    def clear_cache(self) -> None:
        """Clear the classification cache."""
        self._classification_cache.clear()

    # -- Private helpers ---------------------------------------------------

    def _build_provenance_chain(
        self,
        site_id: SiteId,
        sections: Dict[SiteId, LocalSection],
        incoming: Dict[SiteId, List[ConcreteMorphism]],
        visited: Set[SiteId],
    ) -> ProvenanceChain:
        """Recursively build a provenance chain for a site.

        Follows the strongest incoming morphism (the one with the highest
        trust ceiling) and traces back to the origin.
        """
        if site_id in visited:
            return ProvenanceChain()
        visited.add(site_id)

        in_morphisms = incoming.get(site_id, [])
        if not in_morphisms:
            # Origin site: provenance chain starts here
            section = sections.get(site_id)
            if section is not None:
                origin_tag = ProvenanceTag(
                    _step_kind="origin",
                    _source_site=site_id,
                    _trust_ceiling=section.trust,
                )
                return ProvenanceChain(_tags=(origin_tag,))
            return ProvenanceChain()

        # Select the strongest incoming morphism (highest trust ceiling)
        best_morphism: Optional[ConcreteMorphism] = None
        best_ceiling = TrustLevel.ASSUMED
        for m in in_morphisms:
            rdata = _extract_restriction_data(m)
            if rdata is not None:
                if rdata.forced_trust is not None:
                    ceiling = rdata.forced_trust
                else:
                    ceiling = restriction_ceiling(rdata.kind)
            else:
                ceiling = TrustLevel.PROOF_BACKED
            if trust_rank(ceiling) > trust_rank(best_ceiling):
                best_ceiling = ceiling
                best_morphism = m

        if best_morphism is None:
            return ProvenanceChain()

        # Recurse to the source of the best morphism
        parent_chain = self._build_provenance_chain(
            best_morphism.source, sections, incoming, visited
        )

        # Append the current restriction step
        rdata = _extract_restriction_data(best_morphism)
        if rdata is not None:
            tag = ProvenanceTag(
                _step_kind=rdata.kind.value,
                _source_site=best_morphism.source,
                _restriction_kind=rdata.kind,
                _trust_ceiling=best_ceiling,
            )
        else:
            tag = ProvenanceTag(
                _step_kind="structural",
                _source_site=best_morphism.source,
                _trust_ceiling=TrustLevel.PROOF_BACKED,
            )

        return parent_chain.append(tag)

    def _build_reasoning(
        self,
        section: LocalSection,
        effective: TrustLevel,
        chain: ProvenanceChain,
    ) -> str:
        """Build a human-readable explanation of the trust classification."""
        parts: List[str] = []

        if chain.length == 0:
            parts.append(
                f"section at {section.site_id} has base trust {section.trust.value}"
            )
        else:
            parts.append(
                f"section at {section.site_id} derived through "
                f"{chain.length}-step chain"
            )
            weakest = chain.weakest_link()
            if weakest is not None:
                parts.append(
                    f"weakest link: {weakest.step_kind} "
                    f"(ceiling={weakest.trust_ceiling.value})"
                )

        if effective != section.trust:
            parts.append(
                f"trust degraded from {section.trust.value} "
                f"to {effective.value}"
            )

        return "; ".join(parts)


# ---------------------------------------------------------------------------
# Utility
# ---------------------------------------------------------------------------

def _extract_restriction_data(
    morphism: ConcreteMorphism,
) -> Optional[RestrictionData]:
    """Extract RestrictionData from a morphism's metadata."""
    if hasattr(morphism, "metadata") and isinstance(morphism.metadata, dict):
        return morphism.metadata.get("restriction")
    return None
