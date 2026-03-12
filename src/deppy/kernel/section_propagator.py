"""Section propagator -- push and pull sections along morphisms.

In the sheaf-descent framework, sections live at sites and are related by
restriction maps (morphisms).  The SectionPropagator provides the two
fundamental transport operations:

1. **Forward propagation** (push-forward): Given a section at a source site
   and a morphism source -> target, produce a section at the target by
   applying the restriction map.  This is the standard presheaf restriction.

2. **Backward propagation** (pullback): Given a section at a target site
   and a morphism source -> target, produce a section at the source that
   is *consistent* with the target section.  This is the adjoint operation
   used during backward synthesis.

Both operations respect trust degradation through the trust classifier.
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
    Cover,
    LocalSection,
    Morphism,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    RestrictionKind,
    apply_restriction,
)
from deppy.kernel.trust_classifier import (
    TrustClassifier,
    trust_meet,
    trust_rank,
    restriction_ceiling,
    _extract_restriction_data,
)


# ---------------------------------------------------------------------------
# Propagation result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PropagationResult:
    """Result of a single propagation step."""
    _source_site: SiteId
    _target_site: SiteId
    _section: LocalSection
    _trust_before: TrustLevel
    _trust_after: TrustLevel
    _restriction_kind: Optional[RestrictionKind] = None
    _refinements_preserved: int = 0
    _refinements_dropped: int = 0

    @property
    def source_site(self) -> SiteId:
        return self._source_site

    @property
    def target_site(self) -> SiteId:
        return self._target_site

    @property
    def section(self) -> LocalSection:
        return self._section

    @property
    def trust_before(self) -> TrustLevel:
        return self._trust_before

    @property
    def trust_after(self) -> TrustLevel:
        return self._trust_after

    @property
    def restriction_kind(self) -> Optional[RestrictionKind]:
        return self._restriction_kind

    @property
    def trust_degraded(self) -> bool:
        return trust_rank(self._trust_after) < trust_rank(self._trust_before)

    def __repr__(self) -> str:
        return (
            f"PropagationResult({self._source_site} -> {self._target_site}, "
            f"trust={self._trust_after.value})"
        )


@dataclass(frozen=True)
class ChainPropagationResult:
    """Result of propagating through a chain of morphisms."""
    _steps: Tuple[PropagationResult, ...]
    _final_section: LocalSection
    _total_trust_degradation: int = 0

    @property
    def steps(self) -> Tuple[PropagationResult, ...]:
        return self._steps

    @property
    def final_section(self) -> LocalSection:
        return self._final_section

    @property
    def num_steps(self) -> int:
        return len(self._steps)

    @property
    def total_trust_degradation(self) -> int:
        return self._total_trust_degradation

    def __repr__(self) -> str:
        if not self._steps:
            return "ChainPropagationResult(empty)"
        path = " -> ".join(
            str(s.source_site) for s in self._steps
        )
        path += f" -> {self._steps[-1].target_site}"
        return f"ChainPropagationResult({path})"


# ---------------------------------------------------------------------------
# Section Propagator
# ---------------------------------------------------------------------------

class SectionPropagator:
    """Propagate sections forward and backward along morphisms.

    The propagator applies restriction maps to transport section data between
    sites in the observation site category.  It tracks trust degradation and
    refinement preservation statistics.
    """

    def __init__(
        self,
        *,
        trust_classifier: Optional[TrustClassifier] = None,
        preserve_witnesses: bool = True,
        allow_trust_upgrade_on_pullback: bool = False,
    ) -> None:
        self._trust_classifier = trust_classifier or TrustClassifier()
        self._preserve_witnesses = preserve_witnesses
        self._allow_trust_upgrade_on_pullback = allow_trust_upgrade_on_pullback
        self._propagation_log: List[PropagationResult] = []

    # -- Forward propagation (push-forward) --------------------------------

    def propagate_forward(
        self,
        section: LocalSection,
        morphism: ConcreteMorphism,
    ) -> LocalSection:
        """Push a section forward along a morphism (standard presheaf restriction).

        Given a section at morphism.source, produce a section at morphism.target
        by applying the restriction map encoded in the morphism's metadata.
        """
        if section.site_id != morphism.source:
            raise ValueError(
                f"Section site {section.site_id} does not match "
                f"morphism source {morphism.source}"
            )

        # Apply the restriction map
        restricted = apply_restriction(morphism, section)

        # Compute trust after restriction
        rdata = _extract_restriction_data(morphism)
        if rdata is not None:
            new_trust = self._trust_classifier.propagate_trust(
                section.trust, rdata.kind
            )
            # Apply forced trust from restriction data
            if rdata.forced_trust is not None:
                new_trust = rdata.forced_trust
        else:
            new_trust = section.trust

        # Build the result section
        result = LocalSection(
            site_id=morphism.target,
            carrier_type=restricted.carrier_type,
            refinements=restricted.refinements,
            trust=new_trust,
            provenance=f"forward from {section.site_id} via {morphism}",
            witnesses=restricted.witnesses if self._preserve_witnesses else {},
        )

        # Log the propagation
        rkind = rdata.kind if rdata is not None else None
        preserved = len(set(section.refinements.keys()) & set(result.refinements.keys()))
        dropped = len(section.refinements) - preserved
        step = PropagationResult(
            _source_site=morphism.source,
            _target_site=morphism.target,
            _section=result,
            _trust_before=section.trust,
            _trust_after=new_trust,
            _restriction_kind=rkind,
            _refinements_preserved=preserved,
            _refinements_dropped=dropped,
        )
        self._propagation_log.append(step)

        return result

    # -- Backward propagation (pullback) -----------------------------------

    def propagate_backward(
        self,
        section: LocalSection,
        morphism: ConcreteMorphism,
    ) -> LocalSection:
        """Pull a section backward along a morphism (adjoint operation).

        Given a section at morphism.target, produce a section at morphism.source
        that is *consistent* with the target section.  This is the reverse
        direction used in backward synthesis.

        The pullback inverts the projection where possible:
        - If the morphism has an explicit projection, invert it.
        - Refinements at the target that came from the source are mapped back.
        - Trust may or may not upgrade depending on configuration.
        """
        if section.site_id != morphism.target:
            raise ValueError(
                f"Section site {section.site_id} does not match "
                f"morphism target {morphism.target}"
            )

        rdata = _extract_restriction_data(morphism)

        # Invert the projection
        new_refinements = self._invert_refinements(
            section.refinements, morphism, rdata
        )

        # Handle guard predicates for control restrictions
        if rdata is not None and rdata.guard_predicate is not None:
            # On pullback, the guard requirement becomes a viability condition
            guard_key = f"viability_{rdata.kind.value}"
            if rdata.guard_polarity:
                new_refinements[guard_key] = rdata.guard_predicate
            else:
                new_refinements[guard_key] = ("required_negation", rdata.guard_predicate)

        # Handle error pullback: impose viability predicate on source
        if rdata is not None and rdata.viability_predicate is not None:
            new_refinements["error_viability"] = rdata.viability_predicate

        # Compute trust for the pullback
        if self._allow_trust_upgrade_on_pullback:
            new_trust = section.trust
        else:
            if rdata is not None:
                ceiling = restriction_ceiling(rdata.kind)
                new_trust = trust_meet(section.trust, ceiling)
            else:
                new_trust = section.trust

        result = LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=new_refinements,
            trust=new_trust,
            provenance=f"pullback from {section.site_id} via {morphism}",
            witnesses=dict(section.witnesses) if self._preserve_witnesses else {},
        )

        # Log
        rkind = rdata.kind if rdata is not None else None
        step = PropagationResult(
            _source_site=morphism.target,
            _target_site=morphism.source,
            _section=result,
            _trust_before=section.trust,
            _trust_after=new_trust,
            _restriction_kind=rkind,
            _refinements_preserved=len(new_refinements),
            _refinements_dropped=0,
        )
        self._propagation_log.append(step)

        return result

    # -- Chain propagation -------------------------------------------------

    def propagate_chain(
        self,
        section: LocalSection,
        morphism_chain: Sequence[ConcreteMorphism],
    ) -> LocalSection:
        """Propagate a section forward through a chain of morphisms.

        Applies each morphism in sequence, threading the result section
        through the chain.
        """
        current = section
        for morphism in morphism_chain:
            current = self.propagate_forward(current, morphism)
        return current

    def propagate_chain_backward(
        self,
        section: LocalSection,
        morphism_chain: Sequence[ConcreteMorphism],
    ) -> LocalSection:
        """Propagate a section backward through a chain of morphisms.

        Applies each morphism in reverse order using pullback.
        """
        current = section
        for morphism in reversed(morphism_chain):
            current = self.propagate_backward(current, morphism)
        return current

    def propagate_chain_detailed(
        self,
        section: LocalSection,
        morphism_chain: Sequence[ConcreteMorphism],
    ) -> ChainPropagationResult:
        """Propagate forward through a chain, returning detailed step info."""
        steps: List[PropagationResult] = []
        current = section
        initial_trust = trust_rank(section.trust)

        for morphism in morphism_chain:
            before_trust = current.trust
            current = self.propagate_forward(current, morphism)
            rdata = _extract_restriction_data(morphism)
            rkind = rdata.kind if rdata is not None else None
            preserved = len(
                set(section.refinements.keys()) & set(current.refinements.keys())
            )
            steps.append(PropagationResult(
                _source_site=morphism.source,
                _target_site=morphism.target,
                _section=current,
                _trust_before=before_trust,
                _trust_after=current.trust,
                _restriction_kind=rkind,
                _refinements_preserved=preserved,
                _refinements_dropped=0,
            ))

        final_trust = trust_rank(current.trust)
        degradation = initial_trust - final_trust

        return ChainPropagationResult(
            _steps=tuple(steps),
            _final_section=current,
            _total_trust_degradation=max(0, degradation),
        )

    # -- Batch propagation -------------------------------------------------

    def propagate_all_forward(
        self,
        sections: Dict[SiteId, LocalSection],
        morphisms: Sequence[ConcreteMorphism],
    ) -> Dict[SiteId, LocalSection]:
        """Propagate all sections forward along applicable morphisms.

        For each morphism whose source has a section, propagate forward.
        If multiple morphisms target the same site, the section with the
        highest trust wins.
        """
        result = dict(sections)

        for morphism in morphisms:
            source_section = sections.get(morphism.source)
            if source_section is None:
                continue

            new_section = self.propagate_forward(source_section, morphism)
            existing = result.get(morphism.target)

            if existing is None:
                result[morphism.target] = new_section
            else:
                # Keep the section with higher trust, or merge refinements
                if trust_rank(new_section.trust) > trust_rank(existing.trust):
                    result[morphism.target] = new_section
                elif trust_rank(new_section.trust) == trust_rank(existing.trust):
                    # Merge refinements from both
                    merged_refinements = dict(existing.refinements)
                    for k, v in new_section.refinements.items():
                        if k not in merged_refinements:
                            merged_refinements[k] = v
                    result[morphism.target] = LocalSection(
                        site_id=morphism.target,
                        carrier_type=existing.carrier_type or new_section.carrier_type,
                        refinements=merged_refinements,
                        trust=existing.trust,
                        provenance=f"merged forward from multiple sources",
                        witnesses={**existing.witnesses, **new_section.witnesses},
                    )

        return result

    def propagate_all_backward(
        self,
        sections: Dict[SiteId, LocalSection],
        morphisms: Sequence[ConcreteMorphism],
    ) -> Dict[SiteId, LocalSection]:
        """Propagate all sections backward along applicable morphisms.

        For each morphism whose target has a section, propagate backward.
        If multiple morphisms source from the same site, merge the
        pullback results.
        """
        result = dict(sections)

        for morphism in morphisms:
            target_section = sections.get(morphism.target)
            if target_section is None:
                continue

            new_section = self.propagate_backward(target_section, morphism)
            existing = result.get(morphism.source)

            if existing is None:
                result[morphism.source] = new_section
            else:
                # Merge: strengthen refinements by adding pullback constraints
                merged_refinements = dict(existing.refinements)
                for k, v in new_section.refinements.items():
                    if k not in merged_refinements:
                        merged_refinements[k] = v
                    elif merged_refinements[k] != v:
                        # Conjoin conflicting refinements
                        merged_refinements[k] = (
                            "conjunction",
                            merged_refinements[k],
                            v,
                        )
                result[morphism.source] = LocalSection(
                    site_id=morphism.source,
                    carrier_type=existing.carrier_type or new_section.carrier_type,
                    refinements=merged_refinements,
                    trust=trust_meet(existing.trust, new_section.trust),
                    provenance=f"merged pullback at {morphism.source}",
                    witnesses={**existing.witnesses, **new_section.witnesses},
                )

        return result

    # -- Propagation log ---------------------------------------------------

    @property
    def propagation_log(self) -> List[PropagationResult]:
        """Return the log of all propagation steps performed."""
        return list(self._propagation_log)

    def clear_log(self) -> None:
        """Clear the propagation log."""
        self._propagation_log.clear()

    # -- Private helpers ---------------------------------------------------

    def _invert_refinements(
        self,
        target_refinements: Dict[str, Any],
        morphism: ConcreteMorphism,
        rdata: Optional[RestrictionData],
    ) -> Dict[str, Any]:
        """Invert the refinement projection to produce source-site refinements.

        If the morphism has an explicit projection mapping, invert it.
        Otherwise, copy all refinements (conservative pullback).
        """
        result: Dict[str, Any] = {}

        if morphism.projection is not None:
            # The projection maps tgt_key -> src_key.  Invert: src_key -> tgt_key.
            inverse_proj: Dict[str, str] = {}
            for tgt_key, src_key in morphism.projection.items():
                inverse_proj[src_key] = tgt_key

            for src_key, tgt_key in inverse_proj.items():
                if tgt_key in target_refinements:
                    result[src_key] = target_refinements[tgt_key]
        elif rdata is not None and rdata.actual_to_formal is not None:
            # Invert actual-to-formal mapping
            for actual, formal in rdata.actual_to_formal.items():
                for key, value in target_refinements.items():
                    new_key = key.replace(formal, actual)
                    result[new_key] = value
        else:
            # No projection: copy all refinements
            result = dict(target_refinements)

        # Strip guard-specific keys that don't belong at the source
        keys_to_remove = [
            k for k in result
            if k.startswith("guard_") or k.startswith("viability_")
        ]
        for k in keys_to_remove:
            del result[k]

        return result
