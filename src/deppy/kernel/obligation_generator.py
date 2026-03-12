"""Obligation generator -- produce verification conditions from sections.

For each site in the cover, the obligation generator inspects the local
section's refinements and the theory constraints to produce verification
conditions (obligations) that must be discharged for the section to be
considered trustworthy.

Obligations arise from:
1. **Refinement predicates**: If a section claims ``{v: int | v > 0}``,
   an obligation is generated to prove ``v > 0`` holds.
2. **Guard consistency**: When a section passes through a control restriction,
   the guard predicate must be consistent with the section's refinements.
3. **Gluing conditions**: Overlapping sections must agree on shared keys.
4. **Viability predicates**: Error sites generate viability obligations.
5. **Loop invariants**: Loop-header sites need inductive proof obligations.
6. **Interprocedural**: Call sites generate obligation that actual arguments
   satisfy callee preconditions.
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
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    RestrictionKind,
)
from deppy.kernel._protocols import (
    Obligation,
    VerificationResult,
    VerificationStatus,
)
from deppy.kernel.trust_classifier import (
    trust_rank,
    _extract_restriction_data,
)


# ---------------------------------------------------------------------------
# Obligation kind
# ---------------------------------------------------------------------------

class ObligationKind(enum.Enum):
    """Classification of verification obligations."""
    REFINEMENT_PREDICATE = "refinement_predicate"
    GUARD_CONSISTENCY = "guard_consistency"
    GLUING_CONDITION = "gluing_condition"
    VIABILITY = "viability"
    LOOP_INVARIANT_INIT = "loop_invariant_init"
    LOOP_INVARIANT_PRESERVATION = "loop_invariant_preservation"
    PRECONDITION = "precondition"
    POSTCONDITION = "postcondition"
    TYPE_COMPATIBILITY = "type_compatibility"
    WITNESS_VALIDITY = "witness_validity"


# ---------------------------------------------------------------------------
# Enriched obligation
# ---------------------------------------------------------------------------

@dataclass
class EnrichedObligation:
    """An obligation enriched with metadata for prioritization."""
    obligation: Obligation
    kind: ObligationKind
    priority: float = 0.0
    estimated_difficulty: float = 0.0
    related_sites: List[SiteId] = field(default_factory=list)
    description: str = ""

    def __repr__(self) -> str:
        return (
            f"EnrichedObligation(kind={self.kind.value}, "
            f"site={self.obligation.site_id}, "
            f"priority={self.priority:.2f})"
        )


# ---------------------------------------------------------------------------
# Generation result
# ---------------------------------------------------------------------------

@dataclass
class GenerationResult:
    """Result of obligation generation across a cover."""
    obligations: List[EnrichedObligation] = field(default_factory=list)
    per_site: Dict[SiteId, List[EnrichedObligation]] = field(default_factory=dict)
    total_proof_debt: int = 0
    by_kind: Dict[ObligationKind, int] = field(default_factory=dict)

    @property
    def total_obligations(self) -> int:
        return len(self.obligations)

    def for_site(self, site_id: SiteId) -> List[EnrichedObligation]:
        """Return obligations for a specific site."""
        return self.per_site.get(site_id, [])

    def for_kind(self, kind: ObligationKind) -> List[EnrichedObligation]:
        """Return obligations of a specific kind."""
        return [o for o in self.obligations if o.kind == kind]

    def top_priority(self, n: int = 10) -> List[EnrichedObligation]:
        """Return the N highest-priority obligations."""
        return sorted(self.obligations, key=lambda o: -o.priority)[:n]

    def __repr__(self) -> str:
        return (
            f"GenerationResult(total={self.total_obligations}, "
            f"sites={len(self.per_site)}, "
            f"debt={self.total_proof_debt})"
        )


# ---------------------------------------------------------------------------
# Obligation generator
# ---------------------------------------------------------------------------

class ObligationGenerator:
    """Generate verification conditions from sections.

    For each site in the cover, inspect the local section and generate
    appropriate obligations based on the section's refinements, the
    morphism constraints, and the site kind.
    """

    def __init__(
        self,
        *,
        min_trust_for_skip: TrustLevel = TrustLevel.PROOF_BACKED,
        generate_gluing: bool = True,
        generate_witnesses: bool = True,
    ) -> None:
        self._min_trust_for_skip = min_trust_for_skip
        self._generate_gluing = generate_gluing
        self._generate_witnesses = generate_witnesses

    # -- Main entry point --------------------------------------------------

    def generate(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> GenerationResult:
        """Generate all verification obligations for the cover.

        Iterates over all sites and overlaps, producing obligations
        from refinements, guards, gluing conditions, and viability.
        """
        result = GenerationResult()

        # Per-site obligations
        for site_id, section in sections.items():
            site_obs = self._generate_for_site(site_id, section, cover, sections)
            if site_obs:
                result.per_site[site_id] = site_obs
                result.obligations.extend(site_obs)

        # Gluing obligations (from overlaps)
        if self._generate_gluing:
            gluing_obs = self._generate_gluing_obligations(cover, sections)
            result.obligations.extend(gluing_obs)
            for obs in gluing_obs:
                result.per_site.setdefault(obs.obligation.site_id, []).append(obs)

        # Morphism-induced obligations
        morphism_obs = self._generate_morphism_obligations(cover, sections)
        result.obligations.extend(morphism_obs)
        for obs in morphism_obs:
            result.per_site.setdefault(obs.obligation.site_id, []).append(obs)

        # Count by kind
        for obs in result.obligations:
            result.by_kind[obs.kind] = result.by_kind.get(obs.kind, 0) + 1

        # Compute proof debt: obligations that are not yet PROOF_BACKED
        result.total_proof_debt = sum(
            1 for obs in result.obligations
            if trust_rank(sections.get(
                obs.obligation.site_id, LocalSection(site_id=obs.obligation.site_id)
            ).trust) < trust_rank(TrustLevel.PROOF_BACKED)
        )

        return result

    # -- Per-site obligation generation ------------------------------------

    def _generate_for_site(
        self,
        site_id: SiteId,
        section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[EnrichedObligation]:
        """Generate obligations for a single site."""
        obligations: List[EnrichedObligation] = []

        # Skip fully proven sites
        if trust_rank(section.trust) >= trust_rank(self._min_trust_for_skip):
            return obligations

        # Refinement predicate obligations
        obligations.extend(
            self._generate_refinement_obligations(site_id, section)
        )

        # Site-kind-specific obligations
        kind_obs = self._generate_kind_specific(site_id, section, cover, sections)
        obligations.extend(kind_obs)

        # Witness validity obligations
        if self._generate_witnesses:
            witness_obs = self._generate_witness_obligations(site_id, section)
            obligations.extend(witness_obs)

        return obligations

    def _generate_refinement_obligations(
        self,
        site_id: SiteId,
        section: LocalSection,
    ) -> List[EnrichedObligation]:
        """Generate obligations from section refinements.

        Each refinement predicate produces an obligation to prove that
        the predicate holds for values at this site.
        """
        obligations: List[EnrichedObligation] = []

        for key, value in section.refinements.items():
            # Skip tentative/meta refinements
            if key.startswith("tentative_") or key.startswith("_"):
                continue

            # Generate obligation for this refinement
            obligation = Obligation(
                proposition=value,
                site_id=site_id,
                context={
                    "kind": "refinement",
                    "key": key,
                    "carrier_type": section.carrier_type,
                },
                trust_required=TrustLevel.TRUSTED_AUTO,
            )

            # Priority based on refinement key importance
            priority = self._refinement_priority(key, value, site_id)

            obligations.append(EnrichedObligation(
                obligation=obligation,
                kind=ObligationKind.REFINEMENT_PREDICATE,
                priority=priority,
                description=f"prove refinement '{key}' at {site_id}",
                related_sites=[site_id],
            ))

        return obligations

    def _generate_kind_specific(
        self,
        site_id: SiteId,
        section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[EnrichedObligation]:
        """Generate obligations specific to the site kind."""
        obligations: List[EnrichedObligation] = []

        if site_id.kind == SiteKind.ERROR:
            obligations.extend(
                self._generate_error_obligations(site_id, section, cover, sections)
            )
        elif site_id.kind == SiteKind.LOOP_HEADER_INVARIANT:
            obligations.extend(
                self._generate_loop_obligations(site_id, section, cover, sections)
            )
        elif site_id.kind == SiteKind.CALL_RESULT:
            obligations.extend(
                self._generate_call_obligations(site_id, section, cover, sections)
            )
        elif site_id.kind == SiteKind.BRANCH_GUARD:
            obligations.extend(
                self._generate_guard_obligations(site_id, section, cover, sections)
            )

        return obligations

    def _generate_error_obligations(
        self,
        site_id: SiteId,
        section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[EnrichedObligation]:
        """Generate viability obligations for error sites."""
        obligations: List[EnrichedObligation] = []

        # Viability obligation: prove the error is safe
        viability_pred = section.refinements.get("error_viability")
        proposition = viability_pred if viability_pred is not None else (
            "error_site_viable", site_id
        )

        obligation = Obligation(
            proposition=proposition,
            site_id=site_id,
            context={"kind": "error_viability"},
            trust_required=TrustLevel.PROOF_BACKED,
        )

        obligations.append(EnrichedObligation(
            obligation=obligation,
            kind=ObligationKind.VIABILITY,
            priority=10.0,  # High priority
            estimated_difficulty=0.7,
            description=f"prove viability of error site {site_id}",
            related_sites=[site_id],
        ))

        return obligations

    def _generate_loop_obligations(
        self,
        site_id: SiteId,
        section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[EnrichedObligation]:
        """Generate loop invariant obligations."""
        obligations: List[EnrichedObligation] = []

        # Initialization: invariant holds on entry
        init_obligation = Obligation(
            proposition=("loop_init", section.refinements),
            site_id=site_id,
            context={"kind": "loop_invariant_init"},
            trust_required=TrustLevel.BOUNDED_AUTO,
        )
        obligations.append(EnrichedObligation(
            obligation=init_obligation,
            kind=ObligationKind.LOOP_INVARIANT_INIT,
            priority=8.0,
            estimated_difficulty=0.5,
            description=f"prove loop invariant initialization at {site_id}",
            related_sites=[site_id],
        ))

        # Preservation: invariant holds after loop body
        preservation_obligation = Obligation(
            proposition=("loop_preservation", section.refinements),
            site_id=site_id,
            context={"kind": "loop_invariant_preservation"},
            trust_required=TrustLevel.BOUNDED_AUTO,
        )
        obligations.append(EnrichedObligation(
            obligation=preservation_obligation,
            kind=ObligationKind.LOOP_INVARIANT_PRESERVATION,
            priority=8.0,
            estimated_difficulty=0.7,
            description=f"prove loop invariant preservation at {site_id}",
            related_sites=[site_id],
        ))

        return obligations

    def _generate_call_obligations(
        self,
        site_id: SiteId,
        section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[EnrichedObligation]:
        """Generate obligations for call sites."""
        obligations: List[EnrichedObligation] = []

        # Find the actual-to-formal morphisms for this call
        for morphism in cover.morphisms:
            if morphism.target == site_id:
                rdata = _extract_restriction_data(morphism)
                if rdata is not None and rdata.kind == RestrictionKind.FORMAL_TO_RETURN:
                    # Postcondition obligation: callee guarantees hold
                    source_section = sections.get(morphism.source)
                    if source_section is not None:
                        obligation = Obligation(
                            proposition=(
                                "postcondition_holds",
                                morphism.source,
                                source_section.refinements,
                            ),
                            site_id=site_id,
                            context={
                                "kind": "postcondition",
                                "callee": str(morphism.source),
                            },
                            trust_required=TrustLevel.TRUSTED_AUTO,
                        )
                        obligations.append(EnrichedObligation(
                            obligation=obligation,
                            kind=ObligationKind.POSTCONDITION,
                            priority=6.0,
                            description=(
                                f"verify postcondition from {morphism.source} "
                                f"at {site_id}"
                            ),
                            related_sites=[site_id, morphism.source],
                        ))

        # Find outgoing actual-to-formal morphisms
        for morphism in cover.morphisms:
            if morphism.source == site_id:
                rdata = _extract_restriction_data(morphism)
                if rdata is not None and rdata.kind == RestrictionKind.ACTUAL_TO_FORMAL:
                    target_section = sections.get(morphism.target)
                    if target_section is not None:
                        obligation = Obligation(
                            proposition=(
                                "precondition_satisfied",
                                morphism.target,
                                section.refinements,
                            ),
                            site_id=site_id,
                            context={
                                "kind": "precondition",
                                "callee_param": str(morphism.target),
                            },
                            trust_required=TrustLevel.TRUSTED_AUTO,
                        )
                        obligations.append(EnrichedObligation(
                            obligation=obligation,
                            kind=ObligationKind.PRECONDITION,
                            priority=7.0,
                            description=(
                                f"verify precondition at call to {morphism.target}"
                            ),
                            related_sites=[site_id, morphism.target],
                        ))

        return obligations

    def _generate_guard_obligations(
        self,
        site_id: SiteId,
        section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[EnrichedObligation]:
        """Generate guard consistency obligations."""
        obligations: List[EnrichedObligation] = []

        guard_pred = section.refinements.get("guard_predicate")
        if guard_pred is not None:
            obligation = Obligation(
                proposition=("guard_well_typed", guard_pred),
                site_id=site_id,
                context={"kind": "guard_consistency"},
                trust_required=TrustLevel.TRUSTED_AUTO,
            )
            obligations.append(EnrichedObligation(
                obligation=obligation,
                kind=ObligationKind.GUARD_CONSISTENCY,
                priority=5.0,
                description=f"verify guard consistency at {site_id}",
                related_sites=[site_id],
            ))

        return obligations

    def _generate_witness_obligations(
        self,
        site_id: SiteId,
        section: LocalSection,
    ) -> List[EnrichedObligation]:
        """Generate obligations to validate witnesses."""
        obligations: List[EnrichedObligation] = []

        for key, witness in section.witnesses.items():
            obligation = Obligation(
                proposition=("witness_valid", key, witness),
                site_id=site_id,
                context={"kind": "witness_validity", "witness_key": key},
                trust_required=TrustLevel.PROOF_BACKED,
            )
            obligations.append(EnrichedObligation(
                obligation=obligation,
                kind=ObligationKind.WITNESS_VALIDITY,
                priority=3.0,
                description=f"validate witness '{key}' at {site_id}",
                related_sites=[site_id],
            ))

        return obligations

    # -- Gluing obligations ------------------------------------------------

    def _generate_gluing_obligations(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[EnrichedObligation]:
        """Generate obligations from the sheaf gluing condition.

        For each overlap pair, if the sections disagree, generate an
        obligation to resolve the disagreement.
        """
        obligations: List[EnrichedObligation] = []

        for site_a, site_b in cover.overlaps:
            sec_a = sections.get(site_a)
            sec_b = sections.get(site_b)

            if sec_a is None or sec_b is None:
                continue

            # Check shared refinement keys for disagreement
            shared_keys = (
                set(sec_a.refinements.keys())
                & set(sec_b.refinements.keys())
            )

            for key in shared_keys:
                if sec_a.refinements[key] != sec_b.refinements[key]:
                    obligation = Obligation(
                        proposition=(
                            "gluing_agreement",
                            key,
                            sec_a.refinements[key],
                            sec_b.refinements[key],
                        ),
                        site_id=site_a,  # Attribute to site_a
                        context={
                            "kind": "gluing",
                            "overlap_partner": str(site_b),
                            "key": key,
                        },
                        trust_required=TrustLevel.TRUSTED_AUTO,
                    )
                    obligations.append(EnrichedObligation(
                        obligation=obligation,
                        kind=ObligationKind.GLUING_CONDITION,
                        priority=9.0,
                        description=(
                            f"resolve gluing disagreement on '{key}' "
                            f"between {site_a} and {site_b}"
                        ),
                        related_sites=[site_a, site_b],
                    ))

            # Carrier type disagreement
            if (sec_a.carrier_type is not None
                    and sec_b.carrier_type is not None
                    and sec_a.carrier_type != sec_b.carrier_type):
                obligation = Obligation(
                    proposition=(
                        "carrier_agreement",
                        sec_a.carrier_type,
                        sec_b.carrier_type,
                    ),
                    site_id=site_a,
                    context={
                        "kind": "gluing_carrier",
                        "overlap_partner": str(site_b),
                    },
                    trust_required=TrustLevel.TRUSTED_AUTO,
                )
                obligations.append(EnrichedObligation(
                    obligation=obligation,
                    kind=ObligationKind.TYPE_COMPATIBILITY,
                    priority=9.5,
                    description=(
                        f"resolve carrier type mismatch between "
                        f"{site_a} and {site_b}"
                    ),
                    related_sites=[site_a, site_b],
                ))

        return obligations

    # -- Morphism obligations ----------------------------------------------

    def _generate_morphism_obligations(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[EnrichedObligation]:
        """Generate obligations from morphism constraints.

        Certain morphism kinds impose additional proof obligations
        (e.g., actual-to-formal requires precondition checking).
        """
        obligations: List[EnrichedObligation] = []

        for morphism in cover.morphisms:
            rdata = _extract_restriction_data(morphism)
            if rdata is None:
                continue

            source_sec = sections.get(morphism.source)
            target_sec = sections.get(morphism.target)

            if source_sec is None or target_sec is None:
                continue

            if rdata.kind == RestrictionKind.ACTUAL_TO_FORMAL:
                obligation = Obligation(
                    proposition=(
                        "actual_satisfies_formal",
                        source_sec.refinements,
                        target_sec.refinements,
                    ),
                    site_id=morphism.source,
                    context={
                        "kind": "call_precondition",
                        "formal_site": str(morphism.target),
                    },
                    trust_required=TrustLevel.TRUSTED_AUTO,
                )
                obligations.append(EnrichedObligation(
                    obligation=obligation,
                    kind=ObligationKind.PRECONDITION,
                    priority=7.0,
                    description=(
                        f"actual args at {morphism.source} satisfy "
                        f"formal params at {morphism.target}"
                    ),
                    related_sites=[morphism.source, morphism.target],
                ))

            elif rdata.kind == RestrictionKind.ERROR_VIABILITY:
                if rdata.viability_predicate is not None:
                    obligation = Obligation(
                        proposition=rdata.viability_predicate,
                        site_id=morphism.source,
                        context={
                            "kind": "error_viability_morphism",
                            "error_site": str(morphism.target),
                        },
                        trust_required=TrustLevel.BOUNDED_AUTO,
                    )
                    obligations.append(EnrichedObligation(
                        obligation=obligation,
                        kind=ObligationKind.VIABILITY,
                        priority=10.0,
                        description=(
                            f"viability at {morphism.source} for "
                            f"error {morphism.target}"
                        ),
                        related_sites=[morphism.source, morphism.target],
                    ))

        return obligations

    # -- Priority helpers --------------------------------------------------

    def _refinement_priority(
        self,
        key: str,
        value: Any,
        site_id: SiteId,
    ) -> float:
        """Compute priority for a refinement obligation."""
        base = 4.0

        # Higher priority for safety-related refinements
        if "viability" in key or "safety" in key or "error" in key:
            base = 9.0
        elif "guard" in key:
            base = 6.0
        elif "shape" in key or "dtype" in key:
            base = 5.0
        elif "bound" in key or "range" in key:
            base = 5.0

        # Higher priority for error sites
        if site_id.kind == SiteKind.ERROR:
            base += 2.0
        elif site_id.kind == SiteKind.LOOP_HEADER_INVARIANT:
            base += 1.0

        return base
