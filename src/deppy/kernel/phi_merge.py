"""Phi-node section merging at control flow join points.

In SSA form, phi-nodes merge values from different predecessor blocks.
In the sheaf-descent framework, a phi-node is an *overlap site* where
sections from different branches must either agree (glue) or expose an
obstruction (type error).

The PhiMerger performs the section-theoretic analog of phi-node insertion:
given sections from predecessor sites, produce a merged section at the
join site.  The merge operation computes:

1. Carrier type: join (LUB) of the predecessor carrier types.
2. Refinements: intersection of refinements that agree, plus disjunction
   of those that disagree (weakening).
3. Trust: meet (weakest-link) of predecessor trust levels.
4. Witnesses: composite witness from constituent witnesses.
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
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.types.base import TypeBase, type_join, type_meet, ANY_TYPE, NEVER_TYPE
from deppy.kernel.trust_classifier import trust_meet, trust_join, trust_rank


# ---------------------------------------------------------------------------
# Merge result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PhiMergeResult:
    """Result of merging sections at a phi/join site."""
    _merged_section: LocalSection
    _predecessor_count: int
    _agreed_keys: FrozenSet[str]
    _weakened_keys: FrozenSet[str]
    _dropped_keys: FrozenSet[str]
    _carrier_widened: bool = False
    _has_obstruction: bool = False
    _obstruction_detail: str = ""

    @property
    def merged_section(self) -> LocalSection:
        return self._merged_section

    @property
    def predecessor_count(self) -> int:
        return self._predecessor_count

    @property
    def agreed_keys(self) -> FrozenSet[str]:
        return self._agreed_keys

    @property
    def weakened_keys(self) -> FrozenSet[str]:
        return self._weakened_keys

    @property
    def dropped_keys(self) -> FrozenSet[str]:
        return self._dropped_keys

    @property
    def carrier_widened(self) -> bool:
        return self._carrier_widened

    @property
    def has_obstruction(self) -> bool:
        return self._has_obstruction

    def __repr__(self) -> str:
        return (
            f"PhiMergeResult(site={self._merged_section.site_id}, "
            f"preds={self._predecessor_count}, "
            f"agreed={len(self._agreed_keys)}, "
            f"weakened={len(self._weakened_keys)})"
        )


# ---------------------------------------------------------------------------
# PhiMerger
# ---------------------------------------------------------------------------

class PhiMerger:
    """Merge sections from predecessor blocks at phi/join sites.

    The merger implements the sheaf-theoretic join operation on local
    sections.  At a phi-node (overlap site), the sections from different
    predecessors are combined using the information lattice operations.
    """

    def __init__(
        self,
        *,
        allow_carrier_widening: bool = True,
        strict_refinement_agreement: bool = False,
        track_disagreements: bool = True,
    ) -> None:
        self._allow_carrier_widening = allow_carrier_widening
        self._strict_refinement_agreement = strict_refinement_agreement
        self._track_disagreements = track_disagreements

    # -- Main merge operations ---------------------------------------------

    def merge(
        self,
        sections: Sequence[LocalSection],
        phi_site: SiteId,
    ) -> LocalSection:
        """Merge multiple predecessor sections at a phi/join site.

        This is the primary merge operation.  Given sections from all
        predecessors reaching this join point, produce a single merged
        section that captures the intersection of known facts.
        """
        if not sections:
            return LocalSection(
                site_id=phi_site,
                carrier_type=None,
                refinements={},
                trust=TrustLevel.ASSUMED,
                provenance="phi_merge: no predecessors",
            )

        if len(sections) == 1:
            sec = sections[0]
            return LocalSection(
                site_id=phi_site,
                carrier_type=sec.carrier_type,
                refinements=dict(sec.refinements),
                trust=sec.trust,
                provenance=f"phi_merge: single predecessor {sec.site_id}",
                witnesses=dict(sec.witnesses),
            )

        # Merge carrier types
        carrier = self._join_carriers(sections)

        # Merge refinements
        refinements, agreed, weakened, dropped = self._join_refinements_all(sections)

        # Merge trust
        trust = self._join_trust_all(sections)

        # Merge witnesses
        witnesses = self._join_witnesses(sections)

        # Build provenance
        pred_names = ", ".join(str(s.site_id) for s in sections)
        provenance = f"phi_merge: [{pred_names}]"

        return LocalSection(
            site_id=phi_site,
            carrier_type=carrier,
            refinements=refinements,
            trust=trust,
            provenance=provenance,
            witnesses=witnesses,
        )

    def merge_detailed(
        self,
        sections: Sequence[LocalSection],
        phi_site: SiteId,
    ) -> PhiMergeResult:
        """Merge with detailed tracking of agreement/weakening/dropping."""
        merged = self.merge(sections, phi_site)

        if not sections:
            return PhiMergeResult(
                _merged_section=merged,
                _predecessor_count=0,
                _agreed_keys=frozenset(),
                _weakened_keys=frozenset(),
                _dropped_keys=frozenset(),
            )

        # Compute detailed refinement stats
        _, agreed, weakened, dropped = self._join_refinements_all(sections)

        # Check carrier widening
        carriers = [s.carrier_type for s in sections if s.carrier_type is not None]
        carrier_widened = False
        if len(carriers) >= 2:
            first = carriers[0]
            carrier_widened = any(c != first for c in carriers[1:])

        # Check for obstruction (strict disagreement)
        has_obstruction = False
        obstruction_detail = ""
        if self._strict_refinement_agreement and weakened:
            has_obstruction = True
            obstruction_detail = (
                f"refinement disagreement on keys: {weakened}"
            )

        return PhiMergeResult(
            _merged_section=merged,
            _predecessor_count=len(sections),
            _agreed_keys=frozenset(agreed),
            _weakened_keys=frozenset(weakened),
            _dropped_keys=frozenset(dropped),
            _carrier_widened=carrier_widened,
            _has_obstruction=has_obstruction,
            _obstruction_detail=obstruction_detail,
        )

    def merge_pair(
        self,
        section_a: LocalSection,
        section_b: LocalSection,
        phi_site: SiteId,
    ) -> LocalSection:
        """Merge exactly two predecessor sections."""
        return self.merge([section_a, section_b], phi_site)

    # -- Refinement merging ------------------------------------------------

    def _join_refinements(
        self,
        refine_a: Dict[str, Any],
        refine_b: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Join two refinement dictionaries.

        - Keys present in both with equal values: kept as-is (agreed).
        - Keys present in both with different values: weakened to disjunction.
        - Keys present in only one: dropped (not universally known).
        """
        result: Dict[str, Any] = {}

        keys_a = set(refine_a.keys())
        keys_b = set(refine_b.keys())
        shared = keys_a & keys_b

        for key in shared:
            val_a = refine_a[key]
            val_b = refine_b[key]
            if val_a == val_b:
                # Agreement: keep the value
                result[key] = val_a
            else:
                # Disagreement: weaken to disjunction
                result[key] = ("disjunction", val_a, val_b)

        # Keys in only one side are dropped (information lost at join)
        # unless we're in non-strict mode and want to keep them tentatively
        if not self._strict_refinement_agreement:
            for key in keys_a - keys_b:
                result[f"tentative_{key}"] = ("from_branch_a", refine_a[key])
            for key in keys_b - keys_a:
                result[f"tentative_{key}"] = ("from_branch_b", refine_b[key])

        return result

    def _join_refinements_all(
        self,
        sections: Sequence[LocalSection],
    ) -> Tuple[Dict[str, Any], Set[str], Set[str], Set[str]]:
        """Join refinements from all predecessor sections.

        Returns (merged_refinements, agreed_keys, weakened_keys, dropped_keys).
        """
        if not sections:
            return {}, set(), set(), set()

        # Start with the first section's refinements
        all_keys: Set[str] = set()
        for sec in sections:
            all_keys |= set(sec.refinements.keys())

        agreed: Set[str] = set()
        weakened: Set[str] = set()
        dropped: Set[str] = set()
        result: Dict[str, Any] = {}

        for key in all_keys:
            # Collect values for this key across all sections
            values: List[Any] = []
            present_count = 0
            for sec in sections:
                if key in sec.refinements:
                    values.append(sec.refinements[key])
                    present_count += 1

            if present_count == 0:
                dropped.add(key)
                continue

            if present_count < len(sections):
                # Key not present in all branches: drop or tentative
                dropped.add(key)
                if not self._strict_refinement_agreement and values:
                    result[f"tentative_{key}"] = ("partial", values[0])
                continue

            # Key present in all branches: check agreement
            first_val = values[0]
            if all(v == first_val for v in values[1:]):
                agreed.add(key)
                result[key] = first_val
            else:
                weakened.add(key)
                # Form disjunction of all distinct values
                distinct = []
                seen_reprs: Set[str] = set()
                for v in values:
                    r = repr(v)
                    if r not in seen_reprs:
                        seen_reprs.add(r)
                        distinct.append(v)
                if len(distinct) == 1:
                    result[key] = distinct[0]
                    weakened.discard(key)
                    agreed.add(key)
                else:
                    result[key] = ("disjunction",) + tuple(distinct)

        return result, agreed, weakened, dropped

    # -- Trust merging -----------------------------------------------------

    def _join_trust(
        self,
        trust_a: TrustLevel,
        trust_b: TrustLevel,
    ) -> TrustLevel:
        """Compute the trust level of a merged section.

        At a join point, trust is the *meet* (weakest link) of the
        predecessor trusts, because we can only guarantee what holds
        on *all* incoming paths.
        """
        return trust_meet(trust_a, trust_b)

    def _join_trust_all(
        self,
        sections: Sequence[LocalSection],
    ) -> TrustLevel:
        """Compute the merged trust from all predecessors."""
        if not sections:
            return TrustLevel.ASSUMED
        result = sections[0].trust
        for sec in sections[1:]:
            result = trust_meet(result, sec.trust)
        return result

    # -- Carrier type merging ----------------------------------------------

    def _join_carriers(
        self,
        sections: Sequence[LocalSection],
    ) -> Any:
        """Compute the joined carrier type across predecessors.

        Uses type_join (LUB) to widen the carrier type.
        """
        carriers = [s.carrier_type for s in sections if s.carrier_type is not None]
        if not carriers:
            return None

        if not self._allow_carrier_widening:
            # Strict mode: all carriers must agree or we return None
            first = carriers[0]
            if all(c == first for c in carriers[1:]):
                return first
            return None

        # Use type_join for TypeBase carriers
        result = carriers[0]
        for carrier in carriers[1:]:
            if isinstance(result, TypeBase) and isinstance(carrier, TypeBase):
                result = type_join(result, carrier)
            elif result != carrier:
                # Non-TypeBase carriers that disagree: return None
                return None

        return result

    # -- Witness merging ---------------------------------------------------

    def _join_witnesses(
        self,
        sections: Sequence[LocalSection],
    ) -> Dict[str, Any]:
        """Merge witness dictionaries from predecessors.

        Only witnesses that are present and equal across *all* predecessors
        survive the merge.  Others are wrapped in a composite marker.
        """
        if not sections:
            return {}

        all_keys: Set[str] = set()
        for sec in sections:
            all_keys |= set(sec.witnesses.keys())

        result: Dict[str, Any] = {}
        for key in all_keys:
            witnesses = []
            for sec in sections:
                if key in sec.witnesses:
                    witnesses.append(sec.witnesses[key])

            if len(witnesses) == len(sections):
                first = witnesses[0]
                if all(w == first for w in witnesses[1:]):
                    result[key] = first
                else:
                    # Witnesses disagree: mark as composite/weakened
                    result[key] = ("phi_composite", tuple(witnesses))
            # If not all predecessors have the witness, it's dropped

        return result

    # -- Batch merge operations --------------------------------------------

    def merge_at_all_phi_sites(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, LocalSection]:
        """Identify all phi/join sites and merge their predecessor sections.

        A phi site is any site that is the target of multiple morphisms
        with PHI_MERGE restriction kind, or any site with multiple incoming
        morphisms from different branches.
        """
        # Build target -> incoming morphisms mapping
        incoming: Dict[SiteId, List[ConcreteMorphism]] = {}
        for m in cover.morphisms:
            incoming.setdefault(m.target, []).append(m)

        result = dict(sections)

        for site_id, in_morphisms in incoming.items():
            if len(in_morphisms) < 2:
                continue

            # Check if this is a phi-merge site
            is_phi = any(
                _is_phi_morphism(m) for m in in_morphisms
            )
            if not is_phi:
                # Also treat sites with multiple incoming control restrictions
                # as phi sites
                control_count = sum(
                    1 for m in in_morphisms if _is_control_morphism(m)
                )
                is_phi = control_count >= 2

            if not is_phi:
                continue

            # Collect predecessor sections
            predecessors: List[LocalSection] = []
            for m in in_morphisms:
                sec = sections.get(m.source)
                if sec is not None:
                    predecessors.append(sec)

            if predecessors:
                merged = self.merge(predecessors, site_id)
                result[site_id] = merged

        return result


# ---------------------------------------------------------------------------
# Utility functions
# ---------------------------------------------------------------------------

def _is_phi_morphism(morphism: ConcreteMorphism) -> bool:
    """Check if a morphism is a phi-merge restriction."""
    if hasattr(morphism, "metadata") and isinstance(morphism.metadata, dict):
        rdata = morphism.metadata.get("restriction")
        if isinstance(rdata, RestrictionData):
            return rdata.kind == RestrictionKind.PHI_MERGE
    return False


def _is_control_morphism(morphism: ConcreteMorphism) -> bool:
    """Check if a morphism is a control (branch) restriction."""
    if hasattr(morphism, "metadata") and isinstance(morphism.metadata, dict):
        rdata = morphism.metadata.get("restriction")
        if isinstance(rdata, RestrictionData):
            return rdata.kind in (
                RestrictionKind.CONTROL_TRUE,
                RestrictionKind.CONTROL_FALSE,
            )
    return False
