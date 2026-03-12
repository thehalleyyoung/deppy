"""Section gluing — the sheaf condition on observation covers.

The sheaf gluing condition is the central coherence requirement:
local sections on overlapping sites must agree on their overlap.
When they disagree, we get an obstruction (a cohomology class in H^1)
that represents a type error or semantic ambiguity.

This module implements:
1. Checking the gluing condition on a cover with solved local sections
2. Computing obstructions where gluing fails
3. Attempting gluing to produce a global section
4. Extracting minimal obstruction bases for user explanation
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    BoundarySection,
    Cover,
    GlobalSection,
    LocalSection,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    apply_restriction,
)


# ---------------------------------------------------------------------------
# Gluing checker
# ---------------------------------------------------------------------------

@dataclass
class GluingCheckResult:
    """Result of checking the sheaf gluing condition on a cover."""
    is_consistent: bool
    obstructions: List[ObstructionData] = field(default_factory=list)
    agreed_overlaps: List[Tuple[SiteId, SiteId]] = field(default_factory=list)
    disagreed_overlaps: List[Tuple[SiteId, SiteId]] = field(default_factory=list)


def check_gluing_condition(
    cover: Cover,
    local_sections: Dict[SiteId, LocalSection],
) -> GluingCheckResult:
    """Check whether local sections satisfy the sheaf gluing condition.

    For every overlap (site_a, site_b) in the cover, the restrictions of
    the sections at site_a and site_b to the overlap must agree.  When
    they disagree, we record an obstruction.

    This implements the core check: "do the local solutions glue to a
    global section, or do we get a nontrivial H^1 class?"
    """
    agreed: List[Tuple[SiteId, SiteId]] = []
    disagreed: List[Tuple[SiteId, SiteId]] = []
    obstructions: List[ObstructionData] = []

    for site_a, site_b in cover.overlaps:
        section_a = local_sections.get(site_a)
        section_b = local_sections.get(site_b)

        if section_a is None or section_b is None:
            # Missing section — can't check, record as obstruction
            disagreed.append((site_a, site_b))
            obstructions.append(ObstructionData(
                conflicting_overlaps=[(site_a, site_b)],
                explanation=f"missing section at {site_a if section_a is None else site_b}",
            ))
            continue

        # Check refinement agreement
        if _sections_agree_on_overlap(section_a, section_b, cover):
            agreed.append((site_a, site_b))
        else:
            disagreed.append((site_a, site_b))
            obstructions.append(ObstructionData(
                conflicting_overlaps=[(site_a, site_b)],
                explanation=_describe_disagreement(section_a, section_b),
            ))

    return GluingCheckResult(
        is_consistent=len(disagreed) == 0,
        obstructions=obstructions,
        agreed_overlaps=agreed,
        disagreed_overlaps=disagreed,
    )


def _sections_agree_on_overlap(
    section_a: LocalSection,
    section_b: LocalSection,
    cover: Cover,
) -> bool:
    """Check whether two sections agree on their shared refinement keys.

    Agreement means: for every refinement key present in both sections,
    the values must be equal (or at least compatible under the information
    order).
    """
    shared_keys = set(section_a.refinements.keys()) & set(section_b.refinements.keys())
    for key in shared_keys:
        val_a = section_a.refinements[key]
        val_b = section_b.refinements[key]
        if val_a != val_b:
            return False

    # Carrier type agreement (if both have one)
    if section_a.carrier_type is not None and section_b.carrier_type is not None:
        if section_a.carrier_type != section_b.carrier_type:
            return False

    return True


def _describe_disagreement(
    section_a: LocalSection,
    section_b: LocalSection,
) -> str:
    """Produce a human-readable description of the disagreement."""
    parts: List[str] = []

    # Check carrier type
    if section_a.carrier_type is not None and section_b.carrier_type is not None:
        if section_a.carrier_type != section_b.carrier_type:
            parts.append(
                f"carrier mismatch: {section_a.carrier_type} vs {section_b.carrier_type}"
            )

    # Check shared refinements
    shared_keys = set(section_a.refinements.keys()) & set(section_b.refinements.keys())
    for key in shared_keys:
        if section_a.refinements[key] != section_b.refinements[key]:
            parts.append(
                f"refinement '{key}' disagrees: "
                f"{section_a.refinements[key]} vs {section_b.refinements[key]}"
            )

    if not parts:
        return "sections disagree (unknown reason)"
    return "; ".join(parts)


# ---------------------------------------------------------------------------
# Global section assembly
# ---------------------------------------------------------------------------

def assemble_global_section(
    cover: Cover,
    local_sections: Dict[SiteId, LocalSection],
) -> Tuple[Optional[GlobalSection], List[ObstructionData]]:
    """Attempt to glue local sections into a global section.

    Returns:
        - A GlobalSection if gluing succeeds (H^1 is trivial)
        - A list of obstructions if gluing fails (H^1 is nontrivial)
    """
    check = check_gluing_condition(cover, local_sections)

    if not check.is_consistent:
        return None, check.obstructions

    # Separate boundary sections
    input_sections = {
        sid: sec for sid, sec in local_sections.items()
        if sid in cover.input_boundary
    }
    output_sections = {
        sid: sec for sid, sec in local_sections.items()
        if sid in cover.output_boundary
    }

    input_boundary = BoundarySection(
        boundary_sites=input_sections,
        is_input=True,
    ) if input_sections else None

    output_boundary = BoundarySection(
        boundary_sites=output_sections,
        is_input=False,
    ) if output_sections else None

    global_section = GlobalSection(
        local_sections=dict(local_sections),
        input_section=input_boundary,
        output_section=output_boundary,
    )

    return global_section, []


# ---------------------------------------------------------------------------
# Obstruction basis extraction
# ---------------------------------------------------------------------------

@dataclass
class ObstructionBasis:
    """A minimal set of obstructions that explains all gluing failures.

    The monograph says: "Compress disagreements into an obstruction basis
    that is small enough to explain to users."

    An obstruction basis contains:
    1. The conflicting overlap pairs
    2. A ranking of which sites/seeds/proofs would resolve the most
       obstructions if strengthened
    """
    obstructions: List[ObstructionData]
    resolution_candidates: List[ResolutionCandidate] = field(default_factory=list)


@dataclass(frozen=True)
class ResolutionCandidate:
    """A candidate action that would resolve one or more obstructions.

    Ranked by how many obstruction coordinates they resolve.
    """
    description: str
    site_id: Optional[SiteId] = None
    resolves_count: int = 0
    action_type: str = ""  # "add_seed", "add_proof", "strengthen_theory"


def extract_obstruction_basis(
    obstructions: Sequence[ObstructionData],
    cover: Cover,
) -> ObstructionBasis:
    """Extract a minimal obstruction basis from a list of obstructions.

    This implements Algorithm 5 (Obstruction extraction):
    1. Collect precise overlaps whose restrictions disagree
    2. Compress into small basis
    3. Rank candidate resolutions
    """
    if not obstructions:
        return ObstructionBasis(obstructions=[])

    # Collect all conflicting sites
    conflict_sites: Dict[SiteId, int] = {}
    for obs in obstructions:
        for a, b in obs.conflicting_overlaps:
            conflict_sites[a] = conflict_sites.get(a, 0) + 1
            conflict_sites[b] = conflict_sites.get(b, 0) + 1

    # Generate resolution candidates ranked by impact
    candidates: List[ResolutionCandidate] = []

    # Sites near many conflicts are high-value resolution targets
    for sid, count in sorted(conflict_sites.items(), key=lambda x: -x[1]):
        if sid in cover.input_boundary:
            candidates.append(ResolutionCandidate(
                description=f"strengthen input seed at {sid}",
                site_id=sid,
                resolves_count=count,
                action_type="add_seed",
            ))
        elif sid in cover.error_sites:
            candidates.append(ResolutionCandidate(
                description=f"add viability proof for error site {sid}",
                site_id=sid,
                resolves_count=count,
                action_type="add_proof",
            ))
        else:
            candidates.append(ResolutionCandidate(
                description=f"add local theory or proof at {sid}",
                site_id=sid,
                resolves_count=count,
                action_type="strengthen_theory",
            ))

    return ObstructionBasis(
        obstructions=list(obstructions),
        resolution_candidates=candidates,
    )


# ---------------------------------------------------------------------------
# Incremental re-gluing after adding new sections
# ---------------------------------------------------------------------------

def recheck_after_new_section(
    cover: Cover,
    existing_sections: Dict[SiteId, LocalSection],
    new_site: SiteId,
    new_section: LocalSection,
) -> GluingCheckResult:
    """Incrementally check gluing after adding one new local section.

    Instead of rechecking all overlaps, only check overlaps involving
    the newly added site.  This is important for performance during
    the fixed-point iteration of backward/forward synthesis.
    """
    updated = dict(existing_sections)
    updated[new_site] = new_section

    # Only check overlaps involving new_site
    relevant_overlaps = [
        (a, b) for a, b in cover.overlaps
        if a == new_site or b == new_site
    ]

    agreed: List[Tuple[SiteId, SiteId]] = []
    disagreed: List[Tuple[SiteId, SiteId]] = []
    obstructions: List[ObstructionData] = []

    for site_a, site_b in relevant_overlaps:
        section_a = updated.get(site_a)
        section_b = updated.get(site_b)

        if section_a is None or section_b is None:
            continue

        if _sections_agree_on_overlap(section_a, section_b, cover):
            agreed.append((site_a, site_b))
        else:
            disagreed.append((site_a, site_b))
            obstructions.append(ObstructionData(
                conflicting_overlaps=[(site_a, site_b)],
                explanation=_describe_disagreement(section_a, section_b),
            ))

    return GluingCheckResult(
        is_consistent=len(disagreed) == 0,
        obstructions=obstructions,
        agreed_overlaps=agreed,
        disagreed_overlaps=disagreed,
    )
