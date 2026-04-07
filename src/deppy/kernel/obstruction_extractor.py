"""Algorithm 5 -- Obstruction extraction.

Check the gluing condition at all overlap pairs, extract the obstruction
basis (H^1 cohomology representatives), and rank obstructions by severity
for user presentation.

In the sheaf-descent framework, type errors manifest as nontrivial
cohomology classes in H^1(U, T):
- A trivial H^1 means the local sections glue to a global section (no errors).
- A nontrivial H^1 means some overlaps disagree (type errors exist).

The obstruction extractor:
1. Checks every declared overlap for section agreement.
2. Groups disagreements into connected components (clusters).
3. Extracts a minimal obstruction basis (independent H^1 generators).
4. Ranks obstructions by impact (how many downstream sites are affected).
5. Suggests resolution candidates (which sites to strengthen/add proofs).
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
    BoundarySection,
    CechCochainData,
    CohomologyClass,
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
    RestrictionKind,
    apply_restriction,
)
from deppy.static_analysis.section_gluing import (
    check_gluing_condition,
    assemble_global_section,
    extract_obstruction_basis,
    GluingCheckResult,
    ObstructionBasis,
    ResolutionCandidate,
)
from deppy.kernel.trust_classifier import trust_rank, _extract_restriction_data


# ---------------------------------------------------------------------------
# Obstruction severity
# ---------------------------------------------------------------------------

class ObstructionSeverity(enum.Enum):
    """Severity classification for obstructions."""
    CRITICAL = "critical"       # Affects error sites
    HIGH = "high"               # Affects output boundary
    MEDIUM = "medium"           # Interior disagreement
    LOW = "low"                 # Tentative/weak disagreement
    INFORMATIONAL = "info"      # Style/optimization suggestion


# ---------------------------------------------------------------------------
# Enriched obstruction data
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RankedObstruction:
    """An obstruction enriched with ranking and severity information."""
    _obstruction: ObstructionData
    _severity: ObstructionSeverity
    _impact_score: float
    _affected_sites: FrozenSet[SiteId]
    _resolution_candidates: Tuple[ResolutionCandidate, ...]
    _cluster_id: int = 0

    @property
    def obstruction(self) -> ObstructionData:
        return self._obstruction

    @property
    def severity(self) -> ObstructionSeverity:
        return self._severity

    @property
    def impact_score(self) -> float:
        return self._impact_score

    @property
    def affected_sites(self) -> FrozenSet[SiteId]:
        return self._affected_sites

    @property
    def resolution_candidates(self) -> Tuple[ResolutionCandidate, ...]:
        return self._resolution_candidates

    @property
    def cluster_id(self) -> int:
        return self._cluster_id

    def __repr__(self) -> str:
        return (
            f"RankedObstruction(severity={self._severity.value}, "
            f"impact={self._impact_score:.2f}, "
            f"affected={len(self._affected_sites)}, "
            f"cluster={self._cluster_id})"
        )


# ---------------------------------------------------------------------------
# Extraction result
# ---------------------------------------------------------------------------

@dataclass
class ExtractionResult:
    """Result of obstruction extraction."""
    obstructions: List[RankedObstruction] = field(default_factory=list)
    obstruction_basis: Optional[ObstructionBasis] = None
    gluing_result: Optional[GluingCheckResult] = None
    global_section: Optional[GlobalSection] = None
    num_agreed: int = 0
    num_disagreed: int = 0
    num_clusters: int = 0
    h1_dimension: int = 0
    is_consistent: bool = False

    @property
    def has_obstructions(self) -> bool:
        return len(self.obstructions) > 0

    @property
    def critical_count(self) -> int:
        return sum(
            1 for o in self.obstructions
            if o.severity == ObstructionSeverity.CRITICAL
        )

    def by_severity(
        self, severity: ObstructionSeverity
    ) -> List[RankedObstruction]:
        """Filter obstructions by severity."""
        return [o for o in self.obstructions if o.severity == severity]

    def top_obstructions(self, n: int = 5) -> List[RankedObstruction]:
        """Return the top N obstructions by impact score."""
        return sorted(
            self.obstructions, key=lambda o: -o.impact_score
        )[:n]

    def __repr__(self) -> str:
        return (
            f"ExtractionResult(consistent={self.is_consistent}, "
            f"obstructions={len(self.obstructions)}, "
            f"agreed={self.num_agreed}, "
            f"disagreed={self.num_disagreed}, "
            f"h1_dim={self.h1_dimension})"
        )


# ---------------------------------------------------------------------------
# Obstruction extractor
# ---------------------------------------------------------------------------

class ObstructionExtractor:
    """Algorithm 5: Extract disagreeing overlaps and compute obstruction basis.

    The extractor checks the sheaf gluing condition at all overlap pairs,
    groups disagreements into clusters, and extracts a minimal obstruction
    basis for user presentation.
    """

    def __init__(
        self,
        *,
        include_informational: bool = False,
        max_obstructions: int = 100,
    ) -> None:
        self._include_informational = include_informational
        self._max_obstructions = max_obstructions

    # -- Main entry point --------------------------------------------------

    def extract(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> ExtractionResult:
        """Extract obstructions from a cover with local sections.

        This is Algorithm 5:
        1. Check gluing condition at all overlaps.
        2. Group disagreements into clusters.
        3. Extract minimal obstruction basis.
        4. Rank obstructions by severity and impact.
        """
        result = ExtractionResult()

        # Step 1: Check gluing condition
        gluing = check_gluing_condition(cover, sections)
        result.gluing_result = gluing
        result.num_agreed = len(gluing.agreed_overlaps)
        result.num_disagreed = len(gluing.disagreed_overlaps)
        result.is_consistent = gluing.is_consistent

        if gluing.is_consistent:
            # No obstructions: try to assemble global section
            global_sec, obs = assemble_global_section(cover, sections)
            result.global_section = global_sec
            return result

        # Step 2: Check each overlap individually for detailed info
        raw_obstructions: List[Tuple[ObstructionData, Tuple[SiteId, SiteId]]] = []
        for site_a, site_b in cover.overlaps:
            obs = self._check_overlap(site_a, site_b, sections, cover)
            if obs is not None:
                raw_obstructions.append((obs, (site_a, site_b)))

        # Step 3: Cluster disagreements
        clusters = self._cluster_obstructions(raw_obstructions, cover)
        result.num_clusters = len(clusters)

        # Step 4: Extract obstruction basis
        all_obs = [obs for obs, _ in raw_obstructions]
        basis = extract_obstruction_basis(all_obs, cover)
        result.obstruction_basis = basis
        # Use the GF(2) rank (dim H¹) rather than the raw obstruction count.
        # basis.rank is the minimum number of independent fixes required.
        result.h1_dimension = basis.rank

        # Step 5: Rank obstructions
        ranked = self._rank_obstructions(
            raw_obstructions, clusters, cover, sections
        )
        result.obstructions = ranked[:self._max_obstructions]

        return result

    # -- Overlap checking --------------------------------------------------

    def _check_overlap(
        self,
        site_a: SiteId,
        site_b: SiteId,
        sections: Dict[SiteId, LocalSection],
        cover: Cover,
    ) -> Optional[ObstructionData]:
        """Check a single overlap pair for section agreement.

        Returns an ObstructionData if the sections disagree, None if they agree.
        """
        section_a = sections.get(site_a)
        section_b = sections.get(site_b)

        # Missing section: record as obstruction
        if section_a is None or section_b is None:
            missing = site_a if section_a is None else site_b
            return ObstructionData(
                conflicting_overlaps=[(site_a, site_b)],
                explanation=f"missing section at {missing}",
            )

        # Check carrier type agreement
        carrier_disagreement = self._check_carrier_agreement(
            section_a, section_b
        )

        # Check refinement agreement
        refinement_disagreements = self._check_refinement_agreement(
            section_a, section_b
        )

        # Check trust consistency
        trust_issue = self._check_trust_consistency(
            section_a, section_b
        )

        # Combine disagreements
        explanations: List[str] = []
        if carrier_disagreement:
            explanations.append(carrier_disagreement)
        explanations.extend(refinement_disagreements)
        if trust_issue and self._include_informational:
            explanations.append(trust_issue)

        if not explanations:
            return None

        # Build cohomology class representative
        cochain = CechCochainData(
            degree=1,
            values={(site_a, site_b): tuple(explanations)},
        )
        cohomology = CohomologyClass(
            degree=1,
            representative=cochain,
            is_trivial=False,
        )

        return ObstructionData(
            cohomology_class=cohomology,
            conflicting_overlaps=[(site_a, site_b)],
            explanation="; ".join(explanations),
        )

    def _check_carrier_agreement(
        self,
        section_a: LocalSection,
        section_b: LocalSection,
    ) -> Optional[str]:
        """Check if two sections have compatible carrier types."""
        if section_a.carrier_type is None or section_b.carrier_type is None:
            return None
        if section_a.carrier_type != section_b.carrier_type:
            return (
                f"carrier type mismatch: "
                f"{section_a.carrier_type} at {section_a.site_id} vs "
                f"{section_b.carrier_type} at {section_b.site_id}"
            )
        return None

    def _check_refinement_agreement(
        self,
        section_a: LocalSection,
        section_b: LocalSection,
    ) -> List[str]:
        """Check if two sections have compatible refinements on shared keys."""
        disagreements: List[str] = []

        shared_keys = (
            set(section_a.refinements.keys())
            & set(section_b.refinements.keys())
        )

        for key in shared_keys:
            val_a = section_a.refinements[key]
            val_b = section_b.refinements[key]
            if val_a != val_b:
                disagreements.append(
                    f"refinement '{key}' disagrees: "
                    f"{val_a} at {section_a.site_id} vs "
                    f"{val_b} at {section_b.site_id}"
                )

        return disagreements

    def _check_trust_consistency(
        self,
        section_a: LocalSection,
        section_b: LocalSection,
    ) -> Optional[str]:
        """Check for trust level inconsistencies (informational)."""
        rank_a = trust_rank(section_a.trust)
        rank_b = trust_rank(section_b.trust)
        if abs(rank_a - rank_b) >= 3:
            return (
                f"large trust gap: {section_a.trust.value} at "
                f"{section_a.site_id} vs {section_b.trust.value} at "
                f"{section_b.site_id}"
            )
        return None

    # -- Clustering --------------------------------------------------------

    def _cluster_obstructions(
        self,
        raw_obstructions: List[Tuple[ObstructionData, Tuple[SiteId, SiteId]]],
        cover: Cover,
    ) -> Dict[int, List[Tuple[ObstructionData, Tuple[SiteId, SiteId]]]]:
        """Group obstructions into connected components (clusters).

        Two obstructions are in the same cluster if they share a site.
        """
        if not raw_obstructions:
            return {}

        # Union-find for clustering
        parent: Dict[SiteId, SiteId] = {}

        def find(x: SiteId) -> SiteId:
            while parent.get(x, x) != x:
                parent[x] = parent.get(parent[x], parent[x])
                x = parent[x]
            return x

        def union(a: SiteId, b: SiteId) -> None:
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb

        # Build clusters from overlapping sites
        for obs, (site_a, site_b) in raw_obstructions:
            parent.setdefault(site_a, site_a)
            parent.setdefault(site_b, site_b)
            union(site_a, site_b)

        # Group by cluster root
        cluster_map: Dict[SiteId, int] = {}
        cluster_id = 0
        for obs, (site_a, site_b) in raw_obstructions:
            root = find(site_a)
            if root not in cluster_map:
                cluster_map[root] = cluster_id
                cluster_id += 1

        # Build cluster dict
        clusters: Dict[int, List[Tuple[ObstructionData, Tuple[SiteId, SiteId]]]] = {}
        for obs, (site_a, site_b) in raw_obstructions:
            root = find(site_a)
            cid = cluster_map[root]
            clusters.setdefault(cid, []).append((obs, (site_a, site_b)))

        return clusters

    # -- Ranking -----------------------------------------------------------

    def _rank_obstructions(
        self,
        raw_obstructions: List[Tuple[ObstructionData, Tuple[SiteId, SiteId]]],
        clusters: Dict[int, List[Tuple[ObstructionData, Tuple[SiteId, SiteId]]]],
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[RankedObstruction]:
        """Rank obstructions by severity and impact score.

        Severity classification:
        - CRITICAL: involves an error site
        - HIGH: involves an output boundary site
        - MEDIUM: involves interior sites
        - LOW: weak disagreement (tentative refinements only)
        - INFORMATIONAL: trust inconsistency only
        """
        ranked: List[RankedObstruction] = []

        # Build reverse cluster map for each obstruction
        obs_to_cluster: Dict[int, int] = {}
        for cid, cluster_obs in clusters.items():
            for i, _ in enumerate(cluster_obs):
                obs_to_cluster[id(cluster_obs[i])] = cid

        # Build downstream site sets for impact scoring
        forward_adj = self._build_forward_adj(cover)

        for idx, (obs, (site_a, site_b)) in enumerate(raw_obstructions):
            # Classify severity
            severity = self._classify_severity(
                site_a, site_b, obs, cover
            )

            # Compute impact: number of downstream sites affected
            affected = self._compute_affected_sites(
                site_a, site_b, forward_adj, cover
            )

            # Impact score: weighted by severity and affected count
            severity_weight = {
                ObstructionSeverity.CRITICAL: 10.0,
                ObstructionSeverity.HIGH: 5.0,
                ObstructionSeverity.MEDIUM: 2.0,
                ObstructionSeverity.LOW: 0.5,
                ObstructionSeverity.INFORMATIONAL: 0.1,
            }
            impact = severity_weight.get(severity, 1.0) * (1.0 + len(affected))

            # Find cluster ID
            cluster_id = 0
            for cid, cluster_obs in clusters.items():
                for co, cp in cluster_obs:
                    if cp == (site_a, site_b):
                        cluster_id = cid
                        break

            # Generate resolution candidates for this obstruction
            candidates = self._generate_resolution_candidates(
                site_a, site_b, obs, cover, sections
            )

            ranked.append(RankedObstruction(
                _obstruction=obs,
                _severity=severity,
                _impact_score=impact,
                _affected_sites=frozenset(affected),
                _resolution_candidates=tuple(candidates),
                _cluster_id=cluster_id,
            ))

        # Sort by impact score (descending)
        ranked.sort(key=lambda r: -r.impact_score)
        return ranked

    def _classify_severity(
        self,
        site_a: SiteId,
        site_b: SiteId,
        obs: ObstructionData,
        cover: Cover,
    ) -> ObstructionSeverity:
        """Classify the severity of an obstruction."""
        # Critical if involves error sites
        if site_a in cover.error_sites or site_b in cover.error_sites:
            return ObstructionSeverity.CRITICAL

        # High if involves output boundary
        if site_a in cover.output_boundary or site_b in cover.output_boundary:
            return ObstructionSeverity.HIGH

        # Low if explanation mentions tentative
        if obs.explanation and "tentative" in obs.explanation.lower():
            return ObstructionSeverity.LOW

        # Informational if only trust issue
        if obs.explanation and "trust" in obs.explanation.lower():
            if "mismatch" not in obs.explanation.lower():
                return ObstructionSeverity.INFORMATIONAL

        return ObstructionSeverity.MEDIUM

    def _compute_affected_sites(
        self,
        site_a: SiteId,
        site_b: SiteId,
        forward_adj: Dict[SiteId, List[SiteId]],
        cover: Cover,
    ) -> Set[SiteId]:
        """Compute all sites downstream of a disagreement."""
        affected: Set[SiteId] = {site_a, site_b}
        queue: List[SiteId] = [site_a, site_b]

        while queue:
            current = queue.pop()
            for target in forward_adj.get(current, []):
                if target not in affected:
                    affected.add(target)
                    queue.append(target)

        return affected

    def _generate_resolution_candidates(
        self,
        site_a: SiteId,
        site_b: SiteId,
        obs: ObstructionData,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[ResolutionCandidate]:
        """Generate candidates that would resolve this obstruction."""
        candidates: List[ResolutionCandidate] = []

        # Candidate: strengthen section at site_a
        sec_a = sections.get(site_a)
        if sec_a is not None and trust_rank(sec_a.trust) < 4:
            candidates.append(ResolutionCandidate(
                description=f"strengthen section at {site_a}",
                site_id=site_a,
                resolves_count=1,
                action_type="strengthen_section",
            ))

        # Candidate: strengthen section at site_b
        sec_b = sections.get(site_b)
        if sec_b is not None and trust_rank(sec_b.trust) < 4:
            candidates.append(ResolutionCandidate(
                description=f"strengthen section at {site_b}",
                site_id=site_b,
                resolves_count=1,
                action_type="strengthen_section",
            ))

        # Candidate: add proof at an input boundary site upstream
        for in_site in cover.input_boundary:
            candidates.append(ResolutionCandidate(
                description=f"add input seed/annotation at {in_site}",
                site_id=in_site,
                resolves_count=1,
                action_type="add_seed",
            ))
            break  # Just suggest the first one

        return candidates

    def _build_forward_adj(
        self,
        cover: Cover,
    ) -> Dict[SiteId, List[SiteId]]:
        """Build forward adjacency list."""
        adj: Dict[SiteId, List[SiteId]] = {}
        for m in cover.morphisms:
            adj.setdefault(m.source, []).append(m.target)
        return adj
