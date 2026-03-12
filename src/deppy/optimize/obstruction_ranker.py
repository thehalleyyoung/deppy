"""Rank obstructions by resolution power.

ObstructionRanker scores each obstruction in the H^1 basis by three
criteria and produces a ranked list so the user addresses the most
impactful type errors first:

1. **Number of downstream sites affected** -- obstructions whose
   resolution would unblock the most other sites are ranked higher.
2. **Ease of resolution** -- obstructions that require fewer changes
   (e.g. a single guard insertion) score higher for ease.
3. **User impact** -- obstructions at boundaries (input/output) visible
   to callers are weighted more heavily.
"""

from __future__ import annotations

import math
from collections import defaultdict, deque
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
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


# ---------------------------------------------------------------------------
# Ranked obstruction data class
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RankedObstruction:
    """An obstruction annotated with ranking scores.

    Attributes:
        obstruction: The original ObstructionData.
        overall_score: Composite ranking score (higher = address first).
        resolution_power: How many downstream sites are unblocked.
        ease_of_resolution: How easy it is to fix (higher = easier).
        user_impact: Impact on user-visible boundaries (higher = bigger).
        downstream_count: Number of transitively affected sites.
        rank: 1-based rank in the sorted list.
        category: Classification string for the obstruction kind.
    """

    _obstruction: ObstructionData
    _overall_score: float
    _resolution_power: float
    _ease_of_resolution: float
    _user_impact: float
    _downstream_count: int
    _rank: int = 0
    _category: str = "unknown"

    @property
    def obstruction(self) -> ObstructionData:
        return self._obstruction

    @property
    def overall_score(self) -> float:
        return self._overall_score

    @property
    def resolution_power(self) -> float:
        return self._resolution_power

    @property
    def ease_of_resolution(self) -> float:
        return self._ease_of_resolution

    @property
    def user_impact(self) -> float:
        return self._user_impact

    @property
    def downstream_count(self) -> int:
        return self._downstream_count

    @property
    def rank(self) -> int:
        return self._rank

    @property
    def category(self) -> str:
        return self._category


# ---------------------------------------------------------------------------
# Graph utilities
# ---------------------------------------------------------------------------

def _build_forward_adj(cover: Cover) -> Dict[SiteId, Set[SiteId]]:
    """Build forward adjacency from morphisms."""
    adj: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for m in cover.morphisms:
        adj[m.source].add(m.target)
    for a, b in cover.overlaps:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def _build_reverse_adj(cover: Cover) -> Dict[SiteId, Set[SiteId]]:
    """Build reverse adjacency from morphisms."""
    rev: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for m in cover.morphisms:
        rev[m.target].add(m.source)
    return rev


def _bfs_reachable(
    starts: Set[SiteId],
    adj: Dict[SiteId, Set[SiteId]],
    exclude: Optional[Set[SiteId]] = None,
) -> Set[SiteId]:
    """BFS reachability from a set of start nodes."""
    if exclude is None:
        exclude = set()
    visited: Set[SiteId] = set()
    queue: deque[SiteId] = deque(starts - exclude)
    while queue:
        node = queue.popleft()
        if node in visited:
            continue
        visited.add(node)
        for nb in adj.get(node, set()):
            if nb not in visited and nb not in exclude:
                queue.append(nb)
    return visited


def _sites_from_obstruction(obs: ObstructionData) -> Set[SiteId]:
    """Extract all site IDs referenced in an obstruction."""
    sites: Set[SiteId] = set()
    for a_id, b_id in obs.conflicting_overlaps:
        sites.add(a_id)
        sites.add(b_id)
    return sites


# ---------------------------------------------------------------------------
# Scoring functions
# ---------------------------------------------------------------------------

def _resolution_power(
    obs: ObstructionData,
    cover: Cover,
    adj: Dict[SiteId, Set[SiteId]],
) -> float:
    """Compute resolution power: how many sites does fixing this unblock?

    Resolution power is the count of downstream sites reachable from the
    obstruction's conflicting sites, normalized by the total site count.
    """
    obs_sites = _sites_from_obstruction(obs)
    if not obs_sites:
        return 0.0

    downstream = _bfs_reachable(obs_sites, adj)
    downstream -= obs_sites

    total_sites = max(len(cover.sites), 1)
    raw_count = len(downstream)
    normalized = raw_count / total_sites

    output_overlap = downstream & cover.output_boundary
    if output_overlap:
        normalized += 0.2 * len(output_overlap) / max(len(cover.output_boundary), 1)

    return min(normalized, 1.0)


def _downstream_impact(
    obs: ObstructionData,
    cover: Cover,
    adj: Dict[SiteId, Set[SiteId]],
) -> int:
    """Count the number of downstream sites transitively affected."""
    obs_sites = _sites_from_obstruction(obs)
    if not obs_sites:
        return 0
    downstream = _bfs_reachable(obs_sites, adj)
    downstream -= obs_sites
    return len(downstream)


def _ease_of_resolution(obs: ObstructionData) -> float:
    """Score the ease of resolving an obstruction (0=hard, 1=easy).

    Factors:
    - Fewer conflicting overlaps => easier.
    - Conflicts at argument boundaries => easier (just add annotation).
    - Conflicts at complex interior sites => harder.
    """
    n_conflicts = len(obs.conflicting_overlaps)
    if n_conflicts == 0:
        return 1.0

    base_ease = 1.0 / (1.0 + math.log1p(n_conflicts))

    boundary_count = 0
    guard_count = 0
    for a_id, b_id in obs.conflicting_overlaps:
        for sid in (a_id, b_id):
            if sid.kind in (
                SiteKind.ARGUMENT_BOUNDARY,
                SiteKind.RETURN_OUTPUT_BOUNDARY,
            ):
                boundary_count += 1
            if sid.kind == SiteKind.BRANCH_GUARD:
                guard_count += 1

    total_sites = n_conflicts * 2
    if total_sites > 0:
        boundary_fraction = boundary_count / total_sites
        base_ease += 0.3 * boundary_fraction

        guard_fraction = guard_count / total_sites
        base_ease += 0.2 * guard_fraction

    explanation = obs.explanation.lower()
    if "none" in explanation or "optional" in explanation:
        base_ease += 0.15
    elif "guard" in explanation or "isinstance" in explanation:
        base_ease += 0.10

    return min(base_ease, 1.0)


def _user_impact(
    obs: ObstructionData,
    cover: Cover,
) -> float:
    """Score user impact: how visible is this error to the end user?

    Boundary-site obstructions (input/output) have higher impact because
    they affect the function's external interface.
    """
    obs_sites = _sites_from_obstruction(obs)
    if not obs_sites:
        return 0.0

    input_overlap = obs_sites & cover.input_boundary
    output_overlap = obs_sites & cover.output_boundary
    error_overlap = obs_sites & cover.error_sites

    score = 0.0

    if output_overlap:
        score += 0.5 * len(output_overlap) / max(len(obs_sites), 1)

    if input_overlap:
        score += 0.3 * len(input_overlap) / max(len(obs_sites), 1)

    if error_overlap:
        score += 0.2 * len(error_overlap) / max(len(obs_sites), 1)

    for sid in obs_sites:
        if sid.kind == SiteKind.RETURN_OUTPUT_BOUNDARY:
            score += 0.1
        elif sid.kind == SiteKind.ARGUMENT_BOUNDARY:
            score += 0.08
        elif sid.kind == SiteKind.CALL_RESULT:
            score += 0.05

    return min(score, 1.0)


def _classify_obstruction(obs: ObstructionData) -> str:
    """Classify the obstruction type from its explanation."""
    explanation = obs.explanation.lower()
    if "guard" in explanation or "branch" in explanation:
        return "missing_guard"
    if "none" in explanation or "optional" in explanation:
        return "none_safety"
    if "bound" in explanation or "range" in explanation:
        return "bounds_violation"
    if "mismatch" in explanation or "incompatible" in explanation:
        return "type_mismatch"
    if "shape" in explanation or "dimension" in explanation:
        return "shape_mismatch"
    if "unreachable" in explanation:
        return "unreachable"
    return "unknown"


# ---------------------------------------------------------------------------
# ObstructionRanker
# ---------------------------------------------------------------------------

class ObstructionRanker:
    """Rank obstructions by composite score of resolution power, ease, and impact.

    Usage::

        ranker = ObstructionRanker()
        ranked = ranker.rank(obstructions, cover)
        for ro in ranked:
            print(f"#{ro.rank}: score={ro.overall_score:.2f} -- {ro.obstruction.explanation}")
    """

    def __init__(
        self,
        *,
        weight_resolution: float = 0.45,
        weight_ease: float = 0.25,
        weight_impact: float = 0.30,
    ) -> None:
        self._w_resolution = weight_resolution
        self._w_ease = weight_ease
        self._w_impact = weight_impact

    def rank(
        self,
        obstructions: List[ObstructionData],
        cover: Optional[Cover] = None,
    ) -> List[RankedObstruction]:
        """Rank obstructions by composite score, highest first.

        If *cover* is provided, downstream impact and user impact are
        computed using the cover topology.  Otherwise, only the ease
        heuristic and explanation-based scoring are used.
        """
        if cover is None:
            cover = Cover()

        adj = _build_forward_adj(cover)
        scored: List[RankedObstruction] = []

        for obs in obstructions:
            if obs.is_trivial:
                continue

            rp = _resolution_power(obs, cover, adj)
            ease = _ease_of_resolution(obs)
            impact = _user_impact(obs, cover)
            downstream = _downstream_impact(obs, cover, adj)
            category = _classify_obstruction(obs)

            overall = (
                self._w_resolution * rp
                + self._w_ease * ease
                + self._w_impact * impact
            )

            ro = RankedObstruction(
                _obstruction=obs,
                _overall_score=overall,
                _resolution_power=rp,
                _ease_of_resolution=ease,
                _user_impact=impact,
                _downstream_count=downstream,
                _rank=0,
                _category=category,
            )
            scored.append(ro)

        scored.sort(key=lambda r: r.overall_score, reverse=True)

        ranked: List[RankedObstruction] = []
        for i, ro in enumerate(scored, 1):
            ranked.append(
                RankedObstruction(
                    _obstruction=ro.obstruction,
                    _overall_score=ro.overall_score,
                    _resolution_power=ro.resolution_power,
                    _ease_of_resolution=ro.ease_of_resolution,
                    _user_impact=ro.user_impact,
                    _downstream_count=ro.downstream_count,
                    _rank=i,
                    _category=ro.category,
                )
            )

        return ranked

    def _resolution_power(
        self,
        obs: ObstructionData,
        cover: Optional[Cover] = None,
    ) -> float:
        """Compute resolution power for a single obstruction."""
        if cover is None:
            return 0.5
        adj = _build_forward_adj(cover)
        return _resolution_power(obs, cover, adj)

    def _downstream_impact(
        self,
        obs: ObstructionData,
        cover: Cover,
    ) -> int:
        """Count downstream sites affected by this obstruction."""
        adj = _build_forward_adj(cover)
        return _downstream_impact(obs, cover, adj)

    def top_n(
        self,
        obstructions: List[ObstructionData],
        cover: Optional[Cover] = None,
        n: int = 5,
    ) -> List[RankedObstruction]:
        """Return the top-N ranked obstructions."""
        ranked = self.rank(obstructions, cover)
        return ranked[:n]

    def by_category(
        self,
        ranked: List[RankedObstruction],
    ) -> Dict[str, List[RankedObstruction]]:
        """Group ranked obstructions by category."""
        groups: Dict[str, List[RankedObstruction]] = {}
        for ro in ranked:
            groups.setdefault(ro.category, []).append(ro)
        return groups

    def summarize(
        self,
        ranked: List[RankedObstruction],
    ) -> str:
        """Produce a human-readable summary of ranked obstructions."""
        if not ranked:
            return "No obstructions to rank."

        lines: List[str] = []
        lines.append(f"Ranked Obstructions ({len(ranked)} total):")
        lines.append("=" * 60)

        for ro in ranked:
            lines.append(
                f"  #{ro.rank} [score={ro.overall_score:.3f}] "
                f"category={ro.category}"
            )
            lines.append(
                f"       resolution_power={ro.resolution_power:.3f}, "
                f"ease={ro.ease_of_resolution:.3f}, "
                f"impact={ro.user_impact:.3f}"
            )
            lines.append(
                f"       downstream_sites={ro.downstream_count}"
            )
            explanation_preview = ro.obstruction.explanation[:80]
            if len(ro.obstruction.explanation) > 80:
                explanation_preview += "..."
            lines.append(f"       {explanation_preview}")
            lines.append("")

        return "\n".join(lines)

    def compute_aggregate_stats(
        self,
        ranked: List[RankedObstruction],
    ) -> Dict[str, Any]:
        """Compute aggregate statistics across all ranked obstructions."""
        if not ranked:
            return {
                "total": 0,
                "avg_score": 0.0,
                "max_score": 0.0,
                "min_score": 0.0,
                "categories": {},
                "total_downstream": 0,
            }

        scores = [r.overall_score for r in ranked]
        categories = self.by_category(ranked)
        total_downstream = sum(r.downstream_count for r in ranked)

        return {
            "total": len(ranked),
            "avg_score": sum(scores) / len(scores),
            "max_score": max(scores),
            "min_score": min(scores),
            "categories": {k: len(v) for k, v in categories.items()},
            "total_downstream": total_downstream,
        }
