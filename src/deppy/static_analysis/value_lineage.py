"""Value lineage tracking — sheaf-theoretic provenance of SSA values.

In the sheaf-descent view, a lineage chain is not merely a convenience for
wrapper detection; it is a witness that two textual values live in the same
semantic neighbourhood.  This module provides lineage analysis that operates
on the observation site category rather than on classical SSA form.

Lineage answers the question: "Which sites share semantic content because
one was derived from another?"  This determines which restriction maps
preserve refinements (wrapper transparency) and which sites form overlap
neighbourhoods where the sheaf gluing condition must hold.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import Cover, SiteId, SiteKind
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import RestrictionData, RestrictionKind


# ---------------------------------------------------------------------------
# Lineage graph
# ---------------------------------------------------------------------------

@dataclass
class LineageGraph:
    """Tracks value provenance through the site category.

    A lineage graph records which sites derive from which other sites via
    lineage restriction maps.  It supports:

    - Finding the transitive lineage root of any site
    - Finding all descendants of a site
    - Determining whether two sites are in the same lineage chain
      (and therefore should share semantic content)
    - Computing the lineage depth (wrapper nesting level)
    """

    # parent[child_id] = parent_id
    _parents: Dict[SiteId, SiteId] = field(default_factory=dict)
    # children[parent_id] = {child_ids}
    _children: Dict[SiteId, Set[SiteId]] = field(default_factory=dict)

    @classmethod
    def from_cover(cls, cover: Cover) -> LineageGraph:
        """Build a lineage graph from a cover's morphisms.

        Only considers morphisms with RestrictionKind.LINEAGE,
        RestrictionKind.ALIAS_CHAIN, or RestrictionKind.PACK_TRANSPORT.
        """
        graph = cls()
        lineage_kinds = {
            RestrictionKind.LINEAGE,
            RestrictionKind.ALIAS_CHAIN,
            RestrictionKind.PACK_TRANSPORT,
        }

        for morphism in cover.morphisms:
            metadata = getattr(morphism, "metadata", None) or {}
            restriction: Optional[RestrictionData] = metadata.get("restriction")
            if restriction and restriction.kind in lineage_kinds:
                graph.add_edge(morphism.source, morphism.target)

        return graph

    def add_edge(self, parent: SiteId, child: SiteId) -> None:
        """Record that child derives from parent."""
        self._parents[child] = parent
        if parent not in self._children:
            self._children[parent] = set()
        self._children[parent].add(child)

    def parent(self, site_id: SiteId) -> Optional[SiteId]:
        """Return the immediate lineage parent, or None if root."""
        return self._parents.get(site_id)

    def children(self, site_id: SiteId) -> FrozenSet[SiteId]:
        """Return immediate lineage children."""
        return frozenset(self._children.get(site_id, set()))

    def root(self, site_id: SiteId) -> SiteId:
        """Return the transitive lineage root."""
        current = site_id
        visited: Set[SiteId] = set()
        while current in self._parents:
            if current in visited:
                break  # Cycle protection
            visited.add(current)
            current = self._parents[current]
        return current

    def descendants(self, site_id: SiteId) -> FrozenSet[SiteId]:
        """Return all transitive descendants of a site."""
        result: Set[SiteId] = set()
        stack = list(self._children.get(site_id, set()))
        while stack:
            child = stack.pop()
            if child not in result:
                result.add(child)
                stack.extend(self._children.get(child, set()))
        return frozenset(result)

    def ancestors(self, site_id: SiteId) -> FrozenSet[SiteId]:
        """Return all transitive ancestors of a site."""
        result: Set[SiteId] = set()
        current = self._parents.get(site_id)
        while current is not None and current not in result:
            result.add(current)
            current = self._parents.get(current)
        return frozenset(result)

    def same_lineage(self, site_a: SiteId, site_b: SiteId) -> bool:
        """Check whether two sites are in the same lineage chain."""
        return self.root(site_a) == self.root(site_b)

    def lineage_depth(self, site_id: SiteId) -> int:
        """Compute the depth of a site in its lineage chain (0 = root)."""
        depth = 0
        current = site_id
        visited: Set[SiteId] = set()
        while current in self._parents:
            if current in visited:
                break
            visited.add(current)
            current = self._parents[current]
            depth += 1
        return depth

    def lineage_chain(self, site_id: SiteId) -> List[SiteId]:
        """Return the full lineage chain from root to the given site."""
        chain: List[SiteId] = [site_id]
        current = site_id
        visited: Set[SiteId] = set()
        while current in self._parents:
            if current in visited:
                break
            visited.add(current)
            current = self._parents[current]
            chain.append(current)
        chain.reverse()
        return chain

    def all_roots(self) -> FrozenSet[SiteId]:
        """Return all lineage roots (sites with no parent)."""
        all_sites = set(self._parents.keys()) | set(self._children.keys())
        return frozenset(s for s in all_sites if s not in self._parents)

    def lineage_groups(self) -> Dict[SiteId, FrozenSet[SiteId]]:
        """Group sites by their lineage root.

        Returns a mapping from each root to the set of all sites
        in its lineage tree (including the root itself).
        """
        groups: Dict[SiteId, Set[SiteId]] = {}
        all_sites = set(self._parents.keys()) | set(self._children.keys())
        for site in all_sites:
            r = self.root(site)
            if r not in groups:
                groups[r] = set()
            groups[r].add(site)
        return {r: frozenset(members) for r, members in groups.items()}


# ---------------------------------------------------------------------------
# Wrapper transparency analysis
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TransparencyResult:
    """Result of wrapper transparency analysis for a lineage chain.

    A wrapper is semantically transparent if its induced restriction map
    preserves or refines the relevant local sections without introducing
    new obstructions.
    """
    chain: Tuple[SiteId, ...]
    is_transparent: bool
    preserved_keys: FrozenSet[str]
    lost_keys: FrozenSet[str]
    obstruction_sites: FrozenSet[SiteId]


def analyze_wrapper_transparency(
    cover: Cover,
    lineage: LineageGraph,
    site_id: SiteId,
) -> TransparencyResult:
    """Analyze whether a site's lineage chain preserves semantic content.

    This implements the wrapper transparency criterion from the monograph:
    a wrapper is semantically transparent to the extent that its induced
    reindexing map preserves or refines the relevant local sections without
    introducing new obstructions.
    """
    chain = lineage.lineage_chain(site_id)
    all_preserved: Set[str] = set()
    all_lost: Set[str] = set()
    obstructions: Set[SiteId] = set()

    # Walk the chain and check each restriction
    for i in range(len(chain) - 1):
        parent_sid = chain[i]
        child_sid = chain[i + 1]

        # Find the morphism between them
        for morphism in cover.morphisms:
            if morphism.source == parent_sid and morphism.target == child_sid:
                metadata = getattr(morphism, "metadata", None) or {}
                restriction: Optional[RestrictionData] = metadata.get("restriction")
                if restriction:
                    all_preserved.update(restriction.preserved_keys)
                    all_lost.update(restriction.dropped_keys)
                break

        # Check if the child introduces new error sites
        if child_sid in cover.error_sites:
            obstructions.add(child_sid)

    return TransparencyResult(
        chain=tuple(chain),
        is_transparent=len(all_lost) == 0 and len(obstructions) == 0,
        preserved_keys=frozenset(all_preserved),
        lost_keys=frozenset(all_lost),
        obstruction_sites=frozenset(obstructions),
    )


# ---------------------------------------------------------------------------
# Error-site reachability through lineage
# ---------------------------------------------------------------------------

def error_sites_reachable_from(
    cover: Cover,
    lineage: LineageGraph,
    site_id: SiteId,
) -> FrozenSet[SiteId]:
    """Find all error sites reachable through lineage from a given site.

    This is used during backward synthesis to determine which error sites
    a given input parameter can influence.
    """
    descendants = lineage.descendants(site_id)
    all_related = descendants | {site_id}
    return frozenset(all_related & cover.error_sites)


def input_sites_influencing_error(
    cover: Cover,
    lineage: LineageGraph,
    error_site_id: SiteId,
) -> FrozenSet[SiteId]:
    """Find all input-boundary sites that influence an error site.

    This is the backward direction: from an error site, trace back
    through lineage to find which input parameters could prevent it.
    """
    ancestors = lineage.ancestors(error_site_id)
    all_related = ancestors | {error_site_id}
    return frozenset(all_related & cover.input_boundary)
