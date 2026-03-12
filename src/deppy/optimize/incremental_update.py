"""Incremental re-analysis on code edits.

When source code changes, IncrementalUpdater determines which sites in
the cover need re-analysis and which sections can be reused.  This avoids
re-running the full analysis pipeline on every edit.

The algorithm computes a *CoverDelta* describing which sites, morphisms,
and overlaps were added, removed, or modified.  From the delta it derives
the *invalidated* sites (those whose sections may be stale) and produces
a reuse map of still-valid sections.
"""

from __future__ import annotations

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
    Morphism,
    SiteId,
    SiteKind,
    TrustLevel,
)


# ---------------------------------------------------------------------------
# CoverDelta
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CoverDelta:
    """Describes the difference between an old cover and a new cover.

    Attributes:
        added_sites: Sites present in the new cover but not the old.
        removed_sites: Sites present in the old cover but not the new.
        modified_sites: Sites present in both but with changed schemas.
        added_morphisms: New morphisms in the new cover.
        removed_morphisms: Morphisms that existed only in the old cover.
        added_overlaps: New overlap pairs.
        removed_overlaps: Old overlap pairs no longer present.
        input_boundary_changed: Whether input boundary set changed.
        output_boundary_changed: Whether output boundary set changed.
    """

    _added_sites: FrozenSet[SiteId]
    _removed_sites: FrozenSet[SiteId]
    _modified_sites: FrozenSet[SiteId]
    _added_morphisms: Tuple[Tuple[SiteId, SiteId], ...]
    _removed_morphisms: Tuple[Tuple[SiteId, SiteId], ...]
    _added_overlaps: Tuple[Tuple[SiteId, SiteId], ...]
    _removed_overlaps: Tuple[Tuple[SiteId, SiteId], ...]
    _input_boundary_changed: bool = False
    _output_boundary_changed: bool = False

    @property
    def added_sites(self) -> FrozenSet[SiteId]:
        return self._added_sites

    @property
    def removed_sites(self) -> FrozenSet[SiteId]:
        return self._removed_sites

    @property
    def modified_sites(self) -> FrozenSet[SiteId]:
        return self._modified_sites

    @property
    def added_morphisms(self) -> Tuple[Tuple[SiteId, SiteId], ...]:
        return self._added_morphisms

    @property
    def removed_morphisms(self) -> Tuple[Tuple[SiteId, SiteId], ...]:
        return self._removed_morphisms

    @property
    def added_overlaps(self) -> Tuple[Tuple[SiteId, SiteId], ...]:
        return self._added_overlaps

    @property
    def removed_overlaps(self) -> Tuple[Tuple[SiteId, SiteId], ...]:
        return self._removed_overlaps

    @property
    def input_boundary_changed(self) -> bool:
        return self._input_boundary_changed

    @property
    def output_boundary_changed(self) -> bool:
        return self._output_boundary_changed

    @property
    def is_empty(self) -> bool:
        """True if no changes occurred."""
        return (
            not self._added_sites
            and not self._removed_sites
            and not self._modified_sites
            and not self._added_morphisms
            and not self._removed_morphisms
            and not self._added_overlaps
            and not self._removed_overlaps
            and not self._input_boundary_changed
            and not self._output_boundary_changed
        )

    @property
    def directly_changed_sites(self) -> FrozenSet[SiteId]:
        """Sites that are directly added, removed, or modified."""
        return self._added_sites | self._removed_sites | self._modified_sites


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _morphism_key(m: Morphism) -> Tuple[SiteId, SiteId]:
    """Extract a (source, target) key from a morphism."""
    return (m.source, m.target)


def _build_adjacency(cover: Cover) -> Dict[SiteId, Set[SiteId]]:
    """Build forward adjacency from morphisms and overlaps."""
    adj: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for m in cover.morphisms:
        adj[m.source].add(m.target)
    for a, b in cover.overlaps:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def _reverse_adjacency(adj: Dict[SiteId, Set[SiteId]]) -> Dict[SiteId, Set[SiteId]]:
    """Reverse an adjacency map."""
    rev: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for src, targets in adj.items():
        for tgt in targets:
            rev[tgt].add(src)
    return rev


def _transitive_closure(
    starts: Set[SiteId],
    adj: Dict[SiteId, Set[SiteId]],
) -> Set[SiteId]:
    """Compute transitive closure from a set of starting sites."""
    visited: Set[SiteId] = set()
    queue: deque[SiteId] = deque(starts)
    while queue:
        node = queue.popleft()
        if node in visited:
            continue
        visited.add(node)
        for nb in adj.get(node, set()):
            if nb not in visited:
                queue.append(nb)
    return visited


def _sites_equal(
    old_cover: Cover,
    new_cover: Cover,
    site_id: SiteId,
) -> bool:
    """Check if a site has the same schema in both covers."""
    old_site = old_cover.sites.get(site_id)
    new_site = new_cover.sites.get(site_id)
    if old_site is None or new_site is None:
        return False
    old_schema = getattr(old_site, "carrier_schema", None)
    new_schema = getattr(new_site, "carrier_schema", None)
    return old_schema == new_schema


# ---------------------------------------------------------------------------
# IncrementalUpdater
# ---------------------------------------------------------------------------

class IncrementalUpdater:
    """Incremental re-analysis engine for code edits.

    Compares old and new covers, computes the delta, identifies invalidated
    sites, and produces a reuse map of still-valid sections.

    Usage::

        updater = IncrementalUpdater()
        delta = updater.compute_delta(old_cover, new_cover)
        invalid = updater.invalidated_sites(delta, new_cover)
        reusable = updater.reuse_sections(old_sections, delta, new_cover)
    """

    def __init__(
        self,
        *,
        invalidation_depth: int = -1,
        revalidate_assumed: bool = True,
    ) -> None:
        """
        Args:
            invalidation_depth: Max BFS depth for transitive invalidation.
                -1 means unlimited.
            revalidate_assumed: Whether to invalidate sections with ASSUMED trust
                when their neighbors change.
        """
        self._invalidation_depth = invalidation_depth
        self._revalidate_assumed = revalidate_assumed

    def compute_delta(
        self,
        old_cover: Cover,
        new_cover: Cover,
    ) -> CoverDelta:
        """Compute the difference between old and new covers.

        Identifies added, removed, and modified sites; added and removed
        morphisms; added and removed overlaps; and boundary changes.
        """
        old_site_ids = frozenset(old_cover.sites.keys())
        new_site_ids = frozenset(new_cover.sites.keys())

        added = new_site_ids - old_site_ids
        removed = old_site_ids - new_site_ids
        common = old_site_ids & new_site_ids

        modified: Set[SiteId] = set()
        for sid in common:
            if not _sites_equal(old_cover, new_cover, sid):
                modified.add(sid)

        old_morph_keys = {_morphism_key(m) for m in old_cover.morphisms}
        new_morph_keys = {_morphism_key(m) for m in new_cover.morphisms}
        added_morphs = tuple(new_morph_keys - old_morph_keys)
        removed_morphs = tuple(old_morph_keys - new_morph_keys)

        old_overlaps = set(old_cover.overlaps)
        new_overlaps = set(new_cover.overlaps)
        added_overlaps = tuple(new_overlaps - old_overlaps)
        removed_overlaps = tuple(old_overlaps - new_overlaps)

        input_changed = old_cover.input_boundary != new_cover.input_boundary
        output_changed = old_cover.output_boundary != new_cover.output_boundary

        return CoverDelta(
            _added_sites=frozenset(added),
            _removed_sites=frozenset(removed),
            _modified_sites=frozenset(modified),
            _added_morphisms=added_morphs,
            _removed_morphisms=removed_morphs,
            _added_overlaps=added_overlaps,
            _removed_overlaps=removed_overlaps,
            _input_boundary_changed=input_changed,
            _output_boundary_changed=output_changed,
        )

    def invalidated_sites(
        self,
        delta: CoverDelta,
        new_cover: Optional[Cover] = None,
    ) -> Set[SiteId]:
        """Determine which sites need re-analysis.

        A site is invalidated if:
        1. It was added or modified.
        2. It is reachable (forward or backward) from a changed site.
        3. Its morphism connections changed.
        4. Its overlap partners changed.
        """
        if delta.is_empty:
            return set()

        directly_invalid: Set[SiteId] = set()
        directly_invalid |= delta.added_sites
        directly_invalid |= delta.modified_sites

        for src, tgt in delta.added_morphisms:
            directly_invalid.add(src)
            directly_invalid.add(tgt)
        for src, tgt in delta.removed_morphisms:
            directly_invalid.add(src)
            directly_invalid.add(tgt)

        for a, b in delta.added_overlaps:
            directly_invalid.add(a)
            directly_invalid.add(b)
        for a, b in delta.removed_overlaps:
            directly_invalid.add(a)
            directly_invalid.add(b)

        if new_cover is None:
            return directly_invalid

        if delta.input_boundary_changed:
            directly_invalid |= new_cover.input_boundary
        if delta.output_boundary_changed:
            directly_invalid |= new_cover.output_boundary

        valid_in_new = directly_invalid & frozenset(new_cover.sites.keys())
        removed = directly_invalid & delta.removed_sites

        adj = _build_adjacency(new_cover)
        rev = _reverse_adjacency(adj)

        combined_adj: Dict[SiteId, Set[SiteId]] = defaultdict(set)
        for sid, targets in adj.items():
            combined_adj[sid] |= targets
        for sid, sources in rev.items():
            combined_adj[sid] |= sources

        if self._invalidation_depth < 0:
            all_invalid = _transitive_closure(valid_in_new, combined_adj)
        else:
            all_invalid = self._bounded_closure(
                valid_in_new, combined_adj, self._invalidation_depth
            )

        all_invalid |= removed
        return all_invalid

    def reuse_sections(
        self,
        old_sections: Dict[SiteId, LocalSection],
        delta: CoverDelta,
        new_cover: Optional[Cover] = None,
    ) -> Dict[SiteId, LocalSection]:
        """Return sections from the old analysis that are still valid.

        A section can be reused if its site was not invalidated by the delta.
        Sections at removed sites are discarded.
        """
        invalid = self.invalidated_sites(delta, new_cover)

        reusable: Dict[SiteId, LocalSection] = {}
        for sid, sec in old_sections.items():
            if sid in delta.removed_sites:
                continue
            if sid in invalid:
                continue
            if self._revalidate_assumed and sec.trust == TrustLevel.ASSUMED:
                neighbors_changed = False
                for a, b in delta.added_morphisms:
                    if a == sid or b == sid:
                        neighbors_changed = True
                        break
                for a, b in delta.removed_morphisms:
                    if a == sid or b == sid:
                        neighbors_changed = True
                        break
                if neighbors_changed:
                    continue
            reusable[sid] = sec

        return reusable

    def merge_sections(
        self,
        reused: Dict[SiteId, LocalSection],
        fresh: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, LocalSection]:
        """Merge reused sections with freshly computed ones.

        Fresh sections take precedence over reused ones at the same site.
        """
        merged = dict(reused)
        merged.update(fresh)
        return merged

    def _bounded_closure(
        self,
        starts: Set[SiteId],
        adj: Dict[SiteId, Set[SiteId]],
        max_depth: int,
    ) -> Set[SiteId]:
        """BFS with bounded depth."""
        visited: Set[SiteId] = set()
        queue: deque[Tuple[SiteId, int]] = deque(
            (s, 0) for s in starts
        )
        while queue:
            node, depth = queue.popleft()
            if node in visited:
                continue
            visited.add(node)
            if depth < max_depth:
                for nb in adj.get(node, set()):
                    if nb not in visited:
                        queue.append((nb, depth + 1))
        return visited

    def summarize_delta(self, delta: CoverDelta) -> str:
        """Produce a human-readable summary of a CoverDelta."""
        if delta.is_empty:
            return "No changes detected."

        lines: List[str] = []
        lines.append("Cover Delta Summary:")
        lines.append(f"  Added sites:    {len(delta.added_sites)}")
        lines.append(f"  Removed sites:  {len(delta.removed_sites)}")
        lines.append(f"  Modified sites: {len(delta.modified_sites)}")
        lines.append(f"  Added morphisms:   {len(delta.added_morphisms)}")
        lines.append(f"  Removed morphisms: {len(delta.removed_morphisms)}")
        lines.append(f"  Added overlaps:    {len(delta.added_overlaps)}")
        lines.append(f"  Removed overlaps:  {len(delta.removed_overlaps)}")

        if delta.input_boundary_changed:
            lines.append("  Input boundary: CHANGED")
        if delta.output_boundary_changed:
            lines.append("  Output boundary: CHANGED")

        return "\n".join(lines)

    def reanalysis_plan(
        self,
        delta: CoverDelta,
        new_cover: Cover,
        old_sections: Dict[SiteId, LocalSection],
    ) -> Dict[str, Any]:
        """Produce a structured plan for incremental re-analysis.

        Returns a dict with:
        - invalidated: set of sites to re-analyze
        - reusable: dict of sections that can be kept
        - new_sites: sites that need fresh analysis
        - estimated_savings: fraction of work avoided
        """
        invalid = self.invalidated_sites(delta, new_cover)
        reusable = self.reuse_sections(old_sections, delta, new_cover)

        new_sites = delta.added_sites
        total_sites = len(new_cover.sites)
        reused_count = len(reusable)
        savings = reused_count / max(total_sites, 1)

        return {
            "invalidated": invalid,
            "reusable": reusable,
            "new_sites": new_sites,
            "total_sites": total_sites,
            "reused_count": reused_count,
            "reanalysis_count": len(invalid),
            "estimated_savings": savings,
        }
