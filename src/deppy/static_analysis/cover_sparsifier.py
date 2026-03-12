"""Cover sparsification — locality heuristics and summary sites.

A naively constructed cover can explode in size.  This module provides
sparsification strategies that reduce the cover while preserving semantic
information needed for the bidirectional synthesis algorithms.

The monograph (§ Precise implementation blueprint) notes:

    "A site cover can explode if constructed naively.  The implementation
    therefore needs locality heuristics, summary sites, and pack-specific
    sparsification rules from the beginning."

Sparsification operates on a ``Cover`` and returns a smaller ``Cover``
that is semantically equivalent for the purposes of:
1. Safe-input synthesis (backward pass)
2. Output synthesis (forward pass)
3. Error-site viability checking
4. Obstruction extraction

Sites that cannot contribute to any of these goals are candidates for
removal or summarization.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import Cover, SiteId, SiteKind, TrustLevel


# ---------------------------------------------------------------------------
# Sparsification strategies
# ---------------------------------------------------------------------------

class SparsificationStrategy:
    """Base class for cover sparsification strategies."""

    def should_keep(
        self,
        site_id: SiteId,
        cover: Cover,
    ) -> bool:
        """Return True if the site should be kept in the sparsified cover."""
        return True

    def apply(self, cover: Cover) -> Cover:
        """Apply this strategy to produce a sparser cover."""
        kept_sites = {
            sid: site for sid, site in cover.sites.items()
            if self.should_keep(sid, cover)
        }
        kept_ids = set(kept_sites.keys())

        # Keep only morphisms between kept sites
        kept_morphisms = [
            m for m in cover.morphisms
            if m.source in kept_ids and m.target in kept_ids
        ]

        # Keep only overlaps between kept sites
        kept_overlaps = [
            (a, b) for a, b in cover.overlaps
            if a in kept_ids and b in kept_ids
        ]

        return Cover(
            sites=kept_sites,
            morphisms=kept_morphisms,
            overlaps=kept_overlaps,
            error_sites=cover.error_sites & kept_ids,
            input_boundary=cover.input_boundary & kept_ids,
            output_boundary=cover.output_boundary & kept_ids,
        )


class KeepBoundaryAndErrors(SparsificationStrategy):
    """Always keep boundary sites and error-sensitive sites.

    This is the minimal strategy: input boundary, output boundary,
    and error sites are never removed because they are the primary
    subjects of the bidirectional synthesis algorithms.
    """

    def should_keep(self, site_id: SiteId, cover: Cover) -> bool:
        if site_id in cover.input_boundary:
            return True
        if site_id in cover.output_boundary:
            return True
        if site_id in cover.error_sites:
            return True
        return True  # Keep everything by default


class RemoveDisconnectedSites(SparsificationStrategy):
    """Remove sites that have no morphisms connecting them to the cover.

    A site with no incoming or outgoing restriction maps cannot contribute
    to either backward or forward synthesis.
    """

    def should_keep(self, site_id: SiteId, cover: Cover) -> bool:
        # Always keep boundaries and errors
        if site_id in cover.input_boundary:
            return True
        if site_id in cover.output_boundary:
            return True
        if site_id in cover.error_sites:
            return True

        # Check for at least one morphism
        for m in cover.morphisms:
            if m.source == site_id or m.target == site_id:
                return True

        # Check for at least one overlap
        for a, b in cover.overlaps:
            if a == site_id or b == site_id:
                return True

        return False


class RemoveRedundantSSASites(SparsificationStrategy):
    """Remove SSA-value sites that are simple pass-throughs.

    An SSA site that has exactly one incoming lineage morphism and one
    outgoing lineage morphism, with no error sites depending on it,
    can be collapsed into a direct morphism from source to target.
    """

    def should_keep(self, site_id: SiteId, cover: Cover) -> bool:
        if site_id.kind != SiteKind.SSA_VALUE:
            return True
        if site_id in cover.error_sites:
            return True
        if site_id in cover.input_boundary:
            return True
        if site_id in cover.output_boundary:
            return True

        # Count incoming and outgoing lineage morphisms
        incoming = [m for m in cover.morphisms if m.target == site_id]
        outgoing = [m for m in cover.morphisms if m.source == site_id]

        # Simple pass-through: one in, one out, no overlaps
        if len(incoming) == 1 and len(outgoing) == 1:
            has_overlap = any(
                site_id in pair for pair in cover.overlaps
            )
            if not has_overlap:
                return False

        return True


class SummarizeDeepChains(SparsificationStrategy):
    """Summarize long lineage chains into summary sites.

    If a chain of SSA-value sites is longer than ``max_chain_length``,
    replace the interior with a single summary site that preserves the
    endpoints' semantic content.
    """

    def __init__(self, max_chain_length: int = 5) -> None:
        self.max_chain_length = max_chain_length

    def should_keep(self, site_id: SiteId, cover: Cover) -> bool:
        # This strategy is more complex; for now just keep everything
        # and implement chain summarization in a separate pass
        return True


class TheoryPackSparsifier(SparsificationStrategy):
    """Pack-specific sparsification.

    Theory packs may declare that certain site patterns can be
    summarized without losing semantic information.  For example,
    a shape pack might declare that intermediate shape-propagation
    sites can be collapsed if the final shape site captures all
    necessary constraints.
    """

    def __init__(
        self,
        pack_sparsifiers: Optional[Dict[str, Callable[[SiteId, Cover], bool]]] = None,
    ) -> None:
        self._pack_sparsifiers = pack_sparsifiers or {}

    def should_keep(self, site_id: SiteId, cover: Cover) -> bool:
        site = cover.sites.get(site_id)
        if site is None:
            return False

        metadata = getattr(site, "metadata", None) or {}
        pack_name = None
        data = metadata.get("data")
        if data and hasattr(data, "pack_name"):
            pack_name = data.pack_name

        if pack_name and pack_name in self._pack_sparsifiers:
            return self._pack_sparsifiers[pack_name](site_id, cover)

        return True


# ---------------------------------------------------------------------------
# Composite sparsifier
# ---------------------------------------------------------------------------

class CompositeSparsifier:
    """Apply multiple sparsification strategies in sequence."""

    def __init__(self, strategies: Optional[Sequence[SparsificationStrategy]] = None) -> None:
        self._strategies = list(strategies) if strategies else [
            RemoveDisconnectedSites(),
            RemoveRedundantSSASites(),
        ]

    def sparsify(self, cover: Cover) -> Cover:
        """Apply all strategies to produce the sparsest valid cover."""
        result = cover
        for strategy in self._strategies:
            result = strategy.apply(result)
        return result


# ---------------------------------------------------------------------------
# Convenience
# ---------------------------------------------------------------------------

def sparsify_cover(cover: Cover) -> Cover:
    """Apply default sparsification to a cover."""
    return CompositeSparsifier().sparsify(cover)


# ---------------------------------------------------------------------------
# Cover statistics for debugging and benchmarking
# ---------------------------------------------------------------------------

@dataclass
class CoverStats:
    """Statistics about a cover, useful for benchmarking sparsification."""
    total_sites: int = 0
    sites_by_kind: Dict[SiteKind, int] = field(default_factory=dict)
    total_morphisms: int = 0
    total_overlaps: int = 0
    error_site_count: int = 0
    input_boundary_count: int = 0
    output_boundary_count: int = 0
    disconnected_sites: int = 0


def compute_cover_stats(cover: Cover) -> CoverStats:
    """Compute statistics about a cover."""
    connected: Set[SiteId] = set()
    for m in cover.morphisms:
        connected.add(m.source)
        connected.add(m.target)
    for a, b in cover.overlaps:
        connected.add(a)
        connected.add(b)

    kind_counts: Dict[SiteKind, int] = {}
    for sid in cover.sites:
        kind = sid.kind
        kind_counts[kind] = kind_counts.get(kind, 0) + 1

    return CoverStats(
        total_sites=len(cover.sites),
        sites_by_kind=kind_counts,
        total_morphisms=len(cover.morphisms),
        total_overlaps=len(cover.overlaps),
        error_site_count=len(cover.error_sites),
        input_boundary_count=len(cover.input_boundary),
        output_boundary_count=len(cover.output_boundary),
        disconnected_sites=len(set(cover.sites.keys()) - connected),
    )
