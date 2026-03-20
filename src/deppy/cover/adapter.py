from __future__ import annotations

from collections import defaultdict, deque
from typing import Any, DefaultDict, Dict, Iterable, List, Mapping, MutableMapping, Sequence, Set, Tuple

from deppy.core._protocols import Cover, Morphism, SiteId

from .models import AffectedStalk, AffectedStalkReport


def _site_sort_key(site_id: SiteId) -> Tuple[str, str, int, int]:
    location = site_id.source_location or ("", 0, 0)
    source_name = str(location[0]) if len(location) > 0 else ""
    start = int(location[1]) if len(location) > 1 and isinstance(location[1], int) else 0
    end = int(location[2]) if len(location) > 2 and isinstance(location[2], int) else 0
    return (source_name, site_id.kind.value, start, end)


def _get_metadata(site: Any) -> Mapping[str, Any]:
    metadata = getattr(site, "metadata", None)
    if isinstance(metadata, Mapping):
        return metadata
    metadata = getattr(site, "_metadata", None)
    if isinstance(metadata, Mapping):
        return metadata
    return {}


def site_source_lines(site_id: SiteId, site: Any | None = None) -> Tuple[int, ...]:
    """Return normalized source lines for a site.

    The existing codebase uses ``source_location`` in two slightly different ways:
    some sites store ``(module, line, col)``, while others store
    ``(scope, line_start, line_end)``. This helper treats the third position as an
    end line only when it looks like a line span; otherwise it conservatively keeps
    the primary line only.
    """

    lines: Set[int] = set()
    location = site_id.source_location
    if location:
        start = location[1] if len(location) > 1 else None
        third = location[2] if len(location) > 2 else None
        if isinstance(start, int) and start > 0:
            lines.add(start)
            if isinstance(third, int) and third >= start:
                lines.update(range(start, third + 1))

    metadata = _get_metadata(site) if site is not None else {}
    for key in ("line", "source_line", "lineno", "line_start", "line_end"):
        value = metadata.get(key)
        if isinstance(value, int) and value > 0:
            lines.add(value)

    return tuple(sorted(lines))


def overlap_adjacency(cover: Cover) -> Dict[SiteId, Tuple[SiteId, ...]]:
    """Build deterministic undirected adjacency induced by cover overlaps."""

    adjacency: DefaultDict[SiteId, Set[SiteId]] = defaultdict(set)
    for left, right in cover.overlaps:
        adjacency[left].add(right)
        adjacency[right].add(left)
    return {
        site_id: tuple(sorted(neighbors, key=_site_sort_key))
        for site_id, neighbors in sorted(adjacency.items(), key=lambda item: _site_sort_key(item[0]))
    }


def morphism_adjacency(
    cover: Cover,
) -> Tuple[Dict[SiteId, Tuple[SiteId, ...]], Dict[SiteId, Tuple[SiteId, ...]]]:
    """Return deterministic incoming/outgoing morphism adjacency."""

    incoming: DefaultDict[SiteId, Set[SiteId]] = defaultdict(set)
    outgoing: DefaultDict[SiteId, Set[SiteId]] = defaultdict(set)
    for morphism in cover.morphisms:
        outgoing[morphism.source].add(morphism.target)
        incoming[morphism.target].add(morphism.source)
    ordered_incoming = {
        site_id: tuple(sorted(neighbors, key=_site_sort_key))
        for site_id, neighbors in sorted(incoming.items(), key=lambda item: _site_sort_key(item[0]))
    }
    ordered_outgoing = {
        site_id: tuple(sorted(neighbors, key=_site_sort_key))
        for site_id, neighbors in sorted(outgoing.items(), key=lambda item: _site_sort_key(item[0]))
    }
    return ordered_incoming, ordered_outgoing


def locate_sites_for_lines(cover: Cover, changed_lines: Iterable[int]) -> Tuple[SiteId, ...]:
    """Find the sites whose source lines intersect ``changed_lines``."""

    line_set = {line for line in changed_lines if isinstance(line, int) and line > 0}
    if not line_set:
        return ()

    matches: List[SiteId] = []
    for site_id, site in cover.sites.items():
        if line_set.intersection(site_source_lines(site_id, site)):
            matches.append(site_id)
    return tuple(sorted(matches, key=_site_sort_key))


def affected_stalks(
    cover: Cover,
    changed_lines: Iterable[int],
    *,
    max_hops: int = 1,
    include_overlaps: bool = True,
    include_morphisms: bool = True,
) -> AffectedStalkReport:
    """Compute a deterministic local impact set over a cover.

    Seed sites are selected by line overlap. The result may then expand one or more
    hops across cover overlaps and/or morphisms.
    """

    if max_hops < 0:
        raise ValueError("max_hops must be >= 0")

    normalized_lines = tuple(sorted({line for line in changed_lines if isinstance(line, int) and line > 0}))
    if not normalized_lines or not cover.sites:
        return AffectedStalkReport(changed_lines=normalized_lines)

    seed_sites = locate_sites_for_lines(cover, normalized_lines)
    overlap_map = overlap_adjacency(cover)
    incoming_map, outgoing_map = morphism_adjacency(cover)

    graph: DefaultDict[SiteId, Set[SiteId]] = defaultdict(set)
    if include_overlaps:
        for site_id, neighbors in overlap_map.items():
            graph[site_id].update(neighbors)
    if include_morphisms:
        for site_id, neighbors in incoming_map.items():
            graph[site_id].update(neighbors)
            for neighbor in neighbors:
                graph[neighbor].add(site_id)
        for site_id, neighbors in outgoing_map.items():
            graph[site_id].update(neighbors)
            for neighbor in neighbors:
                graph[neighbor].add(site_id)

    seed_set = set(seed_sites)
    distances: Dict[SiteId, int] = {site_id: 0 for site_id in seed_sites}
    queue: deque[SiteId] = deque(seed_sites)
    while queue:
        current = queue.popleft()
        if distances[current] >= max_hops:
            continue
        for neighbor in sorted(graph.get(current, ()), key=_site_sort_key):
            if neighbor in distances:
                continue
            distances[neighbor] = distances[current] + 1
            queue.append(neighbor)

    unmatched_lines = tuple(
        line
        for line in normalized_lines
        if all(line not in site_source_lines(site_id, cover.sites[site_id]) for site_id in seed_sites)
    )
    warnings: List[str] = []
    if normalized_lines and not seed_sites:
        warnings.append("no sites matched changed lines; conservative full reanalysis recommended")

    stalks: List[AffectedStalk] = []
    for site_id in sorted(distances, key=_site_sort_key):
        site = cover.sites.get(site_id)
        lines = site_source_lines(site_id, site)
        matched = tuple(line for line in lines if line in normalized_lines)
        reasons: List[str] = []
        if site_id in seed_set:
            reasons.append("line_overlap")
        if include_overlaps and any(neighbor in seed_set for neighbor in overlap_map.get(site_id, ())):
            reasons.append("overlap_neighbor")
        if include_morphisms and (
            any(neighbor in seed_set for neighbor in incoming_map.get(site_id, ()))
            or any(neighbor in seed_set for neighbor in outgoing_map.get(site_id, ()))
        ):
            reasons.append("morphism_neighbor")
        if not reasons:
            reasons.append("propagated")
        stalks.append(
            AffectedStalk(
                site_id=site_id,
                distance=distances[site_id],
                source_lines=lines,
                matched_lines=matched,
                incoming=incoming_map.get(site_id, ()),
                outgoing=outgoing_map.get(site_id, ()),
                overlaps=overlap_map.get(site_id, ()),
                reasons=tuple(dict.fromkeys(reasons)),
            )
        )

    return AffectedStalkReport(
        changed_lines=normalized_lines,
        seed_sites=seed_sites,
        stalks=tuple(stalks),
        unmatched_lines=unmatched_lines,
        warnings=tuple(warnings),
    )
