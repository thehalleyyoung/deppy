"""Concrete Site, Morphism, SiteCategory, and CoverBuilder implementations.

Provides the foundational objects of the observation site category S:
- ConcreteSite: a dataclass implementing the Site protocol
- ConcreteMorphism: restriction/reindexing maps between sites
- SiteCategory: manages sites and morphisms, finds paths and overlaps
- CoverBuilder: fluent API for constructing Cover objects
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from deppy.core._protocols import (
    Cover,
    LocalSection,
    Morphism,
    Site,
    SiteId,
    SiteKind,
    TrustLevel,
)


@dataclass(frozen=True)
class ConcreteSite:
    """An object in the observation site category S.

    Wraps a SiteId with an optional carrier schema describing the
    shape of type information at this site, and optional metadata
    for site-family-specific payload data.
    """

    _site_id: SiteId
    _carrier_schema: Any = None
    _metadata: Optional[Dict[str, Any]] = None

    @property
    def site_id(self) -> SiteId:
        """Unique identifier for this site."""
        return self._site_id

    @property
    def kind(self) -> SiteKind:
        """The site family this site belongs to."""
        return self._site_id.kind

    @property
    def carrier_schema(self) -> Any:
        """Schema describing what type information lives at this site."""
        return self._carrier_schema

    @property
    def metadata(self) -> Optional[Dict[str, Any]]:
        """Site-family-specific payload data."""
        return self._metadata

    def __repr__(self) -> str:
        return f"ConcreteSite({self._site_id})"


@dataclass(frozen=True)
class ConcreteMorphism:
    """A morphism in S — restriction or reindexing map.

    Carries an optional projection mapping that specifies how
    refinement keys are translated from source to target,
    and optional metadata for restriction data.
    """

    _source: SiteId
    _target: SiteId
    projection: Optional[Dict[str, str]] = None
    _metadata: Optional[Dict[str, Any]] = None

    @property
    def source(self) -> SiteId:
        """The source site of this morphism."""
        return self._source

    @property
    def target(self) -> SiteId:
        """The target site of this morphism."""
        return self._target

    @property
    def metadata(self) -> Optional[Dict[str, Any]]:
        """Morphism metadata (e.g., restriction data)."""
        return self._metadata

    def restrict(self, section: LocalSection) -> LocalSection:
        """Restrict a local section along this morphism.

        Applies the projection mapping to translate refinements from
        the source site to the target site.
        """
        if section.site_id != self._source:
            raise ValueError(
                f"Section site {section.site_id} does not match "
                f"morphism source {self._source}"
            )
        new_refinements: Dict[str, Any] = {}
        if self.projection:
            for tgt_key, src_key in self.projection.items():
                if src_key in section.refinements:
                    new_refinements[tgt_key] = section.refinements[src_key]
        else:
            new_refinements = dict(section.refinements)

        return LocalSection(
            site_id=self._target,
            carrier_type=section.carrier_type,
            refinements=new_refinements,
            trust=section.trust,
            provenance=f"restricted from {self._source}",
        )

    def __repr__(self) -> str:
        return f"ConcreteMorphism({self._source} -> {self._target})"


class SiteCategory:
    """Manages sites and morphisms; supports path-finding and overlap detection.

    This is the concrete category S whose objects are observation sites
    and whose morphisms are restriction/reindexing maps.
    """

    def __init__(self) -> None:
        self._sites: Dict[SiteId, Site] = {}
        self._morphisms: List[ConcreteMorphism] = []
        self._adj: Dict[SiteId, List[ConcreteMorphism]] = {}

    def add_site(self, site: Site) -> None:
        """Register a site in the category."""
        self._sites[site.site_id] = site
        self._adj.setdefault(site.site_id, [])

    def add_morphism(self, morphism: ConcreteMorphism) -> None:
        """Register a morphism in the category."""
        self._morphisms.append(morphism)
        self._adj.setdefault(morphism.source, []).append(morphism)

    def get_site(self, site_id: SiteId) -> Optional[Site]:
        """Look up a site by its id."""
        return self._sites.get(site_id)

    @property
    def sites(self) -> Dict[SiteId, Site]:
        """All registered sites."""
        return dict(self._sites)

    @property
    def morphisms(self) -> List[ConcreteMorphism]:
        """All registered morphisms."""
        return list(self._morphisms)

    def outgoing(self, site_id: SiteId) -> List[ConcreteMorphism]:
        """Return all morphisms originating at the given site."""
        return list(self._adj.get(site_id, []))

    def find_path(
        self, start: SiteId, end: SiteId
    ) -> Optional[List[ConcreteMorphism]]:
        """BFS to find a path of morphisms from start to end.

        Returns None if no path exists.
        """
        if start == end:
            return []
        visited: Set[SiteId] = {start}
        queue: deque[Tuple[SiteId, List[ConcreteMorphism]]] = deque()
        queue.append((start, []))
        while queue:
            current, path = queue.popleft()
            for m in self._adj.get(current, []):
                if m.target == end:
                    return path + [m]
                if m.target not in visited:
                    visited.add(m.target)
                    queue.append((m.target, path + [m]))
        return None

    def find_overlaps(self, sites: FrozenSet[SiteId]) -> List[Tuple[SiteId, SiteId]]:
        """Find all pairs of sites that have a common target via morphisms.

        Two sites overlap if there exist morphisms f: A -> C and g: B -> C
        for some common target C.
        """
        target_map: Dict[SiteId, List[SiteId]] = {}
        for m in self._morphisms:
            if m.source in sites:
                target_map.setdefault(m.target, []).append(m.source)
        overlaps: List[Tuple[SiteId, SiteId]] = []
        for _target, sources in target_map.items():
            for i in range(len(sources)):
                for j in range(i + 1, len(sources)):
                    pair = (sources[i], sources[j])
                    if pair not in overlaps and (sources[j], sources[i]) not in overlaps:
                        overlaps.append(pair)
        # Also include direct morphism connections
        for m in self._morphisms:
            if m.source in sites and m.target in sites:
                pair = (m.source, m.target)
                rpair = (m.target, m.source)
                if pair not in overlaps and rpair not in overlaps:
                    overlaps.append(pair)
        return overlaps


class CoverBuilder:
    """Fluent API for constructing Cover objects.

    Usage:
        cover = (CoverBuilder()
                 .add_site(site_a)
                 .add_site(site_b)
                 .add_morphism(m_ab)
                 .add_overlap(a_id, b_id)
                 .mark_error(a_id)
                 .mark_input(a_id)
                 .mark_output(b_id)
                 .build())
    """

    def __init__(self) -> None:
        self._sites: Dict[SiteId, Site] = {}
        self._morphisms: List[Morphism] = []
        self._overlaps: List[Tuple[SiteId, SiteId]] = []
        self._error_sites: Set[SiteId] = set()
        self._input_boundary: Set[SiteId] = set()
        self._output_boundary: Set[SiteId] = set()

    def add_site(self, site: Site) -> CoverBuilder:
        """Add a site to the cover."""
        self._sites[site.site_id] = site
        return self

    def add_morphism(self, morphism: Morphism) -> CoverBuilder:
        """Add a morphism to the cover."""
        self._morphisms.append(morphism)
        return self

    def add_overlap(self, a: SiteId, b: SiteId) -> CoverBuilder:
        """Declare an overlap between two sites."""
        self._overlaps.append((a, b))
        return self

    def mark_error(self, site_id: SiteId) -> CoverBuilder:
        """Mark a site as an error site."""
        self._error_sites.add(site_id)
        return self

    def mark_input(self, site_id: SiteId) -> CoverBuilder:
        """Mark a site as part of the input boundary."""
        self._input_boundary.add(site_id)
        return self

    def mark_output(self, site_id: SiteId) -> CoverBuilder:
        """Mark a site as part of the output boundary."""
        self._output_boundary.add(site_id)
        return self

    def build(self) -> Cover:
        """Construct the Cover object."""
        return Cover(
            sites=dict(self._sites),
            morphisms=list(self._morphisms),
            overlaps=list(self._overlaps),
            error_sites=set(self._error_sites),
            input_boundary=set(self._input_boundary),
            output_boundary=set(self._output_boundary),
        )
