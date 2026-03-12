"""Handle user queries about sites, sections, and type relationships.

QueryHandler provides an interactive query interface for exploring
the sheaf-descent analysis results.  Users can ask:

- What is the type at a site?
- What sections are associated with a site?
- Why do two sites conflict?
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


# ---------------------------------------------------------------------------
# Query result types
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SiteInfo:
    """Information about a single site.

    Attributes:
        site_id: The site identifier.
        kind: The site family.
        has_section: Whether a section exists at this site.
        carrier_type: The carrier type, if available.
        refinement_count: Number of refinements.
        trust: Trust level, if a section exists.
        neighbors: Adjacent sites (via morphisms).
        is_input_boundary: Whether this is an input boundary site.
        is_output_boundary: Whether this is an output boundary site.
        is_error_site: Whether this is an error site.
    """

    _site_id: SiteId
    _kind: SiteKind
    _has_section: bool
    _carrier_type: Optional[Any] = None
    _refinement_count: int = 0
    _trust: Optional[TrustLevel] = None
    _neighbors: FrozenSet[SiteId] = field(default_factory=frozenset)
    _is_input_boundary: bool = False
    _is_output_boundary: bool = False
    _is_error_site: bool = False

    @property
    def site_id(self) -> SiteId:
        return self._site_id

    @property
    def kind(self) -> SiteKind:
        return self._kind

    @property
    def has_section(self) -> bool:
        return self._has_section

    @property
    def carrier_type(self) -> Optional[Any]:
        return self._carrier_type

    @property
    def refinement_count(self) -> int:
        return self._refinement_count

    @property
    def trust(self) -> Optional[TrustLevel]:
        return self._trust

    @property
    def neighbors(self) -> FrozenSet[SiteId]:
        return self._neighbors

    @property
    def is_input_boundary(self) -> bool:
        return self._is_input_boundary

    @property
    def is_output_boundary(self) -> bool:
        return self._is_output_boundary

    @property
    def is_error_site(self) -> bool:
        return self._is_error_site


@dataclass(frozen=True)
class SectionInfo:
    """Detailed information about a section at a site.

    Attributes:
        site_id: The site identifier.
        carrier_type: The carrier type.
        refinements: The refinement dictionary.
        trust: Trust level.
        provenance: Provenance string.
        witnesses: Witness dictionary.
        is_compatible_with_neighbors: Whether this section is compatible.
        incompatible_neighbors: Neighbors with conflicting sections.
    """

    _site_id: SiteId
    _carrier_type: Optional[Any]
    _refinements: Dict[str, Any]
    _trust: TrustLevel
    _provenance: Optional[str]
    _witnesses: Dict[str, Any]
    _is_compatible_with_neighbors: bool = True
    _incompatible_neighbors: FrozenSet[SiteId] = field(default_factory=frozenset)

    @property
    def site_id(self) -> SiteId:
        return self._site_id

    @property
    def carrier_type(self) -> Optional[Any]:
        return self._carrier_type

    @property
    def refinements(self) -> Dict[str, Any]:
        return dict(self._refinements)

    @property
    def trust(self) -> TrustLevel:
        return self._trust

    @property
    def provenance(self) -> Optional[str]:
        return self._provenance

    @property
    def witnesses(self) -> Dict[str, Any]:
        return dict(self._witnesses)

    @property
    def is_compatible_with_neighbors(self) -> bool:
        return self._is_compatible_with_neighbors

    @property
    def incompatible_neighbors(self) -> FrozenSet[SiteId]:
        return self._incompatible_neighbors


@dataclass(frozen=True)
class WhyExplanation:
    """Explanation of why two sites conflict.

    Attributes:
        site_a: First conflicting site.
        site_b: Second conflicting site.
        is_conflicting: Whether the two sites actually conflict.
        reasons: List of conflict reasons.
        shared_refinements: Refinements present in both sections.
        differing_refinements: Refinements that differ.
        path: Morphism path between the sites, if any.
        suggestions: Suggested fixes.
    """

    _site_a: SiteId
    _site_b: SiteId
    _is_conflicting: bool
    _reasons: Tuple[str, ...]
    _shared_refinements: Dict[str, Any]
    _differing_refinements: Dict[str, Tuple[Any, Any]]
    _path: Tuple[SiteId, ...] = ()
    _suggestions: Tuple[str, ...] = ()

    @property
    def site_a(self) -> SiteId:
        return self._site_a

    @property
    def site_b(self) -> SiteId:
        return self._site_b

    @property
    def is_conflicting(self) -> bool:
        return self._is_conflicting

    @property
    def reasons(self) -> Tuple[str, ...]:
        return self._reasons

    @property
    def shared_refinements(self) -> Dict[str, Any]:
        return dict(self._shared_refinements)

    @property
    def differing_refinements(self) -> Dict[str, Tuple[Any, Any]]:
        return dict(self._differing_refinements)

    @property
    def path(self) -> Tuple[SiteId, ...]:
        return self._path

    @property
    def suggestions(self) -> Tuple[str, ...]:
        return self._suggestions


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _build_adjacency(cover: Cover) -> Dict[SiteId, Set[SiteId]]:
    """Build undirected adjacency from morphisms and overlaps."""
    adj: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for m in cover.morphisms:
        adj[m.source].add(m.target)
        adj[m.target].add(m.source)
    for a, b in cover.overlaps:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def _find_path(
    start: SiteId,
    end: SiteId,
    adj: Dict[SiteId, Set[SiteId]],
) -> List[SiteId]:
    """BFS to find a path between two sites."""
    if start == end:
        return [start]
    visited: Set[SiteId] = {start}
    queue: deque[Tuple[SiteId, List[SiteId]]] = deque([(start, [start])])
    while queue:
        current, path = queue.popleft()
        for nb in adj.get(current, set()):
            if nb == end:
                return path + [nb]
            if nb not in visited:
                visited.add(nb)
                queue.append((nb, path + [nb]))
    return []


def _sections_compatible(a: LocalSection, b: LocalSection) -> bool:
    """Check if two sections are compatible on common refinements."""
    common = set(a.refinements.keys()) & set(b.refinements.keys())
    for k in common:
        if a.refinements[k] != b.refinements[k]:
            return False
    return True


def _extract_variable(site_id: SiteId) -> str:
    """Extract variable name from site ID."""
    name = site_id.name
    for sep in (".", ":", "/"):
        parts = name.rsplit(sep, 1)
        if len(parts) == 2:
            return parts[1]
    return name


def _describe_kind(kind: SiteKind) -> str:
    """Human-readable kind description."""
    descriptions = {
        SiteKind.ARGUMENT_BOUNDARY: "function parameter",
        SiteKind.RETURN_OUTPUT_BOUNDARY: "return value",
        SiteKind.SSA_VALUE: "local variable",
        SiteKind.BRANCH_GUARD: "branch condition",
        SiteKind.CALL_RESULT: "function call result",
        SiteKind.TENSOR_SHAPE: "tensor shape",
        SiteKind.TENSOR_ORDER: "tensor order",
        SiteKind.TENSOR_INDEXING: "tensor indexing",
        SiteKind.HEAP_PROTOCOL: "heap protocol",
        SiteKind.PROOF: "proof obligation",
        SiteKind.TRACE: "runtime trace",
        SiteKind.ERROR: "error handler",
        SiteKind.LOOP_HEADER_INVARIANT: "loop invariant",
        SiteKind.MODULE_SUMMARY: "module summary",
    }
    return descriptions.get(kind, kind.value)


# ---------------------------------------------------------------------------
# QueryHandler
# ---------------------------------------------------------------------------

class QueryHandler:
    """Handle user queries about sites, sections, and relationships.

    Provides a structured query interface for exploring analysis results.

    Usage::

        handler = QueryHandler(cover, sections)
        info = handler.query_site(site_id)
        sec_info = handler.query_section(site_id)
        why = handler.query_why(site_a, site_b)
    """

    def __init__(
        self,
        cover: Optional[Cover] = None,
        sections: Optional[Dict[SiteId, LocalSection]] = None,
        obstructions: Optional[List[ObstructionData]] = None,
    ) -> None:
        self._cover = cover or Cover()
        self._sections = sections or {}
        self._obstructions = obstructions or []
        self._adj = _build_adjacency(self._cover)

    def query_site(
        self,
        site_id: SiteId,
        cover: Optional[Cover] = None,
    ) -> SiteInfo:
        """Query information about a specific site."""
        cov = cover or self._cover
        sec = self._sections.get(site_id)

        neighbors = frozenset(self._adj.get(site_id, set()))

        return SiteInfo(
            _site_id=site_id,
            _kind=site_id.kind,
            _has_section=sec is not None,
            _carrier_type=sec.carrier_type if sec else None,
            _refinement_count=len(sec.refinements) if sec else 0,
            _trust=sec.trust if sec else None,
            _neighbors=neighbors,
            _is_input_boundary=site_id in cov.input_boundary,
            _is_output_boundary=site_id in cov.output_boundary,
            _is_error_site=site_id in cov.error_sites,
        )

    def query_section(
        self,
        site_id: SiteId,
        sections: Optional[Dict[SiteId, LocalSection]] = None,
    ) -> SectionInfo:
        """Query detailed section information at a site."""
        secs = sections or self._sections
        sec = secs.get(site_id)

        if sec is None:
            return SectionInfo(
                _site_id=site_id,
                _carrier_type=None,
                _refinements={},
                _trust=TrustLevel.RESIDUAL,
                _provenance=None,
                _witnesses={},
                _is_compatible_with_neighbors=True,
                _incompatible_neighbors=frozenset(),
            )

        incompatible: Set[SiteId] = set()
        neighbors = self._adj.get(site_id, set())
        for nb_id in neighbors:
            nb_sec = secs.get(nb_id)
            if nb_sec is not None and not _sections_compatible(sec, nb_sec):
                incompatible.add(nb_id)

        return SectionInfo(
            _site_id=site_id,
            _carrier_type=sec.carrier_type,
            _refinements=dict(sec.refinements),
            _trust=sec.trust,
            _provenance=sec.provenance,
            _witnesses=dict(sec.witnesses),
            _is_compatible_with_neighbors=len(incompatible) == 0,
            _incompatible_neighbors=frozenset(incompatible),
        )

    def query_why(
        self,
        site_a: SiteId,
        site_b: SiteId,
        sections: Optional[Dict[SiteId, LocalSection]] = None,
    ) -> WhyExplanation:
        """Explain why two sites conflict (or don't)."""
        secs = sections or self._sections
        sec_a = secs.get(site_a)
        sec_b = secs.get(site_b)

        if sec_a is None or sec_b is None:
            missing = site_a if sec_a is None else site_b
            return WhyExplanation(
                _site_a=site_a,
                _site_b=site_b,
                _is_conflicting=False,
                _reasons=(f"No section at {missing}",),
                _shared_refinements={},
                _differing_refinements={},
            )

        reasons: List[str] = []
        shared: Dict[str, Any] = {}
        differing: Dict[str, Tuple[Any, Any]] = {}

        type_a = repr(sec_a.carrier_type) if sec_a.carrier_type else "None"
        type_b = repr(sec_b.carrier_type) if sec_b.carrier_type else "None"
        if type_a != type_b:
            reasons.append(
                f"Carrier types differ: {type_a} vs {type_b}"
            )

        common_keys = set(sec_a.refinements.keys()) & set(sec_b.refinements.keys())
        for k in sorted(common_keys):
            va = sec_a.refinements[k]
            vb = sec_b.refinements[k]
            if va == vb:
                shared[k] = va
            else:
                differing[k] = (va, vb)
                reasons.append(
                    f"Refinement '{k}' differs: {va!r} vs {vb!r}"
                )

        only_a = set(sec_a.refinements.keys()) - common_keys
        only_b = set(sec_b.refinements.keys()) - common_keys
        if only_a:
            reasons.append(
                f"Refinements only at {site_a.name}: "
                f"{', '.join(sorted(only_a))}"
            )
        if only_b:
            reasons.append(
                f"Refinements only at {site_b.name}: "
                f"{', '.join(sorted(only_b))}"
            )

        is_conflicting = bool(differing) or (type_a != type_b and type_a != "None" and type_b != "None")

        path = _find_path(site_a, site_b, self._adj)

        suggestions = self._generate_conflict_suggestions(
            site_a, site_b, sec_a, sec_b, reasons
        )

        return WhyExplanation(
            _site_a=site_a,
            _site_b=site_b,
            _is_conflicting=is_conflicting,
            _reasons=tuple(reasons) if reasons else ("No conflicts detected.",),
            _shared_refinements=shared,
            _differing_refinements=differing,
            _path=tuple(path),
            _suggestions=tuple(suggestions),
        )

    def query_neighbors(
        self,
        site_id: SiteId,
    ) -> List[SiteInfo]:
        """Query information about a site's neighbors."""
        neighbors = self._adj.get(site_id, set())
        return [self.query_site(nb) for nb in sorted(neighbors, key=str)]

    def query_path(
        self,
        site_a: SiteId,
        site_b: SiteId,
    ) -> List[SiteId]:
        """Find the morphism path between two sites."""
        return _find_path(site_a, site_b, self._adj)

    def query_obstructions_at(
        self,
        site_id: SiteId,
    ) -> List[ObstructionData]:
        """Find all obstructions involving a specific site."""
        result: List[ObstructionData] = []
        for obs in self._obstructions:
            for a_id, b_id in obs.conflicting_overlaps:
                if a_id == site_id or b_id == site_id:
                    result.append(obs)
                    break
        return result

    def query_trust_distribution(self) -> Dict[TrustLevel, int]:
        """Get the distribution of trust levels across all sections."""
        dist: Dict[TrustLevel, int] = defaultdict(int)
        for sec in self._sections.values():
            dist[sec.trust] += 1
        return dict(dist)

    def query_site_kind_distribution(self) -> Dict[SiteKind, int]:
        """Get the distribution of site kinds across all sites."""
        dist: Dict[SiteKind, int] = defaultdict(int)
        for sid in self._cover.sites:
            dist[sid.kind] += 1
        return dict(dist)

    def search_sites(
        self,
        *,
        kind: Optional[SiteKind] = None,
        name_contains: Optional[str] = None,
        has_refinement: Optional[str] = None,
        trust: Optional[TrustLevel] = None,
    ) -> List[SiteId]:
        """Search for sites matching the given criteria."""
        results: List[SiteId] = []

        for sid in sorted(self._cover.sites.keys(), key=str):
            if kind is not None and sid.kind != kind:
                continue
            if name_contains is not None and name_contains not in sid.name:
                continue

            sec = self._sections.get(sid)
            if has_refinement is not None:
                if sec is None or has_refinement not in sec.refinements:
                    continue
            if trust is not None:
                if sec is None or sec.trust != trust:
                    continue

            results.append(sid)

        return results

    def _generate_conflict_suggestions(
        self,
        site_a: SiteId,
        site_b: SiteId,
        sec_a: LocalSection,
        sec_b: LocalSection,
        reasons: List[str],
    ) -> List[str]:
        """Generate suggestions for resolving a conflict."""
        suggestions: List[str] = []

        if any("carrier types differ" in r.lower() for r in reasons):
            suggestions.append(
                "Consider adding a type guard (isinstance check) "
                "to narrow the type before the overlap point."
            )
            suggestions.append(
                "Alternatively, widen the type annotation to a Union "
                "that accommodates both types."
            )

        if any("refinement" in r.lower() and "differs" in r.lower() for r in reasons):
            suggestions.append(
                "Ensure the refinement constraints are consistent "
                "across both sites. You may need to strengthen the "
                "weaker constraint or relax the stronger one."
            )

        if sec_a.trust == TrustLevel.RESIDUAL or sec_b.trust == TrustLevel.RESIDUAL:
            suggestions.append(
                "One or both sections have RESIDUAL trust. "
                "Add runtime checks or proofs to establish stronger trust."
            )

        if not suggestions:
            suggestions.append(
                "Review the type assignments at both sites and ensure "
                "they are consistent on their shared overlap."
            )

        return suggestions

    def format_site_info(self, info: SiteInfo) -> str:
        """Format a SiteInfo as a human-readable string."""
        lines: List[str] = []
        lines.append(f"Site: {info.site_id}")
        lines.append(f"  Kind: {_describe_kind(info.kind)}")
        lines.append(f"  Has section: {info.has_section}")
        if info.carrier_type is not None:
            lines.append(f"  Type: {repr(info.carrier_type)}")
        if info.trust is not None:
            lines.append(f"  Trust: {info.trust.value}")
        lines.append(f"  Refinements: {info.refinement_count}")
        lines.append(f"  Neighbors: {len(info.neighbors)}")

        flags: List[str] = []
        if info.is_input_boundary:
            flags.append("input")
        if info.is_output_boundary:
            flags.append("output")
        if info.is_error_site:
            flags.append("error")
        if flags:
            lines.append(f"  Boundary: {', '.join(flags)}")

        return "\n".join(lines)

    def format_why(self, why: WhyExplanation) -> str:
        """Format a WhyExplanation as a human-readable string."""
        lines: List[str] = []
        status = "CONFLICT" if why.is_conflicting else "COMPATIBLE"
        lines.append(
            f"Why '{why.site_a.name}' vs '{why.site_b.name}': {status}"
        )

        for reason in why.reasons:
            lines.append(f"  - {reason}")

        if why.shared_refinements:
            lines.append(f"  Shared: {list(why.shared_refinements.keys())}")

        if why.path:
            path_str = " -> ".join(s.name for s in why.path)
            lines.append(f"  Path: {path_str}")

        if why.suggestions:
            lines.append("  Suggestions:")
            for i, s in enumerate(why.suggestions, 1):
                lines.append(f"    {i}. {s}")

        return "\n".join(lines)
