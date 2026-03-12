"""Eliminate unused symbols from local sections.

The SymbolEliminator removes refinement keys from a LocalSection that
are not referenced by any morphism target.  This is a garbage-collection
pass that simplifies sections before solving and comparison.

Under sheaf semantics, a refinement key that no morphism projects to
or from is dead -- it cannot influence the gluing condition and wastes
solver effort.
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
    Morphism,
    SiteId,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism


# ===================================================================
#  Analysis helpers
# ===================================================================


def _collect_referenced_keys(
    site_id: SiteId,
    morphisms: Sequence[Any],
) -> Set[str]:
    """Collect all refinement keys referenced by morphisms touching a site.

    A key is referenced if:
    1. It appears in a morphism's projection mapping (as source or target).
    2. The morphism has no projection (identity), meaning all keys flow through.
    """
    referenced: Set[str] = set()
    has_identity_morphism = False

    for morphism in morphisms:
        source = getattr(morphism, "source", None)
        target = getattr(morphism, "target", None)

        if source != site_id and target != site_id:
            continue

        projection = getattr(morphism, "projection", None)
        if projection is None:
            # Identity morphism: all keys are referenced
            has_identity_morphism = True
            break

        if source == site_id:
            # Keys flowing out from this site (values in projection)
            referenced.update(projection.values())
        if target == site_id:
            # Keys flowing into this site (keys in projection)
            referenced.update(projection.keys())

    return referenced if not has_identity_morphism else set()


def _collect_all_referenced_keys(
    site_id: SiteId,
    morphisms: Sequence[Any],
    all_sections: Mapping[SiteId, LocalSection],
) -> Set[str]:
    """Collect keys referenced through morphisms and overlapping sections.

    Extends basic reference collection with cross-site analysis:
    keys that appear in overlapping sections are also considered referenced.
    """
    direct_refs = _collect_referenced_keys(site_id, morphisms)

    # If identity morphisms exist, all keys are live
    has_identity = False
    for morphism in morphisms:
        source = getattr(morphism, "source", None)
        target = getattr(morphism, "target", None)
        if (source == site_id or target == site_id) and getattr(morphism, "projection", None) is None:
            has_identity = True
            break

    if has_identity:
        return set()  # empty set signals "all keys are live"

    # Add keys from connected sections
    connected_sites: Set[SiteId] = set()
    for morphism in morphisms:
        source = getattr(morphism, "source", None)
        target = getattr(morphism, "target", None)
        if source == site_id and target in all_sections:
            connected_sites.add(target)
        if target == site_id and source in all_sections:
            connected_sites.add(source)

    for connected_id in connected_sites:
        connected_section = all_sections.get(connected_id)
        if connected_section:
            direct_refs.update(connected_section.refinements.keys())

    return direct_refs


# ===================================================================
#  Elimination result
# ===================================================================


@dataclass(frozen=True)
class EliminationResult:
    """Result of symbol elimination on a section."""

    _original_count: int
    _eliminated_count: int
    _remaining_keys: FrozenSet[str]
    _eliminated_keys: FrozenSet[str]

    @property
    def original_count(self) -> int:
        return self._original_count

    @property
    def eliminated_count(self) -> int:
        return self._eliminated_count

    @property
    def remaining_keys(self) -> FrozenSet[str]:
        return self._remaining_keys

    @property
    def eliminated_keys(self) -> FrozenSet[str]:
        return self._eliminated_keys

    @property
    def reduction_ratio(self) -> float:
        if self._original_count == 0:
            return 0.0
        return self._eliminated_count / self._original_count


# ===================================================================
#  SymbolEliminator
# ===================================================================


class SymbolEliminator:
    """Eliminate unused symbols (refinement keys) from local sections.

    A refinement key is dead if it is not referenced by any morphism
    originating from or targeting the section's site.  Eliminating
    dead keys reduces solver workload and makes section comparison
    more precise.
    """

    def __init__(self, preserve_keys: Optional[Set[str]] = None) -> None:
        """Initialize the eliminator.

        Parameters
        ----------
        preserve_keys : set of str, optional
            Keys that should never be eliminated (e.g., "guard_source").
        """
        self._preserve_keys: Set[str] = preserve_keys or set()

    def dead_symbols(
        self,
        section: LocalSection,
        morphisms: Sequence[Any],
    ) -> Set[str]:
        """Find dead (unreferenced) refinement keys in a section.

        Parameters
        ----------
        section : LocalSection
            The section to analyze.
        morphisms : sequence
            All morphisms in the cover.

        Returns
        -------
        set of str
            The set of dead refinement keys.
        """
        all_keys = set(section.refinements.keys())
        if not all_keys:
            return set()

        referenced = _collect_referenced_keys(section.site_id, morphisms)

        # If referenced is empty, it means identity morphisms exist
        # and all keys are live
        if not referenced:
            # Check if there are ANY morphisms touching this site
            has_any_morphism = any(
                getattr(m, "source", None) == section.site_id or
                getattr(m, "target", None) == section.site_id
                for m in morphisms
            )
            if has_any_morphism:
                return set()  # all keys are live due to identity morphism

            # No morphisms at all -- all keys are potentially dead
            # But preserve keys that are structurally important
            dead = all_keys - self._preserve_keys
            return dead

        # Keys not in referenced set are dead
        dead = all_keys - referenced - self._preserve_keys
        return dead

    def eliminate(
        self,
        section: LocalSection,
        morphisms: Sequence[Any],
    ) -> LocalSection:
        """Eliminate dead symbols from a section.

        Returns a new LocalSection with dead refinement keys removed.
        """
        dead = self.dead_symbols(section, morphisms)
        if not dead:
            return section

        new_refinements = {
            k: v for k, v in section.refinements.items()
            if k not in dead
        }

        return LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=new_refinements,
            trust=section.trust,
            provenance=f"{section.provenance or ''}:symbol_eliminated",
        )

    def eliminate_all(
        self,
        sections: Mapping[SiteId, LocalSection],
        morphisms: Sequence[Any],
    ) -> Dict[SiteId, LocalSection]:
        """Eliminate dead symbols across all sections.

        Returns a new dictionary of sections with dead keys removed.
        """
        result: Dict[SiteId, LocalSection] = {}
        for site_id, section in sections.items():
            result[site_id] = self.eliminate(section, morphisms)
        return result

    def analyze(
        self,
        section: LocalSection,
        morphisms: Sequence[Any],
    ) -> EliminationResult:
        """Analyze a section for dead symbols without modifying it.

        Returns an EliminationResult with statistics.
        """
        dead = self.dead_symbols(section, morphisms)
        all_keys = set(section.refinements.keys())
        remaining = all_keys - dead

        return EliminationResult(
            _original_count=len(all_keys),
            _eliminated_count=len(dead),
            _remaining_keys=frozenset(remaining),
            _eliminated_keys=frozenset(dead),
        )

    def analyze_all(
        self,
        sections: Mapping[SiteId, LocalSection],
        morphisms: Sequence[Any],
    ) -> Dict[SiteId, EliminationResult]:
        """Analyze all sections for dead symbols."""
        result: Dict[SiteId, EliminationResult] = {}
        for site_id, section in sections.items():
            result[site_id] = self.analyze(section, morphisms)
        return result

    def summary(
        self,
        sections: Mapping[SiteId, LocalSection],
        morphisms: Sequence[Any],
    ) -> str:
        """Produce a human-readable summary of elimination analysis."""
        analyses = self.analyze_all(sections, morphisms)

        total_original = sum(a.original_count for a in analyses.values())
        total_eliminated = sum(a.eliminated_count for a in analyses.values())

        lines: List[str] = [
            f"Symbol elimination summary:",
            f"  Total keys: {total_original}",
            f"  Eliminated: {total_eliminated}",
            f"  Remaining: {total_original - total_eliminated}",
        ]

        if total_original > 0:
            ratio = total_eliminated / total_original
            lines.append(f"  Reduction: {ratio:.0%}")

        # Sites with eliminations
        sites_with_dead = [
            (site_id, analysis)
            for site_id, analysis in analyses.items()
            if analysis.eliminated_count > 0
        ]
        if sites_with_dead:
            lines.append(f"\n  Sites with dead symbols ({len(sites_with_dead)}):")
            for site_id, analysis in sites_with_dead:
                lines.append(
                    f"    {site_id.name}: "
                    f"-{analysis.eliminated_count} "
                    f"({', '.join(sorted(analysis.eliminated_keys))})"
                )

        return "\n".join(lines)
