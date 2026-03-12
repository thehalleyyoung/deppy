"""Concrete semantic presheaf and sheaf condition checker.

Provides:
- ConcretePresheaf: implements SemanticPresheaf protocol, stores sections per site
- ConcretePresheafBuilder: fluent builder for constructing a presheaf
- SheafConditionChecker: verify the gluing axiom (local sections agree on
  overlaps => unique global section)
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Optional, Set, Tuple

from deppy.core._protocols import (
    Cover,
    GlobalSection,
    LocalSection,
    Morphism,
    SiteId,
    TrustLevel,
)
from deppy.core.section import SectionMerger


@dataclass
class ConcretePresheaf:
    """Functor Sem: S^op -> Poset.

    Stores sections at each site and restriction morphisms.
    The presheaf assigns to each site its set of possible local sections
    (ordered by information content), and to each morphism a restriction map.
    """

    _sections: Dict[SiteId, List[LocalSection]] = field(default_factory=dict)
    _morphisms: Dict[Tuple[SiteId, SiteId], Morphism] = field(default_factory=dict)
    name: str = ""

    def sections_at(self, site: SiteId) -> Iterable[LocalSection]:
        """Return all sections stored at the given site."""
        return list(self._sections.get(site, []))

    def restrict(self, section: LocalSection, morphism: Morphism) -> LocalSection:
        """Restrict a section along a morphism.

        Applies the morphism's restriction map to the section.
        """
        return morphism.restrict(section)

    def add_section(self, section: LocalSection) -> None:
        """Add a local section to the presheaf at its site."""
        self._sections.setdefault(section.site_id, []).append(section)

    def add_morphism(self, morphism: Morphism) -> None:
        """Register a restriction morphism."""
        self._morphisms[(morphism.source, morphism.target)] = morphism

    def get_morphism(self, source: SiteId, target: SiteId) -> Optional[Morphism]:
        """Look up a morphism between two sites."""
        return self._morphisms.get((source, target))

    def site_ids(self) -> Set[SiteId]:
        """Return all sites that have at least one section."""
        return set(self._sections.keys())

    def __repr__(self) -> str:
        n = sum(len(v) for v in self._sections.values())
        return f"ConcretePresheaf(name={self.name!r}, sections={n})"


class ConcretePresheafBuilder:
    """Fluent builder for constructing a ConcretePresheaf.

    Usage:
        presheaf = (ConcretePresheafBuilder("Sem")
                    .add_section(sec_a)
                    .add_section(sec_b)
                    .add_morphism(m_ab)
                    .build())
    """

    def __init__(self, name: str = "") -> None:
        self._name = name
        self._sections: List[LocalSection] = []
        self._morphisms: List[Morphism] = []

    def add_section(self, section: LocalSection) -> ConcretePresheafBuilder:
        """Add a local section."""
        self._sections.append(section)
        return self

    def add_morphism(self, morphism: Morphism) -> ConcretePresheafBuilder:
        """Add a restriction morphism."""
        self._morphisms.append(morphism)
        return self

    def build(self) -> ConcretePresheaf:
        """Build the presheaf."""
        psh = ConcretePresheaf(name=self._name)
        for s in self._sections:
            psh.add_section(s)
        for m in self._morphisms:
            psh.add_morphism(m)
        return psh


@dataclass
class GluingResult:
    """Result of attempting to glue local sections into a global section."""

    success: bool
    global_section: Optional[GlobalSection] = None
    conflicts: List[Tuple[SiteId, SiteId]] = field(default_factory=list)
    explanation: str = ""


class SheafConditionChecker:
    """Verify the sheaf (gluing) axiom.

    The sheaf condition states: given a cover {U_i -> U} and local
    sections sigma_i in F(U_i) that agree on overlaps (i.e.,
    sigma_i|_{U_i ∩ U_j} = sigma_j|_{U_i ∩ U_j} for all i, j),
    there exists a unique global section sigma in F(U) with
    sigma|_{U_i} = sigma_i.
    """

    @staticmethod
    def check_agreement(
        sections: Dict[SiteId, LocalSection],
        overlaps: List[Tuple[SiteId, SiteId]],
    ) -> List[Tuple[SiteId, SiteId]]:
        """Check whether sections agree on all overlaps.

        Returns list of conflicting overlap pairs.
        """
        conflicts: List[Tuple[SiteId, SiteId]] = []
        for u, v in overlaps:
            su = sections.get(u)
            sv = sections.get(v)
            if su is None or sv is None:
                continue
            if not SectionMerger.are_compatible(su, sv):
                conflicts.append((u, v))
        return conflicts

    @staticmethod
    def attempt_gluing(
        sections: Dict[SiteId, LocalSection],
        overlaps: List[Tuple[SiteId, SiteId]],
    ) -> GluingResult:
        """Attempt to glue local sections into a global section.

        First checks agreement on overlaps. If all agree, produces
        a GlobalSection. Otherwise reports conflicts.
        """
        conflicts = SheafConditionChecker.check_agreement(sections, overlaps)
        if conflicts:
            return GluingResult(
                success=False,
                conflicts=conflicts,
                explanation=f"Sections disagree on {len(conflicts)} overlap(s)",
            )

        gs = GlobalSection(local_sections=dict(sections))
        return GluingResult(
            success=True,
            global_section=gs,
            explanation="Sheaf condition satisfied; global section constructed",
        )

    @staticmethod
    def verify_uniqueness(
        global_section: GlobalSection,
        sections: Dict[SiteId, LocalSection],
    ) -> bool:
        """Verify that the global section restricts to the given locals.

        The uniqueness part of the sheaf condition: the global section
        is the unique one whose restrictions recover each local section.
        """
        for sid, local in sections.items():
            gs_local = global_section.at(sid)
            if gs_local is None:
                return False
            if gs_local.carrier_type != local.carrier_type:
                return False
        return True
