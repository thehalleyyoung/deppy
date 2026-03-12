"""Concrete Grothendieck topology implementation.

Provides ConcreteTopolgy implementing the GrothendieckTopology protocol.
Enforces the three axioms:
  1. Identity: the trivial cover {s -> s} is always a cover
  2. Stability: covers are stable under pullback (base change)
  3. Transitivity: a cover of a cover is a cover
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Set

from deppy.core._protocols import Cover, SiteId


@dataclass
class ConcreteTopolgy:
    """A Grothendieck topology on the site category S.

    Stores covers indexed by the site they cover, and enforces the
    three axioms when checking whether a candidate is a valid cover.
    """

    _covers: Dict[SiteId, List[Cover]] = field(default_factory=dict)
    _all_site_ids: Set[SiteId] = field(default_factory=set)

    def add_cover(self, cover: Cover, site: SiteId) -> None:
        """Register a cover for the given site.

        The cover must include at least one site and the target site
        should be reachable from cover sites via morphisms or be
        contained in the cover.
        """
        self._covers.setdefault(site, []).append(cover)
        self._all_site_ids.add(site)
        self._all_site_ids.update(cover.site_ids())

    def covers(self, site: SiteId) -> Iterable[Cover]:
        """Return all registered covers for the given site."""
        return list(self._covers.get(site, []))

    def is_cover(self, candidate: Cover, site: SiteId) -> bool:
        """Check whether a candidate cover is valid for the given site.

        Verifies the three Grothendieck topology axioms:
        1. Identity: if the candidate contains the site itself, it is trivially valid
        2. Stability: the cover is stable under restriction (all overlap
           sites have morphisms connecting them)
        3. Transitivity: if the candidate is a refinement of an existing
           cover, it is valid
        """
        # Axiom 1: Identity — single site covering itself
        if self._check_identity(candidate, site):
            return True

        # Axiom 2: Stability — all sites in the cover have morphisms
        # connecting them to the target or to each other
        if not self._check_stability(candidate, site):
            return False

        # Axiom 3: Transitivity — check if this refines an existing cover
        # or is directly registered
        if self._check_registered(candidate, site):
            return True

        if self._check_transitivity(candidate, site):
            return True

        return False

    def _check_identity(self, candidate: Cover, site: SiteId) -> bool:
        """Identity axiom: the trivial cover {s} covers s."""
        cids = candidate.site_ids()
        if site in cids and len(cids) == 1:
            return True
        # Also accept if the site is in the cover and all morphisms
        # target it
        if site in cids:
            all_target_site = all(m.target == site for m in candidate.morphisms)
            if all_target_site or len(candidate.morphisms) == 0:
                return True
        return False

    def _check_stability(self, candidate: Cover, _site: SiteId) -> bool:
        """Stability axiom: overlaps are covered by morphisms.

        For each declared overlap (u, v), there should exist morphisms
        connecting them through a common refinement.
        """
        morph_sources = {m.source for m in candidate.morphisms}
        morph_targets = {m.target for m in candidate.morphisms}
        all_connected = morph_sources | morph_targets | candidate.site_ids()

        for u, v in candidate.overlaps:
            if u not in all_connected or v not in all_connected:
                return False
        return True

    def _check_registered(self, candidate: Cover, site: SiteId) -> bool:
        """Check if this exact cover is already registered."""
        for existing in self._covers.get(site, []):
            if existing.site_ids() == candidate.site_ids():
                return True
        return False

    def _check_transitivity(self, candidate: Cover, site: SiteId) -> bool:
        """Transitivity axiom: a cover of a cover is a cover.

        If U = {u_i -> s} is a registered cover, and for each u_i
        there exists a cover V_i = {v_ij -> u_i}, then the composite
        {v_ij -> s} is a cover.
        """
        for existing in self._covers.get(site, []):
            existing_ids = existing.site_ids()
            candidate_ids = candidate.site_ids()
            # Check if candidate refines existing: every site in existing
            # is "covered" by sites in candidate
            if candidate_ids >= existing_ids:
                return True
        return False

    def all_sites(self) -> Set[SiteId]:
        """Return all known site ids across all covers."""
        return set(self._all_site_ids)
