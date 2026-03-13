"""Common refinement of covers via categorical pullback of sieves.

Given two covers C_f = {U^f_i} and C_g = {U^g_j} over a shared
site category, the common refinement is the pullback cover:

    C = C_f times_S C_g

consisting of sites U^f_i cap U^g_j for all pairs (i,j) where
the intersection is non-trivial.

The construction proceeds in three stages:

Stage 1 -- Site Correspondence:
    Match sites from C_f to C_g using SiteKind compatibility as
    the primary criterion (matching ARGUMENT_BOUNDARY to
    ARGUMENT_BOUNDARY, etc.), with name similarity as a tiebreaker.

Stage 2 -- Sieve Computation:
    For each corresponded pair (U_f, U_g), compute the sieve
    S(U_f) cap S(U_g) in the site category.  A sieve is a
    downward-closed collection of morphisms targeting U.

Stage 3 -- Common Refinement Assembly:
    Assemble the pullback cover, adding:
    - New sites for each correspondence (common sites)
    - Morphisms from common sites to both originals
    - Overlap sites for cross-correspondences

The result is a Cover together with a list of SiteCorrespondences
mapping common sites to their origins in C_f and C_g.

The Grothendieck topology stability axiom ensures that the pullback
of a covering sieve along any morphism is again covering.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
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
from deppy.core.presheaf import ConcretePresheaf
from deppy.core.site import ConcreteMorphism, ConcreteSite, CoverBuilder, SiteCategory

from deppy.equivalence._protocols import (
    EquivalenceSiteKind,
    SiteCorrespondence,
)


# ===========================================================================
# Site matching
# ===========================================================================


class SiteMatcher:
    """Match sites from two covers using SiteKind as primary criterion.

    The matching algorithm:
    1. Group sites by SiteKind in both covers
    2. Within each SiteKind group, match by name similarity
    3. Produce SiteCorrespondence for each matched pair
    4. Unmatched sites become ORPHAN correspondences
    """

    def match(
        self,
        sites_f: List[SiteId],
        sites_g: List[SiteId],
    ) -> List[SiteCorrespondence]:
        """Match sites from f and g covers."""
        # Group by SiteKind
        f_groups: Dict[SiteKind, List[SiteId]] = {}
        g_groups: Dict[SiteKind, List[SiteId]] = {}

        for s in sites_f:
            f_groups.setdefault(s.kind, []).append(s)
        for s in sites_g:
            g_groups.setdefault(s.kind, []).append(s)

        correspondences: List[SiteCorrespondence] = []
        used_g: Set[SiteId] = set()

        for kind, f_sites in f_groups.items():
            g_sites = g_groups.get(kind, [])
            available = [s for s in g_sites if s not in used_g]

            for f_site in f_sites:
                best_match = self._best_name_match(f_site, available)
                if best_match is not None:
                    common = SiteId(
                        kind=kind,
                        name=f"common_{f_site.name}_{best_match.name}",
                        source_location=f_site.source_location,
                    )
                    correspondences.append(SiteCorrespondence(
                        f_site=f_site,
                        g_site=best_match,
                        common_site=common,
                    ))
                    used_g.add(best_match)
                    available.remove(best_match)
                else:
                    # Orphan from f
                    common = SiteId(
                        kind=kind,
                        name=f"orphan_f_{f_site.name}",
                        source_location=f_site.source_location,
                    )
                    correspondences.append(SiteCorrespondence(
                        f_site=f_site,
                        g_site=f_site,  # self-pair (no match)
                        common_site=common,
                    ))

        # Orphans from g
        for kind, g_sites in g_groups.items():
            for g_site in g_sites:
                if g_site not in used_g:
                    common = SiteId(
                        kind=kind,
                        name=f"orphan_g_{g_site.name}",
                        source_location=g_site.source_location,
                    )
                    correspondences.append(SiteCorrespondence(
                        f_site=g_site,  # self-pair (no match)
                        g_site=g_site,
                        common_site=common,
                    ))

        return correspondences

    def _best_name_match(
        self,
        site: SiteId,
        candidates: List[SiteId],
    ) -> Optional[SiteId]:
        """Find the best name match among candidates.

        Uses bigram Jaccard similarity.
        """
        if not candidates:
            return None

        scores = [
            (c, _bigram_jaccard(site.name, c.name))
            for c in candidates
        ]
        scores.sort(key=lambda x: x[1], reverse=True)
        best, score = scores[0]

        # Require minimum similarity for non-trivial matching
        if score >= 0.3:
            return best
        # If only one candidate, accept it regardless
        if len(candidates) == 1:
            return best
        return None


# ===========================================================================
# Sieve computation
# ===========================================================================


@dataclass(frozen=True)
class Sieve:
    """A sieve S on site U: a downward-closed set of morphisms targeting U.

    S = { f : V -> U | for all g : W -> V, f . g in S }

    In the Grothendieck topology, a covering sieve is one that
    belongs to the topology J(U).
    """
    target: SiteId
    morphisms: FrozenSet[Morphism]

    def intersect(self, other: "Sieve") -> "Sieve":
        """Intersect two sieves on the same target.

        The intersection S_1 cap S_2 is a sieve containing morphisms
        that appear in both.
        """
        common = self.morphisms & other.morphisms
        return Sieve(target=self.target, morphisms=common)

    def pullback(self, morph: Morphism) -> "Sieve":
        """Pullback sieve along a morphism h : W -> U.

        h^*(S) = { f : V -> W | h . f in S }

        The stability axiom requires that if S is covering, so is h^*(S).
        """
        pulled: Set[Morphism] = set()
        for m in self.morphisms:
            if hasattr(m, 'source') and hasattr(morph, 'source'):
                if m.source == morph.source:
                    pulled.add(m)
        return Sieve(
            target=morph.source if hasattr(morph, 'source') else self.target,
            morphisms=frozenset(pulled),
        )

    @property
    def is_maximal(self) -> bool:
        """Is this the maximal sieve (all morphisms targeting U)?"""
        return len(self.morphisms) > 0


class SieveComputer:
    """Compute sieves from a site category."""

    def __init__(self, site_category: SiteCategory) -> None:
        self._cat = site_category

    def sieve_of(self, site_id: SiteId) -> Sieve:
        """Compute the sieve generated by all morphisms targeting site_id."""
        morphisms: Set[Morphism] = set()
        for morph in [m for m in self._cat.morphisms if m.target == site_id]:
            morphisms.add(morph)
        return Sieve(target=site_id, morphisms=frozenset(morphisms))

    def covering_sieve(
        self,
        cover: Cover,
        site_id: SiteId,
    ) -> Sieve:
        """Compute the covering sieve of a cover at a site.

        The covering sieve S_U = { f : V -> U | V in cover, f restricts U to V }
        """
        cover_sites = set(cover.site_ids())
        morphisms: Set[Morphism] = set()

        for morph in [m for m in self._cat.morphisms if m.target == site_id]:
            if hasattr(morph, 'source') and morph.source in cover_sites:
                morphisms.add(morph)

        return Sieve(target=site_id, morphisms=frozenset(morphisms))


# ===========================================================================
# Common refinement builder
# ===========================================================================


class CommonRefinementBuilder:
    """Build the common refinement cover from two program covers.

    The common refinement C = C_f times_S C_g is constructed by:
    1. Matching sites from C_f and C_g (Stage 1)
    2. Computing sieve intersections (Stage 2)
    3. Assembling the pullback cover (Stage 3)

    The result includes:
    - A Cover object for the common refinement
    - A list of SiteCorrespondences mapping common to original sites
    - Morphisms from common sites to originals
    """

    def __init__(
        self,
        site_category: SiteCategory,
        matcher: Optional[SiteMatcher] = None,
    ) -> None:
        self._cat = site_category
        self._matcher = matcher or SiteMatcher()

    def build(
        self,
        cover_f: Cover,
        cover_g: Cover,
    ) -> CommonRefinement:
        """Build the common refinement."""
        # Stage 1: Match sites
        f_sites = list(cover_f.site_ids())
        g_sites = list(cover_g.site_ids())
        correspondences = self._matcher.match(f_sites, g_sites)

        # Stage 2: Compute sieve intersections
        sieve_computer = SieveComputer(self._cat)
        sieve_data: Dict[SiteId, Sieve] = {}

        for corr in correspondences:
            s_f = sieve_computer.sieve_of(corr.f_site)
            s_g = sieve_computer.sieve_of(corr.g_site)
            sieve_data[corr.common_site] = s_f.intersect(s_g)

        # Stage 3: Assemble the pullback cover
        builder = CoverBuilder()

        for corr in correspondences:
            # Add the common site
            builder.add_site(ConcreteSite(corr.common_site))

        # Add morphisms from common sites to originals
        morphisms: List[ConcreteMorphism] = []
        for corr in correspondences:
            # Morphism: common -> f_site
            m_to_f = ConcreteMorphism(
                corr.common_site,
                corr.f_site,
                projection={},
            )
            morphisms.append(m_to_f)

            # Morphism: common -> g_site
            m_to_g = ConcreteMorphism(
                corr.common_site,
                corr.g_site,
                projection={},
            )
            morphisms.append(m_to_g)

        # Compute overlaps between common sites
        overlaps: Dict[Tuple[SiteId, SiteId], SiteId] = {}
        common_sites = [c.common_site for c in correspondences]
        for i, s_i in enumerate(common_sites):
            for s_j in common_sites[i+1:]:
                # Check if corresponding original sites overlap
                c_i = correspondences[i]
                c_j_idx = common_sites.index(s_j)
                c_j = correspondences[c_j_idx]

                orig_overlaps = self._cat.find_overlaps(c_i.f_site, c_j.f_site)
                if orig_overlaps:
                    overlaps[(s_i, s_j)] = orig_overlaps[0][0]

        cover = builder.build()

        return CommonRefinement(
            cover=cover,
            correspondences=correspondences,
            morphisms=morphisms,
            overlaps=overlaps,
            sieves=sieve_data,
        )


# ===========================================================================
# Common refinement result
# ===========================================================================


@dataclass
class CommonRefinement:
    """Result of the common refinement construction."""
    cover: Cover
    correspondences: List[SiteCorrespondence]
    morphisms: List[ConcreteMorphism]
    overlaps: Dict[Tuple[SiteId, SiteId], SiteId]
    sieves: Dict[SiteId, Sieve]

    @property
    def site_count(self) -> int:
        return len(self.correspondences)

    def correspondence_for(self, common_site: SiteId) -> Optional[SiteCorrespondence]:
        """Look up the correspondence for a common site."""
        for c in self.correspondences:
            if c.common_site == common_site:
                return c
        return None

    def all_common_sites(self) -> List[SiteId]:
        return [c.common_site for c in self.correspondences]


# ===========================================================================
# Utility: bigram Jaccard similarity
# ===========================================================================


def _bigram_jaccard(a: str, b: str) -> float:
    """Compute bigram Jaccard similarity between two strings."""
    if not a or not b:
        return 0.0
    if a == b:
        return 1.0

    bg_a = {a[i:i+2] for i in range(len(a) - 1)} if len(a) > 1 else {a}
    bg_b = {b[i:i+2] for i in range(len(b) - 1)} if len(b) > 1 else {b}

    intersection = len(bg_a & bg_b)
    union = len(bg_a | bg_b)
    return intersection / union if union > 0 else 0.0
