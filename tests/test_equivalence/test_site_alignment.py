"""Tests for deppy.equivalence.site_alignment — sieve pullback and common refinement."""

from __future__ import annotations

import pytest
from deppy.core._protocols import SiteId, SiteKind, Cover
from deppy.core.site import ConcreteMorphism, ConcreteSite, SiteCategory
from deppy.equivalence._protocols import SiteCorrespondence
from deppy.equivalence.site_alignment import (
    CommonRefinement,
    CommonRefinementBuilder,
    Sieve,
    SieveComputer,
    SiteMatcher,
)


def _site(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


class TestSiteMatcher:
    def test_exact_match(self):
        matcher = SiteMatcher()
        sites_f = [_site("foo")]
        sites_g = [_site("foo")]
        result = matcher.match(sites_f, sites_g)
        assert len(result) == 1
        assert result[0].f_site == _site("foo")
        assert result[0].g_site == _site("foo")

    def test_kind_based_match(self):
        matcher = SiteMatcher()
        s_f = SiteId(kind=SiteKind.ARGUMENT_BOUNDARY, name="x")
        s_g = SiteId(kind=SiteKind.ARGUMENT_BOUNDARY, name="y")
        result = matcher.match([s_f], [s_g])
        assert len(result) == 1
        corr = result[0]
        assert corr.f_site == s_f
        assert corr.g_site == s_g

    def test_unmatched_orphans(self):
        matcher = SiteMatcher()
        s_f = SiteId(kind=SiteKind.ARGUMENT_BOUNDARY, name="x")
        s_g = SiteId(kind=SiteKind.RETURN_OUTPUT_BOUNDARY, name="y")
        result = matcher.match([s_f], [s_g])
        # Different kinds => orphans
        assert len(result) == 2

    def test_empty_input(self):
        matcher = SiteMatcher()
        result = matcher.match([], [])
        assert result == []


class TestSieve:
    def test_creation(self):
        s = Sieve(target=_site("a"), morphisms=frozenset())
        assert s.target == _site("a")
        assert len(s.morphisms) == 0

    def test_intersect_empty(self):
        s1 = Sieve(target=_site("a"), morphisms=frozenset())
        s2 = Sieve(target=_site("a"), morphisms=frozenset())
        result = s1.intersect(s2)
        assert len(result.morphisms) == 0

    def test_is_maximal_empty(self):
        s = Sieve(target=_site("a"), morphisms=frozenset())
        assert not s.is_maximal


class TestSieveComputer:
    def test_sieve_of(self):
        cat = SiteCategory()
        site_a = _site("a")
        cat.add_site(ConcreteSite(site_a))

        comp = SieveComputer(cat)
        sieve = comp.sieve_of(site_a)
        assert isinstance(sieve, Sieve)
        assert sieve.target == site_a


class TestCommonRefinementBuilder:
    def test_build_trivial(self):
        cat = SiteCategory()
        site_a = _site("a")
        cat.add_site(ConcreteSite(site_a))

        # Create a Cover with the site in the dict
        cover = Cover(sites={site_a: ConcreteSite(site_a)})

        builder = CommonRefinementBuilder(cat)
        result = builder.build(cover, cover)
        assert isinstance(result, CommonRefinement)
        assert len(result.correspondences) > 0
