"""Tests for deppy.equivalence.stalk — stalk computation and germ equivalence."""

from __future__ import annotations

import pytest
from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.core.presheaf import ConcretePresheafBuilder
from deppy.core.site import ConcreteSite, SiteCategory
from deppy.types.refinement import TruePred, VarPred
from deppy.equivalence._protocols import EquivalenceVerdict
from deppy.equivalence.stalk import (
    Germ,
    GermMorphism,
    PointStalkResult,
    Stalk,
    StalkEquivalenceChecker,
    StalkEquivalenceResult,
    StalkFunctor,
)


def _site(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _section(name: str) -> LocalSection:
    return LocalSection(
        site_id=_site(name),
        carrier_type=None,
        refinements={},
        trust=TrustLevel.RESIDUAL,
        provenance="test",
    )


class TestGerm:
    def test_creation(self):
        g = Germ(
            point=_site("p"),
            section=_section("a"),
            neighbourhood=_site("a"),
            predicate=TruePred(),
        )
        assert g.point == _site("p")
        assert isinstance(g.predicate, TruePred)

    def test_germ_equality_checks(self):
        g1 = Germ(
            point=_site("p"), section=_section("a"),
            neighbourhood=_site("a"), predicate=VarPred("x"),
        )
        g2 = Germ(
            point=_site("p"), section=_section("a"),
            neighbourhood=_site("a"), predicate=VarPred("x"),
        )
        # Both have same structure
        assert g1.point == g2.point


class TestStalk:
    def test_creation(self):
        g = Germ(
            point=_site("p"), section=_section("a"),
            neighbourhood=_site("a"), predicate=TruePred(),
        )
        stalk = Stalk(point=_site("p"), germs=[g])
        assert stalk.point == _site("p")
        assert len(stalk.germs) == 1

    def test_empty_stalk(self):
        stalk = Stalk(point=_site("p"))
        assert stalk.is_empty


class TestStalkFunctor:
    def test_compute_stalk(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        presheaf = builder.build()

        cat = SiteCategory()
        cat.add_site(ConcreteSite(site_a))

        functor = StalkFunctor(cat)
        stalk = functor.stalk_at(presheaf, site_a)
        assert isinstance(stalk, Stalk)
        assert stalk.point == site_a


class TestGermMorphism:
    def test_creation(self):
        stalk_f = Stalk(point=_site("p"))
        stalk_g = Stalk(point=_site("p"))
        gm = GermMorphism(source=stalk_f, target=stalk_g)
        assert gm.source is stalk_f
        assert gm.target is stalk_g

    def test_empty_is_iso(self):
        stalk_f = Stalk(point=_site("p"))
        stalk_g = Stalk(point=_site("p"))
        gm = GermMorphism(source=stalk_f, target=stalk_g)
        assert gm.is_isomorphism


class TestStalkEquivalenceChecker:
    def test_empty_presheaves(self):
        cat = SiteCategory()
        presheaf_f = ConcretePresheafBuilder().build()
        presheaf_g = ConcretePresheafBuilder().build()

        checker = StalkEquivalenceChecker(cat)
        result = checker.check_stalkwise(presheaf_f, presheaf_g)
        assert isinstance(result, StalkEquivalenceResult)

    def test_trivially_equivalent(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        presheaf = builder.build()

        cat = SiteCategory()
        cat.add_site(ConcreteSite(site_a))

        checker = StalkEquivalenceChecker(cat)
        result = checker.check_stalkwise(presheaf, presheaf)
        assert isinstance(result, StalkEquivalenceResult)
