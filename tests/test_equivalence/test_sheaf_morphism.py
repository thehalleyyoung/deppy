"""Tests for deppy.equivalence.sheaf_morphism — natural transformations."""

from __future__ import annotations

import pytest
from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.core.presheaf import ConcretePresheafBuilder
from deppy.core.site import ConcreteSite, SiteCategory
from deppy.types.refinement import TruePred, VarPred
from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
)
from deppy.equivalence.sheaf_morphism import (
    IsomorphismChecker,
    IsomorphismResult,
    MorphismComponent,
    NaturalitySquare,
    SheafMorphism,
    SheafMorphismBuilder,
)


def _site(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _section(name: str) -> LocalSection:
    return LocalSection(
        site_id=_site(name), carrier_type=None,
        refinements={}, trust=TrustLevel.RESIDUAL, provenance="test",
    )


def _obligation(name: str) -> EquivalenceObligation:
    return EquivalenceObligation(site_id=_site(name), description="test")


def _judgment(name: str, verdict=EquivalenceVerdict.EQUIVALENT) -> LocalEquivalenceJudgment:
    return LocalEquivalenceJudgment(
        site_id=_site(name), verdict=verdict, obligation=_obligation(name),
    )


class TestMorphismComponent:
    def test_creation(self):
        comp = MorphismComponent(
            site_id=_site("a"),
            forward_predicate=VarPred("x"),
        )
        assert comp.site_id == _site("a")
        assert comp.inverse_predicate is None

    def test_with_inverse(self):
        comp = MorphismComponent(
            site_id=_site("a"),
            forward_predicate=VarPred("x"),
            inverse_predicate=VarPred("y"),
        )
        assert comp.inverse_predicate is not None


class TestNaturalitySquare:
    def test_creation(self):
        sq = NaturalitySquare(
            morphism_source=_site("a"),
            morphism_target=_site("b"),
            path1_predicate=VarPred("x"),
            path2_predicate=VarPred("y"),
        )
        assert sq.morphism_source == _site("a")
        assert sq.verdict is not None


class TestSheafMorphismBuilder:
    def test_build_from_judgments(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder_f = ConcretePresheafBuilder()
        builder_f.add_section(sec_a)
        presheaf_f = builder_f.build()

        builder_g = ConcretePresheafBuilder()
        builder_g.add_section(sec_a)
        presheaf_g = builder_g.build()

        cat = SiteCategory()
        cat.add_site(ConcreteSite(site_a))

        smb = SheafMorphismBuilder(presheaf_f, presheaf_g, cat)
        judgments = [_judgment("a")]
        morphism = smb.build(judgments)
        assert isinstance(morphism, SheafMorphism)


class TestIsomorphismChecker:
    def test_check_trivial(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        presheaf = builder.build()

        cat = SiteCategory()
        cat.add_site(ConcreteSite(site_a))

        smb = SheafMorphismBuilder(presheaf, presheaf, cat)
        judgments = [_judgment("a")]
        morphism = smb.build(judgments)

        ic = IsomorphismChecker(morphism)
        result = ic.check()
        assert isinstance(result, IsomorphismResult)
