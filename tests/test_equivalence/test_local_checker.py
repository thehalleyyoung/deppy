"""Tests for deppy.equivalence.local_checker — per-site equivalence checking."""

from __future__ import annotations

import pytest
from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.core.presheaf import ConcretePresheafBuilder
from deppy.core.site import ConcreteSite, SiteCategory
from deppy.types.refinement import TruePred, VarPred, RefinementType, ComparisonPred, ComparisonOp
from deppy.types.base import TypeBase
from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
    SiteCorrespondence,
)
from deppy.equivalence.local_checker import (
    EqualiserLocalChecker,
    LocalEquivalenceChecker,
    check_local_equivalences,
)


def _site(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _section(name: str, pred=None) -> LocalSection:
    refs = {}
    if pred is not None:
        refs["_pred"] = pred
    return LocalSection(
        site_id=_site(name), carrier_type=None,
        refinements=refs, trust=TrustLevel.RESIDUAL, provenance="test",
    )


class DummyType(TypeBase):
    def substitute(self, mapping): return self
    def free_variables(self): return frozenset()
    def __eq__(self, other): return isinstance(other, DummyType)
    def __hash__(self): return 42
    def __repr__(self): return "DummyType()"


class TestLocalEquivalenceChecker:
    def test_creation(self):
        checker = LocalEquivalenceChecker()
        assert checker is not None

    def test_check_identical_sections(self):
        sec = _section("a")
        checker = LocalEquivalenceChecker()
        result = checker.check(_site("a"), sec, sec)
        assert isinstance(result, LocalEquivalenceJudgment)

    def test_check_with_presheaves(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        presheaf = builder.build()

        cat = SiteCategory()
        cat.add_site(ConcreteSite(site_a))

        checker = LocalEquivalenceChecker(
            site_category=cat,
            presheaf_f=presheaf,
            presheaf_g=presheaf,
        )
        result = checker.check(site_a, sec_a, sec_a)
        assert isinstance(result, LocalEquivalenceJudgment)


class TestEqualiserLocalChecker:
    def test_creation(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        presheaf = builder.build()

        cat = SiteCategory()
        cat.add_site(ConcreteSite(site_a))

        checker = EqualiserLocalChecker(presheaf, presheaf, cat)
        assert checker is not None

    def test_check_site(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        presheaf = builder.build()

        cat = SiteCategory()
        cat.add_site(ConcreteSite(site_a))

        checker = EqualiserLocalChecker(presheaf, presheaf, cat)
        result = checker.check(site_a)
        assert isinstance(result, tuple)
        assert len(result) == 2
        ok, preds = result
        assert isinstance(ok, bool)
        assert isinstance(preds, dict)


class TestCheckLocalEquivalences:
    def test_with_correspondences(self):
        site_a = _site("a")
        sec_a = _section("a")
        common_a = _site("common_a")

        corr = SiteCorrespondence(
            f_site=site_a, g_site=site_a, common_site=common_a,
        )
        result = check_local_equivalences(
            correspondences=[corr],
            sections_f={site_a: sec_a},
            sections_g={site_a: sec_a},
        )
        assert isinstance(result, list)
        for j in result:
            assert isinstance(j, LocalEquivalenceJudgment)
