"""Tests for deppy.equivalence.global_checker — 6-phase global orchestration."""

from __future__ import annotations

import pytest
from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.core.presheaf import ConcretePresheafBuilder
from deppy.core.site import ConcreteSite, SiteCategory
from deppy.types.refinement import TruePred
from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
    SiteCorrespondence,
)
from deppy.equivalence.global_checker import (
    GlobalEquivalenceChecker,
    GlobalEquivalenceResult,
    GluingResult,
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


class TestGlobalEquivalenceChecker:
    def test_creation(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        presheaf = builder.build()

        cat = SiteCategory()
        cat.add_site(ConcreteSite(site_a))

        common_a = _site("common_a")
        corr = SiteCorrespondence(
            f_site=site_a, g_site=site_a, common_site=common_a,
        )

        checker = GlobalEquivalenceChecker(
            presheaf_f=presheaf,
            presheaf_g=presheaf,
            site_category=cat,
            correspondences=[corr],
            sections_f={site_a: sec_a},
            sections_g={site_a: sec_a},
        )
        assert checker is not None

    def test_check_trivially_equivalent(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        presheaf = builder.build()

        cat = SiteCategory()
        cat.add_site(ConcreteSite(site_a))

        common_a = _site("common_a")
        corr = SiteCorrespondence(
            f_site=site_a, g_site=site_a, common_site=common_a,
        )

        checker = GlobalEquivalenceChecker(
            presheaf_f=presheaf,
            presheaf_g=presheaf,
            site_category=cat,
            correspondences=[corr],
            sections_f={site_a: sec_a},
            sections_g={site_a: sec_a},
        )
        result = checker.check()
        assert isinstance(result, GlobalEquivalenceResult)


class TestGluingResult:
    def test_glued_true(self):
        r = GluingResult(glued=True)
        assert r.glued is True

    def test_glued_false(self):
        r = GluingResult(glued=False)
        assert r.glued is False
