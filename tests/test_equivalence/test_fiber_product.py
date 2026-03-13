"""Tests for deppy.equivalence.fiber_product — genuine pullback construction."""

from __future__ import annotations

import pytest
from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.core.presheaf import ConcretePresheafBuilder
from deppy.core.site import ConcreteSite, SiteCategory
from deppy.types.refinement import TruePred, VarPred
from deppy.equivalence._protocols import SiteCorrespondence
from deppy.equivalence.fiber_product import (
    FiberProduct,
    FiberProductBuilder,
    FiberProjection,
    FiberSection,
)


def _site(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _section(name: str) -> LocalSection:
    return LocalSection(
        site_id=_site(name), carrier_type=None,
        refinements={}, trust=TrustLevel.RESIDUAL, provenance="test",
    )


class TestFiberSection:
    def test_creation(self):
        fs = FiberSection(
            site_id=_site("a"),
            section_f=_section("a"),
            section_g=_section("a"),
            equaliser_predicate=TruePred(),
        )
        assert fs.site_id == _site("a")
        assert fs.trust == TrustLevel.RESIDUAL


class TestFiberProjection:
    def test_creation(self):
        fp = FiberProjection(
            name="pi_f",
            source_site=_site("a"),
            target_site=_site("a"),
            direction="f",
        )
        assert fp.name == "pi_f"
        assert fp.direction == "f"


class TestFiberProductBuilder:
    def test_build_trivial(self):
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

        fpb = FiberProductBuilder(presheaf_f, presheaf_g, cat)
        corr = SiteCorrespondence(f_site=site_a, g_site=site_a, common_site=site_a)
        product = fpb.build([corr])
        assert isinstance(product, FiberProduct)

    def test_build_multi_site(self):
        site_a = _site("a")
        site_b = _site("b")
        sec_a = _section("a")
        sec_b = _section("b")

        builder_f = ConcretePresheafBuilder()
        builder_f.add_section(sec_a)
        builder_f.add_section(sec_b)
        presheaf_f = builder_f.build()

        builder_g = ConcretePresheafBuilder()
        builder_g.add_section(sec_a)
        builder_g.add_section(sec_b)
        presheaf_g = builder_g.build()

        cat = SiteCategory()
        cat.add_site(ConcreteSite(site_a))
        cat.add_site(ConcreteSite(site_b))

        fpb = FiberProductBuilder(presheaf_f, presheaf_g, cat)
        corrs = [
            SiteCorrespondence(f_site=site_a, g_site=site_a, common_site=site_a),
            SiteCorrespondence(f_site=site_b, g_site=site_b, common_site=site_b),
        ]
        product = fpb.build(corrs)
        assert isinstance(product, FiberProduct)
