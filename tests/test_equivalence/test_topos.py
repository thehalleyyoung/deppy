"""Tests for deppy.equivalence.topos — presheaf morphisms."""

from __future__ import annotations

import pytest
from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.core.presheaf import ConcretePresheafBuilder
from deppy.types.refinement import TruePred
from deppy.equivalence.topos import (
    PresheafMorphism,
    SectionTransformComponent,
)


def _site(name: str) -> SiteId:
    return SiteId(kind=SiteKind.CALL_RESULT, name=name)


def _section(name: str) -> LocalSection:
    return LocalSection(
        site_id=_site(name), carrier_type=None,
        refinements={}, trust=TrustLevel.RESIDUAL, provenance="test",
    )


def _identity_transform(sec: LocalSection) -> LocalSection:
    return sec


class TestPresheafMorphism:
    def test_creation(self):
        builder_f = ConcretePresheafBuilder()
        builder_g = ConcretePresheafBuilder()
        site_a = _site("a")
        sec_a = _section("a")
        builder_f.add_section(sec_a)
        builder_g.add_section(sec_a)
        p_f = builder_f.build()
        p_g = builder_g.build()

        comp = SectionTransformComponent(
            site_id=site_a,
            transform=_identity_transform,
        )
        morph = PresheafMorphism(
            source=p_f, target=p_g,
            components={site_a: comp},
        )
        assert morph.source is p_f
        assert morph.target is p_g
        assert site_a in morph.components

    def test_empty_morphism(self):
        p = ConcretePresheafBuilder().build()
        morph = PresheafMorphism(source=p, target=p)
        assert len(morph.components) == 0
