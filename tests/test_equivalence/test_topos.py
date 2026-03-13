"""Tests for deppy.equivalence.topos — genuine categorical constructions."""

from __future__ import annotations

import pytest
from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.core.presheaf import ConcretePresheafBuilder
from deppy.core.site import ConcreteMorphism, ConcreteSite, SiteCategory
from deppy.types.refinement import TruePred, VarPred
from deppy.equivalence.topos import (
    EqualiserBuilder,
    EqualiserDiagram,
    InternalHomPresheaf,
    PresheafMorphism,
    PullbackBuilder,
    PullbackDiagram,
    PushoutBuilder,
    PushoutDiagram,
    SectionTransformComponent,
    SubobjectClassifier,
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


class TestPullbackBuilder:
    def test_trivial_pullback(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        presheaf = builder.build()

        pb = PullbackBuilder(source_f=presheaf, source_g=presheaf)
        diagram = pb.build()
        assert isinstance(diagram, PullbackDiagram)
        assert diagram.source_f is presheaf
        assert diagram.source_g is presheaf

    def test_pullback_commutativity(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        presheaf = builder.build()

        pb = PullbackBuilder(source_f=presheaf, source_g=presheaf)
        diagram = pb.build()
        assert isinstance(diagram.commutativity, dict)


class TestEqualiserBuilder:
    def test_equaliser_of_identity(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        p = builder.build()

        comp = SectionTransformComponent(
            site_id=site_a, transform=_identity_transform,
        )
        alpha = PresheafMorphism(source=p, target=p, components={site_a: comp})
        beta = PresheafMorphism(source=p, target=p, components={site_a: comp})

        eq = EqualiserBuilder(alpha=alpha, beta=beta)
        diagram = eq.build()
        assert isinstance(diagram, EqualiserDiagram)


class TestSubobjectClassifier:
    def test_sieve_for_site(self):
        cat = SiteCategory()
        site_a = _site("a")
        cat.add_site(ConcreteSite(site_a))

        omega = SubobjectClassifier(cat)
        sieve = omega.sieve_at(site_a)
        assert sieve is not None

    def test_classifying_map(self):
        cat = SiteCategory()
        site_a = _site("a")
        cat.add_site(ConcreteSite(site_a))

        builder = ConcretePresheafBuilder()
        builder.add_section(_section("a"))
        sub = builder.build()
        total = builder.build()

        omega = SubobjectClassifier(cat)
        chi = omega.classify(sub, total)
        assert chi is not None


class TestPushoutBuilder:
    def test_trivial_pushout(self):
        site_a = _site("a")
        sec_a = _section("a")

        builder = ConcretePresheafBuilder()
        builder.add_section(sec_a)
        p = builder.build()

        comp = SectionTransformComponent(
            site_id=site_a, transform=_identity_transform,
        )
        inc_f = PresheafMorphism(source=p, target=p, components={site_a: comp})
        inc_g = PresheafMorphism(source=p, target=p, components={site_a: comp})

        po = PushoutBuilder(
            source_f=p, source_g=p, base=p,
            inclusion_f=inc_f, inclusion_g=inc_g,
        )
        diagram = po.build()
        assert isinstance(diagram, PushoutDiagram)
