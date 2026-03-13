"""Tests for deppy.equivalence._protocols — core data structures."""

from __future__ import annotations

import pytest
from deppy.core._protocols import (
    Cover,
    CohomologyClass,
    DescentDatum,
    LocalSection,
    ObstructionData,
    RepairSuggestion,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.equivalence._protocols import (
    EquivalenceCochainData,
    EquivalenceCohomologyClass,
    EquivalenceDescentDatum,
    EquivalenceJudgment,
    EquivalenceObligation,
    EquivalenceObstruction,
    EquivalenceObstructionKind,
    EquivalenceSiteKind,
    EquivalenceStrength,
    EquivalenceVerdict,
    FiberProductSection,
    IsomorphismWitness,
    LocalEquivalenceJudgment,
    MorphismDirection,
    NaturalTransformation,
    ProgramId,
    SectionPair,
    SiteCorrespondence,
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


class TestEnums:
    def test_equivalence_verdict_values(self):
        assert EquivalenceVerdict.EQUIVALENT is not None
        assert EquivalenceVerdict.INEQUIVALENT is not None
        assert EquivalenceVerdict.UNKNOWN is not None

    def test_equivalence_strength_order(self):
        assert EquivalenceStrength.DENOTATIONAL is not None
        assert EquivalenceStrength.OBSERVATIONAL is not None

    def test_equivalence_site_kind(self):
        assert EquivalenceSiteKind.PAIRED_ARGUMENT is not None
        assert EquivalenceSiteKind.FIBER_PRODUCT is not None
        assert EquivalenceSiteKind.COMMON_REFINEMENT is not None

    def test_morphism_direction(self):
        assert MorphismDirection.FORWARD is not None
        assert MorphismDirection.BACKWARD is not None

    def test_obstruction_kind(self):
        assert EquivalenceObstructionKind.CARRIER_TYPE_MISMATCH is not None


class TestProgramId:
    def test_creation(self):
        pid = ProgramId(name="test_prog")
        assert pid.name == "test_prog"
        assert pid.source_path is None
        assert pid.function_name is None

    def test_with_all_fields(self):
        pid = ProgramId(name="p", source_path="foo.py", function_name="bar")
        assert pid.source_path == "foo.py"
        assert pid.function_name == "bar"


class TestSectionPair:
    def test_creation(self):
        site = _site("a")
        sec = _section("a")
        pair = SectionPair(site_id=site, section_f=sec, section_g=sec)
        assert pair.site_id == site
        assert pair.section_f is sec
        assert pair.section_g is sec
        assert pair.agreement_predicate is None


class TestFiberProductSection:
    def test_creation(self):
        site = _site("a")
        sec = _section("a")
        pair = SectionPair(site_id=site, section_f=sec, section_g=sec)
        fps = FiberProductSection(site_id=site, pair=pair)
        assert fps.site_id == site
        assert not fps.is_inhabited


class TestSiteCorrespondence:
    def test_creation(self):
        s_f = _site("foo")
        s_g = _site("bar")
        s_c = _site("common_foo_bar")
        corr = SiteCorrespondence(f_site=s_f, g_site=s_g, common_site=s_c)
        assert corr.f_site == s_f
        assert corr.g_site == s_g
        assert corr.common_site == s_c
        assert corr.alignment_score == 1.0


class TestEquivalenceObligation:
    def test_creation(self):
        ob = EquivalenceObligation(site_id=_site("a"), description="test")
        assert ob.site_id.name == "a"
        assert ob.description == "test"
        assert ob.forward_predicate is None


class TestLocalEquivalenceJudgment:
    def test_creation(self):
        ob = EquivalenceObligation(site_id=_site("a"), description="test")
        j = LocalEquivalenceJudgment(
            site_id=_site("a"),
            verdict=EquivalenceVerdict.EQUIVALENT,
            obligation=ob,
        )
        assert j.verdict == EquivalenceVerdict.EQUIVALENT

    def test_not_equivalent(self):
        ob = EquivalenceObligation(site_id=_site("a"), description="test")
        j = LocalEquivalenceJudgment(
            site_id=_site("a"),
            verdict=EquivalenceVerdict.INEQUIVALENT,
            obligation=ob,
            explanation="types differ",
        )
        assert j.verdict == EquivalenceVerdict.INEQUIVALENT
        assert j.explanation == "types differ"


class TestEquivalenceJudgment:
    def test_creation(self):
        j = EquivalenceJudgment(
            verdict=EquivalenceVerdict.EQUIVALENT,
            program_f=ProgramId(name="f"),
            program_g=ProgramId(name="g"),
        )
        assert j.verdict == EquivalenceVerdict.EQUIVALENT
        assert j.program_f.name == "f"


class TestNaturalTransformation:
    def test_creation(self):
        nt = NaturalTransformation()
        assert nt.is_natural is None
        assert nt.is_isomorphism is None
        assert len(nt.components) == 0


class TestIsomorphismWitness:
    def test_creation(self):
        nt = NaturalTransformation()
        w = IsomorphismWitness(forward=nt, inverse=nt)
        assert w.forward is nt
        assert w.inverse is nt


class TestEquivalenceDescentDatum:
    def test_creation(self):
        d = EquivalenceDescentDatum()
        assert len(d.cross_transitions) == 0


class TestCochainData:
    def test_creation(self):
        cd = EquivalenceCochainData(degree=0)
        assert cd.degree == 0

    def test_cohomology_class(self):
        cd = EquivalenceCochainData(degree=1)
        cls = EquivalenceCohomologyClass(
            degree=1,
            representative=cd,
            is_trivial=True,
        )
        assert cls.is_trivial


class TestEquivalenceObstruction:
    def test_creation(self):
        o = EquivalenceObstruction(
            kind=EquivalenceObstructionKind.CARRIER_TYPE_MISMATCH,
            description="carrier mismatch",
        )
        assert o.kind == EquivalenceObstructionKind.CARRIER_TYPE_MISMATCH
        assert o.description == "carrier mismatch"
        assert o.severity == "high"
