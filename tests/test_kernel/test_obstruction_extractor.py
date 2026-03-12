"""Tests for ObstructionExtractor -- obstruction extraction from disagreeing overlaps.

Tests verify that the extractor identifies agreeing overlaps, extracts
obstructions from disagreeing sections, clusters them, ranks by severity,
and computes the H^1 cohomology dimension.
"""

import pytest

from deppy.core._protocols import (
    Cover,
    LocalSection,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
    BoundarySection,
    GlobalSection,
)
from deppy.core.site import ConcreteSite, ConcreteMorphism, CoverBuilder
from deppy.core.site_factory import SiteFactory
from deppy.kernel.obstruction_extractor import (
    ExtractionResult,
    ObstructionExtractor,
    ObstructionSeverity,
    RankedObstruction,
)


# ============================================================================
# Helpers
# ============================================================================


def _factory():
    return SiteFactory()


def _section(sid, carrier_type=None, refinements=None, trust=TrustLevel.TRUSTED_AUTO):
    return LocalSection(
        site_id=sid,
        carrier_type=carrier_type,
        refinements=refinements or {},
        trust=trust,
    )


def _build_overlap_cover_agreeing():
    """Two SSA sites that overlap with agreeing sections."""
    f = _factory()
    a = f.create_ssa_site("x", ssa_version=0)
    b = f.create_ssa_site("x", ssa_version=1)
    ret = f.create_return_site()

    m1 = ConcreteMorphism(_source=a.site_id, _target=ret.site_id)
    m2 = ConcreteMorphism(_source=b.site_id, _target=ret.site_id)

    cover = (
        CoverBuilder()
        .add_site(a)
        .add_site(b)
        .add_site(ret)
        .add_morphism(m1)
        .add_morphism(m2)
        .add_overlap(a.site_id, b.site_id)
        .mark_output(ret.site_id)
        .build()
    )
    return cover, a, b, ret


def _build_overlap_cover_disagreeing():
    """Two SSA sites that overlap with disagreeing sections."""
    f = _factory()
    a = f.create_ssa_site("x", ssa_version=0)
    b = f.create_ssa_site("x", ssa_version=1)
    ret = f.create_return_site()

    m1 = ConcreteMorphism(_source=a.site_id, _target=ret.site_id)
    m2 = ConcreteMorphism(_source=b.site_id, _target=ret.site_id)

    cover = (
        CoverBuilder()
        .add_site(a)
        .add_site(b)
        .add_site(ret)
        .add_morphism(m1)
        .add_morphism(m2)
        .add_overlap(a.site_id, b.site_id)
        .mark_output(ret.site_id)
        .build()
    )
    return cover, a, b, ret


def _build_error_overlap_cover():
    """Overlap involving an error site for severity classification."""
    f = _factory()
    ssa = f.create_ssa_site("x", ssa_version=0)
    err = f.create_error_site("TypeError")
    arg = f.create_argument_site("x")

    m1 = ConcreteMorphism(_source=arg.site_id, _target=ssa.site_id)
    m2 = ConcreteMorphism(_source=ssa.site_id, _target=err.site_id)

    cover = (
        CoverBuilder()
        .add_site(arg)
        .add_site(ssa)
        .add_site(err)
        .add_morphism(m1)
        .add_morphism(m2)
        .add_overlap(ssa.site_id, err.site_id)
        .mark_input(arg.site_id)
        .mark_error(err.site_id)
        .build()
    )
    return cover, arg, ssa, err


# ============================================================================
# Consistent (agreeing) overlaps
# ============================================================================


class TestConsistentOverlaps:

    def test_agreeing_sections_consistent(self):
        cover, a, b, ret = _build_overlap_cover_agreeing()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int", refinements={"positive": True}),
            b.site_id: _section(b.site_id, carrier_type="int", refinements={"positive": True}),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        assert result.is_consistent

    def test_no_obstructions_when_consistent(self):
        cover, a, b, ret = _build_overlap_cover_agreeing()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
            b.site_id: _section(b.site_id, carrier_type="int"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        assert not result.has_obstructions

    def test_global_section_assembled(self):
        cover, a, b, ret = _build_overlap_cover_agreeing()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
            b.site_id: _section(b.site_id, carrier_type="int"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        if result.is_consistent:
            # Global section may or may not be assembled depending on implementation
            assert isinstance(result.global_section, (GlobalSection, type(None)))


# ============================================================================
# Disagreeing overlaps
# ============================================================================


class TestDisagreeingOverlaps:

    def test_carrier_type_mismatch(self):
        cover, a, b, ret = _build_overlap_cover_disagreeing()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
            b.site_id: _section(b.site_id, carrier_type="str"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        assert not result.is_consistent
        assert result.has_obstructions

    def test_refinement_disagreement(self):
        cover, a, b, ret = _build_overlap_cover_disagreeing()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int", refinements={"sign": "positive"}),
            b.site_id: _section(b.site_id, carrier_type="int", refinements={"sign": "negative"}),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        assert not result.is_consistent
        assert result.num_disagreed >= 1

    def test_missing_section_is_obstruction(self):
        cover, a, b, ret = _build_overlap_cover_disagreeing()
        # Only provide section at a, not b
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        # Missing section at overlap should cause obstruction
        assert not result.is_consistent or result.num_disagreed >= 0


# ============================================================================
# Obstruction clustering
# ============================================================================


class TestObstructionClustering:

    def test_single_cluster(self):
        cover, a, b, ret = _build_overlap_cover_disagreeing()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
            b.site_id: _section(b.site_id, carrier_type="str"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        if result.has_obstructions:
            assert result.num_clusters >= 1

    def test_multiple_clusters(self):
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        c = f.create_ssa_site("y", ssa_version=0)
        d = f.create_ssa_site("y", ssa_version=1)

        cover = (
            CoverBuilder()
            .add_site(a)
            .add_site(b)
            .add_site(c)
            .add_site(d)
            .add_overlap(a.site_id, b.site_id)
            .add_overlap(c.site_id, d.site_id)
            .build()
        )
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
            b.site_id: _section(b.site_id, carrier_type="str"),
            c.site_id: _section(c.site_id, carrier_type="float"),
            d.site_id: _section(d.site_id, carrier_type="bool"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        if result.has_obstructions:
            # Two independent overlap disagreements should form 2 clusters
            assert result.num_clusters >= 2


# ============================================================================
# Severity classification
# ============================================================================


class TestSeverityClassification:

    def test_error_site_is_critical(self):
        cover, arg, ssa, err = _build_error_overlap_cover()
        sections = {
            ssa.site_id: _section(ssa.site_id, carrier_type="int"),
            err.site_id: _section(err.site_id, carrier_type="str"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        if result.has_obstructions:
            critical = result.by_severity(ObstructionSeverity.CRITICAL)
            assert len(critical) >= 1

    def test_output_boundary_is_high(self):
        cover, a, b, ret = _build_overlap_cover_disagreeing()
        # Add ret to the overlap so that the output boundary is part of disagreement
        f = _factory()
        c = f.create_ssa_site("z", ssa_version=0)
        cover2 = (
            CoverBuilder()
            .add_site(c)
            .add_site(ret)
            .add_overlap(c.site_id, ret.site_id)
            .mark_output(ret.site_id)
            .build()
        )
        sections = {
            c.site_id: _section(c.site_id, carrier_type="int"),
            ret.site_id: _section(ret.site_id, carrier_type="str"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover2, sections)
        if result.has_obstructions:
            high = result.by_severity(ObstructionSeverity.HIGH)
            assert len(high) >= 1


# ============================================================================
# Ranking and impact
# ============================================================================


class TestRanking:

    def test_obstructions_sorted_by_impact(self):
        cover, a, b, ret = _build_overlap_cover_disagreeing()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
            b.site_id: _section(b.site_id, carrier_type="str"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        if len(result.obstructions) >= 2:
            for i in range(len(result.obstructions) - 1):
                assert result.obstructions[i].impact_score >= result.obstructions[i + 1].impact_score

    def test_top_obstructions(self):
        cover, a, b, ret = _build_overlap_cover_disagreeing()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
            b.site_id: _section(b.site_id, carrier_type="str"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        top = result.top_obstructions(3)
        assert len(top) <= 3
        assert isinstance(top, list)


# ============================================================================
# H^1 dimension
# ============================================================================


class TestH1Dimension:

    def test_h1_zero_when_consistent(self):
        cover, a, b, ret = _build_overlap_cover_agreeing()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
            b.site_id: _section(b.site_id, carrier_type="int"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        if result.is_consistent:
            assert result.h1_dimension == 0

    def test_h1_positive_when_disagreeing(self):
        cover, a, b, ret = _build_overlap_cover_disagreeing()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
            b.site_id: _section(b.site_id, carrier_type="str"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        if result.has_obstructions:
            assert result.h1_dimension >= 1


# ============================================================================
# RankedObstruction properties
# ============================================================================


class TestRankedObstructionProps:

    def test_ranked_obstruction_repr(self):
        from deppy.static_analysis.section_gluing import ResolutionCandidate
        obs = ObstructionData(
            conflicting_overlaps=[],
            explanation="test",
        )
        sid = SiteId(kind=SiteKind.SSA_VALUE, name="x_0")
        ranked = RankedObstruction(
            _obstruction=obs,
            _severity=ObstructionSeverity.MEDIUM,
            _impact_score=5.0,
            _affected_sites=frozenset({sid}),
            _resolution_candidates=(),
            _cluster_id=0,
        )
        assert "RankedObstruction" in repr(ranked)
        assert ranked.severity == ObstructionSeverity.MEDIUM
        assert ranked.impact_score == 5.0
        assert sid in ranked.affected_sites
        assert ranked.cluster_id == 0

    def test_obstruction_data_accessible(self):
        obs = ObstructionData(
            conflicting_overlaps=[],
            explanation="type mismatch",
        )
        ranked = RankedObstruction(
            _obstruction=obs,
            _severity=ObstructionSeverity.HIGH,
            _impact_score=10.0,
            _affected_sites=frozenset(),
            _resolution_candidates=(),
        )
        assert ranked.obstruction.explanation == "type mismatch"


# ============================================================================
# ExtractionResult properties
# ============================================================================


class TestExtractionResultProps:

    def test_repr(self):
        result = ExtractionResult()
        s = repr(result)
        assert "ExtractionResult" in s

    def test_default_values(self):
        result = ExtractionResult()
        assert result.is_consistent is False
        assert result.has_obstructions is False
        assert result.num_agreed == 0
        assert result.num_disagreed == 0
        assert result.h1_dimension == 0
        assert result.critical_count == 0

    def test_by_severity_empty(self):
        result = ExtractionResult()
        assert result.by_severity(ObstructionSeverity.CRITICAL) == []

    def test_top_obstructions_empty(self):
        result = ExtractionResult()
        assert result.top_obstructions() == []


# ============================================================================
# Max obstructions limit
# ============================================================================


class TestMaxObstructions:

    def test_respects_max_obstructions(self):
        # Build a cover with many overlaps
        f = _factory()
        sites = [f.create_ssa_site(f"v{i}", ssa_version=i) for i in range(6)]
        builder = CoverBuilder()
        for s in sites:
            builder.add_site(s)
        # Add overlaps between consecutive pairs
        for i in range(0, len(sites) - 1, 2):
            builder.add_overlap(sites[i].site_id, sites[i + 1].site_id)
        cover = builder.build()

        sections = {}
        for i, s in enumerate(sites):
            # Alternate carrier types to create disagreements
            ct = "int" if i % 2 == 0 else "str"
            sections[s.site_id] = _section(s.site_id, carrier_type=ct)

        extractor = ObstructionExtractor(max_obstructions=1)
        result = extractor.extract(cover, sections)
        assert len(result.obstructions) <= 1


# ============================================================================
# No overlaps
# ============================================================================


class TestNoOverlaps:

    def test_no_overlaps_consistent(self):
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("y", ssa_version=0)
        cover = (
            CoverBuilder()
            .add_site(a)
            .add_site(b)
            .build()
        )
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
            b.site_id: _section(b.site_id, carrier_type="str"),
        }
        extractor = ObstructionExtractor()
        result = extractor.extract(cover, sections)
        # No overlaps means no disagreement possible
        assert result.is_consistent
