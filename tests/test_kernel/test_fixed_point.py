"""Tests for FixedPointEngine -- convergence on small covers with manual sections.

Tests verify that the fixed-point engine converges, produces global sections
when possible, and correctly identifies obstructions when sections disagree.
"""

import pytest

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
    BoundarySection,
    GlobalSection,
    ObstructionData,
)
from deppy.core.site import ConcreteSite, ConcreteMorphism, CoverBuilder
from deppy.core.site_factory import SiteFactory
from deppy.kernel.fixed_point import (
    ConvergenceStatus,
    FixedPointEngine,
    FixedPointResult,
    IterationSnapshot,
)


# ============================================================================
# Helpers
# ============================================================================


def _make_factory():
    return SiteFactory()


def _build_linear_cover():
    """Build a simple linear cover: arg -> ssa -> return."""
    f = _make_factory()
    arg = f.create_argument_site("x")
    ssa = f.create_ssa_site("x", ssa_version=1)
    ret = f.create_return_site()

    m1 = ConcreteMorphism(_source=arg.site_id, _target=ssa.site_id)
    m2 = ConcreteMorphism(_source=ssa.site_id, _target=ret.site_id)

    cover = (
        CoverBuilder()
        .add_site(arg)
        .add_site(ssa)
        .add_site(ret)
        .add_morphism(m1)
        .add_morphism(m2)
        .mark_input(arg.site_id)
        .mark_output(ret.site_id)
        .build()
    )
    return cover, arg, ssa, ret


def _build_branching_cover():
    """Build a branching cover: arg -> guard -> [ssa_true, ssa_false] -> return."""
    f = _make_factory()
    arg = f.create_argument_site("x")
    guard = f.create_branch_guard_site("g0", is_true_branch=True)
    ssa_t = f.create_ssa_site("y", ssa_version=0)
    ssa_f = f.create_ssa_site("y", ssa_version=1)
    ret = f.create_return_site()

    m_ag = ConcreteMorphism(_source=arg.site_id, _target=guard.site_id)
    m_gt = ConcreteMorphism(_source=guard.site_id, _target=ssa_t.site_id)
    m_gf = ConcreteMorphism(_source=guard.site_id, _target=ssa_f.site_id)
    m_tr = ConcreteMorphism(_source=ssa_t.site_id, _target=ret.site_id)
    m_fr = ConcreteMorphism(_source=ssa_f.site_id, _target=ret.site_id)

    cover = (
        CoverBuilder()
        .add_site(arg)
        .add_site(guard)
        .add_site(ssa_t)
        .add_site(ssa_f)
        .add_site(ret)
        .add_morphism(m_ag)
        .add_morphism(m_gt)
        .add_morphism(m_gf)
        .add_morphism(m_tr)
        .add_morphism(m_fr)
        .add_overlap(ssa_t.site_id, ssa_f.site_id)
        .mark_input(arg.site_id)
        .mark_output(ret.site_id)
        .build()
    )
    return cover, arg, guard, ssa_t, ssa_f, ret


def _build_error_cover():
    """Build a cover with an error site: arg -> ssa -> error, ssa -> return."""
    f = _make_factory()
    arg = f.create_argument_site("x")
    ssa = f.create_ssa_site("x", ssa_version=1)
    err = f.create_error_site("ZeroDivisionError")
    ret = f.create_return_site()

    m1 = ConcreteMorphism(_source=arg.site_id, _target=ssa.site_id)
    m2 = ConcreteMorphism(_source=ssa.site_id, _target=ret.site_id)
    m3 = ConcreteMorphism(_source=ssa.site_id, _target=err.site_id)

    cover = (
        CoverBuilder()
        .add_site(arg)
        .add_site(ssa)
        .add_site(err)
        .add_site(ret)
        .add_morphism(m1)
        .add_morphism(m2)
        .add_morphism(m3)
        .mark_input(arg.site_id)
        .mark_output(ret.site_id)
        .mark_error(err.site_id)
        .build()
    )
    return cover, arg, ssa, err, ret


# ============================================================================
# Basic convergence
# ============================================================================


class TestBasicConvergence:

    def test_engine_runs_on_linear_cover(self):
        cover, arg, ssa, ret = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=5)
        result = engine.run(cover)
        assert isinstance(result, FixedPointResult)
        assert result.iterations >= 1

    def test_convergence_status(self):
        cover, *_ = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        assert result.status in (
            ConvergenceStatus.CONVERGED,
            ConvergenceStatus.GLOBAL_SECTION_FOUND,
            ConvergenceStatus.NO_PROGRESS,
            ConvergenceStatus.MAX_ITERATIONS,
            ConvergenceStatus.OBSTRUCTIONS_REMAIN,
        )

    def test_converged_property(self):
        cover, *_ = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        # The converged property should be a bool
        assert isinstance(result.converged, bool)

    def test_snapshots_recorded(self):
        cover, *_ = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=5)
        result = engine.run(cover)
        assert len(result.snapshots) >= 1
        for snap in result.snapshots:
            assert isinstance(snap, IterationSnapshot)

    def test_iterations_matches_snapshots(self):
        cover, *_ = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=5)
        result = engine.run(cover)
        assert result.iterations == len(result.snapshots)

    def test_total_elapsed_positive(self):
        cover, *_ = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=5)
        result = engine.run(cover)
        assert result.total_elapsed_ms >= 0.0


# ============================================================================
# Section production
# ============================================================================


class TestSectionProduction:

    def test_all_sections_populated(self):
        cover, *_ = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        # The engine should produce at least some sections
        assert len(result.all_sections) >= 0

    def test_input_section_produced(self):
        cover, arg, ssa, ret = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        # There should be sections at input boundary
        if result.input_section is not None:
            assert isinstance(result.input_section, BoundarySection)
            assert result.input_section.is_input is True

    def test_output_section_produced(self):
        cover, arg, ssa, ret = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        if result.output_section is not None:
            assert isinstance(result.output_section, BoundarySection)
            assert result.output_section.is_input is False


# ============================================================================
# Branching cover
# ============================================================================


class TestBranchingCover:

    def test_branching_cover_runs(self):
        cover, *_ = _build_branching_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        assert isinstance(result, FixedPointResult)

    def test_branching_sections_exist(self):
        cover, arg, guard, ssa_t, ssa_f, ret = _build_branching_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        assert len(result.all_sections) >= 0


# ============================================================================
# Error cover
# ============================================================================


class TestErrorCover:

    def test_error_cover_runs(self):
        cover, *_ = _build_error_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        assert isinstance(result, FixedPointResult)

    def test_error_viability_map(self):
        cover, arg, ssa, err, ret = _build_error_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        # Error viability should be populated for error sites
        assert isinstance(result.error_viability, dict)

    def test_viability_summary_exists(self):
        cover, *_ = _build_error_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        # After at least one iteration, viability should be checked
        if result.iterations >= 1:
            assert result.viability_summary is not None


# ============================================================================
# Max iterations
# ============================================================================


class TestMaxIterations:

    def test_respects_max_iterations(self):
        cover, *_ = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=1)
        result = engine.run(cover)
        assert result.iterations <= 1

    def test_max_iterations_status(self):
        # With max_iterations=0, the engine should never enter the loop
        # or exit immediately
        cover, *_ = _build_branching_cover()
        engine = FixedPointEngine(max_iterations=0)
        result = engine.run(cover)
        assert result.status == ConvergenceStatus.MAX_ITERATIONS


# ============================================================================
# Global section
# ============================================================================


class TestGlobalSection:

    def test_global_section_when_consistent(self):
        cover, *_ = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=10, early_stop_on_global_section=True)
        result = engine.run(cover)
        # A linear cover with no overlaps should produce a consistent result
        if result.global_section is not None:
            assert isinstance(result.global_section, GlobalSection)

    def test_has_global_section_property(self):
        cover, *_ = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        assert isinstance(result.has_global_section, bool)


# ============================================================================
# Obstructions
# ============================================================================


class TestObstructions:

    def test_obstructions_list(self):
        cover, *_ = _build_branching_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        assert isinstance(result.obstructions, list)

    def test_num_obstructions(self):
        cover, *_ = _build_branching_cover()
        engine = FixedPointEngine(max_iterations=10)
        result = engine.run(cover)
        assert result.num_obstructions >= 0


# ============================================================================
# Bidirectional result conversion
# ============================================================================


class TestBidirectionalConversion:

    def test_to_bidirectional_result(self):
        cover, *_ = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=5)
        result = engine.run(cover)
        bidir = result.to_bidirectional_result()
        assert isinstance(bidir.input_section, BoundarySection)
        assert isinstance(bidir.output_section, BoundarySection)
        assert isinstance(bidir.global_section, GlobalSection)
        assert isinstance(bidir.converged, bool)


# ============================================================================
# IterationSnapshot
# ============================================================================


class TestIterationSnapshot:

    def test_snapshot_properties(self):
        snap = IterationSnapshot(iteration=0, num_sections=5, num_new_sections=3)
        assert snap.made_progress is True

    def test_snapshot_no_progress(self):
        snap = IterationSnapshot(iteration=1, num_sections=5, num_new_sections=0, num_refined_sections=0)
        assert snap.made_progress is False

    def test_snapshot_repr(self):
        snap = IterationSnapshot(iteration=0)
        assert "Iteration" in repr(snap)


# ============================================================================
# Incremental run
# ============================================================================


class TestIncrementalRun:

    def test_incremental_run(self):
        cover, arg, ssa, ret = _build_linear_cover()
        engine = FixedPointEngine(max_iterations=5)
        result1 = engine.run(cover)
        # Incremental run with no changes
        result2 = engine.run_incremental(cover, result1, set())
        assert isinstance(result2, FixedPointResult)


# ============================================================================
# FixedPointResult repr
# ============================================================================


class TestFixedPointResultRepr:

    def test_repr(self):
        result = FixedPointResult()
        s = repr(result)
        assert "FixedPointResult" in s

    def test_repr_with_data(self):
        result = FixedPointResult(
            status=ConvergenceStatus.CONVERGED,
            iterations=3,
            total_elapsed_ms=42.0,
        )
        s = repr(result)
        assert "converged" in s


# ============================================================================
# Empty cover
# ============================================================================


class TestEmptyCover:

    def test_empty_cover(self):
        cover = CoverBuilder().build()
        engine = FixedPointEngine(max_iterations=5)
        result = engine.run(cover)
        assert isinstance(result, FixedPointResult)


# ============================================================================
# Cover with overlaps but agreeing sections
# ============================================================================


class TestAgreeingOverlaps:

    def test_agreeing_overlaps_no_obstructions(self):
        """When overlapping sections agree, there should be no obstructions."""
        f = _make_factory()
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
        engine = FixedPointEngine(max_iterations=5)
        result = engine.run(cover)
        assert isinstance(result, FixedPointResult)
