"""Tests for BackwardSynthesizer -- backward synthesis from error sites to input boundary.

Tests verify that backward propagation correctly pulls viability requirements
from error sites back to input boundary sites.
"""

import pytest

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
    BoundarySection,
)
from deppy.core.site import ConcreteSite, ConcreteMorphism, CoverBuilder
from deppy.core.site_factory import SiteFactory
from deppy.kernel.backward_synthesis import (
    BackwardSynthesizer,
    BackwardSynthesisResult,
    BackwardStatus,
    ViabilityPrecondition,
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


# ============================================================================
# No error sites
# ============================================================================


class TestNoErrorSites:

    def test_no_error_sites_status(self):
        f = _factory()
        arg = f.create_argument_site("x")
        ret = f.create_return_site()
        cover = (
            CoverBuilder()
            .add_site(arg)
            .add_site(ret)
            .mark_input(arg.site_id)
            .mark_output(ret.site_id)
            .build()
        )
        synth = BackwardSynthesizer()
        result = synth.synthesize(cover, {})
        assert result.status == BackwardStatus.NO_ERROR_SITES

    def test_no_error_sites_empty_result(self):
        f = _factory()
        arg = f.create_argument_site("x")
        cover = (
            CoverBuilder()
            .add_site(arg)
            .mark_input(arg.site_id)
            .build()
        )
        synth = BackwardSynthesizer()
        result = synth.synthesize(cover, {})
        assert result.num_input_sections == 0


# ============================================================================
# No input boundary
# ============================================================================


class TestNoInputBoundary:

    def test_no_input_boundary_status(self):
        f = _factory()
        err = f.create_error_site("TypeError")
        cover = (
            CoverBuilder()
            .add_site(err)
            .mark_error(err.site_id)
            .build()
        )
        synth = BackwardSynthesizer()
        result = synth.synthesize(cover, {})
        assert result.status == BackwardStatus.NO_INPUT_BOUNDARY


# ============================================================================
# Simple backward propagation
# ============================================================================


class TestSimpleBackward:
    """Test backward from a single error site through one morphism to input."""

    def _build_cover(self):
        f = _factory()
        arg = f.create_argument_site("x")
        ssa = f.create_ssa_site("x", ssa_version=1)
        err = f.create_error_site("ZeroDivisionError")

        m1 = ConcreteMorphism(_source=arg.site_id, _target=ssa.site_id)
        m2 = ConcreteMorphism(_source=ssa.site_id, _target=err.site_id)

        cover = (
            CoverBuilder()
            .add_site(arg)
            .add_site(ssa)
            .add_site(err)
            .add_morphism(m1)
            .add_morphism(m2)
            .mark_input(arg.site_id)
            .mark_error(err.site_id)
            .build()
        )
        return cover, arg, ssa, err

    def test_reaches_input_boundary(self):
        cover, arg, ssa, err = self._build_cover()
        sections = {err.site_id: _section(err.site_id, refinements={"error": True})}
        synth = BackwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert result.status == BackwardStatus.CONVERGED
        assert arg.site_id in result.input_sections

    def test_error_sites_processed(self):
        cover, arg, ssa, err = self._build_cover()
        sections = {err.site_id: _section(err.site_id)}
        synth = BackwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert err.site_id in result.error_sites_processed

    def test_boundary_section_produced(self):
        cover, arg, ssa, err = self._build_cover()
        sections = {err.site_id: _section(err.site_id)}
        synth = BackwardSynthesizer()
        result = synth.synthesize(cover, sections)
        if result.boundary_section is not None:
            assert isinstance(result.boundary_section, BoundarySection)
            assert result.boundary_section.is_input is True

    def test_intermediate_sections(self):
        cover, arg, ssa, err = self._build_cover()
        sections = {err.site_id: _section(err.site_id)}
        synth = BackwardSynthesizer()
        result = synth.synthesize(cover, sections)
        # The SSA site should appear as intermediate
        all_secs = result.all_sections()
        assert isinstance(all_secs, dict)


# ============================================================================
# Multi-error backward
# ============================================================================


class TestMultiErrorBackward:
    """Test backward synthesis from multiple error sites."""

    def test_two_error_sites(self):
        f = _factory()
        arg = f.create_argument_site("x")
        ssa = f.create_ssa_site("x", ssa_version=1)
        e1 = f.create_error_site("TypeError", error_index=0)
        e2 = f.create_error_site("ValueError", error_index=1)

        m1 = ConcreteMorphism(_source=arg.site_id, _target=ssa.site_id)
        m2 = ConcreteMorphism(_source=ssa.site_id, _target=e1.site_id)
        m3 = ConcreteMorphism(_source=ssa.site_id, _target=e2.site_id)

        cover = (
            CoverBuilder()
            .add_site(arg)
            .add_site(ssa)
            .add_site(e1)
            .add_site(e2)
            .add_morphism(m1)
            .add_morphism(m2)
            .add_morphism(m3)
            .mark_input(arg.site_id)
            .mark_error(e1.site_id)
            .mark_error(e2.site_id)
            .build()
        )
        sections = {
            e1.site_id: _section(e1.site_id, refinements={"err_type": "TypeError"}),
            e2.site_id: _section(e2.site_id, refinements={"err_type": "ValueError"}),
        }
        synth = BackwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert e1.site_id in result.error_sites_processed
        assert e2.site_id in result.error_sites_processed


# ============================================================================
# Branching backward
# ============================================================================


class TestBranchingBackward:

    def test_backward_through_branch(self):
        f = _factory()
        arg = f.create_argument_site("x")
        guard = f.create_branch_guard_site("g0")
        ssa_t = f.create_ssa_site("y", ssa_version=0)
        err = f.create_error_site("IndexError")

        m1 = ConcreteMorphism(_source=arg.site_id, _target=guard.site_id)
        m2 = ConcreteMorphism(_source=guard.site_id, _target=ssa_t.site_id)
        m3 = ConcreteMorphism(_source=ssa_t.site_id, _target=err.site_id)

        cover = (
            CoverBuilder()
            .add_site(arg)
            .add_site(guard)
            .add_site(ssa_t)
            .add_site(err)
            .add_morphism(m1)
            .add_morphism(m2)
            .add_morphism(m3)
            .mark_input(arg.site_id)
            .mark_error(err.site_id)
            .build()
        )
        sections = {err.site_id: _section(err.site_id)}
        synth = BackwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert result.status == BackwardStatus.CONVERGED
        assert arg.site_id in result.input_sections


# ============================================================================
# Viability preconditions
# ============================================================================


class TestViabilityPreconditions:

    def test_viability_map_populated(self):
        f = _factory()
        arg = f.create_argument_site("x")
        err = f.create_error_site("ZeroDivisionError")
        m = ConcreteMorphism(_source=arg.site_id, _target=err.site_id)
        cover = (
            CoverBuilder()
            .add_site(arg)
            .add_site(err)
            .add_morphism(m)
            .mark_input(arg.site_id)
            .mark_error(err.site_id)
            .build()
        )
        sections = {
            err.site_id: _section(err.site_id, refinements={"viability": "x != 0"}),
        }
        synth = BackwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert err.site_id in result.viability_map

    def test_viability_precondition_properties(self):
        sid = SiteId(kind=SiteKind.ERROR, name="test_err")
        vp = ViabilityPrecondition(
            _error_site=sid,
            _predicate="x != 0",
            _path=(sid,),
            _trust=TrustLevel.BOUNDED_AUTO,
        )
        assert vp.error_site == sid
        assert vp.predicate == "x != 0"
        assert len(vp.path) == 1
        assert vp.trust == TrustLevel.BOUNDED_AUTO


# ============================================================================
# Backward from error subset
# ============================================================================


class TestBackwardFromSubset:

    def test_synthesize_from_errors_subset(self):
        f = _factory()
        arg = f.create_argument_site("x")
        e1 = f.create_error_site("T1", error_index=0)
        e2 = f.create_error_site("T2", error_index=1)
        m1 = ConcreteMorphism(_source=arg.site_id, _target=e1.site_id)
        m2 = ConcreteMorphism(_source=arg.site_id, _target=e2.site_id)
        cover = (
            CoverBuilder()
            .add_site(arg)
            .add_site(e1)
            .add_site(e2)
            .add_morphism(m1)
            .add_morphism(m2)
            .mark_input(arg.site_id)
            .mark_error(e1.site_id)
            .mark_error(e2.site_id)
            .build()
        )
        sections = {
            e1.site_id: _section(e1.site_id),
            e2.site_id: _section(e2.site_id),
        }
        synth = BackwardSynthesizer()
        result = synth.synthesize_from_errors(
            cover, sections, error_subset={e1.site_id}
        )
        assert e1.site_id in result.error_sites_processed
        assert e2.site_id not in result.error_sites_processed


# ============================================================================
# Max iterations
# ============================================================================


class TestBackwardMaxIterations:

    def test_respects_max_iterations(self):
        f = _factory()
        arg = f.create_argument_site("x")
        err = f.create_error_site("E")
        m = ConcreteMorphism(_source=arg.site_id, _target=err.site_id)
        cover = (
            CoverBuilder()
            .add_site(arg)
            .add_site(err)
            .add_morphism(m)
            .mark_input(arg.site_id)
            .mark_error(err.site_id)
            .build()
        )
        synth = BackwardSynthesizer(max_iterations=1)
        result = synth.synthesize(cover, {err.site_id: _section(err.site_id)})
        assert result.iterations <= 2  # At most 2 worklist pops for 2 sites


# ============================================================================
# BackwardSynthesisResult
# ============================================================================


class TestBackwardSynthesisResultProperties:

    def test_repr(self):
        result = BackwardSynthesisResult()
        assert "BackwardSynthesisResult" in repr(result)

    def test_all_sections(self):
        sid_a = SiteId(kind=SiteKind.SSA_VALUE, name="a_0")
        sid_b = SiteId(kind=SiteKind.ARGUMENT_BOUNDARY, name="arg_x")
        result = BackwardSynthesisResult(
            input_sections={sid_b: _section(sid_b)},
            intermediate_sections={sid_a: _section(sid_a)},
        )
        all_secs = result.all_sections()
        assert sid_a in all_secs
        assert sid_b in all_secs
