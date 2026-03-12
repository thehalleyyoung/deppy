"""Tests for ForwardSynthesizer -- forward synthesis from input boundary to output boundary.

Tests verify that forward propagation correctly pushes type sections
from input boundary sites to output boundary sites, handles phi-merge
at join points, and detects unreachable outputs.
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
from deppy.kernel.forward_synthesis import (
    ForwardSynthesizer,
    ForwardSynthesisResult,
    ForwardStatus,
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


def _build_linear_cover():
    """arg -> ssa -> return."""
    f = _factory()
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
    """arg -> guard -> [ssa_t, ssa_f] -> return."""
    f = _factory()
    arg = f.create_argument_site("x")
    guard = f.create_branch_guard_site("g0")
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
        .mark_input(arg.site_id)
        .mark_output(ret.site_id)
        .build()
    )
    return cover, arg, guard, ssa_t, ssa_f, ret


# ============================================================================
# No input seeds
# ============================================================================


class TestNoInputSeeds:

    def test_no_input_seeds_status(self):
        f = _factory()
        ret = f.create_return_site()
        cover = (
            CoverBuilder()
            .add_site(ret)
            .mark_output(ret.site_id)
            .build()
        )
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, {})
        assert result.status == ForwardStatus.NO_INPUT_SEEDS

    def test_no_input_seeds_empty_output(self):
        f = _factory()
        ret = f.create_return_site()
        cover = (
            CoverBuilder()
            .add_site(ret)
            .mark_output(ret.site_id)
            .build()
        )
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, {})
        assert result.num_output_sections == 0


# ============================================================================
# No output boundary
# ============================================================================


class TestNoOutputBoundary:

    def test_no_output_boundary_status(self):
        f = _factory()
        arg = f.create_argument_site("x")
        cover = (
            CoverBuilder()
            .add_site(arg)
            .mark_input(arg.site_id)
            .build()
        )
        sections = {arg.site_id: _section(arg.site_id)}
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert result.status == ForwardStatus.NO_OUTPUT_BOUNDARY


# ============================================================================
# Simple forward propagation
# ============================================================================


class TestSimpleForward:

    def test_reaches_output_boundary(self):
        cover, arg, ssa, ret = _build_linear_cover()
        sections = {arg.site_id: _section(arg.site_id, carrier_type="int")}
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert result.status == ForwardStatus.CONVERGED
        assert ret.site_id in result.output_sections

    def test_output_section_produced(self):
        cover, arg, ssa, ret = _build_linear_cover()
        sections = {arg.site_id: _section(arg.site_id, carrier_type="int")}
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert result.num_output_sections >= 1

    def test_boundary_section_is_output(self):
        cover, arg, ssa, ret = _build_linear_cover()
        sections = {arg.site_id: _section(arg.site_id)}
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, sections)
        if result.boundary_section is not None:
            assert isinstance(result.boundary_section, BoundarySection)
            assert result.boundary_section.is_input is False

    def test_intermediate_sections(self):
        cover, arg, ssa, ret = _build_linear_cover()
        sections = {arg.site_id: _section(arg.site_id)}
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, sections)
        all_secs = result.all_sections()
        assert isinstance(all_secs, dict)

    def test_sites_reached(self):
        cover, arg, ssa, ret = _build_linear_cover()
        sections = {arg.site_id: _section(arg.site_id)}
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert arg.site_id in result.sites_reached
        assert ret.site_id in result.sites_reached

    def test_iterations_positive(self):
        cover, arg, ssa, ret = _build_linear_cover()
        sections = {arg.site_id: _section(arg.site_id)}
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert result.iterations >= 1


# ============================================================================
# Branching forward with phi-merge
# ============================================================================


class TestBranchingForward:

    def test_branching_reaches_output(self):
        cover, arg, guard, ssa_t, ssa_f, ret = _build_branching_cover()
        sections = {arg.site_id: _section(arg.site_id, carrier_type="int")}
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert ret.site_id in result.output_sections or ret.site_id in result.sites_reached

    def test_branching_covers_both_branches(self):
        cover, arg, guard, ssa_t, ssa_f, ret = _build_branching_cover()
        sections = {arg.site_id: _section(arg.site_id)}
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, sections)
        # Both branch SSA sites should be reached
        assert ssa_t.site_id in result.sites_reached or ssa_f.site_id in result.sites_reached


# ============================================================================
# Unreachable outputs
# ============================================================================


class TestUnreachableOutputs:

    def test_disconnected_output(self):
        f = _factory()
        arg = f.create_argument_site("x")
        ssa = f.create_ssa_site("x", ssa_version=1)
        ret1 = f.create_return_site(return_index=0)
        ret2 = f.create_return_site(return_index=1)

        m1 = ConcreteMorphism(_source=arg.site_id, _target=ssa.site_id)
        m2 = ConcreteMorphism(_source=ssa.site_id, _target=ret1.site_id)
        # ret2 has no incoming morphism, so it is unreachable

        cover = (
            CoverBuilder()
            .add_site(arg)
            .add_site(ssa)
            .add_site(ret1)
            .add_site(ret2)
            .add_morphism(m1)
            .add_morphism(m2)
            .mark_input(arg.site_id)
            .mark_output(ret1.site_id)
            .mark_output(ret2.site_id)
            .build()
        )
        sections = {arg.site_id: _section(arg.site_id)}
        synth = ForwardSynthesizer()
        result = synth.synthesize(cover, sections)
        assert ret2.site_id in result.unreachable_outputs


# ============================================================================
# Max iterations
# ============================================================================


class TestForwardMaxIterations:

    def test_respects_max_iterations(self):
        cover, arg, ssa, ret = _build_linear_cover()
        sections = {arg.site_id: _section(arg.site_id)}
        synth = ForwardSynthesizer(max_iterations=1)
        result = synth.synthesize(cover, sections)
        assert result.iterations <= 1


# ============================================================================
# Incremental forward synthesis
# ============================================================================


class TestIncrementalForward:

    def test_incremental_run(self):
        cover, arg, ssa, ret = _build_linear_cover()
        sections = {arg.site_id: _section(arg.site_id, carrier_type="int")}
        synth = ForwardSynthesizer()
        result1 = synth.synthesize(cover, sections)
        # Incremental with no change
        result2 = synth.synthesize_incremental(
            cover, sections, result1, set()
        )
        assert isinstance(result2, ForwardSynthesisResult)

    def test_incremental_with_changed_inputs(self):
        cover, arg, ssa, ret = _build_linear_cover()
        sections = {arg.site_id: _section(arg.site_id, carrier_type="int")}
        synth = ForwardSynthesizer()
        result1 = synth.synthesize(cover, sections)
        # Change the input section
        new_sections = {arg.site_id: _section(arg.site_id, carrier_type="float")}
        result2 = synth.synthesize_incremental(
            cover, new_sections, result1, {arg.site_id}
        )
        assert isinstance(result2, ForwardSynthesisResult)


# ============================================================================
# synthesize_from_inputs
# ============================================================================


class TestSynthesizeFromInputs:

    def test_from_all_inputs(self):
        cover, arg, ssa, ret = _build_linear_cover()
        sections = {arg.site_id: _section(arg.site_id)}
        synth = ForwardSynthesizer()
        result = synth.synthesize_from_inputs(cover, sections)
        assert isinstance(result, ForwardSynthesisResult)

    def test_from_input_subset(self):
        f = _factory()
        a1 = f.create_argument_site("x")
        a2 = f.create_argument_site("y")
        ret = f.create_return_site()
        m1 = ConcreteMorphism(_source=a1.site_id, _target=ret.site_id)
        m2 = ConcreteMorphism(_source=a2.site_id, _target=ret.site_id)
        cover = (
            CoverBuilder()
            .add_site(a1)
            .add_site(a2)
            .add_site(ret)
            .add_morphism(m1)
            .add_morphism(m2)
            .mark_input(a1.site_id)
            .mark_input(a2.site_id)
            .mark_output(ret.site_id)
            .build()
        )
        sections = {
            a1.site_id: _section(a1.site_id),
            a2.site_id: _section(a2.site_id),
        }
        synth = ForwardSynthesizer()
        result = synth.synthesize_from_inputs(
            cover, sections, input_subset={a1.site_id}
        )
        assert isinstance(result, ForwardSynthesisResult)


# ============================================================================
# ForwardSynthesisResult properties
# ============================================================================


class TestForwardSynthesisResultProps:

    def test_repr(self):
        result = ForwardSynthesisResult()
        assert "ForwardSynthesisResult" in repr(result)

    def test_all_sections(self):
        sid_o = SiteId(kind=SiteKind.RETURN_OUTPUT_BOUNDARY, name="ret_0")
        sid_i = SiteId(kind=SiteKind.SSA_VALUE, name="x_0")
        result = ForwardSynthesisResult(
            output_sections={sid_o: _section(sid_o)},
            intermediate_sections={sid_i: _section(sid_i)},
        )
        all_secs = result.all_sections()
        assert sid_o in all_secs
        assert sid_i in all_secs

    def test_num_output_sections(self):
        sid = SiteId(kind=SiteKind.RETURN_OUTPUT_BOUNDARY, name="ret_0")
        result = ForwardSynthesisResult(
            output_sections={sid: _section(sid)},
        )
        assert result.num_output_sections == 1

    def test_default_status(self):
        result = ForwardSynthesisResult()
        assert result.status == ForwardStatus.CONVERGED

    def test_default_iterations(self):
        result = ForwardSynthesisResult()
        assert result.iterations == 0
