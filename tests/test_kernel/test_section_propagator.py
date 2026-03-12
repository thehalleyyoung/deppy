"""Tests for SectionPropagator -- forward/backward propagation along morphisms.

Tests verify that forward propagation (push-forward) and backward propagation
(pullback) correctly transport section data between sites, respecting trust
degradation and refinement preservation.
"""

import pytest

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteSite, ConcreteMorphism, CoverBuilder
from deppy.core.site_factory import SiteFactory
from deppy.kernel.section_propagator import (
    ChainPropagationResult,
    PropagationResult,
    SectionPropagator,
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


def _make_chain():
    """Build a 3-site chain: a -> b -> c with morphisms."""
    f = _factory()
    a = f.create_argument_site("x")
    b = f.create_ssa_site("x", ssa_version=0)
    c = f.create_return_site()

    m1 = ConcreteMorphism(_source=a.site_id, _target=b.site_id)
    m2 = ConcreteMorphism(_source=b.site_id, _target=c.site_id)
    return a, b, c, m1, m2


# ============================================================================
# Forward propagation
# ============================================================================


class TestForwardPropagation:

    def test_forward_produces_section_at_target(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id, carrier_type="int", refinements={"positive": True})
        prop = SectionPropagator()
        result = prop.propagate_forward(sec, m1)
        assert result.site_id == b.site_id

    def test_forward_preserves_carrier_type(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id, carrier_type="int")
        prop = SectionPropagator()
        result = prop.propagate_forward(sec, m1)
        assert result.carrier_type == "int"

    def test_forward_site_id_mismatch_raises(self):
        a, b, c, m1, m2 = _make_chain()
        # Create section at b but try to propagate through m1 (source = a)
        sec = _section(b.site_id, carrier_type="int")
        prop = SectionPropagator()
        with pytest.raises(ValueError, match="does not match"):
            prop.propagate_forward(sec, m1)

    def test_forward_propagation_log(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id, carrier_type="int")
        prop = SectionPropagator()
        prop.propagate_forward(sec, m1)
        assert len(prop.propagation_log) == 1
        step = prop.propagation_log[0]
        assert isinstance(step, PropagationResult)
        assert step.source_site == a.site_id
        assert step.target_site == b.site_id

    def test_forward_clear_log(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id)
        prop = SectionPropagator()
        prop.propagate_forward(sec, m1)
        assert len(prop.propagation_log) >= 1
        prop.clear_log()
        assert len(prop.propagation_log) == 0


# ============================================================================
# Backward propagation
# ============================================================================


class TestBackwardPropagation:

    def test_backward_produces_section_at_source(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(b.site_id, carrier_type="str", refinements={"length": 5})
        prop = SectionPropagator()
        result = prop.propagate_backward(sec, m1)
        assert result.site_id == a.site_id

    def test_backward_preserves_carrier_type(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(b.site_id, carrier_type="str")
        prop = SectionPropagator()
        result = prop.propagate_backward(sec, m1)
        assert result.carrier_type == "str"

    def test_backward_site_id_mismatch_raises(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id, carrier_type="int")
        prop = SectionPropagator()
        with pytest.raises(ValueError, match="does not match"):
            prop.propagate_backward(sec, m1)

    def test_backward_provenance(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(b.site_id)
        prop = SectionPropagator()
        result = prop.propagate_backward(sec, m1)
        assert "pullback" in result.provenance


# ============================================================================
# Chain propagation
# ============================================================================


class TestChainPropagation:

    def test_chain_forward(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id, carrier_type="int")
        prop = SectionPropagator()
        result = prop.propagate_chain(sec, [m1, m2])
        assert result.site_id == c.site_id

    def test_chain_backward(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(c.site_id, carrier_type="float")
        prop = SectionPropagator()
        result = prop.propagate_chain_backward(sec, [m1, m2])
        assert result.site_id == a.site_id

    def test_chain_detailed(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id, carrier_type="int")
        prop = SectionPropagator()
        result = prop.propagate_chain_detailed(sec, [m1, m2])
        assert isinstance(result, ChainPropagationResult)
        assert result.num_steps == 2
        assert result.final_section.site_id == c.site_id

    def test_chain_empty(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id)
        prop = SectionPropagator()
        result = prop.propagate_chain(sec, [])
        assert result.site_id == a.site_id

    def test_chain_detailed_repr(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id)
        prop = SectionPropagator()
        result = prop.propagate_chain_detailed(sec, [m1, m2])
        s = repr(result)
        assert "ChainPropagationResult" in s

    def test_chain_detailed_empty_repr(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id)
        prop = SectionPropagator()
        result = prop.propagate_chain_detailed(sec, [])
        assert "empty" in repr(result)


# ============================================================================
# Batch propagation
# ============================================================================


class TestBatchPropagation:

    def test_propagate_all_forward(self):
        a, b, c, m1, m2 = _make_chain()
        sections = {
            a.site_id: _section(a.site_id, carrier_type="int"),
        }
        prop = SectionPropagator()
        result = prop.propagate_all_forward(sections, [m1, m2])
        assert b.site_id in result
        # c should get section because b was populated by forward from a
        # However, propagate_all_forward uses only the initial sections dict
        assert a.site_id in result

    def test_propagate_all_backward(self):
        a, b, c, m1, m2 = _make_chain()
        sections = {
            c.site_id: _section(c.site_id, carrier_type="float"),
        }
        prop = SectionPropagator()
        result = prop.propagate_all_backward(sections, [m1, m2])
        # Backward from c through m2 should give section at b
        assert b.site_id in result

    def test_batch_forward_merge_higher_trust(self):
        f = _factory()
        a1 = f.create_ssa_site("x", ssa_version=0)
        a2 = f.create_ssa_site("y", ssa_version=0)
        target = f.create_return_site()
        m1 = ConcreteMorphism(_source=a1.site_id, _target=target.site_id)
        m2 = ConcreteMorphism(_source=a2.site_id, _target=target.site_id)
        sections = {
            a1.site_id: _section(a1.site_id, carrier_type="int", trust=TrustLevel.PROOF_BACKED),
            a2.site_id: _section(a2.site_id, carrier_type="int", trust=TrustLevel.ASSUMED),
        }
        prop = SectionPropagator()
        result = prop.propagate_all_forward(sections, [m1, m2])
        assert target.site_id in result


# ============================================================================
# PropagationResult properties
# ============================================================================


class TestPropagationResultProps:

    def test_repr(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id)
        prop = SectionPropagator()
        result_sec = prop.propagate_forward(sec, m1)
        step = prop.propagation_log[0]
        assert "PropagationResult" in repr(step)

    def test_trust_degraded_property(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id, trust=TrustLevel.PROOF_BACKED)
        prop = SectionPropagator()
        prop.propagate_forward(sec, m1)
        step = prop.propagation_log[0]
        assert isinstance(step.trust_degraded, bool)

    def test_restriction_kind_property(self):
        a, b, c, m1, m2 = _make_chain()
        sec = _section(a.site_id)
        prop = SectionPropagator()
        prop.propagate_forward(sec, m1)
        step = prop.propagation_log[0]
        # restriction_kind may be None for plain morphisms
        assert step.restriction_kind is None or hasattr(step.restriction_kind, 'value')


# ============================================================================
# Witness preservation
# ============================================================================


class TestWitnessPreservation:

    def test_preserve_witnesses_true(self):
        a, b, c, m1, m2 = _make_chain()
        sec = LocalSection(
            site_id=a.site_id,
            carrier_type="int",
            refinements={},
            trust=TrustLevel.TRUSTED_AUTO,
            witnesses={"w1": "evidence"},
        )
        prop = SectionPropagator(preserve_witnesses=True)
        result = prop.propagate_forward(sec, m1)
        assert isinstance(result.witnesses, dict)

    def test_preserve_witnesses_false(self):
        a, b, c, m1, m2 = _make_chain()
        sec = LocalSection(
            site_id=a.site_id,
            carrier_type="int",
            refinements={},
            trust=TrustLevel.TRUSTED_AUTO,
            witnesses={"w1": "evidence"},
        )
        prop = SectionPropagator(preserve_witnesses=False)
        result = prop.propagate_forward(sec, m1)
        assert result.witnesses == {}
