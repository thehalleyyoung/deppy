"""Tests for PhiMerger -- phi-node section merging at control flow join points.

Tests verify that the merger correctly computes carrier type join,
refinement intersection/weakening, trust meet, and witness merging.
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
from deppy.kernel.phi_merge import (
    PhiMerger,
    PhiMergeResult,
)


# ============================================================================
# Helpers
# ============================================================================


def _factory():
    return SiteFactory()


def _section(sid, carrier_type=None, refinements=None, trust=TrustLevel.TRUSTED_AUTO, witnesses=None):
    return LocalSection(
        site_id=sid,
        carrier_type=carrier_type,
        refinements=refinements or {},
        trust=trust,
        witnesses=witnesses or {},
    )


def _phi_site():
    """Create a phi/join site."""
    f = _factory()
    return f.create_ssa_site("phi", ssa_version=0)


# ============================================================================
# Empty / single predecessor
# ============================================================================


class TestEdgeCases:

    def test_no_predecessors(self):
        phi = _phi_site()
        merger = PhiMerger()
        result = merger.merge([], phi.site_id)
        assert result.site_id == phi.site_id
        assert result.trust == TrustLevel.ASSUMED
        assert result.refinements == {}

    def test_single_predecessor(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        sec = _section(a.site_id, carrier_type="int", refinements={"positive": True})
        merger = PhiMerger()
        result = merger.merge([sec], phi.site_id)
        assert result.site_id == phi.site_id
        assert result.carrier_type == "int"
        assert result.refinements.get("positive") is True


# ============================================================================
# Carrier type merging
# ============================================================================


class TestCarrierMerge:

    def test_same_carrier_types(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, carrier_type="int")
        sec_b = _section(b.site_id, carrier_type="int")
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b], phi.site_id)
        assert result.carrier_type == "int"

    def test_different_carrier_types_with_widening(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, carrier_type="int")
        sec_b = _section(b.site_id, carrier_type="str")
        merger = PhiMerger(allow_carrier_widening=True)
        result = merger.merge([sec_a, sec_b], phi.site_id)
        # Non-TypeBase carriers that disagree return None
        assert result.carrier_type is None

    def test_different_carrier_types_no_widening(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, carrier_type="int")
        sec_b = _section(b.site_id, carrier_type="str")
        merger = PhiMerger(allow_carrier_widening=False)
        result = merger.merge([sec_a, sec_b], phi.site_id)
        assert result.carrier_type is None

    def test_none_carrier_types(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, carrier_type=None)
        sec_b = _section(b.site_id, carrier_type=None)
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b], phi.site_id)
        assert result.carrier_type is None


# ============================================================================
# Refinement merging
# ============================================================================


class TestRefinementMerge:

    def test_agreeing_refinements_kept(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, refinements={"positive": True, "bounded": True})
        sec_b = _section(b.site_id, refinements={"positive": True, "bounded": True})
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b], phi.site_id)
        assert result.refinements.get("positive") is True
        assert result.refinements.get("bounded") is True

    def test_disagreeing_refinements_weakened(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, refinements={"sign": "positive"})
        sec_b = _section(b.site_id, refinements={"sign": "negative"})
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b], phi.site_id)
        # The value should be a disjunction tuple
        val = result.refinements.get("sign")
        assert val is not None
        assert isinstance(val, tuple)
        assert val[0] == "disjunction"

    def test_partial_keys_dropped_or_tentative(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, refinements={"only_a": True, "shared": 1})
        sec_b = _section(b.site_id, refinements={"shared": 1})
        merger = PhiMerger(strict_refinement_agreement=False)
        result = merger.merge([sec_a, sec_b], phi.site_id)
        # "shared" should survive since it agrees
        assert result.refinements.get("shared") == 1
        # "only_a" should be dropped or tentative
        assert "only_a" not in result.refinements or "tentative" in str(result.refinements)


# ============================================================================
# Trust merging
# ============================================================================


class TestTrustMerge:

    def test_trust_meet_same_level(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, trust=TrustLevel.PROOF_BACKED)
        sec_b = _section(b.site_id, trust=TrustLevel.PROOF_BACKED)
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b], phi.site_id)
        assert result.trust == TrustLevel.PROOF_BACKED

    def test_trust_meet_different_levels(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, trust=TrustLevel.PROOF_BACKED)
        sec_b = _section(b.site_id, trust=TrustLevel.ASSUMED)
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b], phi.site_id)
        # Should be the weaker of the two
        from deppy.kernel.trust_classifier import trust_rank
        assert trust_rank(result.trust) <= trust_rank(TrustLevel.PROOF_BACKED)


# ============================================================================
# Detailed merge
# ============================================================================


class TestMergeDetailed:

    def test_merge_detailed_returns_result(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, refinements={"pos": True})
        sec_b = _section(b.site_id, refinements={"pos": True})
        merger = PhiMerger()
        result = merger.merge_detailed([sec_a, sec_b], phi.site_id)
        assert isinstance(result, PhiMergeResult)
        assert result.predecessor_count == 2

    def test_merge_detailed_agreed_keys(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, refinements={"k": 1})
        sec_b = _section(b.site_id, refinements={"k": 1})
        merger = PhiMerger()
        result = merger.merge_detailed([sec_a, sec_b], phi.site_id)
        assert "k" in result.agreed_keys

    def test_merge_detailed_weakened_keys(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, refinements={"v": 10})
        sec_b = _section(b.site_id, refinements={"v": 20})
        merger = PhiMerger()
        result = merger.merge_detailed([sec_a, sec_b], phi.site_id)
        assert "v" in result.weakened_keys

    def test_merge_detailed_dropped_keys(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, refinements={"only_a": True})
        sec_b = _section(b.site_id, refinements={})
        merger = PhiMerger(strict_refinement_agreement=True)
        result = merger.merge_detailed([sec_a, sec_b], phi.site_id)
        assert "only_a" in result.dropped_keys

    def test_merge_detailed_carrier_widened(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, carrier_type="int")
        sec_b = _section(b.site_id, carrier_type="str")
        merger = PhiMerger()
        result = merger.merge_detailed([sec_a, sec_b], phi.site_id)
        assert result.carrier_widened is True

    def test_merge_detailed_strict_obstruction(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, refinements={"v": 1})
        sec_b = _section(b.site_id, refinements={"v": 2})
        merger = PhiMerger(strict_refinement_agreement=True)
        result = merger.merge_detailed([sec_a, sec_b], phi.site_id)
        assert result.has_obstruction is True

    def test_merge_detailed_empty(self):
        phi = _phi_site()
        merger = PhiMerger()
        result = merger.merge_detailed([], phi.site_id)
        assert result.predecessor_count == 0
        assert len(result.agreed_keys) == 0

    def test_merge_detailed_repr(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        sec_a = _section(a.site_id)
        merger = PhiMerger()
        result = merger.merge_detailed([sec_a], phi.site_id)
        assert "PhiMergeResult" in repr(result)


# ============================================================================
# merge_pair
# ============================================================================


class TestMergePair:

    def test_merge_pair_two_sections(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, carrier_type="int")
        sec_b = _section(b.site_id, carrier_type="int")
        merger = PhiMerger()
        result = merger.merge_pair(sec_a, sec_b, phi.site_id)
        assert result.site_id == phi.site_id
        assert result.carrier_type == "int"


# ============================================================================
# Witness merging
# ============================================================================


class TestWitnessMerge:

    def test_agreeing_witnesses_kept(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, witnesses={"w": "proof_1"})
        sec_b = _section(b.site_id, witnesses={"w": "proof_1"})
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b], phi.site_id)
        assert result.witnesses.get("w") == "proof_1"

    def test_disagreeing_witnesses_composite(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, witnesses={"w": "proof_a"})
        sec_b = _section(b.site_id, witnesses={"w": "proof_b"})
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b], phi.site_id)
        val = result.witnesses.get("w")
        assert val is not None
        assert isinstance(val, tuple)
        assert val[0] == "phi_composite"

    def test_partial_witnesses_dropped(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        sec_a = _section(a.site_id, witnesses={"w_only_a": "proof"})
        sec_b = _section(b.site_id, witnesses={})
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b], phi.site_id)
        # Witness only in one predecessor should be dropped
        assert "w_only_a" not in result.witnesses


# ============================================================================
# Three-way merge
# ============================================================================


class TestThreeWayMerge:

    def test_three_predecessors(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        c = f.create_ssa_site("x", ssa_version=2)
        sec_a = _section(a.site_id, carrier_type="int", refinements={"k": 1})
        sec_b = _section(b.site_id, carrier_type="int", refinements={"k": 1})
        sec_c = _section(c.site_id, carrier_type="int", refinements={"k": 1})
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b, sec_c], phi.site_id)
        assert result.carrier_type == "int"
        assert result.refinements.get("k") == 1

    def test_three_predecessors_partial_agreement(self):
        phi = _phi_site()
        f = _factory()
        a = f.create_ssa_site("x", ssa_version=0)
        b = f.create_ssa_site("x", ssa_version=1)
        c = f.create_ssa_site("x", ssa_version=2)
        sec_a = _section(a.site_id, refinements={"k": 1})
        sec_b = _section(b.site_id, refinements={"k": 1})
        sec_c = _section(c.site_id, refinements={"k": 2})
        merger = PhiMerger()
        result = merger.merge([sec_a, sec_b, sec_c], phi.site_id)
        # "k" disagrees in one branch -> weakened
        val = result.refinements.get("k")
        assert val is not None
        if isinstance(val, tuple):
            assert val[0] == "disjunction"
