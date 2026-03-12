"""Tests for restriction maps — the morphisms of the site category S."""

from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    RestrictionKind,
    apply_restriction,
    make_actual_to_formal_restriction,
    make_control_restriction,
    make_error_pullback_restriction,
    make_error_viability_restriction,
    make_lineage_restriction,
    make_pack_transport,
    make_phi_merge_restriction,
    make_return_to_caller_restriction,
    sites_overlap,
)


def _sid(kind: SiteKind, name: str) -> SiteId:
    return SiteId(kind=kind, name=name)


SRC = _sid(SiteKind.SSA_VALUE, "x_0")
TGT = _sid(SiteKind.SSA_VALUE, "x_1")
GUARD = _sid(SiteKind.BRANCH_GUARD, "guard_1")
ERR = _sid(SiteKind.ERROR, "err_1")
INP = _sid(SiteKind.ARGUMENT_BOUNDARY, "foo.x")
PARAM = _sid(SiteKind.ARGUMENT_BOUNDARY, "bar.x")


class TestRestrictionKindCatalogue:
    def test_has_all_fundamental_kinds(self):
        assert RestrictionKind.LINEAGE
        assert RestrictionKind.CONTROL_TRUE
        assert RestrictionKind.CONTROL_FALSE
        assert RestrictionKind.PHI_MERGE
        assert RestrictionKind.ACTUAL_TO_FORMAL
        assert RestrictionKind.FORMAL_TO_RETURN
        assert RestrictionKind.PACK_TRANSPORT
        assert RestrictionKind.ERROR_VIABILITY
        assert RestrictionKind.ERROR_PULLBACK


class TestLineageRestriction:
    def test_creates_morphism(self):
        m = make_lineage_restriction(SRC, TGT, preserved_keys=frozenset({"type", "shape"}))
        assert m.source == SRC
        assert m.target == TGT
        assert m.metadata is not None
        r = m.metadata["restriction"]
        assert r.kind == RestrictionKind.LINEAGE
        assert "type" in r.preserved_keys

    def test_default_no_keys(self):
        m = make_lineage_restriction(SRC, TGT)
        r = m.metadata["restriction"]
        assert r.preserved_keys == frozenset()


class TestControlRestriction:
    def test_true_branch(self):
        m = make_control_restriction(
            GUARD, SRC, polarity=True, guard_predicate="x is not None",
        )
        r = m.metadata["restriction"]
        assert r.kind == RestrictionKind.CONTROL_TRUE
        assert r.guard_predicate == "x is not None"

    def test_false_branch(self):
        m = make_control_restriction(GUARD, SRC, polarity=False, guard_predicate="x > 0")
        r = m.metadata["restriction"]
        assert r.kind == RestrictionKind.CONTROL_FALSE


class TestPhiMergeRestriction:
    def test_basic(self):
        phi = _sid(SiteKind.SSA_VALUE, "x_phi")
        m = make_phi_merge_restriction(SRC, phi)
        r = m.metadata["restriction"]
        assert r.kind == RestrictionKind.PHI_MERGE


class TestActualToFormalRestriction:
    def test_mapping(self):
        m = make_actual_to_formal_restriction(
            INP, PARAM, actual_name="my_list", formal_name="lst",
        )
        r = m.metadata["restriction"]
        assert r.kind == RestrictionKind.ACTUAL_TO_FORMAL
        assert r.actual_to_formal == {"my_list": "lst"}


class TestApplyRestriction:
    def test_lineage_preserves_refinements(self):
        m = make_lineage_restriction(
            SRC, TGT,
            preserved_keys=frozenset({"lower_bound", "upper_bound"}),
        )
        section = LocalSection(
            site_id=SRC,
            carrier_type="int",
            refinements={"lower_bound": 0, "upper_bound": 10, "parity": "even"},
            trust=TrustLevel.TRUSTED_AUTO,
        )
        result = apply_restriction(m, section)
        assert result.site_id == TGT
        assert result.refinements["lower_bound"] == 0
        assert result.refinements["upper_bound"] == 10
        assert "parity" not in result.refinements

    def test_control_adds_guard(self):
        m = make_control_restriction(
            GUARD, SRC, polarity=True, guard_predicate="x is not None",
        )
        section = LocalSection(
            site_id=GUARD,
            carrier_type="Optional[int]",
            refinements={"nullable": True},
            trust=TrustLevel.BOUNDED_AUTO,
        )
        result = apply_restriction(m, section)
        assert result.site_id == SRC
        # Guard predicate should be added to refinements
        guard_keys = [k for k in result.refinements if "guard" in k]
        assert len(guard_keys) >= 1

    def test_trust_preserved(self):
        m = make_lineage_restriction(SRC, TGT)
        section = LocalSection(
            site_id=SRC,
            carrier_type="list",
            trust=TrustLevel.PROOF_BACKED,
        )
        result = apply_restriction(m, section)
        assert result.trust == TrustLevel.PROOF_BACKED

    def test_default_restriction_copies_section(self):
        """Morphism without restriction data copies the section."""
        m = ConcreteMorphism(_source=SRC, _target=TGT)
        section = LocalSection(
            site_id=SRC,
            carrier_type="int",
            refinements={"val": 42},
        )
        result = apply_restriction(m, section)
        assert result.site_id == TGT
        assert result.refinements == {"val": 42}


class TestPackTransport:
    def test_basic(self):
        order = _sid(SiteKind.TENSOR_ORDER, "sort_1")
        index = _sid(SiteKind.TENSOR_INDEXING, "idx_1")
        m = make_pack_transport(
            order, index, pack_name="shape", transport_rule="sort_to_index",
        )
        r = m.metadata["restriction"]
        assert r.kind == RestrictionKind.PACK_TRANSPORT
        assert r.pack_name == "shape"


class TestErrorRestrictions:
    def test_viability(self):
        m = make_error_viability_restriction(
            SRC, ERR, viability_predicate="0 <= i < len(lst)",
        )
        r = m.metadata["restriction"]
        assert r.kind == RestrictionKind.ERROR_VIABILITY
        assert r.viability_predicate == "0 <= i < len(lst)"

    def test_pullback(self):
        m = make_error_pullback_restriction(ERR, INP)
        r = m.metadata["restriction"]
        assert r.kind == RestrictionKind.ERROR_PULLBACK


class TestSitesOverlap:
    def test_direct_morphism_overlaps(self):
        m = ConcreteMorphism(_source=SRC, _target=TGT)
        assert sites_overlap(SRC, TGT, [m]) is True

    def test_shared_target_overlaps(self):
        a = _sid(SiteKind.SSA_VALUE, "a")
        b = _sid(SiteKind.SSA_VALUE, "b")
        c = _sid(SiteKind.SSA_VALUE, "c")
        m1 = ConcreteMorphism(_source=a, _target=c)
        m2 = ConcreteMorphism(_source=b, _target=c)
        assert sites_overlap(a, b, [m1, m2]) is True

    def test_no_connection_no_overlap(self):
        a = _sid(SiteKind.SSA_VALUE, "a")
        b = _sid(SiteKind.SSA_VALUE, "b")
        assert sites_overlap(a, b, []) is False
