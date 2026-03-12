"""Tests for the nullability theory pack: None/Optional narrowing.

Covers NullState, null_meet/null_join, OptionalInfo, extract_optional_info,
operation_null_safety, and NullabilityTheoryPack solve_local / forward /
backward / viability / classify.
"""

from __future__ import annotations

import pytest

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.library_theories.nullability_theory import (
    NullState,
    NullabilityTheoryPack,
    OptionalInfo,
    extract_optional_info,
    null_join,
    null_meet,
    null_state_from_refinements,
    null_state_to_refinements,
    operation_null_safety,
)
from deppy.library_theories.theory_pack_base import (
    BoundaryClassification,
    SolverStatus,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _site(name: str, kind: SiteKind = SiteKind.SSA_VALUE) -> SiteId:
    return SiteId(kind=kind, name=name)


def _section(
    name: str,
    carrier: str = "Optional[int]",
    refinements: dict | None = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
    kind: SiteKind = SiteKind.SSA_VALUE,
) -> LocalSection:
    sid = _site(name, kind)
    return LocalSection(
        site_id=sid,
        carrier_type=carrier,
        refinements=refinements or {},
        trust=trust,
    )


# ===================================================================
#  NullState
# ===================================================================


class TestNullState:
    """Tests for NullState enum and properties."""

    def test_is_safe(self):
        assert NullState.DEFINITELY_NON_NULL.is_safe
        assert not NullState.POSSIBLY_NULL.is_safe
        assert not NullState.UNKNOWN.is_safe
        assert not NullState.DEFINITELY_NULL.is_safe

    def test_is_dangerous(self):
        assert NullState.POSSIBLY_NULL.is_dangerous
        assert NullState.UNKNOWN.is_dangerous
        assert not NullState.DEFINITELY_NON_NULL.is_dangerous
        assert not NullState.DEFINITELY_NULL.is_dangerous

    def test_from_refinements_non_null(self):
        state = null_state_from_refinements({"non_null": True})
        assert state == NullState.DEFINITELY_NON_NULL

    def test_from_refinements_is_not_none(self):
        state = null_state_from_refinements({"is_not_none": True})
        assert state == NullState.DEFINITELY_NON_NULL

    def test_from_refinements_is_none(self):
        state = null_state_from_refinements({"is_none": True})
        assert state == NullState.DEFINITELY_NULL

    def test_from_refinements_nullable(self):
        state = null_state_from_refinements({"nullable": True})
        assert state == NullState.POSSIBLY_NULL

    def test_from_refinements_optional(self):
        state = null_state_from_refinements({"optional": True})
        assert state == NullState.POSSIBLY_NULL

    def test_from_refinements_empty(self):
        state = null_state_from_refinements({})
        assert state == NullState.UNKNOWN

    def test_to_refinements_roundtrip_non_null(self):
        refs = null_state_to_refinements(NullState.DEFINITELY_NON_NULL)
        assert refs["non_null"] is True
        state2 = null_state_from_refinements(refs)
        assert state2 == NullState.DEFINITELY_NON_NULL

    def test_to_refinements_roundtrip_null(self):
        refs = null_state_to_refinements(NullState.DEFINITELY_NULL)
        assert refs["is_none"] is True
        state2 = null_state_from_refinements(refs)
        assert state2 == NullState.DEFINITELY_NULL


# ===================================================================
#  Nullability lattice
# ===================================================================


class TestNullLattice:
    """Tests for null_meet and null_join."""

    def test_meet_same(self):
        assert null_meet(NullState.POSSIBLY_NULL, NullState.POSSIBLY_NULL) == NullState.POSSIBLY_NULL

    def test_meet_unknown_lhs(self):
        assert null_meet(NullState.UNKNOWN, NullState.DEFINITELY_NON_NULL) == NullState.DEFINITELY_NON_NULL

    def test_meet_unknown_rhs(self):
        assert null_meet(NullState.DEFINITELY_NULL, NullState.UNKNOWN) == NullState.DEFINITELY_NULL

    def test_meet_possibly_with_non_null(self):
        result = null_meet(NullState.POSSIBLY_NULL, NullState.DEFINITELY_NON_NULL)
        assert result == NullState.DEFINITELY_NON_NULL

    def test_join_same(self):
        assert null_join(NullState.DEFINITELY_NON_NULL, NullState.DEFINITELY_NON_NULL) == NullState.DEFINITELY_NON_NULL

    def test_join_null_nonnull(self):
        result = null_join(NullState.DEFINITELY_NULL, NullState.DEFINITELY_NON_NULL)
        assert result == NullState.POSSIBLY_NULL

    def test_join_unknown_anything(self):
        assert null_join(NullState.UNKNOWN, NullState.DEFINITELY_NON_NULL) == NullState.UNKNOWN

    def test_join_possibly_with_null(self):
        result = null_join(NullState.POSSIBLY_NULL, NullState.DEFINITELY_NULL)
        assert result == NullState.POSSIBLY_NULL


# ===================================================================
#  OptionalInfo
# ===================================================================


class TestOptionalInfo:
    """Tests for OptionalInfo."""

    def test_narrow_non_null(self):
        info = OptionalInfo(inner_type="int", null_state=NullState.POSSIBLY_NULL)
        narrowed = info.narrow_non_null()
        assert narrowed.null_state == NullState.DEFINITELY_NON_NULL
        assert narrowed.guard_checked

    def test_narrow_null(self):
        info = OptionalInfo(inner_type="int", null_state=NullState.POSSIBLY_NULL)
        narrowed = info.narrow_null()
        assert narrowed.null_state == NullState.DEFINITELY_NULL

    def test_is_safe_to_access(self):
        safe = OptionalInfo(null_state=NullState.DEFINITELY_NON_NULL)
        assert safe.is_safe_to_access()
        unsafe = OptionalInfo(null_state=NullState.POSSIBLY_NULL)
        assert not unsafe.is_safe_to_access()

    def test_extract_from_section(self):
        sec = _section("x", refinements={"non_null": True, "inner_type": "int"})
        info = extract_optional_info(sec)
        assert info.null_state == NullState.DEFINITELY_NON_NULL
        assert info.inner_type == "int"


# ===================================================================
#  Operation null safety
# ===================================================================


class TestOperationNullSafety:
    """Tests for operation_null_safety classification."""

    def test_safe_ops(self):
        assert operation_null_safety("is_none_check") == "safe"
        assert operation_null_safety("is_not_none_check") == "safe"

    def test_produces_null(self):
        assert operation_null_safety("dict.get") == "produces_null"
        assert operation_null_safety("re.match") == "produces_null"

    def test_requires_non_null(self):
        assert operation_null_safety("attr_access") == "requires_non_null"
        assert operation_null_safety("subscript") == "requires_non_null"

    def test_unknown(self):
        assert operation_null_safety("some_random_op") == "unknown"


# ===================================================================
#  NullabilityTheoryPack
# ===================================================================


class TestNullabilityTheoryPack:
    """Tests for the NullabilityTheoryPack."""

    def setup_method(self):
        self.pack = NullabilityTheoryPack()

    def test_applicable_site_kinds(self):
        kinds = self.pack.applicable_site_kinds()
        assert SiteKind.SSA_VALUE in kinds
        assert SiteKind.BRANCH_GUARD in kinds
        assert SiteKind.ERROR in kinds

    def test_solve_confirmed_non_null(self):
        sec = _section("x", refinements={"non_null": True})
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.SOLVED
        assert result.section.refinements.get("non_null") is True

    def test_solve_confirmed_null(self):
        sec = _section("x", refinements={"is_none": True})
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.SOLVED
        assert result.section.refinements.get("is_none") is True

    def test_solve_optional_type(self):
        sec = _section("x", carrier="Optional[str]")
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.REFINED
        assert result.section.refinements.get("nullable") is True

    def test_solve_requires_non_null_op(self):
        sec = _section("x", refinements={"operation": "attr_access", "nullable": True})
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.REFINED
        assert "non-null" in result.explanation.lower() or "requires" in result.explanation.lower()

    def test_solve_produces_null_op(self):
        sec = _section("x", refinements={"operation": "dict.get"})
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.REFINED

    def test_forward_refine_propagates_non_null(self):
        source = _site("x")
        target = _site("y")
        sec = _section("x", refinements={"non_null": True})
        morphism = ConcreteMorphism(_source=source, _target=target)
        result = self.pack.forward_refine(sec, morphism)
        assert result.refinements.get("non_null") is True

    def test_backward_pullback_attr_access(self):
        source = _site("x")
        target = _site("y")
        sec = _section("y", refinements={"attr_access": True})
        morphism = ConcreteMorphism(_source=source, _target=target)
        result = self.pack.backward_pullback(sec, morphism)
        assert result.refinements.get("non_null") is True

    def test_viability_predicate_attr(self):
        site = _site("attr_error", SiteKind.ERROR)
        pred = self.pack.viability_predicate(site)
        assert "not None" in pred or "None" in pred

    def test_classify_non_null_proof_backed(self):
        sec = _section("x", refinements={"non_null": True}, trust=TrustLevel.PROOF_BACKED)
        cls = self.pack.classify_proof_boundary(sec)
        assert cls == BoundaryClassification.FULLY_PROVEN

    def test_classify_guard_checked(self):
        sec = _section(
            "x",
            refinements={"non_null": True, "null_checked": True},
            trust=TrustLevel.TRUSTED_AUTO,
        )
        cls = self.pack.classify_proof_boundary(sec)
        assert cls in (BoundaryClassification.CONDITIONALLY_PROVEN, BoundaryClassification.RUNTIME_GUARDED)

    def test_classify_possibly_null(self):
        sec = _section("x", refinements={"nullable": True})
        cls = self.pack.classify_proof_boundary(sec)
        assert cls == BoundaryClassification.REQUIRES_PROOF

    def test_classify_unknown(self):
        sec = _section("x", refinements={})
        cls = self.pack.classify_proof_boundary(sec)
        assert cls == BoundaryClassification.ASSUMED
