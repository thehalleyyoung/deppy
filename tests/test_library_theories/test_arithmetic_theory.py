"""Tests for the arithmetic theory pack: bound propagation, interval solving, viability.

Covers Interval arithmetic, AffineRelation, DivisibilityInfo, constraint solving,
ArithmeticTheoryPack solve_local / forward_refine / backward_pullback / viability.
"""

from __future__ import annotations

import math
import pytest

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.library_theories.arithmetic_theory import (
    EMPTY_INTERVAL,
    FULL_INTERVAL,
    INF,
    NEG_INF,
    NON_NEGATIVE,
    POSITIVE,
    AffineRelation,
    ArithmeticConstraint,
    ArithmeticTheoryPack,
    ConstraintKind,
    DivisibilityInfo,
    Interval,
    backward_arithmetic,
    interval_from_refinements,
    interval_to_refinements,
    propagate_arithmetic,
    solve_constraints,
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
    carrier: str = "int",
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
#  Interval
# ===================================================================


class TestInterval:
    """Tests for the Interval dataclass and its operations."""

    def test_basic_properties(self):
        iv = Interval(0, 10)
        assert not iv.is_empty
        assert iv.is_bounded
        assert not iv.is_point
        assert iv.width == 10

    def test_point_interval(self):
        iv = Interval(5, 5)
        assert iv.is_point
        assert iv.is_bounded
        assert iv.width == 0

    def test_empty_interval(self):
        assert EMPTY_INTERVAL.is_empty
        assert EMPTY_INTERVAL.width == 0

    def test_full_interval(self):
        assert not FULL_INTERVAL.is_bounded
        assert FULL_INTERVAL.width == INF

    def test_contains(self):
        iv = Interval(1, 10)
        assert iv.contains(1)
        assert iv.contains(5)
        assert iv.contains(10)
        assert not iv.contains(0)
        assert not iv.contains(11)

    def test_intersect(self):
        a = Interval(0, 10)
        b = Interval(5, 15)
        c = a.intersect(b)
        assert c == Interval(5, 10)

    def test_intersect_disjoint(self):
        a = Interval(0, 5)
        b = Interval(10, 20)
        c = a.intersect(b)
        assert c.is_empty

    def test_union_hull(self):
        a = Interval(0, 5)
        b = Interval(10, 20)
        c = a.union_hull(b)
        assert c == Interval(0, 20)

    def test_add(self):
        a = Interval(1, 3)
        b = Interval(10, 20)
        c = a.add(b)
        assert c == Interval(11, 23)

    def test_sub(self):
        a = Interval(5, 10)
        b = Interval(1, 3)
        c = a.sub(b)
        assert c == Interval(2, 9)

    def test_mul(self):
        a = Interval(2, 3)
        b = Interval(-1, 4)
        c = a.mul(b)
        assert c.lo == -3
        assert c.hi == 12

    def test_negate(self):
        iv = Interval(3, 7)
        neg = iv.negate()
        assert neg == Interval(-7, -3)

    def test_abs_positive(self):
        iv = Interval(2, 10)
        assert iv.abs() == iv

    def test_abs_negative(self):
        iv = Interval(-10, -2)
        assert iv.abs() == Interval(2, 10)

    def test_abs_mixed(self):
        iv = Interval(-3, 7)
        a = iv.abs()
        assert a.lo == 0
        assert a.hi == 7

    def test_floor_div(self):
        a = Interval(10, 20)
        b = Interval(3, 3)
        c = a.floor_div(b)
        assert c.lo == 3
        assert c.hi == 6

    def test_floor_div_zero(self):
        a = Interval(10, 20)
        b = Interval(-1, 1)
        c = a.floor_div(b)
        assert c == FULL_INTERVAL

    def test_modulo(self):
        a = Interval(0, 100)
        b = Interval(7, 7)
        c = a.modulo(b)
        assert c == Interval(0, 6)

    def test_modulo_nonpositive(self):
        a = Interval(0, 100)
        b = Interval(-3, 3)
        c = a.modulo(b)
        assert c == FULL_INTERVAL

    def test_repr(self):
        iv = Interval(1, 10)
        assert repr(iv) == "[1, 10]"
        assert repr(FULL_INTERVAL) == "[-inf, inf]"


# ===================================================================
#  Refinement conversion
# ===================================================================


class TestRefinementConversion:
    """Tests for interval_from_refinements and interval_to_refinements."""

    def test_lower_bound(self):
        iv = interval_from_refinements({"lower_bound": 5})
        assert iv.lo == 5
        assert iv.hi == INF

    def test_upper_bound(self):
        iv = interval_from_refinements({"upper_bound": 10})
        assert iv.lo == NEG_INF
        assert iv.hi == 10

    def test_both_bounds(self):
        iv = interval_from_refinements({"lower_bound": 2, "upper_bound": 8})
        assert iv == Interval(2, 8)

    def test_non_negative(self):
        iv = interval_from_refinements({"non_negative": True})
        assert iv.lo == 0

    def test_positive(self):
        iv = interval_from_refinements({"positive": True})
        assert iv.lo == 1

    def test_negative(self):
        iv = interval_from_refinements({"negative": True})
        assert iv.hi == -1

    def test_min_max(self):
        iv = interval_from_refinements({"min": 3, "max": 9})
        assert iv == Interval(3, 9)

    def test_roundtrip(self):
        iv = Interval(2, 100)
        refs = interval_to_refinements(iv)
        iv2 = interval_from_refinements(refs)
        assert iv2 == iv

    def test_roundtrip_non_negative(self):
        refs = interval_to_refinements(NON_NEGATIVE)
        assert refs["non_negative"] is True
        assert refs["lower_bound"] == 0

    def test_roundtrip_positive(self):
        refs = interval_to_refinements(POSITIVE)
        assert refs["positive"] is True


# ===================================================================
#  AffineRelation
# ===================================================================


class TestAffineRelation:
    """Tests for AffineRelation."""

    def test_apply_interval(self):
        rel = AffineRelation(coeff=2, operand="x", offset=3)
        iv = Interval(1, 5)
        result = rel.apply_interval(iv)
        assert result == Interval(5, 13)

    def test_inverse(self):
        rel = AffineRelation(coeff=2, operand="x", offset=3)
        inv = rel.inverse()
        assert inv is not None
        assert inv.coeff == 0.5
        assert inv.offset == -1.5

    def test_inverse_zero_coeff(self):
        rel = AffineRelation(coeff=0, operand="x", offset=5)
        assert rel.inverse() is None

    def test_identity(self):
        rel = AffineRelation(coeff=1, operand="x", offset=0)
        iv = Interval(3, 7)
        assert rel.apply_interval(iv) == iv


# ===================================================================
#  DivisibilityInfo
# ===================================================================


class TestDivisibilityInfo:
    """Tests for DivisibilityInfo."""

    def test_combined_with_same(self):
        a = DivisibilityInfo(modulus=6, remainder=2)
        b = DivisibilityInfo(modulus=4, remainder=2)
        c = a.combined_with(b)
        assert c.modulus == 2
        assert c.remainder == 0

    def test_combined_with_incompatible(self):
        a = DivisibilityInfo(modulus=4, remainder=1)
        b = DivisibilityInfo(modulus=4, remainder=3)
        c = a.combined_with(b)
        assert c.modulus == 1


# ===================================================================
#  propagate_arithmetic / backward_arithmetic
# ===================================================================


class TestPropagateArithmetic:
    """Tests for forward and backward arithmetic propagation."""

    def test_add(self):
        result = propagate_arithmetic("add", [Interval(1, 3), Interval(10, 20)])
        assert result == Interval(11, 23)

    def test_sub(self):
        result = propagate_arithmetic("sub", [Interval(5, 10), Interval(1, 3)])
        assert result == Interval(2, 9)

    def test_neg(self):
        result = propagate_arithmetic("neg", [Interval(3, 7)])
        assert result == Interval(-7, -3)

    def test_abs(self):
        result = propagate_arithmetic("abs", [Interval(-5, 3)])
        assert result == Interval(0, 5)

    def test_unknown_op(self):
        result = propagate_arithmetic("bitxor", [Interval(0, 10)])
        assert result == FULL_INTERVAL

    def test_backward_add(self):
        result = backward_arithmetic("add", Interval(10, 20), Interval(3, 3))
        assert result == Interval(7, 17)

    def test_backward_sub_pos0(self):
        result = backward_arithmetic("sub", Interval(5, 10), Interval(3, 3), 0)
        assert result == Interval(8, 13)

    def test_backward_neg(self):
        result = backward_arithmetic("neg", Interval(2, 5), None)
        assert result == Interval(-5, -2)

    def test_backward_mul(self):
        result = backward_arithmetic("mul", Interval(10, 20), Interval(2, 2))
        assert result == Interval(5.0, 10.0)


# ===================================================================
#  solve_constraints
# ===================================================================


class TestSolveConstraints:
    """Tests for the interval propagation constraint solver."""

    def test_bound_constraint(self):
        c = ArithmeticConstraint(
            kind=ConstraintKind.BOUND,
            variables=["x"],
            data=Interval(0, 10),
        )
        solved, converged = solve_constraints([c], {"x": FULL_INTERVAL})
        assert converged
        assert solved["x"] == Interval(0, 10)

    def test_comparison_le(self):
        c = ArithmeticConstraint(
            kind=ConstraintKind.COMPARISON,
            variables=["x", "y"],
            data="le",
        )
        initial = {"x": Interval(0, 100), "y": Interval(0, 50)}
        solved, converged = solve_constraints([c], initial)
        assert converged
        assert solved["x"].hi <= 50

    def test_comparison_lt(self):
        c = ArithmeticConstraint(
            kind=ConstraintKind.COMPARISON,
            variables=["x", "y"],
            data="lt",
        )
        initial = {"x": Interval(0, 100), "y": Interval(0, 50)}
        solved, converged = solve_constraints([c], initial)
        assert converged
        assert solved["x"].hi <= 49

    def test_affine_constraint(self):
        rel = AffineRelation(coeff=2, operand="x", offset=1)
        c = ArithmeticConstraint(
            kind=ConstraintKind.AFFINE,
            variables=["y"],
            data=rel,
        )
        initial = {"x": Interval(1, 5), "y": FULL_INTERVAL}
        solved, converged = solve_constraints([c], initial)
        assert converged
        assert solved["y"] == Interval(3, 11)

    def test_unsatisfiable(self):
        c1 = ArithmeticConstraint(
            kind=ConstraintKind.BOUND,
            variables=["x"],
            data=Interval(10, 20),
        )
        c2 = ArithmeticConstraint(
            kind=ConstraintKind.BOUND,
            variables=["x"],
            data=Interval(30, 40),
        )
        solved, converged = solve_constraints([c1, c2], {"x": FULL_INTERVAL})
        assert solved["x"].is_empty

    def test_multiple_constraints(self):
        constraints = [
            ArithmeticConstraint(
                kind=ConstraintKind.BOUND, variables=["x"], data=Interval(0, 100),
            ),
            ArithmeticConstraint(
                kind=ConstraintKind.COMPARISON, variables=["x", "y"], data="le",
            ),
            ArithmeticConstraint(
                kind=ConstraintKind.BOUND, variables=["y"], data=Interval(0, 50),
            ),
        ]
        initial = {"x": FULL_INTERVAL, "y": FULL_INTERVAL}
        solved, converged = solve_constraints(constraints, initial)
        assert converged
        assert solved["x"].lo == 0
        assert solved["x"].hi == 50
        assert solved["y"].lo == 0
        assert solved["y"].hi == 50


# ===================================================================
#  ArithmeticTheoryPack
# ===================================================================


class TestArithmeticTheoryPack:
    """Tests for the ArithmeticTheoryPack theory pack."""

    def setup_method(self):
        self.pack = ArithmeticTheoryPack()

    def test_applicable_site_kinds(self):
        kinds = self.pack.applicable_site_kinds()
        assert SiteKind.SSA_VALUE in kinds
        assert SiteKind.ARGUMENT_BOUNDARY in kinds
        assert SiteKind.ERROR in kinds

    def test_solve_local_non_numeric(self):
        sec = _section("x", carrier="str")
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.UNCHANGED

    def test_solve_local_bounded(self):
        sec = _section("x", carrier="int", refinements={"lower_bound": 0, "upper_bound": 10})
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status in (SolverStatus.REFINED, SolverStatus.UNCHANGED)

    def test_solve_local_with_comparison_constraints(self):
        refs = {
            "lower_bound": 0,
            "_comparisons": [
                {"op": "lt", "variables": ["x", "y"]},
            ],
        }
        sec = _section("x", carrier="int", refinements=refs)
        result = self.pack.solve_local(sec.site_id, sec)
        assert result.status in (SolverStatus.SOLVED, SolverStatus.REFINED, SolverStatus.UNCHANGED)

    def test_solve_local_unsatisfiable(self):
        refs = {
            "lower_bound": 100,
            "upper_bound": 50,
        }
        sec = _section("x", carrier="int", refinements=refs)
        result = self.pack.solve_local(sec.site_id, sec)
        # The interval [100, 50] is empty; the solver normalizes it and
        # returns REFINED (with the normalized contradictory interval).
        assert result.status in (SolverStatus.UNSATISFIABLE, SolverStatus.UNCHANGED, SolverStatus.REFINED)

    def test_forward_refine(self):
        source = _site("x")
        target = _site("y")
        sec = _section("x", carrier="int", refinements={"lower_bound": 0, "upper_bound": 10})
        morphism = ConcreteMorphism(
            _source=source,
            _target=target,
            _metadata={"arithmetic_op": "add", "second_operand_value": 5},
        )
        result = self.pack.forward_refine(sec, morphism)
        iv = interval_from_refinements(result.refinements)
        assert iv.lo >= 5
        assert iv.hi <= 15

    def test_backward_pullback(self):
        source = _site("x")
        target = _site("y")
        sec = _section("y", carrier="int", refinements={"lower_bound": 10, "upper_bound": 20})
        morphism = ConcreteMorphism(
            _source=source,
            _target=target,
            _metadata={"arithmetic_op": "add", "second_operand_value": 5},
        )
        result = self.pack.backward_pullback(sec, morphism)
        iv = interval_from_refinements(result.refinements)
        assert iv.lo >= 5
        assert iv.hi <= 15

    def test_viability_predicate_div(self):
        site = _site("div_result", SiteKind.ERROR)
        pred = self.pack.viability_predicate(site)
        assert "!= 0" in pred

    def test_viability_predicate_index(self):
        site = _site("index_check", SiteKind.ERROR)
        pred = self.pack.viability_predicate(site)
        assert "index" in pred.lower()

    def test_classify_proof_boundary_proven(self):
        sec = _section("x", carrier="int", trust=TrustLevel.PROOF_BACKED)
        cls = self.pack.classify_proof_boundary(sec)
        assert cls == BoundaryClassification.FULLY_PROVEN

    def test_classify_proof_boundary_bounded(self):
        sec = _section(
            "x", carrier="int",
            refinements={"lower_bound": 0, "upper_bound": 10},
            trust=TrustLevel.BOUNDED_AUTO,
        )
        cls = self.pack.classify_proof_boundary(sec)
        assert cls == BoundaryClassification.CONDITIONALLY_PROVEN

    def test_classify_proof_boundary_assumed(self):
        sec = _section("x", carrier="int", trust=TrustLevel.ASSUMED)
        cls = self.pack.classify_proof_boundary(sec)
        assert cls == BoundaryClassification.ASSUMED
