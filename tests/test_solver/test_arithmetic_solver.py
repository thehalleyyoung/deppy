"""Tests for ArithmeticSolver -- interval arithmetic solving for QF_LIA.

Tests verify Interval operations, IntervalStore feasibility tracking,
and ArithmeticSolver satisfiability checking via interval propagation.
"""

import pytest

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.predicates.base import Var, IntLit
from deppy.predicates.arithmetic import (
    Comparison,
    IntRange,
    LinearInequality,
)
from deppy.predicates.boolean import And, Or, Not
from deppy.solver.arithmetic_solver import (
    ArithmeticSolver,
    Interval,
    IntervalStore,
    _ceildiv,
    _floordiv,
)
from deppy.solver.solver_interface import (
    SolverObligation,
    SolverResult,
    SolverStatus,
)


# ============================================================================
# Interval
# ============================================================================


class TestInterval:

    def test_empty_interval(self):
        iv = Interval(lo=5, hi=3)
        assert iv.is_empty

    def test_non_empty_interval(self):
        iv = Interval(lo=1, hi=10)
        assert not iv.is_empty

    def test_singleton_interval(self):
        iv = Interval(lo=5, hi=5)
        assert iv.is_singleton

    def test_unbounded_interval(self):
        iv = Interval()
        assert iv.is_unbounded

    def test_half_bounded_lo(self):
        iv = Interval(lo=0)
        assert not iv.is_unbounded
        assert not iv.is_empty

    def test_half_bounded_hi(self):
        iv = Interval(hi=10)
        assert not iv.is_unbounded

    def test_intersect_overlapping(self):
        a = Interval(lo=1, hi=10)
        b = Interval(lo=5, hi=15)
        c = a.intersect(b)
        assert c.lo == 5
        assert c.hi == 10

    def test_intersect_disjoint(self):
        a = Interval(lo=1, hi=3)
        b = Interval(lo=5, hi=10)
        c = a.intersect(b)
        assert c.is_empty

    def test_intersect_unbounded(self):
        a = Interval(lo=5)
        b = Interval(hi=10)
        c = a.intersect(b)
        assert c.lo == 5
        assert c.hi == 10

    def test_contains_value(self):
        iv = Interval(lo=1, hi=10)
        assert iv.contains(5)
        assert iv.contains(1)
        assert iv.contains(10)
        assert not iv.contains(0)
        assert not iv.contains(11)

    def test_contains_unbounded(self):
        iv = Interval()
        assert iv.contains(0)
        assert iv.contains(1000)
        assert iv.contains(-1000)

    def test_pick_value_singleton(self):
        iv = Interval(lo=7, hi=7)
        assert iv.pick_value() == 7

    def test_pick_value_empty(self):
        iv = Interval(lo=10, hi=5)
        assert iv.pick_value() is None

    def test_pick_value_unbounded(self):
        iv = Interval()
        assert iv.pick_value() == 0

    def test_pick_value_lo_bounded(self):
        iv = Interval(lo=3)
        assert iv.pick_value() == 3

    def test_pick_value_hi_bounded(self):
        iv = Interval(hi=8)
        assert iv.pick_value() == 8

    def test_repr(self):
        iv = Interval(lo=1, hi=10)
        assert "[1, 10]" in repr(iv)

    def test_repr_unbounded(self):
        iv = Interval()
        assert "-inf" in repr(iv)
        assert "+inf" in repr(iv)


# ============================================================================
# IntervalStore
# ============================================================================


class TestIntervalStore:

    def test_default_interval_unbounded(self):
        store = IntervalStore()
        iv = store.get("x")
        assert iv.is_unbounded

    def test_tighten_lower(self):
        store = IntervalStore()
        assert store.tighten_lower("x", 5) is True
        assert store.get("x").lo == 5

    def test_tighten_upper(self):
        store = IntervalStore()
        assert store.tighten_upper("x", 10) is True
        assert store.get("x").hi == 10

    def test_tighten_to_empty(self):
        store = IntervalStore()
        store.tighten_lower("x", 10)
        result = store.tighten_upper("x", 5)
        assert result is False

    def test_set_equal(self):
        store = IntervalStore()
        assert store.set_equal("x", 7) is True
        iv = store.get("x")
        assert iv.lo == 7 and iv.hi == 7

    def test_set_equal_conflict(self):
        store = IntervalStore()
        store.tighten_lower("x", 10)
        result = store.set_equal("x", 5)
        assert result is False

    def test_add_disequality(self):
        store = IntervalStore()
        assert store.add_disequality("x", 5) is True

    def test_disequality_conflict_with_equality(self):
        store = IntervalStore()
        store.set_equal("x", 5)
        assert store.add_disequality("x", 5) is False

    def test_disequality_conflict_with_singleton(self):
        store = IntervalStore()
        store.tighten_lower("x", 5)
        store.tighten_upper("x", 5)
        assert store.add_disequality("x", 5) is False

    def test_is_feasible_initially(self):
        store = IntervalStore()
        assert store.is_feasible()

    def test_is_feasible_after_contradiction(self):
        store = IntervalStore()
        store.tighten_lower("x", 10)
        store.tighten_upper("x", 5)
        assert not store.is_feasible()

    def test_push_pop(self):
        store = IntervalStore()
        store.tighten_lower("x", 5)
        store.push()
        store.tighten_lower("x", 10)
        assert store.get("x").lo == 10
        store.pop()
        assert store.get("x").lo == 5

    def test_build_model(self):
        store = IntervalStore()
        store.tighten_lower("x", 1)
        store.tighten_upper("x", 10)
        model = store.build_model()
        assert "x" in model
        assert 1 <= model["x"] <= 10

    def test_clear(self):
        store = IntervalStore()
        store.tighten_lower("x", 5)
        store.clear()
        iv = store.get("x")
        assert iv.is_unbounded


# ============================================================================
# Integer arithmetic helpers
# ============================================================================


class TestArithmeticHelpers:

    def test_ceildiv_positive(self):
        assert _ceildiv(7, 3) == 3
        assert _ceildiv(6, 3) == 2

    def test_ceildiv_negative_numerator(self):
        assert _ceildiv(-7, 3) == -2

    def test_ceildiv_zero_denominator(self):
        assert _ceildiv(5, 0) == 0

    def test_floordiv_positive(self):
        assert _floordiv(7, 3) == 2
        assert _floordiv(6, 3) == 2

    def test_floordiv_negative_numerator(self):
        assert _floordiv(-7, 3) == -3

    def test_floordiv_zero_denominator(self):
        assert _floordiv(5, 0) == 0


# ============================================================================
# ArithmeticSolver basic
# ============================================================================


def _make_obligation(formula, context=()):
    sid = SiteId(kind=SiteKind.SSA_VALUE, name="test_site")
    return SolverObligation(
        site_id=sid,
        formula=formula,
        context=tuple(context),
    )


class TestArithmeticSolverBasic:

    def test_simple_range_sat(self):
        solver = ArithmeticSolver()
        # x >= 0 AND x <= 10
        formula = IntRange("x", lo=0, hi=10)
        obl = _make_obligation(formula)
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT
        if result.model:
            assert 0 <= result.model.get("x", 0) <= 10

    def test_contradictory_range_unsat(self):
        solver = ArithmeticSolver()
        # x >= 10 AND x <= 5 -- contradictory
        formula = And([IntRange("x", lo=10, hi=10), IntRange("x", lo=5, hi=5)])
        # This requires x=10 and x=5 simultaneously
        obl = _make_obligation(And([IntRange("x", lo=10), IntRange("x", hi=5)]))
        result = solver.check(obl)
        assert result.status == SolverStatus.UNSAT

    def test_comparison_sat(self):
        solver = ArithmeticSolver()
        # x > 0 encoded as Comparison
        formula = Comparison(">", Var("x"), IntLit(0))
        obl = _make_obligation(formula)
        result = solver.check(obl)
        assert isinstance(result, SolverResult)

    def test_push_pop(self):
        solver = ArithmeticSolver()
        solver.push()
        solver.pop()

    def test_reset(self):
        solver = ArithmeticSolver()
        solver.reset()
        model = solver.get_model()
        assert isinstance(model, dict)

    def test_result_time_positive(self):
        solver = ArithmeticSolver()
        formula = IntRange("x", lo=0, hi=100)
        obl = _make_obligation(formula)
        result = solver.check(obl)
        assert result.time_ms >= 0.0


# ============================================================================
# ArithmeticSolver with context
# ============================================================================


class TestArithmeticSolverContext:

    def test_context_constraints(self):
        solver = ArithmeticSolver()
        context_pred = IntRange("x", lo=0)
        formula = IntRange("x", hi=10)
        obl = _make_obligation(formula, context=(context_pred,))
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT

    def test_context_makes_unsat(self):
        solver = ArithmeticSolver()
        # Context says x >= 20, formula says x <= 10
        context_pred = IntRange("x", lo=20)
        formula = IntRange("x", hi=10)
        obl = _make_obligation(formula, context=(context_pred,))
        result = solver.check(obl)
        assert result.status == SolverStatus.UNSAT


# ============================================================================
# ArithmeticSolver with And formulas
# ============================================================================


class TestArithmeticSolverConjunction:

    def test_conjunction_sat(self):
        solver = ArithmeticSolver()
        formula = And([
            IntRange("x", lo=0, hi=10),
            IntRange("y", lo=5, hi=20),
        ])
        obl = _make_obligation(formula)
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT

    def test_conjunction_unsat(self):
        solver = ArithmeticSolver()
        formula = And([
            IntRange("x", lo=10),
            IntRange("x", hi=5),
        ])
        obl = _make_obligation(formula)
        result = solver.check(obl)
        assert result.status == SolverStatus.UNSAT
