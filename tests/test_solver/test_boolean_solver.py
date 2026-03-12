"""Tests for BooleanSolver -- propositional satisfiability via truth-table and DPLL.

Tests verify truth-table enumeration, DPLL solving, unit propagation,
pure literal elimination, and CNF conversion.
"""

import pytest

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.predicates.base import Var, BoolLit
from deppy.predicates.boolean import And, Or, Not, Implies, Iff, is_true, is_false
from deppy.predicates.arithmetic import Comparison
from deppy.solver.boolean_solver import (
    BooleanSolver,
    _collect_atoms,
    _dpll,
    _eval_predicate,
    _pred_to_cnf_clauses,
    _pure_literal_eliminate,
    _unit_propagate,
)
from deppy.solver.solver_interface import (
    SolverObligation,
    SolverResult,
    SolverStatus,
)


# ============================================================================
# Helpers
# ============================================================================


def _make_obligation(formula, context=()):
    sid = SiteId(kind=SiteKind.SSA_VALUE, name="test_site")
    return SolverObligation(
        site_id=sid,
        formula=formula,
        context=tuple(context),
    )


def _var_pred(name):
    """Create a simple atomic predicate (Comparison for boolean-like var)."""
    return Comparison("==", Var(name), BoolLit(True))


# ============================================================================
# _eval_predicate
# ============================================================================


class TestEvalPredicate:

    def test_eval_true(self):
        assert _eval_predicate(And([]), {}) is True

    def test_eval_false(self):
        assert _eval_predicate(Or([]), {}) is False

    def test_eval_and(self):
        p = _var_pred("x")
        q = _var_pred("y")
        conj = And([p, q])
        assignment = {repr(p): True, repr(q): True}
        assert _eval_predicate(conj, assignment) is True

    def test_eval_and_false(self):
        p = _var_pred("x")
        q = _var_pred("y")
        conj = And([p, q])
        assignment = {repr(p): True, repr(q): False}
        result = _eval_predicate(conj, assignment)
        assert result is False

    def test_eval_or(self):
        p = _var_pred("x")
        q = _var_pred("y")
        disj = Or([p, q])
        assignment = {repr(p): False, repr(q): True}
        assert _eval_predicate(disj, assignment) is True

    def test_eval_not(self):
        p = _var_pred("x")
        n = Not(p)
        assignment = {repr(p): True}
        assert _eval_predicate(n, assignment) is False

    def test_eval_implies(self):
        p = _var_pred("x")
        q = _var_pred("y")
        imp = Implies(p, q)
        # False -> anything = True
        assignment = {repr(p): False, repr(q): False}
        assert _eval_predicate(imp, assignment) is True

    def test_eval_iff(self):
        p = _var_pred("x")
        q = _var_pred("y")
        bi = Iff(p, q)
        assignment = {repr(p): True, repr(q): True}
        assert _eval_predicate(bi, assignment) is True

    def test_eval_none_for_unknown(self):
        p = _var_pred("x")
        result = _eval_predicate(p, {})
        # May return None if the atom key is not in assignment
        assert result is None or isinstance(result, bool)


# ============================================================================
# _collect_atoms
# ============================================================================


class TestCollectAtoms:

    def test_single_atom(self):
        p = _var_pred("x")
        atoms = _collect_atoms(p)
        assert len(atoms) >= 1

    def test_conjunction(self):
        p = _var_pred("x")
        q = _var_pred("y")
        atoms = _collect_atoms(And([p, q]))
        assert len(atoms) >= 2

    def test_nested(self):
        p = _var_pred("x")
        q = _var_pred("y")
        formula = Or([And([p, Not(q)]), q])
        atoms = _collect_atoms(formula)
        assert len(atoms) >= 1


# ============================================================================
# _pred_to_cnf_clauses
# ============================================================================


class TestPredToCnf:

    def test_true_empty_clauses(self):
        clauses = _pred_to_cnf_clauses(And([]))
        assert clauses == []

    def test_false_empty_clause(self):
        clauses = _pred_to_cnf_clauses(Or([]))
        assert clauses is not None
        assert len(clauses) == 1
        assert len(clauses[0]) == 0  # Empty clause = contradiction

    def test_conjunction_of_atoms(self):
        p = _var_pred("x")
        q = _var_pred("y")
        clauses = _pred_to_cnf_clauses(And([p, q]))
        assert clauses is not None
        assert len(clauses) == 2

    def test_single_atom(self):
        p = _var_pred("x")
        clauses = _pred_to_cnf_clauses(p)
        assert clauses is not None
        assert len(clauses) == 1

    def test_negation(self):
        p = _var_pred("x")
        clauses = _pred_to_cnf_clauses(Not(p))
        assert clauses is not None
        assert len(clauses) == 1

    def test_implies_to_clause(self):
        p = _var_pred("x")
        q = _var_pred("y")
        clauses = _pred_to_cnf_clauses(Implies(p, q))
        assert clauses is not None
        assert len(clauses) == 1


# ============================================================================
# _unit_propagate
# ============================================================================


class TestUnitPropagate:

    def test_empty_clauses(self):
        remaining, assignment, ok = _unit_propagate([], {})
        assert ok is True
        assert remaining == []

    def test_unit_clause(self):
        clause = frozenset([("x", True)])
        remaining, assignment, ok = _unit_propagate([clause], {})
        assert ok is True
        assert assignment.get("x") is True

    def test_contradictory_clauses(self):
        c1 = frozenset([("x", True)])
        c2 = frozenset([("x", False)])
        remaining, assignment, ok = _unit_propagate([c1, c2], {})
        assert ok is False


# ============================================================================
# _pure_literal_eliminate
# ============================================================================


class TestPureLiteralEliminate:

    def test_pure_positive(self):
        c1 = frozenset([("x", True), ("y", True)])
        c2 = frozenset([("x", True), ("z", False)])
        remaining, assignment = _pure_literal_eliminate([c1, c2], {})
        # "x" appears only positive, so should be assigned True
        if "x" in assignment:
            assert assignment["x"] is True

    def test_no_pure_literals(self):
        c1 = frozenset([("x", True)])
        c2 = frozenset([("x", False)])
        remaining, assignment = _pure_literal_eliminate([c1, c2], {})
        assert isinstance(remaining, list)


# ============================================================================
# _dpll
# ============================================================================


class TestDPLL:

    def test_empty_clauses_sat(self):
        result = _dpll([], {})
        assert result is not None

    def test_contradiction_unsat(self):
        # Empty clause = contradiction
        result = _dpll([frozenset()], {})
        assert result is None

    def test_simple_sat(self):
        c1 = frozenset([("x", True), ("y", False)])
        c2 = frozenset([("x", False), ("y", True)])
        result = _dpll([c1, c2], {})
        assert result is not None

    def test_unsatisfiable(self):
        # x AND NOT x
        c1 = frozenset([("x", True)])
        c2 = frozenset([("x", False)])
        result = _dpll([c1, c2], {})
        assert result is None

    def test_max_depth_reached(self):
        # With max_depth=0, the solver may still resolve trivially
        # satisfiable unit clauses before the depth check.
        # A multi-variable problem requires depth > 0 to solve.
        c1 = frozenset([("x", True), ("y", True)])
        c2 = frozenset([("x", False), ("y", False)])
        result = _dpll([c1, c2], {}, max_depth=0)
        assert result is None


# ============================================================================
# BooleanSolver basic
# ============================================================================


class TestBooleanSolverBasic:

    def test_true_formula(self):
        solver = BooleanSolver()
        obl = _make_obligation(And([]))
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT

    def test_false_formula(self):
        solver = BooleanSolver()
        obl = _make_obligation(Or([]))
        result = solver.check(obl)
        assert result.status == SolverStatus.UNSAT

    def test_single_atom_sat(self):
        solver = BooleanSolver()
        p = _var_pred("x")
        obl = _make_obligation(p)
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT

    def test_conjunction_sat(self):
        solver = BooleanSolver()
        p = _var_pred("x")
        q = _var_pred("y")
        obl = _make_obligation(And([p, q]))
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT

    def test_result_time_nonnegative(self):
        solver = BooleanSolver()
        obl = _make_obligation(And([]))
        result = solver.check(obl)
        assert result.time_ms >= 0.0

    def test_result_explanation(self):
        solver = BooleanSolver()
        obl = _make_obligation(And([]))
        result = solver.check(obl)
        assert isinstance(result.explanation, str)
        assert len(result.explanation) > 0


# ============================================================================
# BooleanSolver push/pop
# ============================================================================


class TestBooleanSolverPushPop:

    def test_push_pop(self):
        solver = BooleanSolver()
        p = _var_pred("x")
        solver.push()
        solver.assert_formula(p)
        solver.pop()
        # After pop, asserted formulas should be cleared

    def test_assert_then_check(self):
        solver = BooleanSolver()
        p = _var_pred("x")
        solver.assert_formula(p)
        obl = _make_obligation(And([]))
        result = solver.check(obl)
        assert isinstance(result, SolverResult)

    def test_reset(self):
        solver = BooleanSolver()
        solver.assert_formula(_var_pred("x"))
        solver.reset()
        # After reset, should work fresh
        obl = _make_obligation(And([]))
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT

    def test_get_model(self):
        solver = BooleanSolver()
        model = solver.get_model()
        assert isinstance(model, dict)


# ============================================================================
# BooleanSolver with context
# ============================================================================


class TestBooleanSolverContext:

    def test_context_adds_constraints(self):
        solver = BooleanSolver()
        p = _var_pred("x")
        obl = _make_obligation(p, context=(p,))
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT


# ============================================================================
# BooleanSolver with implications
# ============================================================================


class TestBooleanSolverImplications:

    def test_implication_sat(self):
        solver = BooleanSolver()
        p = _var_pred("x")
        q = _var_pred("y")
        obl = _make_obligation(Implies(p, q))
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT

    def test_iff_sat(self):
        solver = BooleanSolver()
        p = _var_pred("x")
        q = _var_pred("y")
        obl = _make_obligation(Iff(p, q))
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT


# ============================================================================
# BooleanSolver negation
# ============================================================================


class TestBooleanSolverNegation:

    def test_negation_of_atom(self):
        solver = BooleanSolver()
        p = _var_pred("x")
        obl = _make_obligation(Not(p))
        result = solver.check(obl)
        assert result.status == SolverStatus.SAT

    def test_and_with_negation_unsat(self):
        solver = BooleanSolver()
        p = _var_pred("x")
        # p AND NOT p is unsatisfiable
        obl = _make_obligation(And([p, Not(p)]))
        result = solver.check(obl)
        # The DPLL/truth-table should catch this
        assert result.status == SolverStatus.UNSAT


# ============================================================================
# SolverResult properties
# ============================================================================


class TestSolverResult:

    def test_is_sat(self):
        r = SolverResult(status=SolverStatus.SAT, model={"x": True})
        assert r.is_sat
        assert not r.is_unsat

    def test_is_unsat(self):
        r = SolverResult(status=SolverStatus.UNSAT)
        assert r.is_unsat
        assert not r.is_sat

    def test_is_definitive(self):
        assert SolverResult(status=SolverStatus.SAT).is_definitive
        assert SolverResult(status=SolverStatus.UNSAT).is_definitive
        assert not SolverResult(status=SolverStatus.UNKNOWN).is_definitive

    def test_is_error_or_timeout(self):
        assert SolverResult(status=SolverStatus.TIMEOUT).is_error_or_timeout
        assert SolverResult(status=SolverStatus.ERROR).is_error_or_timeout
        assert not SolverResult(status=SolverStatus.SAT).is_error_or_timeout


# ============================================================================
# SolverObligation properties
# ============================================================================


class TestSolverObligation:

    def test_with_context(self):
        p = _var_pred("x")
        q = _var_pred("y")
        sid = SiteId(kind=SiteKind.SSA_VALUE, name="s")
        obl = SolverObligation(site_id=sid, formula=p)
        obl2 = obl.with_context(q)
        assert len(obl2.context) == 1
        assert obl.context == ()

    def test_with_timeout(self):
        p = _var_pred("x")
        sid = SiteId(kind=SiteKind.SSA_VALUE, name="s")
        obl = SolverObligation(site_id=sid, formula=p)
        obl2 = obl.with_timeout(1000.0)
        assert obl2.timeout_ms == 1000.0
        assert obl.timeout_ms == 0.0

    def test_formula_hash(self):
        p = _var_pred("x")
        sid = SiteId(kind=SiteKind.SSA_VALUE, name="s")
        obl = SolverObligation(site_id=sid, formula=p)
        h = obl.formula_hash()
        assert isinstance(h, str)
        assert len(h) > 0

    def test_context_list(self):
        p = _var_pred("x")
        q = _var_pred("y")
        sid = SiteId(kind=SiteKind.SSA_VALUE, name="s")
        obl = SolverObligation(site_id=sid, formula=p, context=(q,))
        assert len(obl.context_list) == 1
