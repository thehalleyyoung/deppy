"""Propositional fragment solver using DPLL-style search.

For obligations that are purely propositional (no arithmetic, no quantifiers),
this lightweight solver avoids the overhead of Z3.  It handles:

- Truth-table enumeration for small formulas (up to ~16 variables).
- Simple DPLL (unit propagation + pure literal elimination) for larger
  formulas.
- Constant folding for formulas that reduce to True/False under
  simplification.

Implements ``LocalSolverInterface``.
"""

from __future__ import annotations

import itertools
import logging
import time
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.predicates.base import Predicate, BoolLit, Var
from deppy.predicates.boolean import And, Or, Not, Implies, Iff, is_true, is_false
from deppy.predicates.arithmetic import Comparison
from deppy.solver.solver_interface import (
    LocalSolverInterface,
    SolverObligation,
    SolverResult,
    SolverStatus,
)

logger = logging.getLogger(__name__)

# Maximum number of variables for truth-table enumeration
_MAX_TRUTH_TABLE_VARS = 16


# ═══════════════════════════════════════════════════════════════════════════════
# Propositional evaluation
# ═══════════════════════════════════════════════════════════════════════════════


def _eval_predicate(pred: Predicate, assignment: Dict[str, bool]) -> Optional[bool]:
    """Evaluate a predicate under a boolean assignment.

    Returns None if the predicate cannot be fully evaluated (e.g., contains
    non-boolean atoms that are not in the assignment).
    """
    if is_true(pred):
        return True
    if is_false(pred):
        return False

    if isinstance(pred, And):
        for c in pred.conjuncts:
            val = _eval_predicate(c, assignment)
            if val is None:
                return None
            if not val:
                return False
        return True

    if isinstance(pred, Or):
        for d in pred.disjuncts:
            val = _eval_predicate(d, assignment)
            if val is None:
                return None
            if val:
                return True
        return False

    if isinstance(pred, Not):
        val = _eval_predicate(pred.operand, assignment)
        if val is None:
            return None
        return not val

    if isinstance(pred, Implies):
        ant = _eval_predicate(pred.antecedent, assignment)
        con = _eval_predicate(pred.consequent, assignment)
        if ant is None or con is None:
            return None
        return (not ant) or con

    if isinstance(pred, Iff):
        left = _eval_predicate(pred.left, assignment)
        right = _eval_predicate(pred.right, assignment)
        if left is None or right is None:
            return None
        return left == right

    # Atomic predicates: look up by normalized key
    norm_key, polarity = _normalize_atom(pred)
    if norm_key in assignment:
        val = assignment[norm_key]
        return val if polarity else (not val)

    # Fallback: try raw key
    key = _atom_key(pred)
    if key in assignment:
        return assignment[key]

    # Try to identify variable-like predicates
    fv = pred.free_variables()
    if len(fv) == 1:
        name = next(iter(fv))
        if name in assignment:
            return assignment[name]

    return None


def _atom_key(pred: Predicate) -> str:
    """Generate a unique string key for an atomic predicate."""
    return repr(pred)


def _is_negation_pair(a: Predicate, b: Predicate) -> bool:
    """Check if b is the logical negation of a (or vice versa)."""
    try:
        return a.negate() == b or b.negate() == a
    except Exception:
        return False


def _normalize_atom(pred: Predicate) -> Tuple[str, bool]:
    """Normalize an atomic predicate to (canonical_key, polarity).

    If the predicate is itself a negated form of a simpler atom
    (e.g., Comparison('!=', ...) is the negation of Comparison('==', ...)),
    return the positive form's key with polarity=False.
    """
    if isinstance(pred, Comparison):
        # Normalize comparison negation pairs to the same atom
        from deppy.predicates.arithmetic import _CMP_NEGATE
        neg_map = {"!=": "==", ">": "<=", ">=": "<"}
        if pred.op in neg_map:
            pos_pred = Comparison(neg_map[pred.op], pred.left, pred.right)
            return (_atom_key(pos_pred), False)
    return (_atom_key(pred), True)


def _collect_atoms(pred: Predicate) -> Set[str]:
    """Collect all atomic proposition keys from a predicate."""
    atoms: Set[str] = set()

    if isinstance(pred, (And,)):
        for c in pred.conjuncts:
            atoms |= _collect_atoms(c)
    elif isinstance(pred, (Or,)):
        for d in pred.disjuncts:
            atoms |= _collect_atoms(d)
    elif isinstance(pred, Not):
        atoms |= _collect_atoms(pred.operand)
    elif isinstance(pred, Implies):
        atoms |= _collect_atoms(pred.antecedent)
        atoms |= _collect_atoms(pred.consequent)
    elif isinstance(pred, Iff):
        atoms |= _collect_atoms(pred.left)
        atoms |= _collect_atoms(pred.right)
    else:
        # Atomic: use normalized key
        key, _ = _normalize_atom(pred)
        atoms.add(key)

    return atoms


# ═══════════════════════════════════════════════════════════════════════════════
# Unit propagation
# ═══════════════════════════════════════════════════════════════════════════════


def _unit_propagate(
    clauses: List[FrozenSet[Tuple[str, bool]]],
    assignment: Dict[str, bool],
) -> Tuple[List[FrozenSet[Tuple[str, bool]]], Dict[str, bool], bool]:
    """Perform unit propagation on a CNF clause set.

    A clause is a frozenset of (atom_key, polarity) pairs.

    Returns (remaining_clauses, updated_assignment, is_consistent).
    """
    changed = True
    while changed:
        changed = False
        new_clauses: List[FrozenSet[Tuple[str, bool]]] = []
        for clause in clauses:
            # Remove satisfied literals
            satisfied = False
            reduced: List[Tuple[str, bool]] = []
            for atom, polarity in clause:
                if atom in assignment:
                    if assignment[atom] == polarity:
                        satisfied = True
                        break
                    # Literal is falsified; skip it
                else:
                    reduced.append((atom, polarity))

            if satisfied:
                continue

            if not reduced:
                # Empty clause: contradiction
                return [], assignment, False

            new_clauses.append(frozenset(reduced))

        clauses = new_clauses

        # Find unit clauses
        for clause in clauses:
            if len(clause) == 1:
                atom, polarity = next(iter(clause))
                if atom not in assignment:
                    assignment[atom] = polarity
                    changed = True
                    break

    return clauses, assignment, True


def _pure_literal_eliminate(
    clauses: List[FrozenSet[Tuple[str, bool]]],
    assignment: Dict[str, bool],
) -> Tuple[List[FrozenSet[Tuple[str, bool]]], Dict[str, bool]]:
    """Eliminate pure literals (appearing only positively or only negatively)."""
    positive_atoms: Set[str] = set()
    negative_atoms: Set[str] = set()

    for clause in clauses:
        for atom, polarity in clause:
            if atom not in assignment:
                if polarity:
                    positive_atoms.add(atom)
                else:
                    negative_atoms.add(atom)

    # Pure positive: appears positive but never negative
    pure_pos = positive_atoms - negative_atoms
    # Pure negative: appears negative but never positive
    pure_neg = negative_atoms - positive_atoms

    for atom in pure_pos:
        assignment[atom] = True
    for atom in pure_neg:
        assignment[atom] = False

    if pure_pos or pure_neg:
        # Remove clauses containing pure literals
        remaining: List[FrozenSet[Tuple[str, bool]]] = []
        for clause in clauses:
            keep = True
            for atom, polarity in clause:
                if atom in pure_pos and polarity:
                    keep = False
                    break
                if atom in pure_neg and not polarity:
                    keep = False
                    break
            if keep:
                remaining.append(clause)
        return remaining, assignment

    return clauses, assignment


# ═══════════════════════════════════════════════════════════════════════════════
# DPLL
# ═══════════════════════════════════════════════════════════════════════════════


def _dpll(
    clauses: List[FrozenSet[Tuple[str, bool]]],
    assignment: Dict[str, bool],
    depth: int = 0,
    max_depth: int = 50,
) -> Optional[Dict[str, bool]]:
    """Simple DPLL solver.

    Returns a satisfying assignment or None if UNSAT.
    """
    if depth > max_depth:
        return None

    # Unit propagation
    clauses, assignment, consistent = _unit_propagate(clauses, dict(assignment))
    if not consistent:
        return None

    # All clauses satisfied?
    if not clauses:
        return assignment

    # Pure literal elimination
    clauses, assignment = _pure_literal_eliminate(clauses, assignment)
    if not clauses:
        return assignment

    # Pick an unassigned atom
    unassigned: Optional[str] = None
    for clause in clauses:
        for atom, _ in clause:
            if atom not in assignment:
                unassigned = atom
                break
        if unassigned is not None:
            break

    if unassigned is None:
        # No unassigned atoms but clauses remain: check if all satisfied
        return assignment

    # Branch on the chosen atom
    for value in [True, False]:
        branch_assignment = dict(assignment)
        branch_assignment[unassigned] = value
        result = _dpll(list(clauses), branch_assignment, depth + 1, max_depth)
        if result is not None:
            return result

    return None


# ═══════════════════════════════════════════════════════════════════════════════
# Predicate to CNF conversion (for DPLL)
# ═══════════════════════════════════════════════════════════════════════════════


def _pred_to_cnf_clauses(
    pred: Predicate,
) -> Optional[List[FrozenSet[Tuple[str, bool]]]]:
    """Convert a predicate into CNF clauses for DPLL.

    Returns None if the predicate structure is too complex for simple
    CNF conversion.
    """
    if is_true(pred):
        return []
    if is_false(pred):
        return [frozenset()]  # Empty clause = contradiction

    if isinstance(pred, And):
        clauses: List[FrozenSet[Tuple[str, bool]]] = []
        for c in pred.conjuncts:
            sub = _pred_to_cnf_clauses(c)
            if sub is None:
                return None
            clauses.extend(sub)
        return clauses

    if isinstance(pred, Or):
        # Or of atoms -> single clause
        literals: List[Tuple[str, bool]] = []
        for d in pred.disjuncts:
            if isinstance(d, Not):
                norm_key, norm_pol = _normalize_atom(d.operand)
                literals.append((norm_key, not norm_pol))
            elif isinstance(d, (And, Or)):
                # Complex disjuncts: bail out
                return None
            else:
                norm_key, norm_pol = _normalize_atom(d)
                literals.append((norm_key, norm_pol))
        return [frozenset(literals)]

    if isinstance(pred, Not):
        norm_key, norm_pol = _normalize_atom(pred.operand)
        return [frozenset([(norm_key, not norm_pol)])]

    if isinstance(pred, Implies):
        # A -> B = ~A | B
        ant_key, ant_pol = _normalize_atom(pred.antecedent)
        con_key, con_pol = _normalize_atom(pred.consequent)
        return [frozenset([(ant_key, not ant_pol), (con_key, con_pol)])]

    # Atomic predicate: single unit clause
    norm_key, norm_pol = _normalize_atom(pred)
    return [frozenset([(norm_key, norm_pol)])]


# ═══════════════════════════════════════════════════════════════════════════════
# Boolean Solver
# ═══════════════════════════════════════════════════════════════════════════════


class BooleanSolver:
    """Propositional fragment solver.

    For obligations that are purely propositional (no arithmetic, no
    quantifiers), this solver uses:

    1. Constant folding / simplification.
    2. Truth-table enumeration for small formulas (<=16 atoms).
    3. DPLL for larger formulas.

    Implements ``LocalSolverInterface``.
    """

    def __init__(self) -> None:
        self._asserted: List[Predicate] = []
        self._stack: List[List[Predicate]] = []

    def check(self, obligation: SolverObligation) -> SolverResult:
        t_start = time.perf_counter()

        # Combine context + formula
        all_preds: List[Predicate] = (
            list(obligation.context)
            + self._asserted
            + [obligation.formula]
        )

        # Build conjunction
        if len(all_preds) == 1:
            combined = all_preds[0]
        else:
            combined = And(all_preds)

        # Step 1: simplify
        simplified = combined.simplify()
        if is_true(simplified):
            elapsed = (time.perf_counter() - t_start) * 1000
            return SolverResult(
                status=SolverStatus.SAT,
                model={},
                time_ms=elapsed,
                explanation="Simplified to True",
            )
        if is_false(simplified):
            elapsed = (time.perf_counter() - t_start) * 1000
            return SolverResult(
                status=SolverStatus.UNSAT,
                time_ms=elapsed,
                explanation="Simplified to False",
            )

        # Step 2: collect atoms
        atoms = _collect_atoms(simplified)
        if not atoms:
            # No atoms; evaluate
            val = _eval_predicate(simplified, {})
            elapsed = (time.perf_counter() - t_start) * 1000
            if val is True:
                return SolverResult(
                    status=SolverStatus.SAT, model={}, time_ms=elapsed,
                    explanation="No atoms, evaluates to True",
                )
            if val is False:
                return SolverResult(
                    status=SolverStatus.UNSAT, time_ms=elapsed,
                    explanation="No atoms, evaluates to False",
                )
            return SolverResult(
                status=SolverStatus.UNKNOWN, time_ms=elapsed,
                explanation="Could not evaluate",
            )

        # Step 3: truth-table or DPLL
        if len(atoms) <= _MAX_TRUTH_TABLE_VARS:
            result = self._truth_table_check(simplified, atoms)
        else:
            result = self._dpll_check(simplified)

        elapsed = (time.perf_counter() - t_start) * 1000
        if result is not None:
            return SolverResult(
                status=SolverStatus.SAT,
                model={k: v for k, v in result.items()},
                time_ms=elapsed,
                explanation=f"SAT with {len(result)} assignment(s)",
            )
        return SolverResult(
            status=SolverStatus.UNSAT,
            time_ms=elapsed,
            explanation="UNSAT (all assignments falsify)",
        )

    def push(self) -> None:
        self._stack.append(list(self._asserted))

    def pop(self) -> None:
        if self._stack:
            self._asserted = self._stack.pop()
        else:
            self._asserted.clear()

    def assert_formula(self, formula: Predicate) -> None:
        self._asserted.append(formula)

    def get_model(self) -> Dict[str, Any]:
        return {}

    def reset(self) -> None:
        self._asserted.clear()
        self._stack.clear()

    # -------------------------------------------------------------------
    # Solving strategies
    # -------------------------------------------------------------------

    def _truth_table_check(
        self,
        pred: Predicate,
        atoms: Set[str],
    ) -> Optional[Dict[str, bool]]:
        """Enumerate all truth assignments for the atoms."""
        atom_list = sorted(atoms)
        for values in itertools.product([False, True], repeat=len(atom_list)):
            assignment = dict(zip(atom_list, values))
            result = _eval_predicate(pred, assignment)
            if result is True:
                return assignment
        return None

    def _dpll_check(self, pred: Predicate) -> Optional[Dict[str, bool]]:
        """Use DPLL to check satisfiability."""
        clauses = _pred_to_cnf_clauses(pred)
        if clauses is None:
            # Cannot convert to CNF; try brute force on free variables
            atoms = _collect_atoms(pred)
            if len(atoms) <= _MAX_TRUTH_TABLE_VARS:
                return self._truth_table_check(pred, atoms)
            return None  # Give up
        return _dpll(clauses, {})
