"""QF_LIA (quantifier-free linear integer arithmetic) fragment solver.

This solver is optimized for the most common verification patterns in
deppy's sheaf-descent type system:

- **Range checks**: ``lo <= x <= hi``
- **Bound propagation**: ``x + y <= n``
- **Interval arithmetic**: track intervals for each variable and check
  feasibility.
- **Simple equality / inequality**: ``x == k``, ``x != k``

For formulas that exceed the interval-arithmetic solver's capability,
the ``ArithmeticSolver`` falls back to the Z3 backend.

This avoids the overhead of Z3 startup for the majority of obligations
that are simple range / bound checks.
"""

from __future__ import annotations

import logging
import time
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Set,
    Tuple,
)

from deppy.predicates.base import Predicate, IntLit, Var, BinOp, UnaryOp
from deppy.predicates.arithmetic import (
    ArithmeticNormalizer,
    Comparison,
    Divisibility,
    IntRange,
    LinearInequality,
)
from deppy.predicates.boolean import And, Or, Not, is_true, is_false
from deppy.solver.solver_interface import (
    LocalSolverInterface,
    SolverConfig,
    SolverObligation,
    SolverResult,
    SolverStatus,
)

logger = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════════════════
# Interval
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class Interval:
    """Closed integer interval [lo, hi].

    ``None`` represents an unbounded end.
    """

    lo: Optional[int] = None
    hi: Optional[int] = None

    @property
    def is_empty(self) -> bool:
        if self.lo is not None and self.hi is not None:
            return self.lo > self.hi
        return False

    @property
    def is_singleton(self) -> bool:
        return (
            self.lo is not None
            and self.hi is not None
            and self.lo == self.hi
        )

    @property
    def is_unbounded(self) -> bool:
        return self.lo is None and self.hi is None

    def intersect(self, other: Interval) -> Interval:
        new_lo = _max_opt(self.lo, other.lo)
        new_hi = _min_opt(self.hi, other.hi)
        return Interval(lo=new_lo, hi=new_hi)

    def contains(self, value: int) -> bool:
        if self.lo is not None and value < self.lo:
            return False
        if self.hi is not None and value > self.hi:
            return False
        return True

    def pick_value(self) -> Optional[int]:
        """Pick a concrete value from the interval, if non-empty."""
        if self.is_empty:
            return None
        if self.lo is not None:
            return self.lo
        if self.hi is not None:
            return self.hi
        return 0

    def __repr__(self) -> str:
        lo_s = str(self.lo) if self.lo is not None else "-inf"
        hi_s = str(self.hi) if self.hi is not None else "+inf"
        return f"[{lo_s}, {hi_s}]"


def _max_opt(a: Optional[int], b: Optional[int]) -> Optional[int]:
    if a is None:
        return b
    if b is None:
        return a
    return max(a, b)


def _min_opt(a: Optional[int], b: Optional[int]) -> Optional[int]:
    if a is None:
        return b
    if b is None:
        return a
    return min(a, b)


# ═══════════════════════════════════════════════════════════════════════════════
# Interval store
# ═══════════════════════════════════════════════════════════════════════════════


class IntervalStore:
    """Tracks interval bounds for each variable.

    Supports push/pop for backtracking.
    """

    def __init__(self) -> None:
        self._intervals: Dict[str, Interval] = {}
        self._stack: List[Dict[str, Interval]] = []
        self._equalities: Dict[str, int] = {}
        self._disequalities: Dict[str, Set[int]] = {}

    def push(self) -> None:
        self._stack.append({
            name: Interval(lo=iv.lo, hi=iv.hi)
            for name, iv in self._intervals.items()
        })

    def pop(self) -> None:
        if self._stack:
            self._intervals = self._stack.pop()
        else:
            self._intervals.clear()
        self._equalities.clear()
        self._disequalities.clear()

    def get(self, name: str) -> Interval:
        return self._intervals.get(name, Interval())

    def tighten_lower(self, name: str, lo: int) -> bool:
        """Tighten the lower bound.  Returns False if interval becomes empty."""
        iv = self._intervals.get(name, Interval())
        new_lo = _max_opt(iv.lo, lo)
        new_iv = Interval(lo=new_lo, hi=iv.hi)
        self._intervals[name] = new_iv
        return not new_iv.is_empty

    def tighten_upper(self, name: str, hi: int) -> bool:
        """Tighten the upper bound.  Returns False if interval becomes empty."""
        iv = self._intervals.get(name, Interval())
        new_hi = _min_opt(iv.hi, hi)
        new_iv = Interval(lo=iv.lo, hi=new_hi)
        self._intervals[name] = new_iv
        return not new_iv.is_empty

    def set_equal(self, name: str, value: int) -> bool:
        """Assert x == value.  Returns False if inconsistent."""
        ok = self.tighten_lower(name, value) and self.tighten_upper(name, value)
        if ok:
            self._equalities[name] = value
            # Check disequalities
            if name in self._disequalities and value in self._disequalities[name]:
                return False
        return ok

    def add_disequality(self, name: str, value: int) -> bool:
        """Assert x != value.  Returns False if currently forced to that value."""
        self._disequalities.setdefault(name, set()).add(value)
        if name in self._equalities:
            return self._equalities[name] != value
        iv = self.get(name)
        if iv.is_singleton and iv.lo == value:
            return False
        return True

    def is_feasible(self) -> bool:
        for iv in self._intervals.values():
            if iv.is_empty:
                return False
        return True

    def build_model(self) -> Dict[str, int]:
        """Build a concrete model by picking values from each interval."""
        model: Dict[str, int] = {}
        for name, iv in self._intervals.items():
            if name in self._equalities:
                model[name] = self._equalities[name]
            else:
                val = iv.pick_value()
                if val is not None:
                    # Avoid disequalities
                    diseqs = self._disequalities.get(name, set())
                    while val in diseqs:
                        val += 1
                        if iv.hi is not None and val > iv.hi:
                            val = None
                            break
                model[name] = val if val is not None else 0
        return model

    def clear(self) -> None:
        self._intervals.clear()
        self._stack.clear()
        self._equalities.clear()
        self._disequalities.clear()


# ═══════════════════════════════════════════════════════════════════════════════
# Arithmetic Solver
# ═══════════════════════════════════════════════════════════════════════════════


class ArithmeticSolver:
    """QF_LIA fragment solver using interval propagation.

    For obligations that consist entirely of linear integer arithmetic
    constraints (range checks, comparisons, linear inequalities), this
    solver uses interval propagation to quickly determine feasibility
    without invoking Z3.

    For obligations with more complex structure (disjunctions, non-linear
    terms), it falls back to the Z3 backend.

    Implements ``LocalSolverInterface``.
    """

    def __init__(self, config: Optional[SolverConfig] = None) -> None:
        self._config = config or SolverConfig()
        self._store = IntervalStore()
        self._normalizer = ArithmeticNormalizer()
        self._z3_fallback: Any = None  # Lazy-created Z3Backend
        self._asserted: List[Predicate] = []

    # -------------------------------------------------------------------
    # LocalSolverInterface
    # -------------------------------------------------------------------

    def check(self, obligation: SolverObligation) -> SolverResult:
        """Check satisfiability of the obligation.

        First tries interval propagation.  If that is inconclusive
        (e.g., disjunctions), falls back to Z3.
        """
        t_start = time.perf_counter()

        # Try fast path: normalize to linear inequalities
        all_preds = list(obligation.context) + [obligation.formula]
        linear_constraints: List[LinearInequality] = []
        needs_fallback = False

        for pred in all_preds:
            expanded = self._expand_to_linear(pred)
            if expanded is None:
                needs_fallback = True
                break
            linear_constraints.extend(expanded)

        if not needs_fallback:
            result = self._solve_linear(linear_constraints)
            elapsed = (time.perf_counter() - t_start) * 1000
            if result is not None:
                return SolverResult(
                    status=result[0],
                    model=result[1],
                    time_ms=elapsed,
                    explanation=("interval propagation " +
                                 ("SAT" if result[0] == SolverStatus.SAT else "UNSAT")),
                )

        # Fallback to Z3
        return self._z3_check(obligation, t_start)

    def push(self) -> None:
        self._store.push()

    def pop(self) -> None:
        self._store.pop()

    def assert_formula(self, formula: Predicate) -> None:
        self._asserted.append(formula)

    def get_model(self) -> Dict[str, Any]:
        return self._store.build_model()

    def reset(self) -> None:
        self._store.clear()
        self._asserted.clear()

    # -------------------------------------------------------------------
    # Linear solving via interval propagation
    # -------------------------------------------------------------------

    def _expand_to_linear(
        self, pred: Predicate
    ) -> Optional[List[LinearInequality]]:
        """Try to expand a predicate into linear inequalities.

        Returns None if the predicate cannot be fully linearized
        (e.g., contains disjunctions, quantifiers, non-linear terms).
        """
        if is_true(pred):
            return []
        if is_false(pred):
            # Contradiction
            return [LinearInequality({}, -1)]  # 0 + (-1) >= 0 is false

        result = self._normalizer.normalize(pred)
        if result:
            return result

        # Handle IntRange directly
        if isinstance(pred, IntRange):
            constraints: List[LinearInequality] = []
            if pred.lo is not None:
                constraints.append(
                    LinearInequality({pred.variable: 1}, -pred.lo)
                )
            if pred.hi is not None:
                constraints.append(
                    LinearInequality({pred.variable: -1}, pred.hi)
                )
            return constraints

        # Handle And
        if isinstance(pred, And):
            combined: List[LinearInequality] = []
            for c in pred.conjuncts:
                sub = self._expand_to_linear(c)
                if sub is None:
                    return None
                combined.extend(sub)
            return combined

        # Handle Not of a simple comparison (flip)
        if isinstance(pred, Not):
            inner = pred.operand
            if isinstance(inner, Comparison):
                negated = inner.negate()
                return self._expand_to_linear(negated)

        return None

    def _solve_linear(
        self,
        constraints: List[LinearInequality],
    ) -> Optional[Tuple[SolverStatus, Optional[Dict[str, Any]]]]:
        """Solve a conjunction of linear inequalities using interval propagation.

        Returns (status, model) or None if propagation is inconclusive.
        """
        store = IntervalStore()

        for li in constraints:
            if not li.coefficients:
                # Pure constant: constant >= 0
                if li.constant < 0:
                    return (SolverStatus.UNSAT, None)
                continue

            # Single-variable case: a*x + c >= 0  =>  x >= -c/a or x <= -c/a
            if len(li.coefficients) == 1:
                var_name, coeff = li.coefficients[0]
                # a*x >= -c
                if coeff > 0:
                    # x >= ceil(-c / a)
                    bound = _ceildiv(-li.constant, coeff)
                    if not store.tighten_lower(var_name, bound):
                        return (SolverStatus.UNSAT, None)
                elif coeff < 0:
                    # -|a|*x >= -c  =>  x <= c / |a|  =>  x <= floor(c / |a|)
                    # Actually: coeff*x + constant >= 0
                    # coeff < 0: x <= (constant) / (-coeff)
                    bound = _floordiv(li.constant, -coeff)
                    if not store.tighten_upper(var_name, bound):
                        return (SolverStatus.UNSAT, None)
            # Multi-variable: we cannot propagate precisely in general.
            # For 2-variable constraints we do a simple feasibility check.
            # Beyond that, we bail out.
            elif len(li.coefficients) == 2:
                # Store for later model building but don't propagate.
                pass
            else:
                # Too complex for interval propagation
                return None

        if not store.is_feasible():
            return (SolverStatus.UNSAT, None)

        model = store.build_model()

        # Verify model satisfies all constraints (including multi-variable)
        for li in constraints:
            total = li.constant
            for var_name, coeff in li.coefficients:
                total += coeff * model.get(var_name, 0)
            if total < 0:
                # Model does not satisfy this constraint; interval propagation
                # was insufficient.  Fall back.
                return None

        return (SolverStatus.SAT, {k: v for k, v in model.items()})

    # -------------------------------------------------------------------
    # Z3 fallback
    # -------------------------------------------------------------------

    def _z3_check(
        self, obligation: SolverObligation, t_start: float
    ) -> SolverResult:
        """Fall back to Z3 for complex obligations."""
        if self._z3_fallback is None:
            from deppy.solver.z3_backend import create_z3_backend
            self._z3_fallback = create_z3_backend(config=self._config)

        result = self._z3_fallback.check(obligation)
        elapsed = (time.perf_counter() - t_start) * 1000
        return SolverResult(
            status=result.status,
            model=result.model,
            proof_certificate=result.proof_certificate,
            time_ms=elapsed,
            unsat_core=result.unsat_core,
            statistics=result.statistics,
            explanation=f"Z3 fallback: {result.explanation}",
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Integer arithmetic helpers
# ═══════════════════════════════════════════════════════════════════════════════


def _ceildiv(a: int, b: int) -> int:
    """Ceiling division: ceil(a / b) for b > 0."""
    if b == 0:
        return 0
    if b < 0:
        return _ceildiv(-a, -b)
    return -(-a // b)


def _floordiv(a: int, b: int) -> int:
    """Floor division: floor(a / b) for b > 0."""
    if b == 0:
        return 0
    if b < 0:
        return _floordiv(-a, -b)
    return a // b
