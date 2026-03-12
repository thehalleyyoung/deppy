"""Theory Family 1: Linear Arithmetic & Intervals.

Handles integer bounds, ranges, divisibility, and affine relations.
Solves constraints like ``0 <= x < len(lst)``, ``a + b <= c``.
Forward: propagate bounds through arithmetic operations.
Backward: infer required bounds from error conditions.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism

from .theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    TheoryPackBase,
    make_section,
    merge_refinements,
    narrow_section,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Interval representation
# ═══════════════════════════════════════════════════════════════════════════════

INF = float("inf")
NEG_INF = float("-inf")


@dataclass(frozen=True)
class Interval:
    """Closed interval [lo, hi] with support for unbounded ends."""
    lo: Union[int, float] = NEG_INF
    hi: Union[int, float] = INF

    @property
    def is_empty(self) -> bool:
        return self.lo > self.hi

    @property
    def is_bounded(self) -> bool:
        return self.lo != NEG_INF and self.hi != INF

    @property
    def is_point(self) -> bool:
        return self.lo == self.hi and self.is_bounded

    @property
    def width(self) -> Union[int, float]:
        if self.is_empty:
            return 0
        if not self.is_bounded:
            return INF
        return self.hi - self.lo

    def contains(self, value: Union[int, float]) -> bool:
        return self.lo <= value <= self.hi

    def intersect(self, other: Interval) -> Interval:
        new_lo = max(self.lo, other.lo)
        new_hi = min(self.hi, other.hi)
        return Interval(new_lo, new_hi)

    def union_hull(self, other: Interval) -> Interval:
        if self.is_empty:
            return other
        if other.is_empty:
            return self
        return Interval(min(self.lo, other.lo), max(self.hi, other.hi))

    def add(self, other: Interval) -> Interval:
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def sub(self, other: Interval) -> Interval:
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def mul(self, other: Interval) -> Interval:
        products = [
            self.lo * other.lo, self.lo * other.hi,
            self.hi * other.lo, self.hi * other.hi,
        ]
        finite = [p for p in products if math.isfinite(p)]
        if not finite:
            return Interval(NEG_INF, INF)
        return Interval(min(finite), max(finite))

    def negate(self) -> Interval:
        return Interval(-self.hi, -self.lo)

    def abs(self) -> Interval:
        if self.lo >= 0:
            return self
        if self.hi <= 0:
            return Interval(-self.hi, -self.lo)
        return Interval(0, max(-self.lo, self.hi))

    def floor_div(self, other: Interval) -> Interval:
        if other.contains(0):
            return Interval(NEG_INF, INF)
        if other.lo > 0:
            vals = [
                self.lo // other.lo if math.isfinite(self.lo) else NEG_INF,
                self.lo // other.hi if math.isfinite(self.lo) else NEG_INF,
                self.hi // other.lo if math.isfinite(self.hi) else INF,
                self.hi // other.hi if math.isfinite(self.hi) else INF,
            ]
            finite = [v for v in vals if math.isfinite(v)]
            if finite:
                return Interval(min(finite), max(finite))
        return Interval(NEG_INF, INF)

    def modulo(self, other: Interval) -> Interval:
        if other.lo <= 0 or not other.is_bounded:
            return Interval(NEG_INF, INF)
        return Interval(0, other.hi - 1)

    def __repr__(self) -> str:
        lo_str = "-inf" if self.lo == NEG_INF else str(self.lo)
        hi_str = "inf" if self.hi == INF else str(self.hi)
        return f"[{lo_str}, {hi_str}]"


EMPTY_INTERVAL = Interval(1, 0)
FULL_INTERVAL = Interval(NEG_INF, INF)
NON_NEGATIVE = Interval(0, INF)
POSITIVE = Interval(1, INF)


def interval_from_refinements(refs: Dict[str, Any]) -> Interval:
    """Extract an interval from a section's refinements."""
    lo = NEG_INF
    hi = INF
    if "lower_bound" in refs:
        val = refs["lower_bound"]
        if isinstance(val, (int, float)):
            lo = val
    if "min" in refs:
        val = refs["min"]
        if isinstance(val, (int, float)):
            lo = max(lo, val)
    if "upper_bound" in refs:
        val = refs["upper_bound"]
        if isinstance(val, (int, float)):
            hi = val
    if "max" in refs:
        val = refs["max"]
        if isinstance(val, (int, float)):
            hi = min(hi, val)
    if refs.get("non_negative"):
        lo = max(lo, 0)
    if refs.get("positive"):
        lo = max(lo, 1)
    if refs.get("negative"):
        hi = min(hi, -1)
    return Interval(lo, hi)


def interval_to_refinements(interval: Interval) -> Dict[str, Any]:
    """Convert an interval back to refinement entries."""
    refs: Dict[str, Any] = {}
    if interval.lo != NEG_INF:
        refs["lower_bound"] = interval.lo
        if interval.lo >= 0:
            refs["non_negative"] = True
        if interval.lo >= 1:
            refs["positive"] = True
    if interval.hi != INF:
        refs["upper_bound"] = interval.hi
        if interval.hi < 0:
            refs["negative"] = True
    return refs


# ═══════════════════════════════════════════════════════════════════════════════
# Affine relation tracking
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class AffineRelation:
    """Represents an affine relation: result = coeff * operand + offset."""
    coeff: Union[int, float] = 1
    operand: str = ""
    offset: Union[int, float] = 0

    def apply_interval(self, operand_interval: Interval) -> Interval:
        scaled = operand_interval.mul(Interval(self.coeff, self.coeff))
        return scaled.add(Interval(self.offset, self.offset))

    def inverse(self) -> Optional[AffineRelation]:
        if self.coeff == 0:
            return None
        return AffineRelation(
            coeff=1 / self.coeff,
            operand=self.operand,
            offset=-self.offset / self.coeff,
        )


@dataclass(frozen=True)
class DivisibilityInfo:
    """Tracks that a value is divisible by some modulus."""
    modulus: int
    remainder: int = 0

    def combined_with(self, other: DivisibilityInfo) -> DivisibilityInfo:
        gcd = math.gcd(self.modulus, other.modulus)
        if self.remainder % gcd != other.remainder % gcd:
            return DivisibilityInfo(1, 0)
        return DivisibilityInfo(gcd, self.remainder % gcd)


# ═══════════════════════════════════════════════════════════════════════════════
# Arithmetic operations catalog
# ═══════════════════════════════════════════════════════════════════════════════

_ARITHMETIC_OPS: Dict[str, Any] = {
    "add": lambda a, b: a.add(b),
    "sub": lambda a, b: a.sub(b),
    "mul": lambda a, b: a.mul(b),
    "floordiv": lambda a, b: a.floor_div(b),
    "mod": lambda a, b: a.modulo(b),
    "neg": lambda a: a.negate(),
    "abs": lambda a: a.abs(),
}


def propagate_arithmetic(
    op: str,
    operand_intervals: List[Interval],
) -> Interval:
    """Propagate intervals through an arithmetic operation."""
    handler = _ARITHMETIC_OPS.get(op)
    if handler is None:
        return FULL_INTERVAL
    if op in ("neg", "abs"):
        if len(operand_intervals) >= 1:
            return handler(operand_intervals[0])
        return FULL_INTERVAL
    if len(operand_intervals) >= 2:
        return handler(operand_intervals[0], operand_intervals[1])
    return FULL_INTERVAL


def backward_arithmetic(
    op: str,
    result_interval: Interval,
    known_operand: Optional[Interval],
    operand_position: int = 0,
) -> Interval:
    """Infer operand bounds from a result interval.

    Given ``result = op(a, b)`` and the result interval, plus optionally
    one known operand, infer bounds on the unknown operand.
    """
    if op == "add":
        if known_operand is not None:
            return result_interval.sub(known_operand)
        return FULL_INTERVAL
    elif op == "sub":
        if known_operand is not None:
            if operand_position == 0:
                return result_interval.add(known_operand)
            else:
                return known_operand.sub(result_interval)
        return FULL_INTERVAL
    elif op == "mul":
        if known_operand is not None and known_operand.is_point and known_operand.lo != 0:
            factor = known_operand.lo
            return Interval(result_interval.lo / factor, result_interval.hi / factor)
        return FULL_INTERVAL
    elif op == "neg":
        return result_interval.negate()
    return FULL_INTERVAL


# ═══════════════════════════════════════════════════════════════════════════════
# Constraint representation
# ═══════════════════════════════════════════════════════════════════════════════


class ConstraintKind(Enum):
    BOUND = auto()
    AFFINE = auto()
    DIVISIBILITY = auto()
    COMPARISON = auto()


@dataclass
class ArithmeticConstraint:
    """A constraint in the arithmetic theory."""
    kind: ConstraintKind
    variables: List[str]
    data: Any = None
    explanation: str = ""

    def is_satisfied_by(self, assignments: Dict[str, Interval]) -> bool:
        if self.kind == ConstraintKind.BOUND:
            var = self.variables[0] if self.variables else ""
            interval = assignments.get(var, FULL_INTERVAL)
            bound: Interval = self.data if isinstance(self.data, Interval) else FULL_INTERVAL
            return not interval.intersect(bound).is_empty
        elif self.kind == ConstraintKind.COMPARISON:
            if len(self.variables) >= 2:
                a = assignments.get(self.variables[0], FULL_INTERVAL)
                b = assignments.get(self.variables[1], FULL_INTERVAL)
                op = self.data
                if op == "le":
                    return a.lo <= b.hi
                elif op == "lt":
                    return a.lo < b.hi
                elif op == "ge":
                    return a.hi >= b.lo
                elif op == "gt":
                    return a.hi > b.lo
                elif op == "eq":
                    return not a.intersect(b).is_empty
        return True


def solve_constraints(
    constraints: List[ArithmeticConstraint],
    initial: Dict[str, Interval],
    max_iterations: int = 20,
) -> Tuple[Dict[str, Interval], bool]:
    """Simple interval propagation constraint solver.

    Iteratively tightens variable intervals until convergence or the
    iteration limit is reached.
    """
    current = dict(initial)
    for _ in range(max_iterations):
        changed = False
        for constraint in constraints:
            if constraint.kind == ConstraintKind.BOUND:
                var = constraint.variables[0] if constraint.variables else ""
                if var in current:
                    bound = constraint.data if isinstance(constraint.data, Interval) else FULL_INTERVAL
                    new_interval = current[var].intersect(bound)
                    if new_interval != current[var]:
                        current[var] = new_interval
                        changed = True
            elif constraint.kind == ConstraintKind.COMPARISON:
                if len(constraint.variables) >= 2:
                    var_a, var_b = constraint.variables[0], constraint.variables[1]
                    int_a = current.get(var_a, FULL_INTERVAL)
                    int_b = current.get(var_b, FULL_INTERVAL)
                    op = constraint.data
                    if op == "le":
                        new_a = int_a.intersect(Interval(NEG_INF, int_b.hi))
                        new_b = int_b.intersect(Interval(int_a.lo, INF))
                    elif op == "lt":
                        new_a = int_a.intersect(Interval(NEG_INF, int_b.hi - 1))
                        new_b = int_b.intersect(Interval(int_a.lo + 1, INF))
                    elif op == "ge":
                        new_a = int_a.intersect(Interval(int_b.lo, INF))
                        new_b = int_b.intersect(Interval(NEG_INF, int_a.hi))
                    elif op == "gt":
                        new_a = int_a.intersect(Interval(int_b.lo + 1, INF))
                        new_b = int_b.intersect(Interval(NEG_INF, int_a.hi - 1))
                    else:
                        new_a, new_b = int_a, int_b
                    if new_a != int_a:
                        current[var_a] = new_a
                        changed = True
                    if new_b != int_b:
                        current[var_b] = new_b
                        changed = True
            elif constraint.kind == ConstraintKind.AFFINE:
                rel: AffineRelation = constraint.data
                if rel.operand in current and len(constraint.variables) >= 1:
                    result_var = constraint.variables[0]
                    operand_interval = current[rel.operand]
                    result_interval = rel.apply_interval(operand_interval)
                    if result_var in current:
                        new_result = current[result_var].intersect(result_interval)
                        if new_result != current[result_var]:
                            current[result_var] = new_result
                            changed = True
                    else:
                        current[result_var] = result_interval
                        changed = True
        if not changed:
            return current, True
    return current, False


# ═══════════════════════════════════════════════════════════════════════════════
# ArithmeticTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class ArithmeticTheoryPack(TheoryPackBase):
    """Theory Family 1: Linear Arithmetic & Intervals.

    Handles SSA_VALUE, ARGUMENT_BOUNDARY, RETURN_OUTPUT_BOUNDARY, and
    CALL_RESULT sites where the carrier type is numeric.
    """

    pack_name = "arithmetic"
    pack_priority = 10

    _APPLICABLE = frozenset({
        SiteKind.SSA_VALUE,
        SiteKind.ARGUMENT_BOUNDARY,
        SiteKind.RETURN_OUTPUT_BOUNDARY,
        SiteKind.CALL_RESULT,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        """Refine a section's arithmetic constraints.

        Extracts intervals, runs constraint propagation, and produces
        a tighter section.
        """
        if not self._is_numeric_section(section):
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="non-numeric carrier; arithmetic theory skipped",
            )

        interval = interval_from_refinements(section.refinements)
        constraints = self._extract_constraints(section)

        if not constraints:
            if interval.is_bounded:
                new_refs = merge_refinements(
                    section.refinements,
                    interval_to_refinements(interval),
                    "meet",
                )
                if new_refs != section.refinements:
                    refined = LocalSection(
                        site_id=section.site_id,
                        carrier_type=section.carrier_type,
                        refinements=new_refs,
                        trust=TrustLevel.BOUNDED_AUTO,
                        provenance="arithmetic interval normalization",
                        witnesses=dict(section.witnesses),
                    )
                    return SolverResult(
                        status=SolverStatus.REFINED,
                        section=refined,
                        explanation=f"normalized to interval {interval}",
                    )
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="no arithmetic constraints to solve",
            )

        var_name = site.name
        initial_intervals = {var_name: interval}
        for c in constraints:
            for v in c.variables:
                if v not in initial_intervals:
                    initial_intervals[v] = FULL_INTERVAL

        solved, converged = solve_constraints(constraints, initial_intervals)
        result_interval = solved.get(var_name, interval)

        if result_interval.is_empty:
            return SolverResult(
                status=SolverStatus.UNSATISFIABLE,
                section=section,
                explanation=f"arithmetic constraints unsatisfiable for {var_name}",
            )

        new_refs = merge_refinements(
            section.refinements,
            interval_to_refinements(result_interval),
            "meet",
        )
        new_refs["_interval"] = result_interval

        for rel_key in ("_affine_relations",):
            rels = section.refinements.get(rel_key)
            if rels is not None:
                new_refs[rel_key] = rels

        div_info = section.refinements.get("_divisibility")
        if div_info is not None:
            new_refs["_divisibility"] = div_info

        refined = LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=new_refs,
            trust=TrustLevel.BOUNDED_AUTO if converged else section.trust,
            provenance=f"arithmetic solver: {result_interval}",
            witnesses=dict(section.witnesses),
        )
        return SolverResult(
            status=SolverStatus.SOLVED if converged else SolverStatus.REFINED,
            section=refined,
            explanation=f"interval {interval} -> {result_interval}",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Propagate arithmetic bounds forward."""
        restricted = morphism.restrict(section)

        op = None
        if morphism.metadata:
            op = morphism.metadata.get("arithmetic_op")

        if op is None:
            return restricted

        source_interval = interval_from_refinements(section.refinements)
        operand_intervals = [source_interval]

        second_operand = morphism.metadata.get("second_operand_interval")
        if second_operand is not None and isinstance(second_operand, Interval):
            operand_intervals.append(second_operand)
        elif morphism.metadata.get("second_operand_value") is not None:
            val = morphism.metadata["second_operand_value"]
            if isinstance(val, (int, float)):
                operand_intervals.append(Interval(val, val))

        result_interval = propagate_arithmetic(op, operand_intervals)
        new_refs = merge_refinements(
            restricted.refinements,
            interval_to_refinements(result_interval),
            "meet",
        )

        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance=f"arithmetic forward: {op} -> {result_interval}",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Infer arithmetic preconditions from output requirements."""
        result_interval = interval_from_refinements(section.refinements)

        op = None
        known_operand = None
        operand_position = 0
        if morphism.metadata:
            op = morphism.metadata.get("arithmetic_op")
            second_val = morphism.metadata.get("second_operand_value")
            if second_val is not None and isinstance(second_val, (int, float)):
                known_operand = Interval(second_val, second_val)
                operand_position = 1

        if op is not None:
            required_interval = backward_arithmetic(
                op, result_interval, known_operand, operand_position
            )
        else:
            required_interval = result_interval

        new_refs = interval_to_refinements(required_interval)

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=new_refs,
            trust=TrustLevel.RESIDUAL,
            provenance=f"arithmetic pullback: requires {required_interval}",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        """Describe conditions under which the arithmetic is safe."""
        name = error_site.name
        if "div" in name.lower() or "mod" in name.lower():
            return "divisor != 0"
        if "index" in name.lower():
            return "0 <= index < length"
        if "overflow" in name.lower():
            return "result within representable range"
        return f"arithmetic precondition for {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        """Classify a section for proof-boundary purposes."""
        interval = interval_from_refinements(section.refinements)
        if section.trust == TrustLevel.PROOF_BACKED:
            return BoundaryClassification.FULLY_PROVEN
        if section.trust == TrustLevel.BOUNDED_AUTO and interval.is_bounded:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        if section.trust in (TrustLevel.TRACE_BACKED, TrustLevel.TRUSTED_AUTO):
            return BoundaryClassification.RUNTIME_GUARDED
        if section.trust == TrustLevel.ASSUMED:
            return BoundaryClassification.ASSUMED
        return BoundaryClassification.REQUIRES_PROOF

    # ── Internal helpers ──────────────────────────────────────────────────

    def _is_numeric_section(self, section: LocalSection) -> bool:
        """Check if a section's carrier type is numeric."""
        ct = section.carrier_type
        if ct is None:
            return False
        type_str = str(ct).lower()
        if any(t in type_str for t in ("int", "float", "complex", "number", "bool")):
            return True
        refs = section.refinements
        if any(k in refs for k in ("lower_bound", "upper_bound", "min", "max",
                                    "positive", "non_negative", "negative",
                                    "_interval", "_divisibility")):
            return True
        return False

    def _extract_constraints(self, section: LocalSection) -> List[ArithmeticConstraint]:
        """Extract arithmetic constraints from a section's refinements."""
        constraints: List[ArithmeticConstraint] = []
        refs = section.refinements

        comparisons = refs.get("_comparisons")
        if isinstance(comparisons, list):
            for comp in comparisons:
                if isinstance(comp, dict) and "op" in comp:
                    variables = comp.get("variables", [])
                    constraints.append(ArithmeticConstraint(
                        kind=ConstraintKind.COMPARISON,
                        variables=variables,
                        data=comp["op"],
                        explanation=comp.get("explanation", ""),
                    ))

        affine_rels = refs.get("_affine_relations")
        if isinstance(affine_rels, list):
            for rel in affine_rels:
                if isinstance(rel, AffineRelation):
                    constraints.append(ArithmeticConstraint(
                        kind=ConstraintKind.AFFINE,
                        variables=[section.site_id.name],
                        data=rel,
                    ))

        bounds = refs.get("_bound_constraints")
        if isinstance(bounds, list):
            for bc in bounds:
                if isinstance(bc, dict):
                    var = bc.get("variable", section.site_id.name)
                    lo = bc.get("lo", NEG_INF)
                    hi = bc.get("hi", INF)
                    constraints.append(ArithmeticConstraint(
                        kind=ConstraintKind.BOUND,
                        variables=[var],
                        data=Interval(lo, hi),
                    ))

        return constraints
