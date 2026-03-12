"""Decode Z3 models back into deppy values and counterexamples.

When the solver returns SAT, the Z3 model contains variable assignments in
Z3's internal representation.  This module converts those back into plain
Python values that the deppy kernel and error-reporting layers can consume.

Key types:

- **CounterExample**: A frozen dataclass containing the decoded variable
  values together with a human-readable explanation of *why* the obligation
  failed (i.e., why a satisfying assignment to the negation exists).
- **Z3Decoder**: The stateful decoder that interprets a Z3 model in the
  context of a ``VariableEnvironment`` and an obligation.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field
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

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Lazy Z3 import
# ---------------------------------------------------------------------------

_z3: Any = None


def _ensure_z3() -> Any:
    global _z3
    if _z3 is not None:
        return _z3
    try:
        import z3 as _z3_mod
        _z3 = _z3_mod
        return _z3
    except ImportError:
        raise ImportError(
            "z3-solver is not installed.  Install it with: pip install z3-solver"
        )


# ---------------------------------------------------------------------------
# CounterExample
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CounterExample:
    """A concrete counterexample demonstrating why an obligation is invalid.

    Attributes:
        variable_values: Mapping from variable names to their concrete values
            in the counterexample.  Values are plain Python types (int, float,
            bool, str, None).
        explanation: A human-readable string explaining the counterexample.
        obligation_description: Description of the obligation that was violated.
        violated_constraints: List of constraint descriptions that are violated
            under this assignment.
        raw_model: The raw Z3 model (for debugging; not frozen-safe, so stored
            as ``Any``).
    """

    variable_values: Dict[str, Any] = field(default_factory=dict)
    explanation: str = ""
    obligation_description: str = ""
    violated_constraints: Tuple[str, ...] = ()
    raw_model: Optional[Any] = field(default=None, compare=False, hash=False)

    def pretty(self) -> str:
        """Format the counterexample for human consumption."""
        lines = ["Counterexample:"]
        if self.obligation_description:
            lines.append(f"  Obligation: {self.obligation_description}")
        lines.append("  Variable assignments:")
        for name, value in sorted(self.variable_values.items()):
            # Skip internal variables
            if name.startswith("__"):
                continue
            lines.append(f"    {name} = {value!r}")
        if self.violated_constraints:
            lines.append("  Violated constraints:")
            for vc in self.violated_constraints:
                lines.append(f"    - {vc}")
        if self.explanation:
            lines.append(f"  Explanation: {self.explanation}")
        return "\n".join(lines)

    @property
    def user_variables(self) -> Dict[str, Any]:
        """Return only user-visible variables (excluding internal __xxx ones)."""
        return {k: v for k, v in self.variable_values.items()
                if not k.startswith("__")}


# ---------------------------------------------------------------------------
# Decoded value types
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DecodedArray:
    """Decoded representation of a Z3 array value."""
    default_value: Any = None
    entries: Tuple[Tuple[Any, Any], ...] = ()

    def as_dict(self) -> Dict[Any, Any]:
        d = {k: v for k, v in self.entries}
        return d

    def __repr__(self) -> str:
        entries_str = ", ".join(f"{k}: {v}" for k, v in self.entries)
        return f"Array(default={self.default_value!r}, {{{entries_str}}})"


@dataclass(frozen=True)
class DecodedBitVec:
    """Decoded representation of a Z3 bitvector value."""
    value: int
    width: int

    def __repr__(self) -> str:
        return f"BitVec({self.value}, width={self.width})"


@dataclass(frozen=True)
class DecodedRational:
    """Decoded representation of a Z3 rational value."""
    numerator: int
    denominator: int

    @property
    def as_float(self) -> float:
        if self.denominator == 0:
            return float("inf")
        return self.numerator / self.denominator

    def __repr__(self) -> str:
        return f"Rational({self.numerator}/{self.denominator})"


# ---------------------------------------------------------------------------
# Z3 Decoder
# ---------------------------------------------------------------------------


class Z3Decoder:
    """Decodes Z3 models into plain Python values.

    Given a Z3 model and the variable environment used during encoding,
    extracts concrete values for each variable.

    Usage::

        decoder = Z3Decoder()
        values = decoder.decode_model(z3_model, env)
        counter = decoder.decode_counterexample(z3_model, env, obligation)
    """

    def __init__(self) -> None:
        self._z3 = _ensure_z3()

    # -------------------------------------------------------------------
    # Public API
    # -------------------------------------------------------------------

    def decode_model(
        self,
        model: Any,
        env: Optional[Any] = None,
    ) -> Dict[str, Any]:
        """Decode a Z3 model into a dict of variable_name -> Python value.

        Args:
            model: A ``z3.ModelRef`` from a SAT result.
            env: Optional ``VariableEnvironment`` from the encoder.  If
                provided, only variables in the environment are decoded.
                Otherwise, all model declarations are decoded.

        Returns:
            A dict mapping variable names to decoded Python values.
        """
        z3 = self._z3
        result: Dict[str, Any] = {}

        if env is not None:
            # Decode variables that were registered in the environment
            for name, z3_var in env.z3_vars().items():
                try:
                    val = model.eval(z3_var, model_completion=True)
                    result[name] = self._decode_value(val)
                except Exception as e:
                    logger.debug("Could not decode variable %s: %s", name, e)
                    result[name] = None
        else:
            # Decode all declarations in the model
            for decl in model.decls():
                name = decl.name()
                try:
                    val = model[decl]
                    result[name] = self._decode_value(val)
                except Exception as e:
                    logger.debug("Could not decode decl %s: %s", name, e)
                    result[name] = None

        return result

    def decode_counterexample(
        self,
        model: Any,
        env: Optional[Any] = None,
        obligation: Optional[Any] = None,
    ) -> CounterExample:
        """Decode a Z3 model into a ``CounterExample``.

        Args:
            model: A ``z3.ModelRef`` from a SAT result.
            env: Optional ``VariableEnvironment`` from encoding.
            obligation: Optional ``SolverObligation`` for context.

        Returns:
            A ``CounterExample`` with decoded values and explanation.
        """
        values = self.decode_model(model, env)
        description = ""
        if obligation is not None and hasattr(obligation, "description"):
            description = obligation.description

        # Build explanation
        explanation = self._build_explanation(values, obligation)

        # Identify violated constraints
        violated = self._identify_violated_constraints(values, obligation)

        return CounterExample(
            variable_values=values,
            explanation=explanation,
            obligation_description=description,
            violated_constraints=tuple(violated),
            raw_model=model,
        )

    def decode_unsat_core(
        self,
        core: Any,
    ) -> List[str]:
        """Decode a Z3 UNSAT core into human-readable constraint names.

        Args:
            core: A list of Z3 expressions forming the UNSAT core.

        Returns:
            A list of string representations of the core constraints.
        """
        result: List[str] = []
        for expr in core:
            result.append(str(expr))
        return result

    # -------------------------------------------------------------------
    # Value decoding
    # -------------------------------------------------------------------

    def _decode_value(self, val: Any) -> Any:
        """Decode a single Z3 value into a Python value."""
        z3 = self._z3

        if val is None:
            return None

        # Boolean
        if z3.is_true(val):
            return True
        if z3.is_false(val):
            return False

        # Integer
        if z3.is_int_value(val):
            return val.as_long()

        # Rational / Real
        if z3.is_rational_value(val):
            num = val.numerator_as_long()
            den = val.denominator_as_long()
            if den == 1:
                return num
            return DecodedRational(num, den)

        # Algebraic number (irrational real)
        if z3.is_algebraic_value(val):
            try:
                approx = val.approx(20)
                num = approx.numerator_as_long()
                den = approx.denominator_as_long()
                return num / den if den != 0 else float("nan")
            except Exception:
                return str(val)

        # Bitvector
        if z3.is_bv_value(val):
            return DecodedBitVec(
                value=val.as_long(),
                width=val.size(),
            )

        # String
        if z3.is_string_value(val):
            return val.as_string()

        # Array
        if hasattr(val, "as_list") and callable(getattr(val, "as_list", None)):
            try:
                entries_raw = val.as_list()
                if entries_raw:
                    default = self._decode_value(entries_raw[-1])
                    entries = []
                    for entry in entries_raw[:-1]:
                        if len(entry) == 2:
                            k = self._decode_value(entry[0])
                            v = self._decode_value(entry[1])
                            entries.append((k, v))
                    return DecodedArray(
                        default_value=default,
                        entries=tuple(entries),
                    )
            except Exception:
                pass

        # Fallback: use Z3's string representation
        try:
            # Try to extract a numeric value from the string
            s = str(val)
            if s.lstrip("-").isdigit():
                return int(s)
            try:
                return float(s)
            except ValueError:
                pass
            return s
        except Exception:
            return str(val)

    # -------------------------------------------------------------------
    # Explanation generation
    # -------------------------------------------------------------------

    def _build_explanation(
        self,
        values: Dict[str, Any],
        obligation: Optional[Any],
    ) -> str:
        """Generate a human-readable explanation of the counterexample."""
        parts: List[str] = []

        # Filter to user-visible variables
        user_vars = {k: v for k, v in values.items() if not k.startswith("__")}

        if not user_vars:
            return "No user-visible variables in counterexample."

        parts.append(f"Found concrete values for {len(user_vars)} variable(s)")
        parts.append("that violate the obligation:")

        if obligation is not None and hasattr(obligation, "formula"):
            try:
                formula_str = obligation.formula.pretty()
                if len(formula_str) > 200:
                    formula_str = formula_str[:200] + "..."
                parts.append(f"  Formula: {formula_str}")
            except Exception:
                pass

        parts.append("  Assignments:")
        for name, val in sorted(user_vars.items()):
            parts.append(f"    {name} = {val!r}")

        return "\n".join(parts)

    def _identify_violated_constraints(
        self,
        values: Dict[str, Any],
        obligation: Optional[Any],
    ) -> List[str]:
        """Identify which constraints from the obligation are violated.

        This does a best-effort evaluation of each sub-predicate under
        the concrete assignment.
        """
        if obligation is None or not hasattr(obligation, "formula"):
            return []

        violated: List[str] = []
        formula = obligation.formula

        # Walk top-level conjuncts if it is an And
        from deppy.predicates.boolean import And
        if isinstance(formula, And):
            for conjunct in formula.conjuncts:
                if self._is_violated(conjunct, values):
                    violated.append(conjunct.pretty())
        else:
            if self._is_violated(formula, values):
                violated.append(formula.pretty())

        return violated

    def _is_violated(self, pred: Any, values: Dict[str, Any]) -> bool:
        """Best-effort check whether a predicate is violated under values.

        Returns True if we can definitively determine violation, False otherwise.
        """
        from deppy.predicates.arithmetic import Comparison, IntRange, LinearInequality
        from deppy.predicates.base import IntLit, Var

        if isinstance(pred, Comparison):
            left_val = self._eval_term(pred.left, values)
            right_val = self._eval_term(pred.right, values)
            if left_val is None or right_val is None:
                return False
            try:
                op = pred.op
                if op == "<":
                    return not (left_val < right_val)
                if op == "<=":
                    return not (left_val <= right_val)
                if op == ">":
                    return not (left_val > right_val)
                if op == ">=":
                    return not (left_val >= right_val)
                if op == "==":
                    return not (left_val == right_val)
                if op == "!=":
                    return not (left_val != right_val)
            except TypeError:
                return False

        if isinstance(pred, IntRange):
            val = values.get(pred.variable)
            if val is None or not isinstance(val, (int, float)):
                return False
            if pred.lo is not None and val < pred.lo:
                return True
            if pred.hi is not None and val > pred.hi:
                return True
            return False

        if isinstance(pred, LinearInequality):
            total = pred.constant
            for var_name, coeff in pred.coefficients:
                val = values.get(var_name)
                if val is None or not isinstance(val, (int, float)):
                    return False
                total += coeff * val
            return total < 0

        return False

    def _eval_term(self, term: Any, values: Dict[str, Any]) -> Any:
        """Best-effort evaluation of a term under concrete values."""
        from deppy.predicates.base import (
            Var, IntLit, FloatLit, BoolLit, StrLit, NoneLit,
            BinOp, UnaryOp,
        )

        if isinstance(term, IntLit):
            return term.value
        if isinstance(term, FloatLit):
            return term.value
        if isinstance(term, BoolLit):
            return term.value
        if isinstance(term, StrLit):
            return term.value
        if isinstance(term, NoneLit):
            return None
        if isinstance(term, Var):
            return values.get(term.name)
        if isinstance(term, UnaryOp):
            operand = self._eval_term(term.operand, values)
            if operand is None:
                return None
            if term.op == "-":
                return -operand
            if term.op == "+":
                return operand
            if term.op == "~":
                return ~operand
            return None
        if isinstance(term, BinOp):
            left = self._eval_term(term.left, values)
            right = self._eval_term(term.right, values)
            if left is None or right is None:
                return None
            try:
                op = term.op
                if op == "+":
                    return left + right
                if op == "-":
                    return left - right
                if op == "*":
                    return left * right
                if op == "//":
                    return left // right if right != 0 else None
                if op == "%":
                    return left % right if right != 0 else None
                if op == "**":
                    return left ** right
                if op == "&":
                    return left & right
                if op == "|":
                    return left | right
                if op == "^":
                    return left ^ right
                if op == "<<":
                    return left << right
                if op == ">>":
                    return left >> right
            except (TypeError, OverflowError, ValueError):
                return None
        return None


# ---------------------------------------------------------------------------
# Convenience functions
# ---------------------------------------------------------------------------


def decode_model(model: Any, env: Optional[Any] = None) -> Dict[str, Any]:
    """One-shot model decoding."""
    decoder = Z3Decoder()
    return decoder.decode_model(model, env)


def decode_counterexample(
    model: Any,
    env: Optional[Any] = None,
    obligation: Optional[Any] = None,
) -> CounterExample:
    """One-shot counterexample decoding."""
    decoder = Z3Decoder()
    return decoder.decode_counterexample(model, env, obligation)
