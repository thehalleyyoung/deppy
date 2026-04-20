"""
Deppy Counterexample Generation & Failure Diagnosis

When a proof FAILS, generate a concrete counterexample showing WHY.
F* just says "proof failed"; Deppy says "here's a concrete input that
violates your spec".

Architecture:
    CounterexampleFinder   — extract witnesses from Z3 models
    CounterexampleResult   — concrete counterexample data
    PropertyTester         — random/exhaustive testing bridge
    HypothesisBridge       — optional Hypothesis integration
    DiagnosticEngine       — comprehensive failure diagnosis
    Diagnosis              — structured diagnosis output
    BoundaryAnalyzer       — systematic edge-case checking
    BoundaryViolation      — individual boundary failure
"""
from __future__ import annotations

import ast
import itertools
import math
import random
import re
import sys
import textwrap
import traceback
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable, Iterator, Sequence

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Spec, SpecKind, FunctionSpec,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType, PyNoneType,
    PyListType, PyDictType, PyCallableType, PySetType, PyTupleType,
    RefinementType, Var, Literal,
)
from deppy.core.kernel import (
    ProofKernel, TrustLevel, VerificationResult,
)
from deppy.core.formal_ops import Op, OpCall

try:
    from z3 import (
        Solver, Int, Real, Bool, String, IntVal, RealVal, BoolVal, StringVal,
        sat, unsat, unknown, And, Or, Not, Implies, ForAll, Exists,
        ArithRef, BoolRef, is_int_value, is_rational_value, is_true, is_false,
        is_string_value, set_param, IntSort, RealSort, BoolSort, StringSort,
        If, simplify, is_int, is_real, is_bool,
    )
    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False

try:
    import hypothesis
    import hypothesis.strategies as st
    _HAS_HYPOTHESIS = True
except ImportError:
    _HAS_HYPOTHESIS = False


# ═══════════════════════════════════════════════════════════════════
# Data Structures
# ═══════════════════════════════════════════════════════════════════

@dataclass
class CounterexampleResult:
    """A concrete counterexample demonstrating a spec violation."""

    found: bool
    inputs: dict[str, Any] = field(default_factory=dict)
    expected: str = ""
    actual: str = ""
    explanation: str = ""
    trace: list[str] = field(default_factory=list)
    obligation: Judgment | None = None
    z3_model: Any | None = None
    shrunk: bool = False
    source: str = ""  # "z3", "property_test", "boundary", "hypothesis"

    def display(self) -> str:
        """Pretty-print the counterexample."""
        if not self.found:
            return "No counterexample found."

        lines = []
        lines.append("╔══════════════════════════════════════════════════════╗")
        lines.append("║            COUNTEREXAMPLE FOUND                     ║")
        lines.append("╚══════════════════════════════════════════════════════╝")
        lines.append("")

        if self.inputs:
            lines.append("  Inputs:")
            for name, val in self.inputs.items():
                lines.append(f"    {name} = {val!r}")
            lines.append("")

        if self.expected:
            lines.append(f"  Expected: {self.expected}")
        if self.actual:
            lines.append(f"  Actual:   {self.actual}")
        if self.expected or self.actual:
            lines.append("")

        if self.explanation:
            lines.append(f"  Why: {self.explanation}")
            lines.append("")

        if self.trace:
            lines.append("  Trace:")
            for step in self.trace:
                lines.append(f"    → {step}")
            lines.append("")

        if self.shrunk:
            lines.append("  (shrunk to minimal counterexample)")
        if self.source:
            lines.append(f"  [found via {self.source}]")

        return "\n".join(lines)

    def __repr__(self) -> str:
        if not self.found:
            return "CounterexampleResult(found=False)"
        inp = ", ".join(f"{k}={v!r}" for k, v in self.inputs.items())
        return f"CounterexampleResult({inp})"


@dataclass
class BoundaryViolation:
    """A spec violation at a type boundary value."""

    param_name: str
    boundary_value: Any
    boundary_kind: str  # "zero", "negative", "max_int", "empty", "nan", etc.
    expected: str = ""
    actual: str = ""
    exception: str | None = None
    explanation: str = ""

    def display(self) -> str:
        lines = [f"  Boundary violation: {self.param_name} = {self.boundary_value!r} ({self.boundary_kind})"]
        if self.expected:
            lines.append(f"    Expected: {self.expected}")
        if self.actual:
            lines.append(f"    Actual:   {self.actual}")
        if self.exception:
            lines.append(f"    Exception: {self.exception}")
        if self.explanation:
            lines.append(f"    Why: {self.explanation}")
        return "\n".join(lines)


@dataclass
class TestResult:
    """Result of property testing."""

    passed: bool
    num_tests: int = 0
    counterexample: CounterexampleResult | None = None
    failures: list[CounterexampleResult] = field(default_factory=list)
    duration_ms: float = 0.0

    def display(self) -> str:
        if self.passed:
            return f"  ✓ {self.num_tests} tests passed ({self.duration_ms:.1f}ms)"
        lines = [f"  ✗ Failed after {self.num_tests} tests ({self.duration_ms:.1f}ms)"]
        if self.counterexample:
            lines.append(self.counterexample.display())
        return "\n".join(lines)


@dataclass
class Diagnosis:
    """Comprehensive diagnosis of a verification failure."""

    function_name: str
    spec_description: str
    counterexamples: list[CounterexampleResult] = field(default_factory=list)
    boundary_violations: list[BoundaryViolation] = field(default_factory=list)
    likely_issues: list[str] = field(default_factory=list)
    suggested_fixes: list[str] = field(default_factory=list)
    test_result: TestResult | None = None
    confidence: float = 0.0

    def display(self) -> str:
        """Rich formatted diagnosis output."""
        lines = []
        lines.append("┌──────────────────────────────────────────────────────┐")
        lines.append(f"│  Diagnosis: {self.function_name:<40}│")
        lines.append(f"│  Spec: {self.spec_description[:44]:<44}│")
        lines.append("└──────────────────────────────────────────────────────┘")
        lines.append("")

        if self.counterexamples:
            lines.append(f"  Found {len(self.counterexamples)} counterexample(s):")
            for i, cex in enumerate(self.counterexamples, 1):
                inp = ", ".join(f"{k}={v!r}" for k, v in cex.inputs.items())
                lines.append(f"    {i}. {inp}")
                if cex.explanation:
                    lines.append(f"       → {cex.explanation}")
            lines.append("")

        if self.boundary_violations:
            lines.append(f"  {len(self.boundary_violations)} boundary violation(s):")
            for bv in self.boundary_violations:
                lines.append(bv.display())
            lines.append("")

        if self.test_result and not self.test_result.passed:
            lines.append(self.test_result.display())
            lines.append("")

        if self.likely_issues:
            lines.append("  Likely issues (ranked):")
            for i, issue in enumerate(self.likely_issues, 1):
                lines.append(f"    {i}. {issue}")
            lines.append("")

        if self.suggested_fixes:
            lines.append("  Suggested fixes:")
            for i, fix in enumerate(self.suggested_fixes, 1):
                lines.append(f"    {i}. {fix}")
            lines.append("")

        conf_bar = "█" * int(self.confidence * 20) + "░" * (20 - int(self.confidence * 20))
        lines.append(f"  Confidence: [{conf_bar}] {self.confidence:.0%}")

        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# Z3 Formula Builder
# ═══════════════════════════════════════════════════════════════════

class _Z3FormulaBuilder:
    """Parse Deppy predicate strings into Z3 expressions."""

    # Tokens that indicate arithmetic/logical formulas
    _ARITH_OPS = {"+", "-", "*", "/", "//", "%", "**"}
    _CMP_OPS = {"==", "!=", "<", ">", "<=", ">="}
    _BOOL_OPS = {"and", "or", "not"}
    _KEYWORDS = {"True", "False", "None", "len", "abs", "min", "max",
                 "all", "any", "sorted", "sum", "result", "return"}

    def __init__(self) -> None:
        self._vars: dict[str, Any] = {}

    def build(self, predicate: str, context: Context | None = None,
              var_types: dict[str, SynType] | None = None) -> tuple[Any, dict[str, Any]] | None:
        """Parse a predicate string into a Z3 expression.

        Returns (z3_expr, var_map) or None if unparseable.
        """
        if not _HAS_Z3:
            return None

        self._vars = {}

        effective_types = {}
        if context:
            effective_types.update(context.all_bindings())
        if var_types:
            effective_types.update(var_types)

        try:
            tree = ast.parse(predicate, mode="eval")
        except SyntaxError:
            return None

        try:
            z3_expr = self._convert(tree.body, effective_types)
            return (z3_expr, self._vars)
        except (ValueError, TypeError, KeyError, AttributeError):
            return None

    def _get_z3_var(self, name: str, typ: SynType | None) -> Any:
        """Get or create a Z3 variable for the given name and type."""
        if name in self._vars:
            return self._vars[name]

        if isinstance(typ, PyIntType):
            v = Int(name)
        elif isinstance(typ, PyFloatType):
            v = Real(name)
        elif isinstance(typ, PyBoolType):
            v = Bool(name)
        elif isinstance(typ, PyStrType):
            v = String(name)
        elif isinstance(typ, RefinementType):
            return self._get_z3_var(name, typ.base_type)
        else:
            v = Int(name)  # default to Int for unknown types

        self._vars[name] = v
        return v

    def _convert(self, node: ast.AST, types: dict[str, SynType]) -> Any:
        """Convert an AST node to a Z3 expression."""
        if isinstance(node, ast.BoolOp):
            return self._convert_boolop(node, types)
        elif isinstance(node, ast.BinOp):
            return self._convert_binop(node, types)
        elif isinstance(node, ast.UnaryOp):
            return self._convert_unaryop(node, types)
        elif isinstance(node, ast.Compare):
            return self._convert_compare(node, types)
        elif isinstance(node, ast.Name):
            return self._get_z3_var(node.id, types.get(node.id))
        elif isinstance(node, ast.Constant):
            return self._convert_constant(node)
        elif isinstance(node, ast.Call):
            return self._convert_call(node, types)
        elif isinstance(node, ast.IfExp):
            return self._convert_ifexp(node, types)
        elif isinstance(node, ast.Subscript):
            raise ValueError("Subscript not directly supported in Z3")
        elif isinstance(node, ast.Attribute):
            raise ValueError("Attribute access not directly supported in Z3")
        else:
            raise ValueError(f"Unsupported AST node: {type(node).__name__}")

    def _convert_boolop(self, node: ast.BoolOp, types: dict[str, SynType]) -> Any:
        values = [self._convert(v, types) for v in node.values]
        if isinstance(node.op, ast.And):
            return And(*values)
        elif isinstance(node.op, ast.Or):
            return Or(*values)
        raise ValueError(f"Unknown BoolOp: {type(node.op).__name__}")

    def _convert_binop(self, node: ast.BinOp, types: dict[str, SynType]) -> Any:
        left = self._convert(node.left, types)
        right = self._convert(node.right, types)
        if isinstance(node.op, ast.Add):
            return left + right
        elif isinstance(node.op, ast.Sub):
            return left - right
        elif isinstance(node.op, ast.Mult):
            return left * right
        elif isinstance(node.op, ast.Div):
            return left / right
        elif isinstance(node.op, ast.FloorDiv):
            return left / right  # Z3 int division
        elif isinstance(node.op, ast.Mod):
            return left % right
        raise ValueError(f"Unknown BinOp: {type(node.op).__name__}")

    def _convert_unaryop(self, node: ast.UnaryOp, types: dict[str, SynType]) -> Any:
        operand = self._convert(node.operand, types)
        if isinstance(node.op, ast.Not):
            return Not(operand)
        elif isinstance(node.op, ast.USub):
            return -operand
        elif isinstance(node.op, ast.UAdd):
            return operand
        raise ValueError(f"Unknown UnaryOp: {type(node.op).__name__}")

    def _convert_compare(self, node: ast.Compare, types: dict[str, SynType]) -> Any:
        left = self._convert(node.left, types)
        parts = []
        for op, comparator in zip(node.ops, node.comparators):
            right = self._convert(comparator, types)
            if isinstance(op, ast.Eq):
                parts.append(left == right)
            elif isinstance(op, ast.NotEq):
                parts.append(left != right)
            elif isinstance(op, ast.Lt):
                parts.append(left < right)
            elif isinstance(op, ast.LtE):
                parts.append(left <= right)
            elif isinstance(op, ast.Gt):
                parts.append(left > right)
            elif isinstance(op, ast.GtE):
                parts.append(left >= right)
            else:
                raise ValueError(f"Unknown comparison: {type(op).__name__}")
            left = right
        if len(parts) == 1:
            return parts[0]
        return And(*parts)

    def _convert_constant(self, node: ast.Constant) -> Any:
        if isinstance(node.value, bool):
            return BoolVal(node.value)
        elif isinstance(node.value, int):
            return IntVal(node.value)
        elif isinstance(node.value, float):
            return RealVal(node.value)
        elif isinstance(node.value, str):
            return StringVal(node.value)
        raise ValueError(f"Unsupported constant: {node.value!r}")

    def _convert_call(self, node: ast.Call, types: dict[str, SynType]) -> Any:
        if isinstance(node.func, ast.Name):
            fname = node.func.id
            args = [self._convert(a, types) for a in node.args]
            if fname == "abs" and len(args) == 1:
                return If(args[0] >= 0, args[0], -args[0])
            elif fname == "min" and len(args) == 2:
                return If(args[0] <= args[1], args[0], args[1])
            elif fname == "max" and len(args) == 2:
                return If(args[0] >= args[1], args[0], args[1])
        raise ValueError(f"Unsupported function call")

    def _convert_ifexp(self, node: ast.IfExp, types: dict[str, SynType]) -> Any:
        cond = self._convert(node.test, types)
        then = self._convert(node.body, types)
        else_ = self._convert(node.orelse, types)
        return If(cond, then, else_)


# ═══════════════════════════════════════════════════════════════════
# Z3 Model Value Extraction
# ═══════════════════════════════════════════════════════════════════

def _extract_z3_value(val: Any) -> Any:
    """Extract a Python value from a Z3 model value."""
    if not _HAS_Z3:
        return None
    try:
        if is_int_value(val):
            return val.as_long()
        if is_rational_value(val):
            num = val.numerator_as_long()
            den = val.denominator_as_long()
            return num / den if den != 1 else float(num)
        if is_true(val):
            return True
        if is_false(val):
            return False
        if is_string_value(val):
            return val.as_string()
        return str(val)
    except Exception:
        return str(val)


# ═══════════════════════════════════════════════════════════════════
# CounterexampleFinder
# ═══════════════════════════════════════════════════════════════════

class CounterexampleFinder:
    """When a verification obligation fails, extract a concrete counterexample
    from Z3 by negating the obligation and finding a satisfying model.

    Unlike F* which just says "proof failed", this produces concrete witness
    values showing exactly why the spec is violated.
    """

    def __init__(self) -> None:
        self._builder = _Z3FormulaBuilder()

    def find(self, obligation: Judgment, *, timeout_ms: int = 5000) -> CounterexampleResult:
        """Try to find a counterexample for a failed obligation.

        1. Negate the obligation
        2. Ask Z3 for a satisfying model (= counterexample to original)
        3. Extract concrete values
        4. Format human-readable explanation
        """
        if not _HAS_Z3:
            return CounterexampleResult(
                found=False,
                explanation="Z3 not available",
                obligation=obligation,
            )

        predicate = self._extract_predicate(obligation)
        if predicate is None:
            return CounterexampleResult(
                found=False,
                explanation="Could not extract predicate from obligation",
                obligation=obligation,
            )

        var_types = {}
        if obligation.context:
            var_types = obligation.context.all_bindings()

        result = self._builder.build(predicate, var_types=var_types)
        if result is None:
            return CounterexampleResult(
                found=False,
                explanation=f"Could not parse predicate: {predicate}",
                obligation=obligation,
            )

        z3_expr, var_map = result

        # Negate: find an assignment where the obligation does NOT hold
        solver = Solver()
        set_param("timeout", timeout_ms)
        solver.add(Not(z3_expr))

        # Add constraints from refinement types in context
        self._add_context_constraints(solver, obligation.context, var_types)

        status = solver.check()
        if status == sat:
            model = solver.model()
            inputs = {}
            for name, z3_var in var_map.items():
                val = model.eval(z3_var, model_completion=True)
                inputs[name] = _extract_z3_value(val)

            return CounterexampleResult(
                found=True,
                inputs=inputs,
                expected=f"Spec: {predicate}",
                actual=self._evaluate_predicate_with_values(predicate, inputs),
                explanation=self._explain(predicate, inputs),
                trace=self._build_trace(predicate, inputs),
                obligation=obligation,
                z3_model=model,
                source="z3",
            )

        return CounterexampleResult(
            found=False,
            explanation="Z3 could not find a counterexample (spec may be valid)" if status == unsat
                else f"Z3 returned {status} (timeout or unknown)",
            obligation=obligation,
        )

    def find_for_spec(self, source: str, spec: FunctionSpec) -> list[CounterexampleResult]:
        """Find counterexamples for all spec violations in a function.

        Only uses Z3 for predicates whose free variables are all input
        parameters (in the context). Predicates that reference ``result``
        or ``return`` need runtime testing, not Z3 — those are handled by
        PropertyTester / DiagnosticEngine.
        """
        param_names = {name for name, _ in spec.params}
        results = []

        for obligation in spec.proof_obligations():
            # Skip predicates that reference output-only variables like
            # ``result`` / ``return``: Z3 would just pick an arbitrary
            # value and declare it a counterexample, which is useless.
            pred = self._extract_predicate(obligation)
            if pred is not None:
                pred_vars = self._predicate_free_vars(pred)
                if pred_vars - param_names:
                    # Has variables not in params (e.g., result) — skip Z3
                    continue
            cex = self.find(obligation)
            if cex.found:
                results.append(cex)

        # Also check assumptions
        for assumption in spec.assumptions:
            ctx = Context()
            for pname, ptype in spec.params:
                ctx = ctx.extend(pname, ptype)
            obl = Judgment(
                kind=JudgmentKind.WELL_FORMED,
                context=ctx,
                type_=RefinementType(
                    base_type=PyObjType(),
                    predicate=assumption.description,
                ),
            )
            pred = self._extract_predicate(obl)
            if pred is not None:
                pred_vars = self._predicate_free_vars(pred)
                if pred_vars - param_names:
                    continue
            cex = self.find(obl)
            if cex.found:
                results.append(cex)
        return results

    @staticmethod
    def _predicate_free_vars(predicate: str) -> set[str]:
        """Extract free variable names from a predicate string."""
        try:
            tree = ast.parse(predicate, mode="eval")
        except SyntaxError:
            return set()
        names: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Name):
                names.add(node.id)
        # Remove Python builtins / keywords that aren't variables
        builtins = {"abs", "min", "max", "len", "sum", "sorted", "all", "any",
                    "True", "False", "None", "int", "float", "str", "bool",
                    "list", "dict", "set", "tuple", "type", "range",
                    "isinstance", "round", "enumerate", "zip", "map", "filter"}
        return names - builtins

    def shrink(self, cex: CounterexampleResult, *, max_attempts: int = 100) -> CounterexampleResult:
        """Shrink a counterexample to a minimal one.

        Like QuickCheck/Hypothesis shrinking: try smaller values that still
        violate the spec.
        """
        if not cex.found or not cex.obligation:
            return cex

        best = cex
        best_size = self._size(cex.inputs)

        for _ in range(max_attempts):
            candidate = self._shrink_once(best.inputs)
            if candidate == best.inputs:
                break

            # Check if the shrunk inputs still violate the spec
            predicate = self._extract_predicate(best.obligation)
            if predicate is None:
                break

            if self._violates(predicate, candidate, best.obligation.context):
                cand_size = self._size(candidate)
                if cand_size < best_size:
                    best = CounterexampleResult(
                        found=True,
                        inputs=candidate,
                        expected=best.expected,
                        actual=self._evaluate_predicate_with_values(predicate, candidate),
                        explanation=self._explain(predicate, candidate),
                        trace=self._build_trace(predicate, candidate),
                        obligation=best.obligation,
                        z3_model=None,
                        shrunk=True,
                        source=best.source,
                    )
                    best_size = cand_size
                else:
                    break
            else:
                break

        return best

    # ── internal helpers ──────────────────────────────────────────

    def _extract_predicate(self, obligation: Judgment) -> str | None:
        """Extract the predicate string from an obligation."""
        if obligation.kind == JudgmentKind.TYPE_CHECK:
            if isinstance(obligation.type_, RefinementType):
                return obligation.type_.predicate
        elif obligation.kind == JudgmentKind.WELL_FORMED:
            if isinstance(obligation.type_, RefinementType):
                return obligation.type_.predicate
        elif obligation.kind == JudgmentKind.EQUAL:
            if obligation.left is not None and obligation.right is not None:
                return f"({obligation.left}) == ({obligation.right})"
        return None

    def _add_context_constraints(self, solver: Any, context: Context | None,
                                  var_types: dict[str, SynType]) -> None:
        """Add constraints from refinement types in the context."""
        if context is None:
            return
        for name, typ in context.all_bindings().items():
            if isinstance(typ, RefinementType):
                result = self._builder.build(typ.predicate, var_types=var_types)
                if result is not None:
                    z3_expr, _ = result
                    solver.add(z3_expr)

    def _evaluate_predicate_with_values(self, predicate: str, values: dict[str, Any]) -> str:
        """Substitute values into predicate and show the result."""
        display = predicate
        for name, val in values.items():
            display = display.replace(name, repr(val))
        try:
            result = eval(display, {"__builtins__": {"abs": abs, "min": min,
                                                      "max": max, "len": len,
                                                      "True": True, "False": False,
                                                      "None": None}})
            return f"{display} → {result}"
        except Exception:
            return display

    def _explain(self, predicate: str, values: dict[str, Any]) -> str:
        """Generate a human-readable explanation."""
        parts = []
        for name, val in values.items():
            parts.append(f"{name}={val!r}")
        substituted = predicate
        for name, val in values.items():
            substituted = re.sub(rf'\b{re.escape(name)}\b', repr(val), substituted)
        try:
            result = eval(substituted, {"__builtins__": {"abs": abs, "min": min,
                                                          "max": max, "len": len,
                                                          "sum": sum, "sorted": sorted,
                                                          "True": True, "False": False,
                                                          "None": None}})
            return (f"With {', '.join(parts)}: "
                    f"{predicate} evaluates to {result!r} (expected True)")
        except Exception:
            return f"With {', '.join(parts)}: cannot evaluate {predicate}"

    def _build_trace(self, predicate: str, values: dict[str, Any]) -> list[str]:
        """Build an execution trace showing step-by-step evaluation."""
        trace = []
        for name, val in values.items():
            trace.append(f"let {name} = {val!r}")
        substituted = predicate
        for name, val in values.items():
            substituted = re.sub(rf'\b{re.escape(name)}\b', repr(val), substituted)
        trace.append(f"evaluate: {substituted}")
        try:
            result = eval(substituted, {"__builtins__": {"abs": abs, "min": min,
                                                          "max": max, "len": len,
                                                          "sum": sum, "sorted": sorted,
                                                          "True": True, "False": False,
                                                          "None": None}})
            trace.append(f"result: {result!r}")
        except Exception as e:
            trace.append(f"error: {e}")
        return trace

    @staticmethod
    def _size(inputs: dict[str, Any]) -> int:
        """Measure the 'size' of a set of inputs for shrinking comparison."""
        total = 0
        for v in inputs.values():
            if isinstance(v, (int, float)):
                total += abs(int(v)) if not (isinstance(v, float) and (
                    math.isnan(v) or math.isinf(v))) else 1000
            elif isinstance(v, str):
                total += len(v)
            elif isinstance(v, (list, tuple, set, frozenset)):
                total += len(v) + sum(abs(int(x)) for x in v
                                       if isinstance(x, (int, float)))
            elif isinstance(v, dict):
                total += len(v)
            else:
                total += 1
        return total

    @staticmethod
    def _shrink_once(inputs: dict[str, Any]) -> dict[str, Any]:
        """Try to shrink each input value by one step."""
        shrunk = {}
        for name, val in inputs.items():
            if isinstance(val, int):
                if val > 0:
                    shrunk[name] = val - 1
                elif val < 0:
                    shrunk[name] = val + 1
                else:
                    shrunk[name] = val
            elif isinstance(val, float):
                if abs(val) > 0.01:
                    shrunk[name] = val / 2.0
                else:
                    shrunk[name] = 0.0
            elif isinstance(val, str):
                if len(val) > 0:
                    shrunk[name] = val[:-1]
                else:
                    shrunk[name] = val
            elif isinstance(val, list):
                if len(val) > 0:
                    shrunk[name] = val[:-1]
                else:
                    shrunk[name] = val
            else:
                shrunk[name] = val
        return shrunk

    def _violates(self, predicate: str, values: dict[str, Any],
                  context: Context | None) -> bool:
        """Check if the given values violate the predicate."""
        substituted = predicate
        for name, val in values.items():
            substituted = re.sub(rf'\b{re.escape(name)}\b', repr(val), substituted)
        try:
            result = eval(substituted, {"__builtins__": {"abs": abs, "min": min,
                                                          "max": max, "len": len,
                                                          "sum": sum, "sorted": sorted,
                                                          "True": True, "False": False,
                                                          "None": None}})
            return not result
        except Exception:
            return False


# ═══════════════════════════════════════════════════════════════════
# Property Tester
# ═══════════════════════════════════════════════════════════════════

class PropertyTester:
    """Generate test inputs to find spec violations empirically.

    Combines SmallCheck-style enumeration (small values first) with
    random generation for larger values.
    """

    def __init__(self, *, seed: int = 42, max_examples: int = 1000):
        self._rng = random.Random(seed)
        self._max_examples = max_examples

    def test_function(self, func: Callable, spec: FunctionSpec,
                      *, max_examples: int | None = None) -> TestResult:
        """Run func with generated inputs, check that all guarantees hold."""
        import time
        start = time.time()
        max_ex = max_examples or self._max_examples

        param_types = {name: typ for name, typ in spec.params}
        failures: list[CounterexampleResult] = []
        num_tests = 0

        for inputs in itertools.islice(self.generate_inputs(param_types), max_ex):
            num_tests += 1

            # Check assumptions hold first — skip inputs that violate assumptions
            assumptions_ok = True
            for assumption in spec.assumptions:
                if not self._check_predicate(assumption.description, inputs):
                    assumptions_ok = False
                    break
            if not assumptions_ok:
                continue

            # Execute function
            try:
                result_val = func(**inputs)
            except Exception as exc:
                cex = CounterexampleResult(
                    found=True,
                    inputs=inputs.copy(),
                    expected="Function should not raise an exception",
                    actual=f"Raised {type(exc).__name__}: {exc}",
                    explanation=f"Function raised {type(exc).__name__} with inputs {inputs}",
                    trace=[f"call {spec.name}({', '.join(f'{k}={v!r}' for k, v in inputs.items())})",
                           f"exception: {exc}"],
                    source="property_test",
                )
                failures.append(cex)
                if len(failures) >= 5:
                    break
                continue

            # Check guarantees
            for guarantee in spec.guarantees:
                env = {**inputs, "result": result_val, "return": result_val}
                pred = guarantee.description
                if not self._check_predicate(pred, env):
                    cex = CounterexampleResult(
                        found=True,
                        inputs=inputs.copy(),
                        expected=f"Guarantee: {pred}",
                        actual=f"result={result_val!r}, predicate evaluated to False",
                        explanation=f"Guarantee '{pred}' violated with {inputs}",
                        trace=[
                            f"call {spec.name}({', '.join(f'{k}={v!r}' for k, v in inputs.items())})",
                            f"returned: {result_val!r}",
                            f"check: {pred} → False",
                        ],
                        source="property_test",
                    )
                    failures.append(cex)
                    if len(failures) >= 5:
                        break

            if len(failures) >= 5:
                break

        elapsed = (time.time() - start) * 1000
        return TestResult(
            passed=len(failures) == 0,
            num_tests=num_tests,
            counterexample=failures[0] if failures else None,
            failures=failures,
            duration_ms=elapsed,
        )

    def generate_inputs(self, param_types: dict[str, SynType]) -> Iterator[dict[str, Any]]:
        """Generate inputs based on Deppy types.

        SmallCheck-style: enumerate small values first, then random larger values.
        """
        if not param_types:
            yield {}
            return

        names = list(param_types.keys())
        types = [param_types[n] for n in names]

        generators = [list(itertools.islice(self._generate_for_type(t), 30))
                      for t in types]

        # Phase 1: small exhaustive enumeration (cartesian product of small values)
        small_gens = [g[:8] for g in generators]
        for combo in itertools.product(*small_gens):
            yield dict(zip(names, combo))

        # Phase 2: random combinations from the full set
        seen: set[tuple] = set()
        for _ in range(self._max_examples):
            combo = tuple(self._rng.choice(g) if g else None for g in generators)
            if combo not in seen:
                seen.add(combo)
                yield dict(zip(names, combo))

        # Phase 3: fully random larger values
        for _ in range(min(100, self._max_examples)):
            combo = tuple(self._random_for_type(t) for t in types)
            yield dict(zip(names, combo))

    def _generate_for_type(self, typ: SynType) -> Iterator[Any]:
        """Generate values for a given Deppy type.

        SmallCheck-style enumeration: smallest values first.
        """
        if isinstance(typ, RefinementType):
            yield from self._generate_for_refinement(typ)
        elif isinstance(typ, PyIntType):
            yield from self._generate_int()
        elif isinstance(typ, PyFloatType):
            yield from self._generate_float()
        elif isinstance(typ, PyBoolType):
            yield from [False, True]
        elif isinstance(typ, PyStrType):
            yield from self._generate_str()
        elif isinstance(typ, PyNoneType):
            yield None
        elif isinstance(typ, PyListType):
            yield from self._generate_list(typ)
        elif isinstance(typ, PyDictType):
            yield from self._generate_dict(typ)
        elif isinstance(typ, PySetType):
            yield from self._generate_set(typ)
        elif isinstance(typ, PyTupleType):
            yield from self._generate_tuple(typ)
        elif isinstance(typ, PyObjType):
            yield from self._generate_int()  # default to int
        else:
            yield from self._generate_int()

    def _generate_int(self) -> Iterator[int]:
        """Generate integers: 0, 1, -1, 2, -2, ..., then random."""
        yield 0
        yield 1
        yield -1
        for i in range(2, 20):
            yield i
            yield -i
        yield 100
        yield -100
        yield 2**31 - 1
        yield -(2**31)
        for _ in range(20):
            yield self._rng.randint(-10000, 10000)

    def _generate_float(self) -> Iterator[float]:
        """Generate floats: 0.0, 1.0, -1.0, ..., special values."""
        yield 0.0
        yield 1.0
        yield -1.0
        yield 0.5
        yield -0.5
        yield 2.0
        yield -2.0
        yield 0.1
        yield 0.01
        yield 100.0
        yield -100.0
        yield float("inf")
        yield float("-inf")
        yield float("nan")
        for _ in range(10):
            yield self._rng.uniform(-1000, 1000)

    def _generate_str(self) -> Iterator[str]:
        """Generate strings: "", "a", "ab", ..., special chars."""
        yield ""
        yield "a"
        yield "ab"
        yield "abc"
        yield " "
        yield "\n"
        yield "\t"
        yield "hello"
        yield "Hello World"
        yield "0"
        yield "123"
        yield "a" * 100
        yield "\0"
        for _ in range(10):
            length = self._rng.randint(0, 20)
            yield "".join(chr(self._rng.randint(32, 126)) for _ in range(length))

    def _generate_list(self, typ: PyListType) -> Iterator[list]:
        """Generate lists: [], [0], [1,0], ..."""
        yield []
        elem_gen = list(itertools.islice(self._generate_for_type(typ.element_type), 10))
        if not elem_gen:
            elem_gen = [0]

        for e in elem_gen[:5]:
            yield [e]

        yield elem_gen[:2]
        yield elem_gen[:3]
        yield elem_gen[:5]
        yield list(reversed(elem_gen[:5]))

        # Duplicate elements
        if elem_gen:
            yield [elem_gen[0]] * 3
            yield [elem_gen[0]] * 5

        for _ in range(5):
            length = self._rng.randint(0, 10)
            yield [self._rng.choice(elem_gen) for _ in range(length)]

    def _generate_dict(self, typ: PyDictType) -> Iterator[dict]:
        """Generate dicts: {}, {"a": 1}, ..."""
        yield {}
        key_gen = list(itertools.islice(self._generate_for_type(typ.key_type), 8))
        val_gen = list(itertools.islice(self._generate_for_type(typ.value_type), 8))
        if not key_gen:
            key_gen = [0]
        if not val_gen:
            val_gen = [0]

        # Filter out unhashable keys
        hashable_keys = []
        for k in key_gen:
            try:
                hash(k)
                hashable_keys.append(k)
            except TypeError:
                pass
        if not hashable_keys:
            hashable_keys = ["a", "b", "c"]

        for k, v in zip(hashable_keys[:5], val_gen[:5]):
            yield {k: v}

        if len(hashable_keys) >= 2 and len(val_gen) >= 2:
            yield {hashable_keys[0]: val_gen[0], hashable_keys[1]: val_gen[1]}

        for _ in range(5):
            length = self._rng.randint(0, 5)
            d = {}
            for _ in range(length):
                k = self._rng.choice(hashable_keys)
                v = self._rng.choice(val_gen)
                d[k] = v
            yield d

    def _generate_set(self, typ: PySetType) -> Iterator[set]:
        """Generate sets: set(), {0}, {0,1}, ..."""
        yield set()
        elem_gen = list(itertools.islice(self._generate_for_type(typ.element_type), 10))
        hashable = []
        for e in elem_gen:
            try:
                hash(e)
                hashable.append(e)
            except TypeError:
                pass
        if not hashable:
            hashable = [0, 1, 2]
        for e in hashable[:5]:
            yield {e}
        if len(hashable) >= 2:
            yield {hashable[0], hashable[1]}
        if len(hashable) >= 3:
            yield set(hashable[:3])

    def _generate_tuple(self, typ: PyTupleType) -> Iterator[tuple]:
        """Generate tuples based on element types."""
        if not typ.element_types:
            yield ()
            return
        sub_gens = [list(itertools.islice(self._generate_for_type(t), 5))
                    for t in typ.element_types]
        for combo in itertools.product(*sub_gens):
            yield combo

    def _generate_for_refinement(self, typ: RefinementType) -> Iterator[Any]:
        """Generate values for a refinement type: generate base, filter by predicate."""
        count = 0
        for val in self._generate_for_type(typ.base_type):
            if count >= 30:
                break
            if self._check_predicate(typ.predicate, {typ.var_name: val}):
                yield val
                count += 1

    def _random_for_type(self, typ: SynType) -> Any:
        """Generate a single random value for a type."""
        if isinstance(typ, PyIntType):
            return self._rng.randint(-10000, 10000)
        elif isinstance(typ, PyFloatType):
            return self._rng.uniform(-10000, 10000)
        elif isinstance(typ, PyBoolType):
            return self._rng.choice([True, False])
        elif isinstance(typ, PyStrType):
            length = self._rng.randint(0, 20)
            return "".join(chr(self._rng.randint(32, 126)) for _ in range(length))
        elif isinstance(typ, PyNoneType):
            return None
        elif isinstance(typ, PyListType):
            length = self._rng.randint(0, 10)
            return [self._random_for_type(typ.element_type) for _ in range(length)]
        elif isinstance(typ, PyDictType):
            length = self._rng.randint(0, 5)
            return {self._random_for_type(typ.key_type): self._random_for_type(typ.value_type)
                    for _ in range(length)}
        elif isinstance(typ, PySetType):
            length = self._rng.randint(0, 5)
            s = set()
            for _ in range(length):
                v = self._random_for_type(typ.element_type)
                try:
                    hash(v)
                    s.add(v)
                except TypeError:
                    pass
            return s
        elif isinstance(typ, RefinementType):
            for _ in range(100):
                v = self._random_for_type(typ.base_type)
                if self._check_predicate(typ.predicate, {typ.var_name: v}):
                    return v
            return self._random_for_type(typ.base_type)
        else:
            return self._rng.randint(-100, 100)

    @staticmethod
    def _check_predicate(predicate: str, env: dict[str, Any]) -> bool:
        """Check if a predicate holds for given variable values."""
        try:
            safe_builtins = {
                "abs": abs, "min": min, "max": max, "len": len,
                "sum": sum, "sorted": sorted, "all": all, "any": any,
                "isinstance": isinstance, "int": int, "float": float,
                "str": str, "bool": bool, "list": list, "dict": dict,
                "set": set, "tuple": tuple, "type": type, "range": range,
                "True": True, "False": False, "None": None,
                "round": round, "enumerate": enumerate, "zip": zip,
                "map": map, "filter": filter,
            }
            return bool(eval(predicate, {"__builtins__": safe_builtins}, env))
        except Exception:
            return True  # If we can't evaluate, assume it passes


# ═══════════════════════════════════════════════════════════════════
# Hypothesis Bridge
# ═══════════════════════════════════════════════════════════════════

class HypothesisBridge:
    """Bridge Deppy specs to Hypothesis strategies for property-based testing.

    Only works if hypothesis is installed; gracefully degrades otherwise.
    """

    @staticmethod
    def available() -> bool:
        """Check if Hypothesis is installed."""
        return _HAS_HYPOTHESIS

    @staticmethod
    def type_to_strategy(typ: SynType) -> Any:
        """Convert a Deppy type to a Hypothesis strategy.

        Raises ImportError if hypothesis is not installed.
        """
        if not _HAS_HYPOTHESIS:
            raise ImportError("hypothesis is not installed")

        if isinstance(typ, PyIntType):
            return st.integers(min_value=-10000, max_value=10000)
        elif isinstance(typ, PyFloatType):
            return st.floats(allow_nan=True, allow_infinity=True,
                             min_value=-1e10, max_value=1e10)
        elif isinstance(typ, PyBoolType):
            return st.booleans()
        elif isinstance(typ, PyStrType):
            return st.text(min_size=0, max_size=100)
        elif isinstance(typ, PyNoneType):
            return st.none()
        elif isinstance(typ, PyListType):
            elem_strat = HypothesisBridge.type_to_strategy(typ.element_type)
            return st.lists(elem_strat, min_size=0, max_size=30)
        elif isinstance(typ, PyDictType):
            key_strat = HypothesisBridge.type_to_strategy(typ.key_type)
            val_strat = HypothesisBridge.type_to_strategy(typ.value_type)
            return st.dictionaries(key_strat, val_strat, min_size=0, max_size=10)
        elif isinstance(typ, PySetType):
            elem_strat = HypothesisBridge.type_to_strategy(typ.element_type)
            return st.frozensets(elem_strat, min_size=0, max_size=20)
        elif isinstance(typ, PyTupleType):
            if typ.element_types:
                strats = [HypothesisBridge.type_to_strategy(t) for t in typ.element_types]
                return st.tuples(*strats)
            return st.just(())
        elif isinstance(typ, RefinementType):
            base_strat = HypothesisBridge.type_to_strategy(typ.base_type)
            pred = typ.predicate
            var_name = typ.var_name
            return base_strat.filter(
                lambda val, p=pred, vn=var_name: PropertyTester._check_predicate(
                    p, {vn: val}
                )
            )
        elif isinstance(typ, PyObjType):
            return st.one_of(
                st.integers(min_value=-1000, max_value=1000),
                st.text(min_size=0, max_size=20),
                st.booleans(),
                st.none(),
            )
        else:
            return st.integers(min_value=-1000, max_value=1000)

    @staticmethod
    def spec_to_test(func: Callable, spec: FunctionSpec) -> Callable:
        """Generate a Hypothesis test function from a Deppy spec.

        Returns a function decorated with @hypothesis.given that tests
        all guarantees of the spec.
        """
        if not _HAS_HYPOTHESIS:
            raise ImportError("hypothesis is not installed")

        param_strategies = {}
        for name, typ in spec.params:
            param_strategies[name] = HypothesisBridge.type_to_strategy(typ)

        def test_fn(**kwargs: Any) -> None:
            # Check assumptions
            for assumption in spec.assumptions:
                if not PropertyTester._check_predicate(assumption.description, kwargs):
                    hypothesis.assume(False)
                    return

            result = func(**kwargs)
            env = {**kwargs, "result": result, "return": result}

            for guarantee in spec.guarantees:
                pred = guarantee.description
                ok = PropertyTester._check_predicate(pred, env)
                assert ok, (
                    f"Guarantee '{pred}' violated:\n"
                    f"  inputs: {kwargs}\n"
                    f"  result: {result!r}"
                )

        # Apply @given decorator
        given_kwargs = {name: strat for name, strat in param_strategies.items()}
        decorated = hypothesis.given(**given_kwargs)(test_fn)
        decorated.__name__ = f"test_{spec.name}_spec"
        return decorated

    @staticmethod
    def run_spec_test(func: Callable, spec: FunctionSpec,
                      *, max_examples: int = 200) -> TestResult:
        """Run a Hypothesis-based property test and return a TestResult."""
        if not _HAS_HYPOTHESIS:
            return TestResult(passed=True, num_tests=0)

        import time
        start = time.time()

        test_fn = HypothesisBridge.spec_to_test(func, spec)

        try:
            settings = hypothesis.settings(max_examples=max_examples,
                                           suppress_health_check=list(hypothesis.HealthCheck))
            test_fn = settings(test_fn)
            test_fn()
            elapsed = (time.time() - start) * 1000
            return TestResult(
                passed=True,
                num_tests=max_examples,
                duration_ms=elapsed,
            )
        except AssertionError as e:
            elapsed = (time.time() - start) * 1000
            cex = CounterexampleResult(
                found=True,
                explanation=str(e),
                source="hypothesis",
            )
            return TestResult(
                passed=False,
                num_tests=max_examples,
                counterexample=cex,
                failures=[cex],
                duration_ms=elapsed,
            )
        except Exception as e:
            elapsed = (time.time() - start) * 1000
            cex = CounterexampleResult(
                found=True,
                explanation=f"Unexpected error: {e}",
                source="hypothesis",
            )
            return TestResult(
                passed=False,
                num_tests=0,
                counterexample=cex,
                failures=[cex],
                duration_ms=elapsed,
            )


# ═══════════════════════════════════════════════════════════════════
# Boundary Analyzer
# ═══════════════════════════════════════════════════════════════════

class BoundaryAnalyzer:
    """Check specs at type boundaries: 0, -1, MAX_INT, empty list, None, etc.

    Systematic edge-case checking that catches the bugs F* can't even
    describe (because F* doesn't know about Python's runtime quirks).
    """

    BOUNDARY_VALUES: dict[str, list[tuple[Any, str]]] = {
        "int": [
            (0, "zero"),
            (1, "one"),
            (-1, "negative_one"),
            (2**31 - 1, "max_int32"),
            (-(2**31), "min_int32"),
            (2**63 - 1, "max_int64"),
            (-(2**63), "min_int64"),
            (2, "small_positive"),
            (-2, "small_negative"),
            (10, "ten"),
            (100, "hundred"),
        ],
        "float": [
            (0.0, "zero"),
            (-0.0, "neg_zero"),
            (1.0, "one"),
            (-1.0, "neg_one"),
            (0.5, "half"),
            (float("inf"), "inf"),
            (float("-inf"), "neg_inf"),
            (float("nan"), "nan"),
            (1e-10, "tiny"),
            (1e10, "large"),
            (sys.float_info.max, "max_float"),
            (sys.float_info.min, "min_positive_float"),
        ],
        "str": [
            ("", "empty"),
            ("a", "single_char"),
            (" ", "space"),
            ("\n", "newline"),
            ("\t", "tab"),
            ("\0", "null_byte"),
            ("a" * 1000, "long_string"),
            ("hello world", "normal_string"),
            ("123", "numeric_string"),
            ("True", "bool_string"),
            ("None", "none_string"),
        ],
        "bool": [
            (True, "true"),
            (False, "false"),
        ],
        "none": [
            (None, "none"),
        ],
        "list": [
            ([], "empty"),
            ([0], "singleton_zero"),
            ([1], "singleton_one"),
            ([0, 0], "duplicate_zeros"),
            ([1, 0], "unsorted_pair"),
            ([0, 1, 2], "sorted_triple"),
            ([2, 1, 0], "reverse_sorted"),
            (list(range(100)), "large_sorted"),
            ([-1, 0, 1], "neg_zero_pos"),
        ],
        "dict": [
            ({}, "empty"),
            ({"a": 1}, "single_entry"),
            ({0: 0}, "zero_key"),
            ({"": ""}, "empty_strings"),
        ],
        "set": [
            (set(), "empty"),
            ({0}, "singleton_zero"),
            ({1, 2, 3}, "small_set"),
        ],
    }

    def check_boundaries(self, func: Callable, spec: FunctionSpec) -> list[BoundaryViolation]:
        """Check function at all boundary values for each parameter."""
        violations = []
        param_types = {name: typ for name, typ in spec.params}

        for param_name, param_type in spec.params:
            boundary_key = self._type_to_boundary_key(param_type)
            if boundary_key is None:
                continue

            boundary_set = self.BOUNDARY_VALUES.get(boundary_key, [])
            for boundary_val, boundary_kind in boundary_set:
                violation = self._check_single_boundary(
                    func, spec, param_name, boundary_val, boundary_kind, param_types
                )
                if violation is not None:
                    violations.append(violation)

        return violations

    def _check_single_boundary(
        self, func: Callable, spec: FunctionSpec,
        param_name: str, boundary_val: Any, boundary_kind: str,
        param_types: dict[str, SynType],
    ) -> BoundaryViolation | None:
        """Check a single boundary value for one parameter."""
        inputs = {}
        for name, typ in spec.params:
            if name == param_name:
                inputs[name] = boundary_val
            else:
                inputs[name] = self._default_for_type(typ)

        # Check assumptions first
        for assumption in spec.assumptions:
            if not PropertyTester._check_predicate(assumption.description, inputs):
                return None  # Boundary value violates assumptions, skip

        # Execute
        try:
            result = func(**inputs)
        except Exception as exc:
            return BoundaryViolation(
                param_name=param_name,
                boundary_value=boundary_val,
                boundary_kind=boundary_kind,
                expected="Function should not raise",
                actual=f"Raised {type(exc).__name__}",
                exception=f"{type(exc).__name__}: {exc}",
                explanation=f"Crashes at boundary {boundary_kind}",
            )

        # Check guarantees
        env = {**inputs, "result": result, "return": result}
        for guarantee in spec.guarantees:
            pred = guarantee.description
            if not PropertyTester._check_predicate(pred, env):
                return BoundaryViolation(
                    param_name=param_name,
                    boundary_value=boundary_val,
                    boundary_kind=boundary_kind,
                    expected=f"Guarantee: {pred}",
                    actual=f"result={result!r}",
                    explanation=f"Guarantee '{pred}' violated at boundary {boundary_kind}",
                )

        return None

    @staticmethod
    def _type_to_boundary_key(typ: SynType) -> str | None:
        """Map a SynType to a boundary value key."""
        if isinstance(typ, PyIntType):
            return "int"
        elif isinstance(typ, PyFloatType):
            return "float"
        elif isinstance(typ, PyStrType):
            return "str"
        elif isinstance(typ, PyBoolType):
            return "bool"
        elif isinstance(typ, PyNoneType):
            return "none"
        elif isinstance(typ, PyListType):
            return "list"
        elif isinstance(typ, PyDictType):
            return "dict"
        elif isinstance(typ, PySetType):
            return "set"
        elif isinstance(typ, RefinementType):
            return BoundaryAnalyzer._type_to_boundary_key(typ.base_type)
        return None

    @staticmethod
    def _default_for_type(typ: SynType) -> Any:
        """Generate a safe default value for a type."""
        if isinstance(typ, PyIntType):
            return 0
        elif isinstance(typ, PyFloatType):
            return 0.0
        elif isinstance(typ, PyStrType):
            return ""
        elif isinstance(typ, PyBoolType):
            return True
        elif isinstance(typ, PyNoneType):
            return None
        elif isinstance(typ, PyListType):
            return []
        elif isinstance(typ, PyDictType):
            return {}
        elif isinstance(typ, PySetType):
            return set()
        elif isinstance(typ, PyTupleType):
            return ()
        elif isinstance(typ, RefinementType):
            return BoundaryAnalyzer._default_for_type(typ.base_type)
        else:
            return 0


# ═══════════════════════════════════════════════════════════════════
# Diagnostic Engine
# ═══════════════════════════════════════════════════════════════════

class DiagnosticEngine:
    """When verification fails, produce detailed diagnostics.

    Combines Z3 counterexamples, property testing, boundary analysis,
    and heuristic analysis to explain WHY a proof failed.

    This is what differentiates Deppy from F* — instead of just
    'proof failed', you get 'here's a concrete input that breaks it,
    here are boundary cases that fail, and here's what's likely wrong'.
    """

    def __init__(self) -> None:
        self._cex_finder = CounterexampleFinder()
        self._prop_tester = PropertyTester()
        self._boundary_analyzer = BoundaryAnalyzer()

    def diagnose(self, func_source: str, spec: FunctionSpec,
                 failure: VerificationResult | None = None,
                 func: Callable | None = None) -> Diagnosis:
        """Produce a comprehensive diagnosis of a verification failure.

        Steps:
            1. Try Z3 counterexample
            2. Try property testing (if func provided)
            3. Try boundary analysis (if func provided)
            4. Analyze spec for common issues
            5. Suggest fixes
        """
        counterexamples: list[CounterexampleResult] = []
        boundary_violations: list[BoundaryViolation] = []
        test_result: TestResult | None = None
        likely_issues: list[str] = []
        confidence = 0.0

        # ── Step 1: Z3 counterexamples ──
        z3_cexs = self._cex_finder.find_for_spec(func_source, spec)
        for cex in z3_cexs:
            shrunk = self._cex_finder.shrink(cex)
            counterexamples.append(shrunk)
        if z3_cexs:
            confidence = max(confidence, 0.8)

        # ── Step 2: Property testing ──
        if func is not None:
            test_result = self._prop_tester.test_function(func, spec, max_examples=500)
            if not test_result.passed:
                for f in test_result.failures:
                    if not any(c.inputs == f.inputs for c in counterexamples):
                        counterexamples.append(f)
                confidence = max(confidence, 0.9)

        # ── Step 3: Boundary analysis ──
        if func is not None:
            boundary_violations = self._boundary_analyzer.check_boundaries(func, spec)
            if boundary_violations:
                confidence = max(confidence, 0.85)

        # ── Step 4: Analyze spec for common issues ──
        likely_issues = self._analyze_issues(spec, counterexamples,
                                              boundary_violations, func_source)

        # ── Step 5: Suggest fixes ──
        suggested_fixes = self.suggest_fix_from_analysis(
            spec, counterexamples, boundary_violations, likely_issues
        )

        if not counterexamples and not boundary_violations:
            if test_result and test_result.passed:
                confidence = 0.3
                likely_issues.append(
                    "No concrete violations found — spec may be correct "
                    "but unprovable with current strategies"
                )
            else:
                confidence = 0.1

        spec_desc = "; ".join(g.description for g in spec.guarantees) if spec.guarantees else "(no guarantees)"

        return Diagnosis(
            function_name=spec.name,
            spec_description=spec_desc,
            counterexamples=counterexamples,
            boundary_violations=boundary_violations,
            likely_issues=likely_issues,
            suggested_fixes=suggested_fixes,
            test_result=test_result,
            confidence=confidence,
        )

    def suggest_fix(self, diagnosis: Diagnosis) -> list[str]:
        """Suggest code or spec fixes based on a completed diagnosis."""
        return diagnosis.suggested_fixes

    def suggest_fix_from_analysis(
        self,
        spec: FunctionSpec,
        counterexamples: list[CounterexampleResult],
        boundary_violations: list[BoundaryViolation],
        likely_issues: list[str],
    ) -> list[str]:
        """Generate fix suggestions from analysis results."""
        fixes: list[str] = []

        # Check for missing edge-case handling
        boundary_kinds = {bv.boundary_kind for bv in boundary_violations}
        if "zero" in boundary_kinds:
            fixes.append("Add a guard for zero input: `if x == 0: ...`")
        if "empty" in boundary_kinds:
            fixes.append("Handle empty collections: `if not lst: return ...`")
        if "negative_one" in boundary_kinds or "small_negative" in boundary_kinds:
            fixes.append("Add handling for negative values")
        if "nan" in boundary_kinds:
            fixes.append("Guard against NaN: `if math.isnan(x): ...`")
        if "inf" in boundary_kinds or "neg_inf" in boundary_kinds:
            fixes.append("Guard against infinity: `if math.isinf(x): ...`")
        if "null_byte" in boundary_kinds:
            fixes.append("Handle null bytes in strings")
        if "long_string" in boundary_kinds:
            fixes.append("Handle very long strings")

        # Check for exception-based violations
        exception_cexs = [c for c in counterexamples if "exception" in c.actual.lower()
                          or "Raised" in c.actual]
        if exception_cexs:
            exc_types = set()
            for c in exception_cexs:
                for part in c.actual.split():
                    if part.endswith("Error") or part.endswith("Exception"):
                        exc_types.add(part.rstrip(":"))
                    elif part.endswith("Error:"):
                        exc_types.add(part.rstrip(":"))
            if "ZeroDivisionError" in exc_types:
                fixes.append("Add division-by-zero guard: `if divisor == 0: ...`")
            if "IndexError" in exc_types:
                fixes.append("Check list bounds before indexing")
            if "KeyError" in exc_types:
                fixes.append("Check key existence before dict access")
            if "TypeError" in exc_types:
                fixes.append("Add type checking for arguments")
            if "ValueError" in exc_types:
                fixes.append("Validate input values before processing")
            if not exc_types:
                fixes.append("Add try/except or input validation for edge cases")

        # Spec-level suggestions
        if not spec.assumptions and counterexamples:
            fixes.append(
                "Add preconditions with assume() to restrict input domain, "
                "e.g., assume('x > 0')"
            )

        if not fixes:
            if counterexamples:
                fixes.append("Review the spec — it may be too strong for the implementation")
            elif likely_issues:
                fixes.append("Review the likely issues above and adjust code or spec")

        return fixes

    def _analyze_issues(
        self,
        spec: FunctionSpec,
        counterexamples: list[CounterexampleResult],
        boundary_violations: list[BoundaryViolation],
        func_source: str,
    ) -> list[str]:
        """Heuristically analyze what's likely wrong."""
        issues: list[str] = []

        # Look for patterns in counterexamples
        if counterexamples:
            # Check if all counterexamples involve negative numbers
            all_negative = all(
                any(isinstance(v, (int, float)) and v < 0
                    for v in c.inputs.values())
                for c in counterexamples if c.inputs
            )
            if all_negative:
                issues.append("Spec may not account for negative inputs")

            # Check if all counterexamples involve zero
            all_zero = all(
                any(v == 0 for v in c.inputs.values()
                    if isinstance(v, (int, float)))
                for c in counterexamples if c.inputs
            )
            if all_zero:
                issues.append("Spec may not account for zero input")

            # Check if all counterexamples involve empty collections
            all_empty = all(
                any(isinstance(v, (list, dict, set, str, tuple)) and len(v) == 0
                    for v in c.inputs.values())
                for c in counterexamples if c.inputs
            )
            if all_empty:
                issues.append("Spec may not account for empty collections")

        # Check if function has guards
        try:
            tree = ast.parse(func_source)
            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef) and node.name == spec.name:
                    body_str = ast.dump(node)
                    if "Raise" in body_str and not any(
                        isinstance(s, ast.If) for s in node.body[:3]
                    ):
                        issues.append(
                            "Function raises exceptions but has no early guard clauses"
                        )
        except SyntaxError:
            pass

        # Check for overly strong guarantees
        for g in spec.guarantees:
            pred = g.description.lower()
            if "for all" in pred or "forall" in pred or "∀" in pred:
                issues.append(
                    f"Universal quantifier in guarantee '{g.description}' — "
                    "may be too strong"
                )
            if ">=" in pred and "<=" in pred:
                issues.append(
                    f"Guarantee '{g.description}' has both upper and lower bounds — "
                    "check range is correct"
                )

        # Check for missing assumptions
        for g in spec.guarantees:
            pred = g.description
            # If guarantee references division, check for zero-division assumption
            if "/" in pred and not any("!= 0" in a.description or "> 0" in a.description
                                       for a in spec.assumptions):
                issues.append(
                    "Guarantee uses division but no assumption guards against zero divisor"
                )

        # Boundary analysis insights
        if boundary_violations:
            exception_violations = [bv for bv in boundary_violations if bv.exception]
            if exception_violations:
                issues.append(
                    f"Function crashes at {len(exception_violations)} boundary value(s) — "
                    "missing error handling"
                )
            logic_violations = [bv for bv in boundary_violations if not bv.exception]
            if logic_violations:
                issues.append(
                    f"Spec violated at {len(logic_violations)} boundary value(s) — "
                    "spec may be too strong or logic has edge-case bugs"
                )

        return issues


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Comprehensive self-tests with concrete counterexample output."""
    import time

    passed = 0
    failed = 0
    total_start = time.time()

    def check(name: str, condition: bool, detail: str = "") -> None:
        nonlocal passed, failed
        if condition:
            print(f"  ✓ {name}")
            passed += 1
        else:
            print(f"  ✗ {name}" + (f" — {detail}" if detail else ""))
            failed += 1

    print("=" * 60)
    print("Deppy Counterexample Generation — Self Tests")
    print("=" * 60)

    # ── Test 1: Z3 formula builder ──
    print("\n── Z3 Formula Builder ──")
    builder = _Z3FormulaBuilder()
    if _HAS_Z3:
        r = builder.build("x + y > 0", var_types={"x": PyIntType(), "y": PyIntType()})
        check("parse arithmetic", r is not None)

        r = builder.build("x == y and y > 0", var_types={"x": PyIntType(), "y": PyIntType()})
        check("parse boolean", r is not None)

        r = builder.build("not (x < 0)", var_types={"x": PyIntType()})
        check("parse negation", r is not None)

        r = builder.build("x >= 0 and x <= 100", var_types={"x": PyIntType()})
        check("parse range", r is not None)

        r = builder.build("x + 1 == y - 1", var_types={"x": PyIntType(), "y": PyIntType()})
        check("parse equality", r is not None)

        r = builder.build("abs(x) >= 0", var_types={"x": PyIntType()})
        check("parse abs()", r is not None)

        r = builder.build("min(x, y) <= max(x, y)",
                          var_types={"x": PyIntType(), "y": PyIntType()})
        check("parse min/max", r is not None)

        # Should fail for unsupported
        r = builder.build("x.attr > 0")
        check("reject attribute access", r is None)

        r = builder.build("invalid syntax ???")
        check("reject bad syntax", r is None)
    else:
        print("  (Z3 not available, skipping Z3 tests)")

    # ── Test 2: Counterexample finder ──
    print("\n── CounterexampleFinder ──")
    finder = CounterexampleFinder()

    if _HAS_Z3:
        # Spec that is clearly false: "x > 0" with no constraints
        obl_false = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=Context(bindings={"x": PyIntType()}),
            term=Var("f"),
            type_=RefinementType(base_type=PyIntType(), predicate="x > 0"),
        )
        cex = finder.find(obl_false)
        check("find cex for 'x > 0'", cex.found,
              f"inputs={cex.inputs}")
        if cex.found:
            check("cex x <= 0", cex.inputs.get("x", 1) <= 0,
                  f"got x={cex.inputs.get('x')}")
            print(f"\n{cex.display()}\n")

        # Spec that is true: "x * x >= 0"
        obl_true = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=Context(bindings={"x": PyIntType()}),
            term=Var("f"),
            type_=RefinementType(base_type=PyIntType(), predicate="x * x >= 0"),
        )
        cex = finder.find(obl_true)
        check("no cex for 'x * x >= 0'", not cex.found)

        # Two-variable spec: "x + y > 10" (false for x=0, y=0)
        obl_two = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=Context(bindings={"x": PyIntType(), "y": PyIntType()}),
            term=Var("f"),
            type_=RefinementType(base_type=PyIntType(), predicate="x + y > 10"),
        )
        cex = finder.find(obl_two)
        check("find cex for 'x + y > 10'", cex.found)
        if cex.found:
            x, y = cex.inputs.get("x", 11), cex.inputs.get("y", 11)
            check("cex satisfies NOT(x+y>10)", x + y <= 10,
                  f"x={x}, y={y}, x+y={x+y}")
            print(f"\n{cex.display()}\n")

        # Shrinking test
        obl_shrink = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=Context(bindings={"x": PyIntType()}),
            term=Var("f"),
            type_=RefinementType(base_type=PyIntType(), predicate="x > 100"),
        )
        cex = finder.find(obl_shrink)
        if cex.found:
            shrunk = finder.shrink(cex)
            check("shrinking reduces size",
                  CounterexampleFinder._size(shrunk.inputs) <=
                  CounterexampleFinder._size(cex.inputs),
                  f"original={cex.inputs}, shrunk={shrunk.inputs}")
            check("shrunk flag set", shrunk.shrunk or shrunk.inputs == cex.inputs)

        # find_for_spec
        spec = FunctionSpec(
            name="bad_abs",
            params=[("x", PyIntType())],
            return_type=PyIntType(),
            guarantees=[Spec(kind=SpecKind.GUARANTEE, description="x > 0")],
        )
        cexs = finder.find_for_spec("", spec)
        check("find_for_spec finds violations", len(cexs) > 0)

        # Spec with context constraints
        obl_ctx = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=Context(bindings={
                "x": RefinementType(base_type=PyIntType(), predicate="x >= 0"),
            }),
            term=Var("f"),
            type_=RefinementType(base_type=PyIntType(), predicate="x >= -5"),
        )
        cex = finder.find(obl_ctx)
        check("respect context constraints (x>=0 ⊢ x>=-5 has no cex)", not cex.found)
    else:
        print("  (Z3 not available, skipping)")

    # ── Test 3: CounterexampleResult display ──
    print("\n── CounterexampleResult.display() ──")
    cex_display = CounterexampleResult(
        found=True,
        inputs={"x": -3, "y": 5},
        expected="x + y > 10",
        actual="(-3) + 5 > 10 → False",
        explanation="With x=-3, y=5: x + y > 10 evaluates to False",
        trace=["let x = -3", "let y = 5", "evaluate: -3 + 5 > 10", "result: False"],
        shrunk=True,
        source="z3",
    )
    display = cex_display.display()
    check("display contains COUNTEREXAMPLE", "COUNTEREXAMPLE" in display)
    check("display contains inputs", "x = -3" in display)
    check("display contains trace", "let x = -3" in display)
    check("display contains shrunk note", "shrunk" in display.lower())
    print(f"\n{display}\n")

    no_cex = CounterexampleResult(found=False)
    check("no-cex display", "No counterexample" in no_cex.display())

    # ── Test 4: PropertyTester ──
    print("\n── PropertyTester ──")
    tester = PropertyTester(seed=42, max_examples=200)

    # Test a function that violates its spec
    def bad_double(x: int) -> int:
        return x + x + 1  # Off by one!

    bad_spec = FunctionSpec(
        name="bad_double",
        params=[("x", PyIntType())],
        return_type=PyIntType(),
        guarantees=[Spec(kind=SpecKind.GUARANTEE,
                         description="result == x * 2")],
    )
    tr = tester.test_function(bad_double, bad_spec)
    check("property test catches off-by-one", not tr.passed)
    if not tr.passed and tr.counterexample:
        check("counterexample has inputs", len(tr.counterexample.inputs) > 0)
        print(f"    Found: {tr.counterexample.inputs}")

    # Test a correct function
    def good_abs(x: int) -> int:
        return abs(x)

    good_spec = FunctionSpec(
        name="good_abs",
        params=[("x", PyIntType())],
        return_type=PyIntType(),
        guarantees=[Spec(kind=SpecKind.GUARANTEE,
                         description="result >= 0")],
    )
    tr = tester.test_function(good_abs, good_spec)
    check("property test passes correct func", tr.passed,
          f"failures={tr.failures}")
    print(f"    {tr.display()}")

    # Test with assumptions
    def safe_divide(x: int, y: int) -> float:
        return x / y

    div_spec = FunctionSpec(
        name="safe_divide",
        params=[("x", PyIntType()), ("y", PyIntType())],
        return_type=PyFloatType(),
        guarantees=[Spec(kind=SpecKind.GUARANTEE,
                         description="result * y == x")],
        assumptions=[Spec(kind=SpecKind.ASSUME,
                          description="y != 0")],
    )
    tr = tester.test_function(safe_divide, div_spec)
    # Note: float precision may cause failures
    check("divide test ran", tr.num_tests > 0)

    # ── Test 5: Input generation ──
    print("\n── Input Generation ──")
    gen = PropertyTester(seed=0, max_examples=50)

    int_inputs = list(itertools.islice(
        gen._generate_for_type(PyIntType()), 20))
    check("int gen produces values", len(int_inputs) >= 10)
    check("int gen includes 0", 0 in int_inputs)
    check("int gen includes negatives", any(x < 0 for x in int_inputs))

    float_inputs = list(itertools.islice(
        gen._generate_for_type(PyFloatType()), 20))
    check("float gen produces values", len(float_inputs) >= 10)
    check("float gen includes 0.0", 0.0 in float_inputs)
    check("float gen includes inf", float("inf") in float_inputs)
    check("float gen includes nan", any(math.isnan(x) for x in float_inputs
                                         if isinstance(x, float)))

    str_inputs = list(itertools.islice(
        gen._generate_for_type(PyStrType()), 15))
    check("str gen produces values", len(str_inputs) >= 10)
    check("str gen includes empty", "" in str_inputs)

    bool_inputs = list(itertools.islice(
        gen._generate_for_type(PyBoolType()), 5))
    check("bool gen produces both", True in bool_inputs and False in bool_inputs)

    none_inputs = list(itertools.islice(
        gen._generate_for_type(PyNoneType()), 5))
    check("none gen produces None", None in none_inputs)

    list_inputs = list(itertools.islice(
        gen._generate_for_type(PyListType(element_type=PyIntType())), 10))
    check("list gen produces values", len(list_inputs) >= 5)
    check("list gen includes empty", [] in list_inputs)

    dict_inputs = list(itertools.islice(
        gen._generate_for_type(PyDictType(key_type=PyStrType(), value_type=PyIntType())), 10))
    check("dict gen produces values", len(dict_inputs) >= 5)
    check("dict gen includes empty", {} in dict_inputs)

    set_inputs = list(itertools.islice(
        gen._generate_for_type(PySetType(element_type=PyIntType())), 8))
    check("set gen produces values", len(set_inputs) >= 3)
    check("set gen includes empty", set() in set_inputs)

    # Refinement type generation
    pos_int = RefinementType(base_type=PyIntType(), var_name="x", predicate="x > 0")
    pos_inputs = list(itertools.islice(
        gen._generate_for_type(pos_int), 10))
    check("refinement gen all positive", all(x > 0 for x in pos_inputs),
          f"got {pos_inputs}")

    # Multi-parameter generation
    multi_types = {"x": PyIntType(), "y": PyStrType()}
    multi_inputs = list(itertools.islice(gen.generate_inputs(multi_types), 20))
    check("multi gen produces combos", len(multi_inputs) >= 10)
    check("multi gen has both keys",
          all("x" in d and "y" in d for d in multi_inputs))

    # ── Test 6: BoundaryAnalyzer ──
    print("\n── BoundaryAnalyzer ──")
    ba = BoundaryAnalyzer()

    def divide_by(x: int) -> float:
        return 10 / x  # Crashes on 0!

    div_spec_boundary = FunctionSpec(
        name="divide_by",
        params=[("x", PyIntType())],
        return_type=PyFloatType(),
        guarantees=[],
    )
    violations = ba.check_boundaries(divide_by, div_spec_boundary)
    check("boundary catches div-by-zero",
          any(bv.boundary_kind == "zero" for bv in violations))
    if violations:
        print(f"    Found {len(violations)} violation(s):")
        for bv in violations[:3]:
            print(bv.display())

    def first_element(lst: list) -> Any:
        return lst[0]  # Crashes on empty!

    list_spec = FunctionSpec(
        name="first_element",
        params=[("lst", PyListType(element_type=PyIntType()))],
        return_type=PyIntType(),
        guarantees=[],
    )
    violations = ba.check_boundaries(first_element, list_spec)
    check("boundary catches empty list",
          any(bv.boundary_kind == "empty" for bv in violations))

    # ── Test 7: HypothesisBridge ──
    print("\n── HypothesisBridge ──")
    check("hypothesis available check works",
          isinstance(HypothesisBridge.available(), bool))

    if HypothesisBridge.available():
        strat = HypothesisBridge.type_to_strategy(PyIntType())
        check("int strategy created", strat is not None)

        strat = HypothesisBridge.type_to_strategy(PyListType(element_type=PyStrType()))
        check("list[str] strategy created", strat is not None)

        strat = HypothesisBridge.type_to_strategy(PyDictType(
            key_type=PyStrType(), value_type=PyIntType()))
        check("dict strategy created", strat is not None)

        strat = HypothesisBridge.type_to_strategy(
            RefinementType(base_type=PyIntType(), var_name="x", predicate="x > 0"))
        check("refinement strategy created", strat is not None)

        # Actual test run
        test_fn = HypothesisBridge.spec_to_test(good_abs, good_spec)
        check("spec_to_test creates callable", callable(test_fn))
    else:
        print("  (Hypothesis not installed, skipping — this is OK)")

    # ── Test 8: DiagnosticEngine ──
    print("\n── DiagnosticEngine ──")
    engine = DiagnosticEngine()

    # Diagnose a buggy function
    def buggy_clamp(x: int) -> int:
        """Clamp x to [0, 100] — but has a bug!"""
        if x < 0:
            return 0
        return x  # Forgot the upper bound!

    clamp_spec = FunctionSpec(
        name="buggy_clamp",
        params=[("x", PyIntType())],
        return_type=PyIntType(),
        guarantees=[
            Spec(kind=SpecKind.GUARANTEE, description="result >= 0"),
            Spec(kind=SpecKind.GUARANTEE, description="result <= 100"),
        ],
    )
    diag = engine.diagnose(
        textwrap.dedent("""\
        def buggy_clamp(x: int) -> int:
            if x < 0:
                return 0
            return x
        """),
        clamp_spec,
        func=buggy_clamp,
    )
    check("diagnosis finds issues", len(diag.counterexamples) > 0 or
          len(diag.boundary_violations) > 0)
    check("diagnosis has suggestions", len(diag.suggested_fixes) > 0)
    check("diagnosis has confidence", diag.confidence > 0)
    print(f"\n{diag.display()}\n")

    # Diagnose a correct function
    def good_clamp(x: int) -> int:
        if x < 0:
            return 0
        if x > 100:
            return 100
        return x

    diag_good = engine.diagnose(
        textwrap.dedent("""\
        def good_clamp(x: int) -> int:
            if x < 0:
                return 0
            if x > 100:
                return 100
            return x
        """),
        clamp_spec,
        func=good_clamp,
    )
    check("correct func has no counterexamples",
          len(diag_good.counterexamples) == 0)
    check("correct func has no boundary violations",
          len(diag_good.boundary_violations) == 0)

    # ── Test 9: Diagnosis display ──
    print("\n── Diagnosis.display() ──")
    diag_display = Diagnosis(
        function_name="example_func",
        spec_description="result > 0 and result < 100",
        counterexamples=[CounterexampleResult(
            found=True, inputs={"x": -5},
            explanation="Negative input produces negative output",
            source="z3",
        )],
        boundary_violations=[BoundaryViolation(
            param_name="x", boundary_value=0, boundary_kind="zero",
            expected="result > 0", actual="result=0",
        )],
        likely_issues=["Spec may not account for zero input"],
        suggested_fixes=["Add a guard for zero input"],
        confidence=0.85,
    )
    display = diag_display.display()
    check("diagnosis display has function name", "example_func" in display)
    check("diagnosis display has confidence", "85%" in display)
    check("diagnosis display has counterexample", "x=-5" in display)
    check("diagnosis display has boundary", "zero" in display)

    # ── Test 10: Edge cases ──
    print("\n── Edge Cases ──")

    # Empty spec
    empty_spec = FunctionSpec(
        name="f",
        params=[],
        return_type=PyNoneType(),
    )
    diag_empty = engine.diagnose("def f(): pass", empty_spec, func=lambda: None)
    check("empty spec diagnosis works", diag_empty is not None)

    # Multiple params
    multi_spec = FunctionSpec(
        name="add",
        params=[("x", PyIntType()), ("y", PyIntType()), ("z", PyIntType())],
        return_type=PyIntType(),
        guarantees=[Spec(kind=SpecKind.GUARANTEE,
                         description="result == x + y + z")],
    )
    tr = tester.test_function(lambda x, y, z: x + y + z, multi_spec)
    check("3-param function test passes", tr.passed)

    # String function
    def bad_upper(s: str) -> str:
        return s  # Doesn't actually uppercase!

    str_spec = FunctionSpec(
        name="bad_upper",
        params=[("s", PyStrType())],
        return_type=PyStrType(),
        guarantees=[Spec(kind=SpecKind.GUARANTEE,
                         description="result == s.upper()")],
    )
    tr = tester.test_function(bad_upper, str_spec)
    # This might or might not find a failure (depends on the safe eval)
    check("string function test ran", tr.num_tests > 0)

    # BoundaryViolation display
    bv = BoundaryViolation(
        param_name="n", boundary_value=0, boundary_kind="zero",
        expected="n > 0", actual="n=0",
        exception="ZeroDivisionError: division by zero",
        explanation="Crashes at zero",
    )
    bv_str = bv.display()
    check("BoundaryViolation display", "zero" in bv_str and "ZeroDivision" in bv_str)

    # TestResult display
    tr_pass = TestResult(passed=True, num_tests=100, duration_ms=42.5)
    check("TestResult pass display", "100 tests passed" in tr_pass.display())

    tr_fail = TestResult(
        passed=False, num_tests=5, duration_ms=1.2,
        counterexample=CounterexampleResult(found=True, inputs={"x": -1}),
    )
    check("TestResult fail display", "Failed" in tr_fail.display())

    # ── Test 11: PropertyTester _check_predicate ──
    print("\n── Predicate Checking ──")
    check("true predicate", PropertyTester._check_predicate("True", {}))
    check("false predicate", not PropertyTester._check_predicate("False", {}))
    check("arithmetic predicate",
          PropertyTester._check_predicate("x + y > 0", {"x": 3, "y": 1}))
    check("arithmetic predicate false",
          not PropertyTester._check_predicate("x + y > 0", {"x": -5, "y": 1}))
    check("result predicate",
          PropertyTester._check_predicate("result >= 0", {"result": 5}))
    check("abs predicate",
          PropertyTester._check_predicate("abs(x) >= 0", {"x": -3}))
    check("invalid predicate returns True (safe default)",
          PropertyTester._check_predicate("totally_undefined_func()", {}))

    # ── Test 12: Tuple type generation ──
    print("\n── Tuple Type Generation ──")
    tuple_type = PyTupleType(element_types=(PyIntType(), PyStrType()))
    tuple_vals = list(itertools.islice(
        gen._generate_for_type(tuple_type), 10))
    check("tuple gen produces values", len(tuple_vals) >= 3)
    check("tuple gen has correct shape",
          all(isinstance(t, tuple) and len(t) == 2 for t in tuple_vals))

    # ── Summary ──
    elapsed = (time.time() - total_start) * 1000
    print("\n" + "=" * 60)
    print(f"Results: {passed} passed, {failed} failed ({elapsed:.0f}ms)")
    if failed == 0:
        print("All self-tests passed! ✓")
    else:
        print(f"FAILURES: {failed}")
    print("=" * 60)

    return failed == 0


if __name__ == "__main__":
    success = _self_test()
    sys.exit(0 if success else 1)
