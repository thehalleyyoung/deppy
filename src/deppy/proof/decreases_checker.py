"""Decreases checker: verify well-founded decreases annotations.

Checks that a ranking function decreases on each recursive call or
loop iteration, ensuring termination. Supports single measures,
lexicographic ordering, and structural recursion patterns.
"""

from __future__ import annotations

import ast
import enum
import logging
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.types.witnesses import ProofTerm, ReflProof, StaticProof
from deppy.proof._protocols import ProofObligation, ObligationStatus

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Decreases result types
# ---------------------------------------------------------------------------


class DecreasesVerdict(enum.Enum):
    """Outcome of a decreases check."""

    VERIFIED = "verified"
    LIKELY = "likely"
    UNKNOWN = "unknown"
    FAILED = "failed"


class MeasureKind(enum.Enum):
    """Kind of ranking measure."""

    NATURAL = "natural"
    INTEGER = "integer"
    LEXICOGRAPHIC = "lexicographic"
    STRUCTURAL = "structural"
    CUSTOM = "custom"


@dataclass(frozen=True)
class RecursiveCallInfo:
    """Information about a single recursive call.

    Attributes:
        _function_name: Name of the called function.
        _args_text: Textual representation of the call arguments.
        _line_number: Line number in source.
        _arg_names: Argument name -> expression text mapping.
        _is_tail: Whether this is a tail call.
        _context: Additional context (e.g., surrounding conditions).
    """

    _function_name: str
    _args_text: Tuple[str, ...] = ()
    _line_number: int = 0
    _arg_names: Dict[str, str] = field(default_factory=dict)
    _is_tail: bool = False
    _context: Dict[str, Any] = field(default_factory=dict)

    @property
    def function_name(self) -> str:
        return self._function_name

    @property
    def args_text(self) -> Tuple[str, ...]:
        return self._args_text

    @property
    def line_number(self) -> int:
        return self._line_number

    @property
    def is_tail(self) -> bool:
        return self._is_tail

    def __repr__(self) -> str:
        args = ", ".join(self._args_text)
        return f"RecursiveCall({self._function_name}({args}), line={self._line_number})"


@dataclass(frozen=True)
class LoopIterationInfo:
    """Information about a loop iteration.

    Attributes:
        _loop_kind: "for" or "while".
        _line_number: Line number of the loop header.
        _iterator_var: Iterator variable (for loops).
        _condition_text: Loop condition text (while loops).
        _body_modifies: Variables modified in the loop body.
    """

    _loop_kind: str = "while"
    _line_number: int = 0
    _iterator_var: Optional[str] = None
    _condition_text: str = ""
    _body_modifies: Tuple[str, ...] = ()

    @property
    def loop_kind(self) -> str:
        return self._loop_kind

    @property
    def line_number(self) -> int:
        return self._line_number

    def __repr__(self) -> str:
        return f"LoopIteration({self._loop_kind}, line={self._line_number})"


@dataclass(frozen=True)
class MeasureDecreaseEvidence:
    """Evidence that the measure decreases at a specific point.

    Attributes:
        _call_or_loop: The recursive call or loop iteration.
        _measure_before: Textual representation of measure before.
        _measure_after: Textual representation of measure after.
        _decrease_reason: Explanation of why it decreases.
        _verified: Whether the decrease was verified.
        _guard_conditions: Conditions guarding this decrease.
    """

    _call_or_loop: Union[RecursiveCallInfo, LoopIterationInfo]
    _measure_before: str = ""
    _measure_after: str = ""
    _decrease_reason: str = ""
    _verified: bool = False
    _guard_conditions: Tuple[str, ...] = ()

    @property
    def verified(self) -> bool:
        return self._verified

    @property
    def decrease_reason(self) -> str:
        return self._decrease_reason

    def __repr__(self) -> str:
        status = "verified" if self._verified else "unverified"
        return f"MeasureDecrease({status}, {self._decrease_reason!r})"


@dataclass(frozen=True)
class DecreasesResult:
    """Result of checking a decreases annotation.

    Attributes:
        _verdict: Overall verdict.
        _measure_kind: Kind of measure used.
        _ranking_function_text: Textual representation of the ranking function.
        _recursive_calls: All recursive calls found.
        _loop_iterations: All loops found.
        _evidence: Decrease evidence for each call/loop.
        _unverified_calls: Calls where decrease could not be verified.
        _explanation: Human-readable explanation.
        _proof_term: Optional proof term for verified cases.
        _trust_level: Trust level of the result.
    """

    _verdict: DecreasesVerdict
    _measure_kind: MeasureKind = MeasureKind.NATURAL
    _ranking_function_text: str = ""
    _recursive_calls: Tuple[RecursiveCallInfo, ...] = ()
    _loop_iterations: Tuple[LoopIterationInfo, ...] = ()
    _evidence: Tuple[MeasureDecreaseEvidence, ...] = ()
    _unverified_calls: Tuple[RecursiveCallInfo, ...] = ()
    _explanation: str = ""
    _proof_term: Optional[ProofTerm] = None
    _trust_level: TrustLevel = TrustLevel.RESIDUAL

    @property
    def verdict(self) -> DecreasesVerdict:
        return self._verdict

    @property
    def measure_kind(self) -> MeasureKind:
        return self._measure_kind

    @property
    def ranking_function_text(self) -> str:
        return self._ranking_function_text

    @property
    def recursive_calls(self) -> Tuple[RecursiveCallInfo, ...]:
        return self._recursive_calls

    @property
    def loop_iterations(self) -> Tuple[LoopIterationInfo, ...]:
        return self._loop_iterations

    @property
    def evidence(self) -> Tuple[MeasureDecreaseEvidence, ...]:
        return self._evidence

    @property
    def unverified_calls(self) -> Tuple[RecursiveCallInfo, ...]:
        return self._unverified_calls

    @property
    def explanation(self) -> str:
        return self._explanation

    @property
    def proof_term(self) -> Optional[ProofTerm]:
        return self._proof_term

    @property
    def is_verified(self) -> bool:
        return self._verdict == DecreasesVerdict.VERIFIED

    @property
    def is_likely(self) -> bool:
        return self._verdict in (DecreasesVerdict.VERIFIED, DecreasesVerdict.LIKELY)

    def __repr__(self) -> str:
        return (
            f"DecreasesResult({self._verdict.value}, "
            f"calls={len(self._recursive_calls)}, "
            f"loops={len(self._loop_iterations)})"
        )


# ---------------------------------------------------------------------------
# AST analysis helpers
# ---------------------------------------------------------------------------


def _extract_call_args_text(call: ast.Call) -> Tuple[str, ...]:
    """Extract argument text from a Call AST node."""
    args: List[str] = []
    for arg in call.args:
        try:
            args.append(ast.unparse(arg))
        except Exception:
            args.append(ast.dump(arg))
    return tuple(args)


def _is_tail_position(node: ast.AST, func_body: List[ast.stmt]) -> bool:
    """Check if a node is in tail position within a function body."""
    if not func_body:
        return False
    last = func_body[-1]
    if isinstance(last, ast.Return) and last.value is not None:
        if isinstance(last.value, ast.Call):
            return True
    return False


class _RecursiveCallFinder(ast.NodeVisitor):
    """AST visitor that finds all recursive calls to a given function."""

    def __init__(self, func_name: str, func_body: List[ast.stmt]) -> None:
        self._func_name = func_name
        self._func_body = func_body
        self._calls: List[RecursiveCallInfo] = []
        self._current_guards: List[str] = []

    @property
    def calls(self) -> List[RecursiveCallInfo]:
        return self._calls

    def visit_Call(self, node: ast.Call) -> None:
        if isinstance(node.func, ast.Name) and node.func.id == self._func_name:
            args_text = _extract_call_args_text(node)
            arg_names: Dict[str, str] = {}
            for i, arg_text in enumerate(args_text):
                arg_names[f"arg_{i}"] = arg_text
            for kw in node.keywords:
                if kw.arg is not None:
                    try:
                        arg_names[kw.arg] = ast.unparse(kw.value)
                    except Exception:
                        arg_names[kw.arg] = ast.dump(kw.value)

            info = RecursiveCallInfo(
                _function_name=self._func_name,
                _args_text=args_text,
                _line_number=getattr(node, "lineno", 0),
                _arg_names=arg_names,
                _context={"guards": list(self._current_guards)},
            )
            self._calls.append(info)
        self.generic_visit(node)

    def visit_If(self, node: ast.If) -> None:
        try:
            guard_text = ast.unparse(node.test)
        except Exception:
            guard_text = ast.dump(node.test)
        self._current_guards.append(guard_text)
        for child in node.body:
            self.visit(child)
        self._current_guards.pop()
        neg_guard = f"not ({guard_text})"
        self._current_guards.append(neg_guard)
        for child in node.orelse:
            self.visit(child)
        self._current_guards.pop()

    def visit_While(self, node: ast.While) -> None:
        try:
            guard_text = ast.unparse(node.test)
        except Exception:
            guard_text = ast.dump(node.test)
        self._current_guards.append(guard_text)
        for child in node.body:
            self.visit(child)
        self._current_guards.pop()

    def visit_For(self, node: ast.For) -> None:
        for child in node.body:
            self.visit(child)


class _LoopFinder(ast.NodeVisitor):
    """AST visitor that finds all loops in a function body."""

    def __init__(self) -> None:
        self._loops: List[LoopIterationInfo] = []

    @property
    def loops(self) -> List[LoopIterationInfo]:
        return self._loops

    def visit_While(self, node: ast.While) -> None:
        try:
            cond_text = ast.unparse(node.test)
        except Exception:
            cond_text = ast.dump(node.test)

        modifies = self._find_assignments(node.body)
        info = LoopIterationInfo(
            _loop_kind="while",
            _line_number=getattr(node, "lineno", 0),
            _condition_text=cond_text,
            _body_modifies=tuple(modifies),
        )
        self._loops.append(info)
        self.generic_visit(node)

    def visit_For(self, node: ast.For) -> None:
        iter_var = None
        if isinstance(node.target, ast.Name):
            iter_var = node.target.id

        modifies = self._find_assignments(node.body)
        info = LoopIterationInfo(
            _loop_kind="for",
            _line_number=getattr(node, "lineno", 0),
            _iterator_var=iter_var,
            _body_modifies=tuple(modifies),
        )
        self._loops.append(info)
        self.generic_visit(node)

    def _find_assignments(self, body: List[ast.stmt]) -> List[str]:
        """Find variable names assigned in a body."""
        assigned: List[str] = []
        for stmt in body:
            if isinstance(stmt, ast.Assign):
                for target in stmt.targets:
                    if isinstance(target, ast.Name):
                        if target.id not in assigned:
                            assigned.append(target.id)
            elif isinstance(stmt, ast.AugAssign):
                if isinstance(stmt.target, ast.Name):
                    if stmt.target.id not in assigned:
                        assigned.append(stmt.target.id)
        return assigned


def _find_recursive_calls(
    func_ast: ast.FunctionDef,
) -> List[RecursiveCallInfo]:
    """Find all recursive calls in a function."""
    finder = _RecursiveCallFinder(func_ast.name, func_ast.body)
    finder.visit(func_ast)
    return finder.calls


def _find_loops(func_ast: ast.FunctionDef) -> List[LoopIterationInfo]:
    """Find all loops in a function."""
    finder = _LoopFinder()
    finder.visit(func_ast)
    return finder.loops


# ---------------------------------------------------------------------------
# Ranking function parsing
# ---------------------------------------------------------------------------


def _parse_ranking_function(ranking_text: str) -> Tuple[MeasureKind, List[str]]:
    """Parse a ranking function specification.

    Supports:
    - Simple: "n" or "len(xs)" -> single natural number measure
    - Lexicographic: "(n, m)" or "n, len(xs)" -> tuple ordering
    - Custom: "custom_measure(x)" -> custom function
    """
    text = ranking_text.strip()
    if not text:
        return MeasureKind.NATURAL, []

    # Check for tuple/lexicographic
    if text.startswith("(") and text.endswith(")"):
        inner = text[1:-1]
        components = [c.strip() for c in inner.split(",") if c.strip()]
        if len(components) > 1:
            return MeasureKind.LEXICOGRAPHIC, components
        if components:
            return MeasureKind.NATURAL, components
        return MeasureKind.NATURAL, []

    # Check for comma-separated (without parens)
    if "," in text:
        components = [c.strip() for c in text.split(",") if c.strip()]
        if len(components) > 1:
            return MeasureKind.LEXICOGRAPHIC, components

    # Single measure
    return MeasureKind.NATURAL, [text]


# ---------------------------------------------------------------------------
# Decrease analysis
# ---------------------------------------------------------------------------


def _analyze_decrease_for_call(
    call: RecursiveCallInfo,
    param_names: List[str],
    measure_components: List[str],
    measure_kind: MeasureKind,
) -> MeasureDecreaseEvidence:
    """Analyze whether the ranking function decreases for a recursive call.

    Performs a best-effort syntactic analysis of the call arguments
    relative to the ranking function.
    """
    guards = call._context.get("guards", [])

    # Map function parameters to call arguments
    arg_mapping: Dict[str, str] = {}
    for i, arg_text in enumerate(call.args_text):
        if i < len(param_names):
            arg_mapping[param_names[i]] = arg_text

    # Check each measure component
    decrease_reasons: List[str] = []
    all_verified = True

    for component in measure_components:
        component_stripped = component.strip()
        verified, reason = _check_single_decrease(
            component_stripped, arg_mapping, param_names, guards
        )
        decrease_reasons.append(reason)
        if not verified:
            all_verified = False

    # For lexicographic ordering, we need at least the first component
    # that changes to decrease, with all earlier components non-increasing
    if measure_kind == MeasureKind.LEXICOGRAPHIC and not all_verified:
        lex_result = _check_lexicographic_decrease(
            measure_components, arg_mapping, param_names, guards
        )
        if lex_result[0]:
            all_verified = True
            decrease_reasons = [lex_result[1]]

    combined_reason = "; ".join(decrease_reasons) if decrease_reasons else "no analysis"

    return MeasureDecreaseEvidence(
        _call_or_loop=call,
        _measure_before=", ".join(measure_components),
        _measure_after=", ".join(
            arg_mapping.get(c.strip(), f"?({c.strip()})") for c in measure_components
        ),
        _decrease_reason=combined_reason,
        _verified=all_verified,
        _guard_conditions=tuple(guards),
    )


def _check_single_decrease(
    measure: str,
    arg_mapping: Dict[str, str],
    param_names: List[str],
    guards: List[str],
) -> Tuple[bool, str]:
    """Check if a single measure component decreases."""
    # Direct parameter measure: e.g., measure="n" and call arg is "n - 1"
    if measure in param_names:
        new_value = arg_mapping.get(measure, "")
        if new_value:
            # Check for "measure - k" pattern
            if _is_subtract_pattern(measure, new_value):
                return True, f"{measure} decreases: {new_value} < {measure}"
            # Check for "measure // k" pattern (integer division)
            if _is_divide_pattern(measure, new_value):
                return True, f"{measure} decreases by division: {new_value} < {measure}"
            # Check for structural sub-term patterns
            if _is_structural_sub(measure, new_value):
                return True, f"{measure} decreases structurally: {new_value}"
        return False, f"Cannot verify {measure} decreases"

    # len(x) measure
    if measure.startswith("len(") and measure.endswith(")"):
        inner = measure[4:-1]
        if inner in param_names:
            new_value = arg_mapping.get(inner, "")
            if new_value:
                # Check for slicing patterns like xs[1:] or xs[:-1]
                if _is_slice_decrease(inner, new_value):
                    return True, f"len({inner}) decreases via slicing: {new_value}"
        return False, f"Cannot verify {measure} decreases"

    return False, f"Unrecognized measure pattern: {measure}"


def _is_subtract_pattern(var: str, expr: str) -> bool:
    """Check if expr is var - k for some positive constant k."""
    expr = expr.strip()
    # "var - 1", "var - 2", etc.
    if expr.startswith(f"{var} - ") or expr.startswith(f"{var}-"):
        remainder = expr[len(var):].strip().lstrip("-").strip()
        try:
            k = int(remainder)
            return k > 0
        except ValueError:
            pass
    # "(var - 1)" with parens
    if expr.startswith(f"({var} - ") and expr.endswith(")"):
        inner = expr[1:-1]
        return _is_subtract_pattern(var, inner)
    return False


def _is_divide_pattern(var: str, expr: str) -> bool:
    """Check if expr is var // k for some k > 1."""
    expr = expr.strip()
    if f"{var} // " in expr or f"{var}//" in expr:
        parts = expr.split("//")
        if len(parts) == 2:
            try:
                k = int(parts[1].strip())
                return k > 1
            except ValueError:
                pass
    return False


def _is_structural_sub(var: str, expr: str) -> bool:
    """Check if expr accesses a sub-structure of var."""
    expr = expr.strip()
    # x.left, x.right, x.tail, x.rest, etc.
    structural_suffixes = [
        ".left", ".right", ".tail", ".rest", ".children",
        ".head", ".car", ".cdr", ".next",
    ]
    for suffix in structural_suffixes:
        if expr == f"{var}{suffix}":
            return True
    # x[0], x[1:], x[:-1]
    if expr.startswith(f"{var}[") and expr.endswith("]"):
        return True
    return False


def _is_slice_decrease(var: str, expr: str) -> bool:
    """Check if expr is a slice of var that reduces length."""
    expr = expr.strip()
    # xs[1:], xs[:-1], xs[:n-1], etc.
    decreasing_slices = [
        f"{var}[1:]", f"{var}[:-1]", f"{var}[2:]",
        f"{var}[:-2]", f"{var}[1:-1]",
    ]
    return expr in decreasing_slices


def _check_lexicographic_decrease(
    components: List[str],
    arg_mapping: Dict[str, str],
    param_names: List[str],
    guards: List[str],
) -> Tuple[bool, str]:
    """Check lexicographic decrease across components.

    For (m1, m2, ..., mk) to decrease lexicographically, there must
    exist an index i such that m_i strictly decreases and all m_j
    for j < i remain non-increasing.
    """
    for i, component in enumerate(components):
        comp = component.strip()
        verified, reason = _check_single_decrease(
            comp, arg_mapping, param_names, guards
        )
        if verified:
            prefix_ok = True
            for j in range(i):
                prev_comp = components[j].strip()
                prev_val = arg_mapping.get(prev_comp, "")
                if prev_val and prev_val != prev_comp:
                    # If the previous component changed, it must not increase
                    if not _could_be_non_increasing(prev_comp, prev_val):
                        prefix_ok = False
                        break
            if prefix_ok:
                return True, f"Lexicographic decrease at component {i}: {reason}"
    return False, "No lexicographic decrease found"


def _could_be_non_increasing(var: str, expr: str) -> bool:
    """Check if expr could be non-increasing relative to var."""
    if expr == var:
        return True
    if _is_subtract_pattern(var, expr):
        return True
    if _is_divide_pattern(var, expr):
        return True
    return False


def _analyze_decrease_for_loop(
    loop: LoopIterationInfo,
    measure_components: List[str],
) -> MeasureDecreaseEvidence:
    """Analyze whether the ranking function decreases for a loop iteration."""
    if loop.loop_kind == "for":
        # For loops over finite iterables always terminate
        return MeasureDecreaseEvidence(
            _call_or_loop=loop,
            _decrease_reason="For loop over finite iterable",
            _verified=True,
        )

    # While loops: check if measure components are modified in the body
    modified = set(loop._body_modifies)
    measure_vars = set()
    for comp in measure_components:
        comp = comp.strip()
        if comp.isidentifier():
            measure_vars.add(comp)

    if measure_vars & modified:
        return MeasureDecreaseEvidence(
            _call_or_loop=loop,
            _decrease_reason=(
                f"Measure variables {measure_vars & modified} modified in loop body "
                f"(decrease not verified -- requires runtime analysis)"
            ),
            _verified=False,
        )

    return MeasureDecreaseEvidence(
        _call_or_loop=loop,
        _decrease_reason="Measure variables not modified in loop body",
        _verified=False,
    )


# ---------------------------------------------------------------------------
# Decreases checker
# ---------------------------------------------------------------------------


class DecreasesChecker:
    """Check well-founded decreases annotations.

    Verifies that a user-specified ranking function decreases on each
    recursive call and loop iteration, providing evidence of termination.

    Attributes:
        _strict_mode: If True, require verified decrease for every call.
        _max_depth: Maximum AST depth to analyze.
    """

    def __init__(
        self,
        strict_mode: bool = False,
        max_depth: int = 100,
    ) -> None:
        self._strict_mode: bool = strict_mode
        self._max_depth: int = max_depth

    def check(
        self,
        func_ast: ast.FunctionDef,
        ranking_func: str,
    ) -> DecreasesResult:
        """Check that the ranking function decreases on every recursive call.

        Args:
            func_ast: The function AST to analyze.
            ranking_func: The ranking function specification (e.g., "n"
                         or "(n, len(xs))").

        Returns:
            A DecreasesResult with the verification outcome.
        """
        func_name = func_ast.name

        # Parse the ranking function
        measure_kind, measure_components = _parse_ranking_function(ranking_func)

        # Extract parameter names
        param_names = [
            arg.arg for arg in func_ast.args.args if arg.arg != "self"
        ]

        # Find recursive calls
        recursive_calls = _find_recursive_calls(func_ast)

        # Find loops
        loops = _find_loops(func_ast)

        # Analyze decrease for each recursive call
        evidence_list: List[MeasureDecreaseEvidence] = []
        unverified: List[RecursiveCallInfo] = []

        for call in recursive_calls:
            ev = _analyze_decrease_for_call(
                call, param_names, measure_components, measure_kind
            )
            evidence_list.append(ev)
            if not ev.verified:
                unverified.append(call)

        # Analyze decrease for each loop
        for loop in loops:
            ev = _analyze_decrease_for_loop(loop, measure_components)
            evidence_list.append(ev)

        # Determine verdict
        if not recursive_calls and not loops:
            verdict = DecreasesVerdict.VERIFIED
            explanation = f"Function {func_name} is not recursive and has no loops"
            trust = TrustLevel.PROOF_BACKED
        elif not unverified and all(e.verified for e in evidence_list):
            verdict = DecreasesVerdict.VERIFIED
            explanation = (
                f"All {len(recursive_calls)} recursive calls and "
                f"{len(loops)} loops verified to decrease"
            )
            trust = TrustLevel.TRUSTED_AUTO
        elif len(unverified) < len(recursive_calls):
            verdict = DecreasesVerdict.LIKELY
            explanation = (
                f"{len(recursive_calls) - len(unverified)}/{len(recursive_calls)} "
                f"recursive calls verified; {len(unverified)} unverified"
            )
            trust = TrustLevel.BOUNDED_AUTO
        else:
            if self._strict_mode:
                verdict = DecreasesVerdict.FAILED
                explanation = (
                    f"Could not verify decrease for {len(unverified)} "
                    f"recursive call(s) in strict mode"
                )
                trust = TrustLevel.RESIDUAL
            else:
                verdict = DecreasesVerdict.UNKNOWN
                explanation = (
                    f"Could not verify decrease for {len(unverified)} "
                    f"recursive call(s)"
                )
                trust = TrustLevel.RESIDUAL

        # Build proof term
        proof_term: Optional[ProofTerm] = None
        if verdict == DecreasesVerdict.VERIFIED:
            proof_term = StaticProof(
                method="decreases_check",
                detail=f"Ranking function {ranking_func!r} verified for {func_name}",
            )

        return DecreasesResult(
            _verdict=verdict,
            _measure_kind=measure_kind,
            _ranking_function_text=ranking_func,
            _recursive_calls=tuple(recursive_calls),
            _loop_iterations=tuple(loops),
            _evidence=tuple(evidence_list),
            _unverified_calls=tuple(unverified),
            _explanation=explanation,
            _proof_term=proof_term,
            _trust_level=trust,
        )

    def check_source(
        self,
        source: str,
        ranking_func: str,
        function_name: Optional[str] = None,
    ) -> Optional[DecreasesResult]:
        """Check a decreases annotation in source code.

        Args:
            source: Python source code.
            ranking_func: The ranking function specification.
            function_name: Optional specific function to check.
                          If None, checks the first function found.

        Returns:
            A DecreasesResult, or None if no function found.
        """
        try:
            tree = ast.parse(source)
        except SyntaxError:
            return None
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                if function_name is None or node.name == function_name:
                    return self.check(node, ranking_func)
        return None

    def check_multiple(
        self,
        func_ast: ast.FunctionDef,
        ranking_funcs: List[str],
    ) -> List[DecreasesResult]:
        """Try multiple ranking functions and return all results."""
        return [self.check(func_ast, rf) for rf in ranking_funcs]

    def suggest_ranking_function(
        self,
        func_ast: ast.FunctionDef,
    ) -> List[str]:
        """Suggest candidate ranking functions for a recursive function.

        Examines the function parameters and recursive call patterns
        to suggest plausible ranking functions.
        """
        func_name = func_ast.name
        param_names = [
            arg.arg for arg in func_ast.args.args if arg.arg != "self"
        ]
        recursive_calls = _find_recursive_calls(func_ast)

        candidates: List[str] = []

        if not recursive_calls:
            return candidates

        # For each parameter, check if it appears to decrease in calls
        for param in param_names:
            for call in recursive_calls:
                arg_val = call._arg_names.get(param, "")
                if not arg_val:
                    # Try positional
                    idx = param_names.index(param)
                    if idx < len(call.args_text):
                        arg_val = call.args_text[idx]
                if arg_val and _is_subtract_pattern(param, arg_val):
                    if param not in candidates:
                        candidates.append(param)
                if arg_val and _is_slice_decrease(param, arg_val):
                    if f"len({param})" not in candidates:
                        candidates.append(f"len({param})")

        # Suggest lexicographic ordering if multiple candidates
        if len(candidates) >= 2:
            lex = f"({', '.join(candidates[:3])})"
            candidates.append(lex)

        # Fallback: suggest each parameter as natural number
        if not candidates:
            for param in param_names:
                candidates.append(param)

        return candidates

    def to_obligation(
        self,
        func_name: str,
        ranking_func: str,
        result: DecreasesResult,
    ) -> ProofObligation:
        """Convert a decreases check result into a proof obligation."""
        status = ObligationStatus.DISCHARGED if result.is_verified else ObligationStatus.GENERATED
        return ProofObligation(
            prop=("decreases", ranking_func, func_name),
            site_id=SiteId(SiteKind.PROOF, f"{func_name}.decreases"),
            context={
                "kind": "decreases",
                "function": func_name,
                "ranking_function": ranking_func,
                "verdict": result.verdict.value,
                "measure_kind": result.measure_kind.value,
            },
            status=status,
            proof=result.proof_term,
        )
