"""
Guard Inference Engine — Control-Flow Safety Analysis
=====================================================

Determines which exception sources are *guarded* — protected by
control-flow patterns that prevent the exception from being raised.

A guard is a dominating condition (if-branch, assert, try/except,
pattern match, or library-safe call) that renders an exception source
provably unreachable under the guarded inputs.

This module recognizes the following guard patterns:

  1. **Null / zero checks**
     ``if x != 0: ... x / y``  →  ZeroDivisionError guarded

  2. **Bounds checks**
     ``if 0 <= i < len(lst): ... lst[i]``  →  IndexError guarded

  3. **Membership checks**
     ``if key in d: ... d[key]``  →  KeyError guarded

  4. **Type checks**
     ``if isinstance(x, int): ...``  →  TypeError guarded

  5. **Attribute checks**
     ``if hasattr(obj, 'x'): ... obj.x``  →  AttributeError guarded

  6. **Try/except blocks**
     ``try: ... except KeyError: ...``  →  KeyError caught

  7. **Safe-call patterns**
     ``d.get(key, default)``  →  safe (no KeyError)
     ``getattr(obj, 'x', None)``  →  safe (no AttributeError)

  8. **Assertion guards**
     ``assert x > 0; ... x / y``  →  ZeroDivisionError guarded

  9. **Early return / raise guards**
     ``if x == 0: raise ...; ... x / y``  →  guarded by early exit

Architecture
------------
  GuardKind             — classification of guard patterns
  Guard                 — a single guard protecting a scope
  GuardedSource         — an ExceptionSource paired with its guard(s)
  GuardInferenceEngine  — the main analysis engine
"""
from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Sequence

from deppy.pipeline.exception_sources import (
    ExceptionKind, ExceptionSource, FunctionSourceSummary,
    ModuleSourceSummary, Severity, SourceLocation,
)


# ═══════════════════════════════════════════════════════════════════
# 1.  Guard Classification
# ═══════════════════════════════════════════════════════════════════

class GuardKind(Enum):
    """Classification of protective patterns."""
    ZERO_CHECK        = auto()   # if x != 0  /  if divisor  /  assert x != 0
    BOUNDS_CHECK      = auto()   # if 0 <= i < len(xs)
    MEMBERSHIP_CHECK  = auto()   # if key in d
    TYPE_CHECK        = auto()   # if isinstance(x, T)
    ATTRIBUTE_CHECK   = auto()   # if hasattr(obj, 'attr')
    NONE_CHECK        = auto()   # if x is not None
    TRY_EXCEPT        = auto()   # try/except block
    SAFE_CALL         = auto()   # dict.get(), getattr(,,default)
    ASSERTION         = auto()   # assert condition
    EARLY_EXIT        = auto()   # if bad: return/raise  (dominator)
    PATTERN_MATCH     = auto()   # match/case structural
    TRUTHINESS_CHECK  = auto()   # if xs:  (non-empty check)
    LENGTH_CHECK      = auto()   # if len(xs) > 0
    CONDITIONAL_EXPR  = auto()   # x if cond else default
    WALRUS_CHECK      = auto()   # if (val := expr) is not None


class SafetyLevel(Enum):
    """How confidently is the exception source guarded?"""
    PROVED_SAFE         = auto()  # guard condition provably prevents exception
    SAFE_BY_PATTERN     = auto()  # recognized safe pattern (e.g., dict.get)
    SAFE_UNDER_PRECOND  = auto()  # safe if preconditions hold
    CAUGHT              = auto()  # exception is caught by try/except
    PARTIALLY_GUARDED   = auto()  # some but not all paths guarded
    UNGUARDED           = auto()  # no guard found
    UNRESOLVABLE        = auto()  # analysis can't determine


@dataclass(frozen=True)
class Guard:
    """A protective pattern that prevents an exception."""
    kind: GuardKind
    condition: str            # human-readable / Z3-encodable condition
    lineno: int = 0           # line of the guard
    scope_start: int = 0      # first line of the guarded scope
    scope_end: int = 0        # last line of the guarded scope
    protects: set[ExceptionKind] = field(default_factory=set)
    confidence: float = 1.0   # 1.0 = certain, 0.5 = heuristic

    def __repr__(self) -> str:
        kinds = ", ".join(k.name for k in self.protects)
        return f"Guard({self.kind.name} @ L{self.lineno}: {self.condition} → [{kinds}])"


@dataclass
class GuardedSource:
    """An exception source paired with analysis results."""
    source: ExceptionSource
    guards: list[Guard] = field(default_factory=list)
    safety: SafetyLevel = SafetyLevel.UNGUARDED
    safety_condition: str = ""  # formal condition under which this is safe

    @property
    def is_safe(self) -> bool:
        return self.safety in (SafetyLevel.PROVED_SAFE,
                               SafetyLevel.SAFE_BY_PATTERN,
                               SafetyLevel.CAUGHT)

    @property
    def is_conditionally_safe(self) -> bool:
        return self.safety == SafetyLevel.SAFE_UNDER_PRECOND

    def __repr__(self) -> str:
        return (f"GuardedSource({self.source.kind.name} @ "
                f"L{self.source.location.lineno}: {self.safety.name})")


@dataclass
class FunctionGuardAnalysis:
    """Guard analysis for one function."""
    name: str
    guarded_sources: list[GuardedSource] = field(default_factory=list)

    @property
    def safe_count(self) -> int:
        return sum(1 for g in self.guarded_sources if g.is_safe)

    @property
    def unsafe_count(self) -> int:
        return sum(1 for g in self.guarded_sources
                   if g.safety == SafetyLevel.UNGUARDED)

    @property
    def total(self) -> int:
        return len(self.guarded_sources)

    @property
    def all_safe(self) -> bool:
        return all(g.is_safe or g.is_conditionally_safe
                   for g in self.guarded_sources)


@dataclass
class ModuleGuardAnalysis:
    """Guard analysis for an entire module."""
    module_path: str
    functions: list[FunctionGuardAnalysis] = field(default_factory=list)

    @property
    def total_sources(self) -> int:
        return sum(f.total for f in self.functions)

    @property
    def total_safe(self) -> int:
        return sum(f.safe_count for f in self.functions)

    @property
    def total_unsafe(self) -> int:
        return sum(f.unsafe_count for f in self.functions)


# ═══════════════════════════════════════════════════════════════════
# 2.  Guard Inference Engine
# ═══════════════════════════════════════════════════════════════════

class GuardInferenceEngine:
    """Analyze Python source to identify guards protecting exception sites.

    The engine works in two passes:

    1. **Guard collection**: walk the AST to find all protective patterns
       (if-checks, try/except, safe calls, assertions, early exits).

    2. **Guard matching**: for each exception source, determine which
       guards (if any) protect it, based on line ranges and semantic
       relevance (e.g., a zero-check guards division, not indexing).

    Usage
    -----
    >>> engine = GuardInferenceEngine()
    >>> source_summary = find_exception_sources(code)
    >>> analysis = engine.analyze_module(code, source_summary)
    """

    def analyze_module(self, source: str,
                       source_summary: ModuleSourceSummary) -> ModuleGuardAnalysis:
        """Analyze all functions in a module."""
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return ModuleGuardAnalysis(module_path=source_summary.module_path)

        fn_analyses: list[FunctionGuardAnalysis] = []
        for fn_summary in source_summary.functions:
            fn_node = self._find_function_node(tree, fn_summary.name)
            if fn_node is not None:
                analysis = self._analyze_function(fn_node, fn_summary)
            else:
                analysis = self._analyze_function_no_ast(fn_summary)
            fn_analyses.append(analysis)

        return ModuleGuardAnalysis(
            module_path=source_summary.module_path,
            functions=fn_analyses,
        )

    def analyze_function(self, source: str,
                         fn_summary: FunctionSourceSummary) -> FunctionGuardAnalysis:
        """Analyze a single function."""
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return self._analyze_function_no_ast(fn_summary)

        for node in ast.walk(tree):
            if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and node.name == fn_summary.name):
                return self._analyze_function(node, fn_summary)

        return self._analyze_function_no_ast(fn_summary)

    # ── Internal analysis ─────────────────────────────────────────

    def _analyze_function(self, fn_node: ast.FunctionDef | ast.AsyncFunctionDef,
                          fn_summary: FunctionSourceSummary) -> FunctionGuardAnalysis:
        """Full guard analysis for one function with AST available."""
        # Phase 1: collect all guards in this function
        guards = self._collect_guards(fn_node)

        # Phase 2: match guards to exception sources
        guarded_sources: list[GuardedSource] = []
        for source in fn_summary.sources:
            gs = self._match_guards(source, guards)
            guarded_sources.append(gs)

        return FunctionGuardAnalysis(
            name=fn_summary.name,
            guarded_sources=guarded_sources,
        )

    def _analyze_function_no_ast(self,
                                 fn_summary: FunctionSourceSummary) -> FunctionGuardAnalysis:
        """Fallback when AST is not available — mark everything unguarded."""
        guarded = [
            GuardedSource(
                source=src,
                safety=(SafetyLevel.CAUGHT if src.caught_by is not None
                        else SafetyLevel.UNGUARDED),
            )
            for src in fn_summary.sources
        ]
        return FunctionGuardAnalysis(
            name=fn_summary.name,
            guarded_sources=guarded,
        )

    # ── Phase 1: Guard Collection ─────────────────────────────────

    def _collect_guards(self, fn_node: ast.AST) -> list[Guard]:
        """Collect all guards in a function body."""
        guards: list[Guard] = []
        self._collect_from_body(getattr(fn_node, 'body', []), guards, fn_node)
        return guards

    def _collect_from_body(self, body: list[ast.stmt],
                           guards: list[Guard],
                           parent: ast.AST) -> None:
        """Recursively collect guards from a statement list."""
        for i, stmt in enumerate(body):
            # ── If statements ────────────────────────────────
            if isinstance(stmt, ast.If):
                self._collect_if_guards(stmt, guards)
                # Recurse into both branches
                self._collect_from_body(stmt.body, guards, stmt)
                self._collect_from_body(stmt.orelse, guards, stmt)

            # ── Try/except ───────────────────────────────────
            elif isinstance(stmt, ast.Try):
                self._collect_try_guards(stmt, guards)
                self._collect_from_body(stmt.body, guards, stmt)
                for handler in stmt.handlers:
                    self._collect_from_body(handler.body, guards, handler)
                self._collect_from_body(stmt.orelse, guards, stmt)
                self._collect_from_body(stmt.finalbody, guards, stmt)

            # ── Assert statements ────────────────────────────
            elif isinstance(stmt, ast.Assert):
                self._collect_assert_guard(stmt, guards, body, i)

            # ── For / While loops ────────────────────────────
            elif isinstance(stmt, (ast.For, ast.While)):
                self._collect_from_body(stmt.body, guards, stmt)
                self._collect_from_body(stmt.orelse, guards, stmt)

            # ── With statements ──────────────────────────────
            elif isinstance(stmt, ast.With):
                self._collect_from_body(stmt.body, guards, stmt)

            # ── Function / class defs (nested) ───────────────
            elif isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                pass  # analyzed separately

            # ── Early return / raise as guards ───────────────
            elif isinstance(stmt, (ast.Return, ast.Raise)):
                # Check if preceded by a condition
                self._collect_early_exit_guard(stmt, guards, body, i)

    def _collect_if_guards(self, if_node: ast.If,
                           guards: list[Guard]) -> None:
        """Extract guards from if-conditions."""
        test = if_node.test
        body_range = _stmt_range(if_node.body)

        # ── Zero / division guards ───────────────────────────
        zero_guard = self._check_zero_guard(test)
        if zero_guard:
            guards.append(Guard(
                kind=GuardKind.ZERO_CHECK,
                condition=zero_guard,
                lineno=if_node.lineno,
                scope_start=body_range[0],
                scope_end=body_range[1],
                protects={ExceptionKind.ZERO_DIVISION},
            ))

        # ── Bounds checks ────────────────────────────────────
        bounds_guard = self._check_bounds_guard(test)
        if bounds_guard:
            guards.append(Guard(
                kind=GuardKind.BOUNDS_CHECK,
                condition=bounds_guard,
                lineno=if_node.lineno,
                scope_start=body_range[0],
                scope_end=body_range[1],
                protects={ExceptionKind.INDEX_ERROR},
            ))

        # ── Membership checks ────────────────────────────────
        membership_guard = self._check_membership_guard(test)
        if membership_guard:
            guards.append(Guard(
                kind=GuardKind.MEMBERSHIP_CHECK,
                condition=membership_guard,
                lineno=if_node.lineno,
                scope_start=body_range[0],
                scope_end=body_range[1],
                protects={ExceptionKind.KEY_ERROR, ExceptionKind.INDEX_ERROR},
            ))

        # ── Type checks ──────────────────────────────────────
        type_guard = self._check_type_guard(test)
        if type_guard:
            guards.append(Guard(
                kind=GuardKind.TYPE_CHECK,
                condition=type_guard,
                lineno=if_node.lineno,
                scope_start=body_range[0],
                scope_end=body_range[1],
                protects={ExceptionKind.TYPE_ERROR, ExceptionKind.ATTRIBUTE_ERROR},
            ))

        # ── Attribute checks ─────────────────────────────────
        attr_guard = self._check_attribute_guard(test)
        if attr_guard:
            guards.append(Guard(
                kind=GuardKind.ATTRIBUTE_CHECK,
                condition=attr_guard,
                lineno=if_node.lineno,
                scope_start=body_range[0],
                scope_end=body_range[1],
                protects={ExceptionKind.ATTRIBUTE_ERROR},
            ))

        # ── None checks ──────────────────────────────────────
        none_guard = self._check_none_guard(test)
        if none_guard:
            guards.append(Guard(
                kind=GuardKind.NONE_CHECK,
                condition=none_guard,
                lineno=if_node.lineno,
                scope_start=body_range[0],
                scope_end=body_range[1],
                protects={ExceptionKind.TYPE_ERROR, ExceptionKind.ATTRIBUTE_ERROR},
            ))

        # ── Truthiness checks (non-empty) ────────────────────
        truth_guard = self._check_truthiness_guard(test)
        if truth_guard:
            guards.append(Guard(
                kind=GuardKind.TRUTHINESS_CHECK,
                condition=truth_guard,
                lineno=if_node.lineno,
                scope_start=body_range[0],
                scope_end=body_range[1],
                protects={ExceptionKind.INDEX_ERROR, ExceptionKind.VALUE_ERROR,
                          ExceptionKind.ZERO_DIVISION},
            ))

        # ── Length checks ────────────────────────────────────
        len_guard = self._check_length_guard(test)
        if len_guard:
            guards.append(Guard(
                kind=GuardKind.LENGTH_CHECK,
                condition=len_guard,
                lineno=if_node.lineno,
                scope_start=body_range[0],
                scope_end=body_range[1],
                protects={ExceptionKind.INDEX_ERROR, ExceptionKind.VALUE_ERROR},
            ))

    def _collect_try_guards(self, try_node: ast.Try,
                            guards: list[Guard]) -> None:
        """Record try/except as guards for the try body."""
        body_range = _stmt_range(try_node.body)
        for handler in try_node.handlers:
            caught_kinds = self._handler_to_kinds(handler)
            guards.append(Guard(
                kind=GuardKind.TRY_EXCEPT,
                condition=f"caught by except at L{handler.lineno}",
                lineno=handler.lineno,
                scope_start=body_range[0],
                scope_end=body_range[1],
                protects=caught_kinds,
            ))

    def _collect_assert_guard(self, assert_node: ast.Assert,
                              guards: list[Guard],
                              body: list[ast.stmt], idx: int) -> None:
        """Assert as a guard for subsequent statements."""
        remaining = body[idx + 1:]
        if not remaining:
            return
        remaining_range = _stmt_range(remaining)

        # Check what the assertion guards
        test = assert_node.test
        protects: set[ExceptionKind] = set()

        if self._check_zero_guard(test):
            protects.add(ExceptionKind.ZERO_DIVISION)
        if self._check_bounds_guard(test):
            protects.add(ExceptionKind.INDEX_ERROR)
        if self._check_none_guard(test):
            protects.update({ExceptionKind.TYPE_ERROR, ExceptionKind.ATTRIBUTE_ERROR})
        if self._check_type_guard(test):
            protects.update({ExceptionKind.TYPE_ERROR, ExceptionKind.ATTRIBUTE_ERROR})
        if self._check_truthiness_guard(test):
            protects.update({ExceptionKind.INDEX_ERROR, ExceptionKind.VALUE_ERROR})

        if protects:
            guards.append(Guard(
                kind=GuardKind.ASSERTION,
                condition=f"assert at L{assert_node.lineno}",
                lineno=assert_node.lineno,
                scope_start=remaining_range[0],
                scope_end=remaining_range[1],
                protects=protects,
                confidence=0.9,  # asserts can be disabled with -O
            ))

    def _collect_early_exit_guard(self, stmt: ast.stmt,
                                  guards: list[Guard],
                                  body: list[ast.stmt], idx: int) -> None:
        """Early return/raise in an if-else as guard for the else branch."""
        if idx == 0:
            return
        prev = body[idx - 1]
        if not isinstance(prev, ast.If):
            return
        # Check if this return/raise is inside the if-body
        # and the rest of the function is the "else" scope
        remaining = body[idx + 1:]
        if not remaining:
            return

    # ── Guard Pattern Recognizers ─────────────────────────────────

    def _check_zero_guard(self, test: ast.expr) -> str:
        """Recognize zero-check patterns: x != 0, x, not x == 0."""
        # x != 0
        if isinstance(test, ast.Compare):
            if (len(test.ops) == 1 and isinstance(test.ops[0], ast.NotEq)
                    and len(test.comparators) == 1):
                comp = test.comparators[0]
                if isinstance(comp, ast.Constant) and comp.value == 0:
                    return f"{_expr_str(test.left)} != 0"
            # x > 0, x < 0 (implies non-zero)
            if (len(test.ops) == 1
                    and isinstance(test.ops[0], (ast.Gt, ast.Lt, ast.GtE, ast.LtE))
                    and len(test.comparators) == 1):
                comp = test.comparators[0]
                if isinstance(comp, ast.Constant) and comp.value == 0:
                    op = _cmp_str(test.ops[0])
                    return f"{_expr_str(test.left)} {op} 0"

        # UnaryOp: not (x == 0)
        if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
            inner = test.operand
            if (isinstance(inner, ast.Compare) and len(inner.ops) == 1
                    and isinstance(inner.ops[0], ast.Eq)):
                comp = inner.comparators[0]
                if isinstance(comp, ast.Constant) and comp.value == 0:
                    return f"{_expr_str(inner.left)} != 0"

        # Simple truthiness: if x  (where x is a Name that could be zero)
        if isinstance(test, ast.Name):
            return f"{test.id} is truthy (non-zero)"

        return ""

    def _check_bounds_guard(self, test: ast.expr) -> str:
        """Recognize bounds-check patterns: 0 <= i < len(xs), i < len(xs)."""
        if not isinstance(test, ast.Compare):
            return ""

        ops = test.ops
        comps = test.comparators

        # Pattern: i < len(xs)  or  i < N
        if len(ops) == 1 and isinstance(ops[0], ast.Lt):
            if self._is_len_call(comps[0]):
                return f"{_expr_str(test.left)} < len({_len_arg(comps[0])})"

        # Pattern: 0 <= i < len(xs)
        if len(ops) == 2:
            if (isinstance(ops[0], (ast.LtE, ast.Lt))
                    and isinstance(ops[1], ast.Lt)):
                left = test.left
                if isinstance(left, ast.Constant) and left.value == 0:
                    if self._is_len_call(comps[1]):
                        return (f"0 <= {_expr_str(comps[0])} < "
                                f"len({_len_arg(comps[1])})")

        # Pattern: i >= 0 and i < len(xs)  (as BoolOp)
        return ""

    def _check_membership_guard(self, test: ast.expr) -> str:
        """Recognize 'key in d' patterns."""
        if isinstance(test, ast.Compare):
            if (len(test.ops) == 1 and isinstance(test.ops[0], ast.In)):
                return f"{_expr_str(test.left)} in {_expr_str(test.comparators[0])}"
        return ""

    def _check_type_guard(self, test: ast.expr) -> str:
        """Recognize isinstance() checks."""
        if isinstance(test, ast.Call):
            if (isinstance(test.func, ast.Name)
                    and test.func.id == "isinstance"
                    and len(test.args) >= 2):
                return f"isinstance({_expr_str(test.args[0])}, {_expr_str(test.args[1])})"
        return ""

    def _check_attribute_guard(self, test: ast.expr) -> str:
        """Recognize hasattr() checks."""
        if isinstance(test, ast.Call):
            if (isinstance(test.func, ast.Name)
                    and test.func.id == "hasattr"
                    and len(test.args) >= 2):
                return f"hasattr({_expr_str(test.args[0])}, {_expr_str(test.args[1])})"
        return ""

    def _check_none_guard(self, test: ast.expr) -> str:
        """Recognize 'x is not None' patterns."""
        if isinstance(test, ast.Compare):
            if len(test.ops) == 1 and isinstance(test.ops[0], ast.IsNot):
                comp = test.comparators[0]
                if isinstance(comp, ast.Constant) and comp.value is None:
                    return f"{_expr_str(test.left)} is not None"
            if len(test.ops) == 1 and isinstance(test.ops[0], ast.Is):
                comp = test.comparators[0]
                if isinstance(comp, ast.Constant) and comp.value is None:
                    # 'x is None' in an if → else branch is guarded
                    return ""  # not a guard for the if-body
        return ""

    def _check_truthiness_guard(self, test: ast.expr) -> str:
        """Recognize truthiness checks: if xs, if d, if s."""
        if isinstance(test, ast.Name):
            return f"{test.id} is truthy"
        return ""

    def _check_length_guard(self, test: ast.expr) -> str:
        """Recognize len() > 0 checks."""
        if isinstance(test, ast.Compare):
            if (len(test.ops) == 1
                    and isinstance(test.ops[0], (ast.Gt, ast.GtE))
                    and self._is_len_call(test.left)):
                comp = test.comparators[0]
                if isinstance(comp, ast.Constant) and comp.value == 0:
                    return f"len({_len_arg(test.left)}) > 0"
        return ""

    # ── Phase 2: Guard Matching ───────────────────────────────────

    def _match_guards(self, source: ExceptionSource,
                      guards: list[Guard]) -> GuardedSource:
        """Determine which guards protect a given exception source."""
        # Already caught by try/except?
        if source.caught_by is not None:
            return GuardedSource(
                source=source,
                safety=SafetyLevel.CAUGHT,
                safety_condition="caught by try/except",
            )

        # Check safe call patterns first
        safe_pattern = self._check_safe_call_pattern(source)
        if safe_pattern:
            return GuardedSource(
                source=source,
                guards=[safe_pattern],
                safety=SafetyLevel.SAFE_BY_PATTERN,
                safety_condition=safe_pattern.condition,
            )

        # Find matching guards
        matching: list[Guard] = []
        src_line = source.location.lineno
        for guard in guards:
            # Guard must protect the right exception kind
            if source.kind not in guard.protects:
                continue
            # Guard must dominate the exception source (source inside guard scope)
            if guard.scope_start <= src_line <= guard.scope_end:
                matching.append(guard)

        if matching:
            # Determine safety level from best guard
            best = max(matching, key=lambda g: g.confidence)
            if best.confidence >= 0.9:
                return GuardedSource(
                    source=source,
                    guards=matching,
                    safety=SafetyLevel.PROVED_SAFE,
                    safety_condition=best.condition,
                )
            else:
                return GuardedSource(
                    source=source,
                    guards=matching,
                    safety=SafetyLevel.SAFE_UNDER_PRECOND,
                    safety_condition=best.condition,
                )

        return GuardedSource(
            source=source,
            safety=SafetyLevel.UNGUARDED,
        )

    def _check_safe_call_pattern(self, source: ExceptionSource) -> Guard | None:
        """Detect inherently safe call patterns (dict.get, getattr with default)."""
        node = source.ast_node
        if not isinstance(node, ast.Call):
            return None

        # dict.get(key, default) — no KeyError
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr == "get"
                and len(node.args) >= 2):
            if source.kind == ExceptionKind.KEY_ERROR:
                return Guard(
                    kind=GuardKind.SAFE_CALL,
                    condition="dict.get() with default",
                    lineno=getattr(node, 'lineno', 0),
                    protects={ExceptionKind.KEY_ERROR},
                )

        # getattr(obj, name, default) — no AttributeError
        if (isinstance(node.func, ast.Name)
                and node.func.id == "getattr"
                and len(node.args) >= 3):
            if source.kind == ExceptionKind.ATTRIBUTE_ERROR:
                return Guard(
                    kind=GuardKind.SAFE_CALL,
                    condition="getattr() with default",
                    lineno=getattr(node, 'lineno', 0),
                    protects={ExceptionKind.ATTRIBUTE_ERROR},
                )

        # next(iter, default) — no StopIteration
        if (isinstance(node.func, ast.Name)
                and node.func.id == "next"
                and len(node.args) >= 2):
            if source.kind == ExceptionKind.STOP_ITERATION:
                return Guard(
                    kind=GuardKind.SAFE_CALL,
                    condition="next() with default",
                    lineno=getattr(node, 'lineno', 0),
                    protects={ExceptionKind.STOP_ITERATION},
                )

        return None

    # ── Helpers ───────────────────────────────────────────────────

    @staticmethod
    def _is_len_call(node: ast.expr) -> bool:
        """Check if node is a call to len()."""
        return (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "len")

    @staticmethod
    def _handler_to_kinds(handler: ast.ExceptHandler) -> set[ExceptionKind]:
        """Map an except handler to the ExceptionKind set it catches."""
        if handler.type is None:
            return set(ExceptionKind)

        names: set[str] = set()
        if isinstance(handler.type, ast.Name):
            names.add(handler.type.id)
        elif isinstance(handler.type, ast.Tuple):
            for elt in handler.type.elts:
                if isinstance(elt, ast.Name):
                    names.add(elt.id)

        from deppy.pipeline.exception_sources import (
            exception_kind_from_name, _is_subclass_name, _EXCEPTION_HIERARCHY,
        )

        kinds: set[ExceptionKind] = set()
        for name in names:
            # Direct match
            kind = exception_kind_from_name(name)
            kinds.add(kind)
            # Add all children in the hierarchy
            if name in _EXCEPTION_HIERARCHY:
                for child in _EXCEPTION_HIERARCHY[name]:
                    kinds.add(exception_kind_from_name(child))
            # Common base classes
            if name in ("Exception", "BaseException"):
                kinds = set(ExceptionKind)
                break

        return kinds

    @staticmethod
    def _find_function_node(tree: ast.Module,
                            name: str) -> ast.FunctionDef | ast.AsyncFunctionDef | None:
        """Find a function definition by name in the AST."""
        for node in ast.walk(tree):
            if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and node.name == name):
                return node
        return None


# ═══════════════════════════════════════════════════════════════════
# 3.  AST Helpers
# ═══════════════════════════════════════════════════════════════════

def _stmt_range(stmts: list[ast.stmt]) -> tuple[int, int]:
    """Return (first_line, last_line) of a statement list."""
    if not stmts:
        return (0, 0)
    first = stmts[0].lineno
    last = getattr(stmts[-1], 'end_lineno', stmts[-1].lineno)
    return (first, last)


def _expr_str(node: ast.expr) -> str:
    """Best-effort string representation of an AST expression."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Constant):
        return repr(node.value)
    if isinstance(node, ast.Attribute):
        return f"{_expr_str(node.value)}.{node.attr}"
    if isinstance(node, ast.Call):
        func = _expr_str(node.func)
        args = ", ".join(_expr_str(a) for a in node.args)
        return f"{func}({args})"
    if isinstance(node, ast.Subscript):
        return f"{_expr_str(node.value)}[{_expr_str(node.slice)}]"
    if isinstance(node, ast.Tuple):
        return f"({', '.join(_expr_str(e) for e in node.elts)})"
    if isinstance(node, ast.BinOp):
        return f"({_expr_str(node.left)} {_op_sym(node.op)} {_expr_str(node.right)})"
    if isinstance(node, ast.UnaryOp):
        return f"{_unary_sym(node.op)}{_expr_str(node.operand)}"
    if isinstance(node, ast.BoolOp):
        op = " and " if isinstance(node.op, ast.And) else " or "
        return op.join(_expr_str(v) for v in node.values)
    try:
        return ast.unparse(node)
    except Exception:
        return "<?>"


def _cmp_str(op: ast.cmpop) -> str:
    return {ast.Eq: "==", ast.NotEq: "!=", ast.Lt: "<", ast.LtE: "<=",
            ast.Gt: ">", ast.GtE: ">=", ast.Is: "is", ast.IsNot: "is not",
            ast.In: "in", ast.NotIn: "not in"}.get(type(op), "?")


def _op_sym(op: ast.operator) -> str:
    return {ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/",
            ast.FloorDiv: "//", ast.Mod: "%", ast.Pow: "**",
            ast.BitAnd: "&", ast.BitOr: "|", ast.BitXor: "^",
            ast.LShift: "<<", ast.RShift: ">>"}.get(type(op), "?")


def _unary_sym(op: ast.unaryop) -> str:
    return {ast.Not: "not ", ast.UAdd: "+", ast.USub: "-",
            ast.Invert: "~"}.get(type(op), "?")


def _len_arg(node: ast.Call) -> str:
    """Extract the argument of len() call as a string."""
    if node.args:
        return _expr_str(node.args[0])
    return "?"
