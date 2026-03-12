"""None-guard harvester -- extract None-check patterns from Python AST.

Identifies patterns that check for ``None``-ness: explicit ``x is None``,
``x is not None``, truthiness tests ``if x:``, short-circuit defaults
``x or default``, and ternary defaults ``x if x else default``.

Each discovered pattern is recorded as a frozen ``NoneGuard`` dataclass.
"""

from __future__ import annotations

import ast
import enum
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
    Union,
)

from deppy.core._protocols import TrustLevel
from deppy.predicates.base import (
    Predicate,
    SourceLocation,
    Term,
    Var,
)
from deppy.predicates.nullability import (
    Falsy,
    IsNone,
    IsNotNone,
    Truthy,
)
from deppy.static_analysis.observation_sites import SourceSpan


# ===================================================================
#  NoneGuard pattern kind
# ===================================================================

class NoneCheckKind(enum.Enum):
    """The syntactic pattern that produced the None check."""
    IS_NONE = "is_none"
    IS_NOT_NONE = "is_not_none"
    TRUTHINESS = "truthiness"
    FALSINESS = "falsiness"
    OR_DEFAULT = "or_default"
    TERNARY_DEFAULT = "ternary_default"
    AND_GUARD = "and_guard"
    OPTIONAL_CHAIN = "optional_chain"
    ASSERT_NOT_NONE = "assert_not_none"
    WALRUS_NONE_CHECK = "walrus_none_check"
    NONE_RETURN_GUARD = "none_return_guard"
    NONE_COMPARISON = "none_comparison"


# ===================================================================
#  NoneGuard dataclass
# ===================================================================

@dataclass(frozen=True)
class NoneGuard:
    """A None-check pattern extracted from the AST.

    Attributes:
        variable: The variable being checked for None.
        is_none_check: ``True`` if the pattern checks that the variable IS None.
        polarity: ``True`` for the true-branch of the enclosing conditional.
        none_check_kind: The syntactic pattern that produced this check.
        predicate: The corresponding predicate from deppy.predicates.
        source_span: Location in source code.
        trust_level: Provenance trust level.
        default_value: For or-default and ternary-default, the default expression.
        enclosing_function: Name of the enclosing function, if any.
        is_in_assertion: Whether this check appears inside an assert.
        is_in_return: Whether this check appears inside a return statement.
        chain_variable: For optional chaining like ``x.y``, the attribute chain.
    """
    variable: str
    is_none_check: bool
    polarity: bool = True
    none_check_kind: NoneCheckKind = NoneCheckKind.IS_NONE
    predicate: Optional[Predicate] = None
    source_span: Optional[SourceSpan] = None
    trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO
    default_value: Optional[str] = None
    enclosing_function: Optional[str] = None
    is_in_assertion: bool = False
    is_in_return: bool = False
    chain_variable: Optional[str] = None


# ===================================================================
#  Helper functions
# ===================================================================

def _extract_var_name(node: ast.expr) -> Optional[str]:
    """Extract a variable name from an AST expression."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = _extract_var_name(node.value)
        if base is not None:
            return f"{base}.{node.attr}"
    return None


def _is_none_constant(node: ast.expr) -> bool:
    """Check if an AST node is the ``None`` constant."""
    return isinstance(node, ast.Constant) and node.value is None


def _source_loc(node: ast.AST, file: str) -> SourceLocation:
    """Build a SourceLocation from an AST node."""
    return SourceLocation(
        file=file,
        line=getattr(node, "lineno", 0),
        col=getattr(node, "col_offset", 0),
        end_line=getattr(node, "end_lineno", None),
        end_col=getattr(node, "end_col_offset", None),
    )


def _expr_to_str(node: ast.expr) -> str:
    """Best-effort pretty-print of an AST expression."""
    try:
        return ast.unparse(node)
    except Exception:
        return "<expr>"


# ===================================================================
#  NoneGuardHarvester visitor
# ===================================================================

class NoneGuardHarvester(ast.NodeVisitor):
    """AST visitor that extracts None-check patterns.

    Handles:
    - ``x is None`` / ``x is not None`` in if/elif/while/assert
    - Truthiness: ``if x:`` (implies x is not None for Optional[T])
    - Or-default: ``x or default``
    - Ternary default: ``x if x else default``
    - And-guard: ``x and x.attr``
    - None-return guard: ``if x is None: return``
    - Assert not None: ``assert x is not None``

    Usage::

        harvester = NoneGuardHarvester(file="example.py")
        harvester.visit(tree)
        guards = harvester.guards
    """

    def __init__(self, file: str = "<unknown>") -> None:
        self._file = file
        self._guards: List[NoneGuard] = []
        self._function_stack: List[str] = []
        self._in_assertion: bool = False

    @property
    def guards(self) -> List[NoneGuard]:
        """All collected None guards."""
        return list(self._guards)

    @property
    def _current_function(self) -> Optional[str]:
        return self._function_stack[-1] if self._function_stack else None

    def _span(self, node: ast.AST) -> SourceSpan:
        return SourceSpan.from_ast(node, self._file)

    def _add_guard(
        self,
        variable: str,
        is_none_check: bool,
        node: ast.AST,
        *,
        polarity: bool = True,
        kind: NoneCheckKind = NoneCheckKind.IS_NONE,
        default_value: Optional[str] = None,
        is_in_return: bool = False,
        chain_variable: Optional[str] = None,
    ) -> None:
        src = _source_loc(node, self._file)
        var_term = Var(variable.split(".")[0])
        if is_none_check:
            pred: Predicate = IsNone(term=var_term, source_location=src)
        else:
            pred = IsNotNone(term=var_term, source_location=src)

        trust = (
            TrustLevel.PROOF_BACKED if self._in_assertion
            else TrustLevel.TRUSTED_AUTO
        )
        self._guards.append(NoneGuard(
            variable=variable,
            is_none_check=is_none_check,
            polarity=polarity,
            none_check_kind=kind,
            predicate=pred,
            source_span=self._span(node),
            trust_level=trust,
            default_value=default_value,
            enclosing_function=self._current_function,
            is_in_assertion=self._in_assertion,
            is_in_return=is_in_return,
            chain_variable=chain_variable,
        ))

    # -- Scope tracking --

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._function_stack.append(node.name)
        self.generic_visit(node)
        self._function_stack.pop()

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._function_stack.append(node.name)
        self.generic_visit(node)
        self._function_stack.pop()

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._function_stack.append(node.name)
        self.generic_visit(node)
        self._function_stack.pop()

    # -- If statements --

    def visit_If(self, node: ast.If) -> None:
        self._extract_none_from_test(node.test, node, polarity=True)
        self._extract_none_from_test(node.test, node, polarity=False)

        # Check for None-return guard: if x is None: return
        self._check_none_return_guard(node)

        # Handle elif
        for else_node in node.orelse:
            if isinstance(else_node, ast.If):
                self._extract_none_from_test(else_node.test, else_node, polarity=True)
                self._extract_none_from_test(else_node.test, else_node, polarity=False)
                self._check_none_return_guard(else_node)

        self.generic_visit(node)

    def _check_none_return_guard(self, node: ast.If) -> None:
        """Check for pattern: if x is None: return (early return guard)."""
        if not node.body:
            return
        # Check if body is a single return statement
        if len(node.body) == 1 and isinstance(node.body[0], (ast.Return, ast.Raise)):
            # Extract variable from the None check
            test = node.test
            if isinstance(test, ast.Compare):
                for i, op in enumerate(test.ops):
                    comparators = [test.left] + test.comparators
                    left = comparators[i]
                    right = comparators[i + 1]

                    if isinstance(op, ast.Is) and _is_none_constant(right):
                        var_name = _extract_var_name(left)
                        if var_name is not None:
                            self._add_guard(
                                var_name, True, node,
                                polarity=True,
                                kind=NoneCheckKind.NONE_RETURN_GUARD,
                                is_in_return=True,
                            )
                    elif isinstance(op, ast.Is) and _is_none_constant(left):
                        var_name = _extract_var_name(right)
                        if var_name is not None:
                            self._add_guard(
                                var_name, True, node,
                                polarity=True,
                                kind=NoneCheckKind.NONE_RETURN_GUARD,
                                is_in_return=True,
                            )

    # -- While loops --

    def visit_While(self, node: ast.While) -> None:
        self._extract_none_from_test(node.test, node, polarity=True)
        self.generic_visit(node)

    # -- Assert statements --

    def visit_Assert(self, node: ast.Assert) -> None:
        old = self._in_assertion
        self._in_assertion = True
        self._extract_none_from_test(node.test, node, polarity=True)
        self._in_assertion = old
        self.generic_visit(node)

    # -- BoolOp: x or default, x and x.attr --

    def visit_BoolOp(self, node: ast.BoolOp) -> None:
        if isinstance(node.op, ast.Or) and len(node.values) >= 2:
            # x or default pattern
            first = node.values[0]
            var_name = _extract_var_name(first)
            if var_name is not None:
                for default in node.values[1:]:
                    self._add_guard(
                        var_name, False, node,
                        polarity=True,
                        kind=NoneCheckKind.OR_DEFAULT,
                        default_value=_expr_to_str(default),
                    )
                    # Also: if we reach the default, the variable was falsy
                    self._add_guard(
                        var_name, True, default,
                        polarity=True,
                        kind=NoneCheckKind.OR_DEFAULT,
                        default_value=_expr_to_str(default),
                    )

        elif isinstance(node.op, ast.And) and len(node.values) >= 2:
            # x and x.attr pattern (optional chaining)
            first = node.values[0]
            var_name = _extract_var_name(first)
            if var_name is not None:
                for subsequent in node.values[1:]:
                    # If we reach subsequent, first was truthy => not None
                    self._add_guard(
                        var_name, False, subsequent,
                        polarity=True,
                        kind=NoneCheckKind.AND_GUARD,
                    )
                    # Check for optional chaining: x and x.attr
                    if isinstance(subsequent, ast.Attribute):
                        chain_var = _extract_var_name(subsequent.value)
                        if chain_var == var_name:
                            self._add_guard(
                                var_name, False, subsequent,
                                polarity=True,
                                kind=NoneCheckKind.OPTIONAL_CHAIN,
                                chain_variable=f"{var_name}.{subsequent.attr}",
                            )

        self.generic_visit(node)

    # -- Ternary: x if x else default --

    def visit_IfExp(self, node: ast.IfExp) -> None:
        test = node.test
        var_name = _extract_var_name(test)
        if var_name is not None:
            # x if x else default -> check for None
            body_var = _extract_var_name(node.body)
            if body_var == var_name:
                self._add_guard(
                    var_name, False, node,
                    polarity=True,
                    kind=NoneCheckKind.TERNARY_DEFAULT,
                    default_value=_expr_to_str(node.orelse),
                )
                self._add_guard(
                    var_name, True, node.orelse,
                    polarity=True,
                    kind=NoneCheckKind.TERNARY_DEFAULT,
                    default_value=_expr_to_str(node.orelse),
                )
            else:
                # General ternary with a None check in the test
                self._extract_none_from_test(test, node, polarity=True)
                self._extract_none_from_test(test, node, polarity=False)
        else:
            self._extract_none_from_test(test, node, polarity=True)
            self._extract_none_from_test(test, node, polarity=False)
        self.generic_visit(node)

    # -- Core None-check extraction from tests --

    def _extract_none_from_test(
        self,
        test: ast.expr,
        parent_node: ast.AST,
        *,
        polarity: bool = True,
    ) -> None:
        """Extract None-check facts from a test expression.

        Handles:
        - ``x is None``, ``x is not None``
        - ``not x`` (implies falsiness)
        - bare ``x`` (truthiness implies not None)
        - ``x == None``, ``x != None``
        - and/or with None checks
        """
        # not <expr>
        if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
            self._extract_none_from_test(
                test.operand, parent_node, polarity=not polarity,
            )
            return

        # BoolOp
        if isinstance(test, ast.BoolOp):
            if isinstance(test.op, ast.And):
                for val in test.values:
                    self._extract_none_from_test(val, parent_node, polarity=polarity)
            elif isinstance(test.op, ast.Or):
                for val in test.values:
                    self._extract_none_from_test(val, parent_node, polarity=polarity)
            return

        # Compare: x is None, x is not None, x == None, x != None
        if isinstance(test, ast.Compare):
            self._extract_none_from_compare(test, parent_node, polarity=polarity)
            return

        # Bare name: truthiness test
        if isinstance(test, ast.Name):
            if polarity:
                # if x: -> x is truthy -> not None
                self._add_guard(
                    test.id, False, parent_node,
                    polarity=True,
                    kind=NoneCheckKind.TRUTHINESS,
                )
            else:
                # else branch: x is falsy -> possibly None
                self._add_guard(
                    test.id, True, parent_node,
                    polarity=False,
                    kind=NoneCheckKind.FALSINESS,
                )
            return

        # Attribute: obj.attr used as truthiness
        if isinstance(test, ast.Attribute):
            var_name = _extract_var_name(test)
            if var_name is not None:
                if polarity:
                    self._add_guard(
                        var_name, False, parent_node,
                        polarity=True,
                        kind=NoneCheckKind.TRUTHINESS,
                    )
                else:
                    self._add_guard(
                        var_name, True, parent_node,
                        polarity=False,
                        kind=NoneCheckKind.FALSINESS,
                    )
            return

        # NamedExpr (walrus): (x := expr) used as truthiness test
        if isinstance(test, ast.NamedExpr):
            var_name = test.target.id
            if polarity:
                self._add_guard(
                    var_name, False, parent_node,
                    polarity=True,
                    kind=NoneCheckKind.WALRUS_NONE_CHECK,
                )
            else:
                self._add_guard(
                    var_name, True, parent_node,
                    polarity=False,
                    kind=NoneCheckKind.WALRUS_NONE_CHECK,
                )
            return

    def _extract_none_from_compare(
        self,
        compare: ast.Compare,
        parent_node: ast.AST,
        *,
        polarity: bool = True,
    ) -> None:
        """Extract None checks from comparison operators."""
        comparators = [compare.left] + compare.comparators
        ops = compare.ops

        for i, op in enumerate(ops):
            left = comparators[i]
            right = comparators[i + 1]

            # x is None
            if isinstance(op, ast.Is):
                if _is_none_constant(right):
                    var_name = _extract_var_name(left)
                    if var_name is not None:
                        self._add_guard(
                            var_name,
                            is_none_check=polarity,
                            node=parent_node,
                            polarity=polarity,
                            kind=NoneCheckKind.IS_NONE if polarity else NoneCheckKind.IS_NOT_NONE,
                        )
                elif _is_none_constant(left):
                    var_name = _extract_var_name(right)
                    if var_name is not None:
                        self._add_guard(
                            var_name,
                            is_none_check=polarity,
                            node=parent_node,
                            polarity=polarity,
                            kind=NoneCheckKind.IS_NONE if polarity else NoneCheckKind.IS_NOT_NONE,
                        )

            # x is not None
            elif isinstance(op, ast.IsNot):
                if _is_none_constant(right):
                    var_name = _extract_var_name(left)
                    if var_name is not None:
                        self._add_guard(
                            var_name,
                            is_none_check=not polarity,
                            node=parent_node,
                            polarity=polarity,
                            kind=NoneCheckKind.IS_NOT_NONE if polarity else NoneCheckKind.IS_NONE,
                        )
                elif _is_none_constant(left):
                    var_name = _extract_var_name(right)
                    if var_name is not None:
                        self._add_guard(
                            var_name,
                            is_none_check=not polarity,
                            node=parent_node,
                            polarity=polarity,
                            kind=NoneCheckKind.IS_NOT_NONE if polarity else NoneCheckKind.IS_NONE,
                        )

            # x == None (less idiomatic but seen in practice)
            elif isinstance(op, ast.Eq):
                if _is_none_constant(right):
                    var_name = _extract_var_name(left)
                    if var_name is not None:
                        self._add_guard(
                            var_name,
                            is_none_check=polarity,
                            node=parent_node,
                            polarity=polarity,
                            kind=NoneCheckKind.NONE_COMPARISON,
                        )
                elif _is_none_constant(left):
                    var_name = _extract_var_name(right)
                    if var_name is not None:
                        self._add_guard(
                            var_name,
                            is_none_check=polarity,
                            node=parent_node,
                            polarity=polarity,
                            kind=NoneCheckKind.NONE_COMPARISON,
                        )

            # x != None
            elif isinstance(op, ast.NotEq):
                if _is_none_constant(right):
                    var_name = _extract_var_name(left)
                    if var_name is not None:
                        self._add_guard(
                            var_name,
                            is_none_check=not polarity,
                            node=parent_node,
                            polarity=polarity,
                            kind=NoneCheckKind.NONE_COMPARISON,
                        )
                elif _is_none_constant(left):
                    var_name = _extract_var_name(right)
                    if var_name is not None:
                        self._add_guard(
                            var_name,
                            is_none_check=not polarity,
                            node=parent_node,
                            polarity=polarity,
                            kind=NoneCheckKind.NONE_COMPARISON,
                        )


# ===================================================================
#  Convenience function
# ===================================================================

def harvest_none_guards(
    ast_tree: ast.AST,
    *,
    file: str = "<unknown>",
) -> List[NoneGuard]:
    """Extract all None-check patterns from a Python AST.

    Args:
        ast_tree: The parsed AST (typically from ``ast.parse``).
        file: Source file name for provenance.

    Returns:
        A list of ``NoneGuard`` facts.
    """
    harvester = NoneGuardHarvester(file=file)
    harvester.visit(ast_tree)
    return harvester.guards


# ===================================================================
#  Filtering utilities
# ===================================================================

def filter_is_none(guards: List[NoneGuard]) -> List[NoneGuard]:
    """Return guards where the variable IS None."""
    return [g for g in guards if g.is_none_check]


def filter_is_not_none(guards: List[NoneGuard]) -> List[NoneGuard]:
    """Return guards where the variable is NOT None."""
    return [g for g in guards if not g.is_none_check]


def filter_by_variable(
    guards: List[NoneGuard],
    variable: str,
) -> List[NoneGuard]:
    """Return guards for a specific variable."""
    return [g for g in guards if g.variable == variable]


def filter_by_kind(
    guards: List[NoneGuard],
    kind: NoneCheckKind,
) -> List[NoneGuard]:
    """Return guards of a specific check kind."""
    return [g for g in guards if g.none_check_kind == kind]


def has_none_guard(
    guards: List[NoneGuard],
    variable: str,
) -> bool:
    """Return ``True`` if there is any None guard for the variable."""
    return any(g.variable == variable for g in guards)


def collect_guarded_variables(
    guards: List[NoneGuard],
) -> FrozenSet[str]:
    """Return the set of all variables that have None guards."""
    return frozenset(g.variable for g in guards)
