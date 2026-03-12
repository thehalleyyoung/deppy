"""Type guard harvester -- isinstance/issubclass/hasattr/callable narrowing.

Walks a Python AST and extracts type narrowing facts from type-guard
patterns: ``isinstance(x, T)``, ``issubclass(C, T)``, ``hasattr(x, attr)``,
and ``callable(x)``.  Each discovered narrowing is returned as a frozen
``TypeNarrowingFact`` dataclass.
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
from deppy.predicates.nullability import IsInstance, IsNotInstance
from deppy.predicates.heap import HasField, ProtocolConformance
from deppy.static_analysis.observation_sites import SourceSpan


# ===================================================================
#  Narrowing kind
# ===================================================================

class NarrowingKind(enum.Enum):
    """What kind of type guard produced this narrowing."""
    ISINSTANCE = "isinstance"
    ISSUBCLASS = "issubclass"
    HASATTR = "hasattr"
    CALLABLE = "callable"
    TYPE_GUARD_RETURN = "type_guard_return"
    TYPEIS_RETURN = "typeis_return"
    CLASS_PATTERN = "class_pattern"
    PROTOCOL_CHECK = "protocol_check"


# ===================================================================
#  TypeNarrowingFact dataclass
# ===================================================================

@dataclass(frozen=True)
class TypeNarrowingFact:
    """A type narrowing fact extracted from the AST.

    Attributes:
        variable: The variable being narrowed.
        narrowed_type: The type the variable is narrowed to (as string).
        original_type: The original (wider) type, if known (as string).
        polarity: ``True`` when the guard holds, ``False`` when negated.
        narrowing_kind: What syntactic pattern produced this narrowing.
        predicate: The predicate representing the narrowing condition.
        source_span: Location in source code.
        trust_level: Provenance trust level.
        is_negated: Whether this narrowing comes from a negated context.
        is_union_type: Whether the narrowed type is a union of types.
        union_members: Individual type names when narrowing to a union.
        checked_attribute: For hasattr checks, the attribute name checked.
        is_in_elif: Whether this narrowing occurs in an elif branch.
        enclosing_function: Name of the enclosing function.
    """
    variable: str
    narrowed_type: str
    original_type: Optional[str] = None
    polarity: bool = True
    narrowing_kind: NarrowingKind = NarrowingKind.ISINSTANCE
    predicate: Optional[Predicate] = None
    source_span: Optional[SourceSpan] = None
    trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO
    is_negated: bool = False
    is_union_type: bool = False
    union_members: Tuple[str, ...] = ()
    checked_attribute: Optional[str] = None
    is_in_elif: bool = False
    enclosing_function: Optional[str] = None


# ===================================================================
#  Helper: extract type names from AST
# ===================================================================

def _extract_type_name_from_ast(node: ast.expr) -> Optional[str]:
    """Extract a type name string from an AST expression."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = _extract_type_name_from_ast(node.value)
        if base is not None:
            return f"{base}.{node.attr}"
        return node.attr
    if isinstance(node, ast.Constant) and isinstance(node.value, type):
        return node.value.__name__
    return None


def _extract_union_members(node: ast.expr) -> Tuple[str, ...]:
    """Extract tuple of type names from a tuple expression in isinstance."""
    if isinstance(node, ast.Tuple):
        members: List[str] = []
        for elt in node.elts:
            name = _extract_type_name_from_ast(elt)
            if name is not None:
                members.append(name)
        return tuple(members)
    name = _extract_type_name_from_ast(node)
    if name is not None:
        return (name,)
    return ()


def _extract_variable_name(node: ast.expr) -> Optional[str]:
    """Extract a simple variable name from an expression."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = _extract_variable_name(node.value)
        if base is not None:
            return f"{base}.{node.attr}"
    return None


def _source_loc_from_ast(
    node: ast.AST,
    file: str = "<unknown>",
) -> SourceLocation:
    """Build a SourceLocation from an AST node."""
    return SourceLocation(
        file=file,
        line=getattr(node, "lineno", 0),
        col=getattr(node, "col_offset", 0),
        end_line=getattr(node, "end_lineno", None),
        end_col=getattr(node, "end_col_offset", None),
    )


# ===================================================================
#  TypeGuardHarvester visitor
# ===================================================================

class TypeGuardHarvester(ast.NodeVisitor):
    """AST visitor that extracts type narrowing facts.

    Handles:
    - ``isinstance(x, T)`` in if-tests, asserts, while-tests
    - ``issubclass(C, T)`` in the same contexts
    - ``hasattr(x, "attr")``
    - ``callable(x)``
    - Negated forms: ``not isinstance(...)``
    - Chained forms: ``isinstance(x, (int, str))``
    - TypeGuard / TypeIs return annotations (Python 3.10+)
    - Match/case class patterns

    Usage::

        harvester = TypeGuardHarvester(file="example.py")
        harvester.visit(tree)
        facts = harvester.facts
    """

    def __init__(self, file: str = "<unknown>") -> None:
        self._file = file
        self._facts: List[TypeNarrowingFact] = []
        self._function_stack: List[str] = []
        self._in_elif: bool = False

    @property
    def facts(self) -> List[TypeNarrowingFact]:
        """All collected type narrowing facts."""
        return list(self._facts)

    @property
    def _current_function(self) -> Optional[str]:
        return self._function_stack[-1] if self._function_stack else None

    def _span(self, node: ast.AST) -> SourceSpan:
        return SourceSpan.from_ast(node, self._file)

    def _add_fact(
        self,
        variable: str,
        narrowed_type: str,
        node: ast.AST,
        *,
        polarity: bool = True,
        narrowing_kind: NarrowingKind = NarrowingKind.ISINSTANCE,
        predicate: Optional[Predicate] = None,
        is_negated: bool = False,
        union_members: Tuple[str, ...] = (),
        checked_attribute: Optional[str] = None,
    ) -> None:
        """Record a type narrowing fact."""
        is_union = len(union_members) > 1
        self._facts.append(TypeNarrowingFact(
            variable=variable,
            narrowed_type=narrowed_type,
            polarity=polarity,
            narrowing_kind=narrowing_kind,
            predicate=predicate,
            source_span=self._span(node),
            trust_level=TrustLevel.TRUSTED_AUTO,
            is_negated=is_negated,
            is_union_type=is_union,
            union_members=union_members,
            checked_attribute=checked_attribute,
            is_in_elif=self._in_elif,
            enclosing_function=self._current_function,
        ))

    # -- Scope tracking --

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._function_stack.append(node.name)
        # Check for TypeGuard / TypeIs return annotations
        self._check_type_guard_return(node)
        self.generic_visit(node)
        self._function_stack.pop()

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._function_stack.append(node.name)
        self._check_type_guard_return(node)
        self.generic_visit(node)
        self._function_stack.pop()

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._function_stack.append(node.name)
        self.generic_visit(node)
        self._function_stack.pop()

    def _check_type_guard_return(
        self,
        node: Union[ast.FunctionDef, ast.AsyncFunctionDef],
    ) -> None:
        """Check if the function has a TypeGuard or TypeIs return annotation."""
        ret = node.returns
        if ret is None:
            return
        # TypeGuard[T] or TypeIs[T]
        if isinstance(ret, ast.Subscript):
            base = ret.value
            if isinstance(base, ast.Name) and base.id in ("TypeGuard", "TypeIs"):
                type_name = _extract_type_name_from_ast(ret.slice)
                if type_name is not None:
                    kind = (
                        NarrowingKind.TYPE_GUARD_RETURN
                        if base.id == "TypeGuard"
                        else NarrowingKind.TYPEIS_RETURN
                    )
                    # The first parameter is the narrowed variable
                    if node.args.args:
                        param = node.args.args[0]
                        var_name = param.arg
                        self._add_fact(
                            var_name, type_name, node,
                            narrowing_kind=kind,
                        )
            # Also handle typing.TypeGuard / typing.TypeIs
            if isinstance(base, ast.Attribute) and base.attr in ("TypeGuard", "TypeIs"):
                type_name = _extract_type_name_from_ast(ret.slice)
                if type_name is not None:
                    kind = (
                        NarrowingKind.TYPE_GUARD_RETURN
                        if base.attr == "TypeGuard"
                        else NarrowingKind.TYPEIS_RETURN
                    )
                    if node.args.args:
                        param = node.args.args[0]
                        self._add_fact(
                            param.arg, type_name, node,
                            narrowing_kind=kind,
                        )

    # -- If/elif --

    def visit_If(self, node: ast.If) -> None:
        self._extract_from_test(node.test, node, polarity=True)
        self._extract_from_test(node.test, node, polarity=False)

        for child in node.body:
            self.visit(child)

        # Handle elif
        for else_node in node.orelse:
            if isinstance(else_node, ast.If):
                old_elif = self._in_elif
                self._in_elif = True
                self._extract_from_test(else_node.test, else_node, polarity=True)
                self._extract_from_test(else_node.test, else_node, polarity=False)
                for child in else_node.body:
                    self.visit(child)
                for child in else_node.orelse:
                    self.visit(child)
                self._in_elif = old_elif
            else:
                self.visit(else_node)

    # -- Assert --

    def visit_Assert(self, node: ast.Assert) -> None:
        self._extract_from_test(node.test, node, polarity=True)
        self.generic_visit(node)

    # -- While --

    def visit_While(self, node: ast.While) -> None:
        self._extract_from_test(node.test, node, polarity=True)
        self.generic_visit(node)

    # -- Match/case patterns --

    def visit_Match(self, node: ast.AST) -> None:
        subject = getattr(node, "subject", None)
        cases = getattr(node, "cases", [])
        if subject is None:
            self.generic_visit(node)
            return

        var_name = _extract_variable_name(subject)
        if var_name is None:
            self.generic_visit(node)
            return

        for case in cases:
            pattern = getattr(case, "pattern", None)
            if pattern is not None:
                self._extract_from_pattern(var_name, pattern)
            # Also check guard expressions
            guard = getattr(case, "guard", None)
            if guard is not None:
                self._extract_from_test(guard, guard, polarity=True)

        self.generic_visit(node)

    def _extract_from_pattern(
        self,
        variable: str,
        pattern: ast.AST,
    ) -> None:
        """Extract narrowing from match/case patterns."""
        # MatchClass: case ClassName(...):
        cls_node = getattr(pattern, "cls", None)
        if cls_node is not None:
            type_name = _extract_type_name_from_ast(cls_node)
            if type_name is not None:
                self._add_fact(
                    variable, type_name, pattern,
                    narrowing_kind=NarrowingKind.CLASS_PATTERN,
                )

    # -- Core extraction logic --

    def _extract_from_test(
        self,
        test: ast.expr,
        parent_node: ast.AST,
        *,
        polarity: bool = True,
    ) -> None:
        """Extract type narrowing facts from a test expression.

        Handles isinstance, issubclass, hasattr, callable, and their
        negations. Recurses through BoolOp (and/or) and UnaryOp (not).
        """
        # not <expr>
        if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
            self._extract_from_test(
                test.operand, parent_node, polarity=not polarity,
            )
            return

        # BoolOp: and / or
        if isinstance(test, ast.BoolOp):
            if isinstance(test.op, ast.And):
                # In the true branch, all operands hold
                if polarity:
                    for val in test.values:
                        self._extract_from_test(val, parent_node, polarity=True)
                else:
                    # In the false branch, at least one fails -- extract each
                    for val in test.values:
                        self._extract_from_test(val, parent_node, polarity=False)
            elif isinstance(test.op, ast.Or):
                if not polarity:
                    # All are false
                    for val in test.values:
                        self._extract_from_test(val, parent_node, polarity=False)
                else:
                    for val in test.values:
                        self._extract_from_test(val, parent_node, polarity=True)
            return

        # isinstance(x, T)
        if isinstance(test, ast.Call) and isinstance(test.func, ast.Name):
            self._extract_from_call(test, parent_node, polarity=polarity)
            return

        # Comparison with isinstance in a chain
        if isinstance(test, ast.Compare):
            # 'is None' / 'is not None' can imply type narrowing
            self._extract_from_compare(test, parent_node, polarity=polarity)
            return

    def _extract_from_call(
        self,
        call: ast.Call,
        parent_node: ast.AST,
        *,
        polarity: bool = True,
    ) -> None:
        """Extract narrowing from isinstance/issubclass/hasattr/callable calls."""
        if not isinstance(call.func, ast.Name):
            return
        fname = call.func.id
        src = _source_loc_from_ast(call, self._file)

        # isinstance(x, T)
        if fname == "isinstance" and len(call.args) >= 2:
            var_name = _extract_variable_name(call.args[0])
            if var_name is None:
                return
            members = _extract_union_members(call.args[1])
            if not members:
                return
            if len(members) == 1:
                type_str = members[0]
            else:
                type_str = "Union[" + ", ".join(members) + "]"

            var_term = Var(var_name)
            if polarity:
                pred = IsInstance(term=var_term, type_name=type_str, source_location=src)
            else:
                pred = IsNotInstance(term=var_term, type_name=type_str, source_location=src)

            self._add_fact(
                var_name, type_str, call,
                polarity=polarity,
                narrowing_kind=NarrowingKind.ISINSTANCE,
                predicate=pred,
                is_negated=not polarity,
                union_members=members,
            )

        # issubclass(C, T)
        elif fname == "issubclass" and len(call.args) >= 2:
            var_name = _extract_variable_name(call.args[0])
            if var_name is None:
                return
            members = _extract_union_members(call.args[1])
            if not members:
                return
            type_str = members[0] if len(members) == 1 else "Union[" + ", ".join(members) + "]"

            var_term = Var(var_name)
            pred: Predicate
            if polarity:
                pred = IsInstance(term=var_term, type_name=type_str, source_location=src)
            else:
                pred = IsNotInstance(term=var_term, type_name=type_str, source_location=src)

            self._add_fact(
                var_name, type_str, call,
                polarity=polarity,
                narrowing_kind=NarrowingKind.ISSUBCLASS,
                predicate=pred,
                is_negated=not polarity,
                union_members=members,
            )

        # hasattr(x, "attr")
        elif fname == "hasattr" and len(call.args) >= 2:
            var_name = _extract_variable_name(call.args[0])
            if var_name is None:
                return
            if not (isinstance(call.args[1], ast.Constant) and isinstance(call.args[1].value, str)):
                return
            attr_name = call.args[1].value
            obj_term = Var(var_name)
            pred = HasField(
                obj=obj_term, field_name=attr_name, source_location=src,
            )
            narrowed = f"HasAttr[{attr_name}]"
            self._add_fact(
                var_name, narrowed, call,
                polarity=polarity,
                narrowing_kind=NarrowingKind.HASATTR,
                predicate=pred,
                is_negated=not polarity,
                checked_attribute=attr_name,
            )

        # callable(x)
        elif fname == "callable" and len(call.args) >= 1:
            var_name = _extract_variable_name(call.args[0])
            if var_name is None:
                return
            obj_term = Var(var_name)
            pred = ProtocolConformance(
                obj=obj_term,
                protocol_name="Callable",
                required_methods=["__call__"],
                source_location=src,
            )
            self._add_fact(
                var_name, "Callable", call,
                polarity=polarity,
                narrowing_kind=NarrowingKind.CALLABLE,
                predicate=pred,
                is_negated=not polarity,
            )

    def _extract_from_compare(
        self,
        compare: ast.Compare,
        parent_node: ast.AST,
        *,
        polarity: bool = True,
    ) -> None:
        """Extract type narrowing from comparison operators.

        Specifically handles ``x is None`` and ``x is not None`` patterns,
        and ``type(x) is T`` patterns.
        """
        comparators = [compare.left] + compare.comparators
        ops = compare.ops

        for i, op in enumerate(ops):
            left = comparators[i]
            right = comparators[i + 1]

            # type(x) is T / type(x) is not T
            if isinstance(left, ast.Call) and isinstance(left.func, ast.Name) and left.func.id == "type":
                if len(left.args) >= 1:
                    var_name = _extract_variable_name(left.args[0])
                    type_name = _extract_type_name_from_ast(right)
                    if var_name is not None and type_name is not None:
                        if isinstance(op, ast.Is):
                            effective_polarity = polarity
                        elif isinstance(op, ast.IsNot):
                            effective_polarity = not polarity
                        elif isinstance(op, ast.Eq):
                            effective_polarity = polarity
                        elif isinstance(op, ast.NotEq):
                            effective_polarity = not polarity
                        else:
                            continue
                        src = _source_loc_from_ast(compare, self._file)
                        var_term = Var(var_name)
                        if effective_polarity:
                            pred = IsInstance(term=var_term, type_name=type_name, source_location=src)
                        else:
                            pred = IsNotInstance(term=var_term, type_name=type_name, source_location=src)
                        self._add_fact(
                            var_name, type_name, compare,
                            polarity=effective_polarity,
                            narrowing_kind=NarrowingKind.ISINSTANCE,
                            predicate=pred,
                            is_negated=not effective_polarity,
                        )


# ===================================================================
#  Convenience function
# ===================================================================

def harvest_type_guards(
    ast_tree: ast.AST,
    *,
    file: str = "<unknown>",
) -> List[TypeNarrowingFact]:
    """Extract all type guard narrowing facts from a Python AST.

    Args:
        ast_tree: The parsed AST (typically from ``ast.parse``).
        file: Source file name for provenance.

    Returns:
        A list of ``TypeNarrowingFact`` objects.
    """
    harvester = TypeGuardHarvester(file=file)
    harvester.visit(ast_tree)
    return harvester.facts


# ===================================================================
#  Filtering utilities
# ===================================================================

def filter_by_variable(
    facts: List[TypeNarrowingFact],
    variable: str,
) -> List[TypeNarrowingFact]:
    """Return facts narrowing a specific variable."""
    return [f for f in facts if f.variable == variable]


def filter_by_kind(
    facts: List[TypeNarrowingFact],
    kind: NarrowingKind,
) -> List[TypeNarrowingFact]:
    """Return facts of a specific narrowing kind."""
    return [f for f in facts if f.narrowing_kind == kind]


def positive_narrowings(
    facts: List[TypeNarrowingFact],
) -> List[TypeNarrowingFact]:
    """Return only narrowings from the true (positive) polarity."""
    return [f for f in facts if f.polarity and not f.is_negated]


def negative_narrowings(
    facts: List[TypeNarrowingFact],
) -> List[TypeNarrowingFact]:
    """Return narrowings from the false (negated) branch."""
    return [f for f in facts if not f.polarity or f.is_negated]


def narrowings_for_function(
    facts: List[TypeNarrowingFact],
    function_name: str,
) -> List[TypeNarrowingFact]:
    """Return facts from a specific function."""
    return [f for f in facts if f.enclosing_function == function_name]


def collect_narrowed_types(
    facts: List[TypeNarrowingFact],
    variable: str,
) -> List[str]:
    """Collect all narrowed type names for a variable."""
    return [
        f.narrowed_type for f in facts
        if f.variable == variable and f.polarity
    ]
