"""Guard harvester -- extract guard predicates from if/assert/try/walrus.

Walks a Python AST and produces ``HarvestedGuard`` facts for every
control-flow guard encountered: if/elif chains, assert statements,
walrus operators ``:=`` inside ``if`` tests, and try/except guards.

Each guard is represented as a frozen dataclass carrying the extracted
predicate, source span, polarity (true/false branch), narrowed variable
set, and a trust level indicating provenance.
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
    Attr,
    BinOp,
    BoolLit,
    Call,
    FloatLit,
    IntLit,
    NoneLit,
    Predicate,
    SourceLocation,
    StrLit,
    Term,
    Var,
)
from deppy.predicates.arithmetic import Comparison
from deppy.predicates.boolean import And, Not, Or
from deppy.predicates.nullability import (
    Falsy,
    IsInstance,
    IsNone,
    IsNotNone,
    Truthy,
)
from deppy.static_analysis.observation_sites import SourceSpan


# ===================================================================
#  Guard kind classification
# ===================================================================

class GuardKind(enum.Enum):
    """Classification of the syntactic origin of a guard."""
    IF_TEST = "if_test"
    ELIF_TEST = "elif_test"
    ASSERT_TEST = "assert_test"
    WALRUS_IF = "walrus_if"
    TRY_EXCEPT = "try_except"
    WHILE_TEST = "while_test"
    TERNARY = "ternary"
    BOOLEAN_OP = "boolean_op"
    COMPREHENSION_IF = "comprehension_if"
    MATCH_CASE = "match_case"


# ===================================================================
#  HarvestedGuard dataclass
# ===================================================================

@dataclass(frozen=True)
class HarvestedGuard:
    """A guard predicate extracted from the AST.

    Attributes:
        predicate: The logical predicate representing the guard condition.
        source_span: The location in source code where the guard was found.
        polarity: ``True`` for the true-branch, ``False`` for the false-branch.
        narrowed_variables: Variables whose types are narrowed by this guard.
        trust_level: Provenance indicator for how the guard was established.
        guard_kind: Syntactic category of the guard.
        parent_function: Name of the enclosing function, if any.
        walrus_target: If the guard uses ``:=``, the name being bound.
        nesting_depth: How deeply nested this guard is within other guards.
        associated_else: Whether there is an else branch paired with this guard.
    """
    predicate: Predicate
    source_span: SourceSpan
    polarity: bool = True
    narrowed_variables: FrozenSet[str] = field(default_factory=frozenset)
    trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO
    guard_kind: GuardKind = GuardKind.IF_TEST
    parent_function: Optional[str] = None
    walrus_target: Optional[str] = None
    nesting_depth: int = 0
    associated_else: bool = False


# ===================================================================
#  AST-to-Term / AST-to-Predicate helpers
# ===================================================================

_AST_CMP_MAP: Dict[type, str] = {
    ast.Lt: "<",
    ast.LtE: "<=",
    ast.Gt: ">",
    ast.GtE: ">=",
    ast.Eq: "==",
    ast.NotEq: "!=",
}

_AST_BINOP_MAP: Dict[type, str] = {
    ast.Add: "+",
    ast.Sub: "-",
    ast.Mult: "*",
    ast.FloorDiv: "//",
    ast.Mod: "%",
    ast.Pow: "**",
    ast.BitAnd: "&",
    ast.BitOr: "|",
    ast.BitXor: "^",
    ast.LShift: "<<",
    ast.RShift: ">>",
}

_AST_UNARYOP_MAP: Dict[type, str] = {
    ast.USub: "-",
    ast.UAdd: "+",
    ast.Invert: "~",
}


def _ast_to_term(node: ast.expr) -> Optional[Term]:
    """Best-effort conversion of a Python AST expression to a predicate Term."""
    if isinstance(node, ast.Name):
        return Var(node.id)

    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool):
            return BoolLit(node.value)
        if isinstance(node.value, int):
            return IntLit(node.value)
        if isinstance(node.value, float):
            return FloatLit(node.value)
        if isinstance(node.value, str):
            return StrLit(node.value)
        if node.value is None:
            return NoneLit()
        return None

    if isinstance(node, ast.Attribute):
        obj = _ast_to_term(node.value)
        if obj is not None:
            return Attr(obj=obj, attr=node.attr)
        return None

    if isinstance(node, ast.Subscript):
        from deppy.predicates.base import Index
        obj = _ast_to_term(node.value)
        idx = _ast_to_term(node.slice) if not isinstance(node.slice, ast.Slice) else None
        if obj is not None and idx is not None:
            return Index(obj=obj, idx=idx)
        return None

    if isinstance(node, ast.BinOp):
        op_str = _AST_BINOP_MAP.get(type(node.op))
        if op_str is None:
            return None
        left = _ast_to_term(node.left)
        right = _ast_to_term(node.right)
        if left is not None and right is not None:
            return BinOp(op=op_str, left=left, right=right)
        return None

    if isinstance(node, ast.UnaryOp):
        op_str = _AST_UNARYOP_MAP.get(type(node.op))
        if op_str is None:
            return None
        from deppy.predicates.base import UnaryOp
        operand = _ast_to_term(node.operand)
        if operand is not None:
            return UnaryOp(op=op_str, operand=operand)
        return None

    if isinstance(node, ast.Call):
        func_name = _extract_call_name(node)
        if func_name is not None:
            args: List[Term] = []
            for arg in node.args:
                t = _ast_to_term(arg)
                if t is None:
                    return None
                args.append(t)
            return Call(func=func_name, args=args)
        return None

    if isinstance(node, ast.Tuple):
        from deppy.predicates.base import TupleLit
        elts: List[Term] = []
        for elt in node.elts:
            t = _ast_to_term(elt)
            if t is None:
                return None
            elts.append(t)
        return TupleLit(elts)

    if isinstance(node, ast.NamedExpr):
        # walrus: (target := value) -- treat the value as the term
        return _ast_to_term(node.value)

    return None


def _extract_call_name(node: ast.Call) -> Optional[str]:
    """Extract a simple function name from a Call node."""
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        obj = _ast_to_term(node.func.value)
        if obj is not None:
            return f"{obj.pretty()}.{node.func.attr}"
        return node.func.attr
    return None


def _extract_variables(node: ast.expr) -> FrozenSet[str]:
    """Extract all variable names referenced in an AST expression."""
    names: Set[str] = set()
    for child in ast.walk(node):
        if isinstance(child, ast.Name):
            names.add(child.id)
    return frozenset(names)


def _source_loc(node: ast.AST, file: str = "<unknown>") -> SourceLocation:
    """Build a SourceLocation from an AST node."""
    return SourceLocation(
        file=file,
        line=getattr(node, "lineno", 0),
        col=getattr(node, "col_offset", 0),
        end_line=getattr(node, "end_lineno", None),
        end_col=getattr(node, "end_col_offset", None),
    )


# ===================================================================
#  AST test -> Predicate conversion
# ===================================================================

def _ast_test_to_predicate(
    node: ast.expr,
    file: str = "<unknown>",
) -> Optional[Predicate]:
    """Convert an AST test expression to a Predicate.

    Handles:
    - Comparisons: x > 0, x == y, etc.
    - Boolean ops: and, or, not
    - isinstance / issubclass / hasattr / callable calls
    - is None / is not None
    - Truthiness tests (bare name)
    - Walrus operator in tests
    """
    src = _source_loc(node, file)

    # -- Compare: x < y, x == 0, etc. and chained 0 < x < n
    if isinstance(node, ast.Compare):
        return _convert_compare(node, file)

    # -- BoolOp: x and y, x or y
    if isinstance(node, ast.BoolOp):
        parts: List[Predicate] = []
        for val in node.values:
            p = _ast_test_to_predicate(val, file)
            if p is not None:
                parts.append(p)
        if not parts:
            return None
        if isinstance(node.op, ast.And):
            return And(parts, source_location=src) if len(parts) > 1 else parts[0]
        if isinstance(node.op, ast.Or):
            return Or(parts, source_location=src) if len(parts) > 1 else parts[0]
        return None

    # -- UnaryOp: not x
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        inner = _ast_test_to_predicate(node.operand, file)
        if inner is not None:
            return Not(inner, source_location=src)
        return None

    # -- Call: isinstance, issubclass, hasattr, callable, len
    if isinstance(node, ast.Call):
        return _convert_call_predicate(node, file)

    # -- Bare name: truthiness check
    if isinstance(node, ast.Name):
        return Truthy(term=Var(node.id), source_location=src)

    # -- Attribute: obj.attr used as a truthy test
    if isinstance(node, ast.Attribute):
        obj_term = _ast_to_term(node)
        if obj_term is not None:
            return Truthy(term=obj_term, source_location=src)
        return None

    # -- NamedExpr (walrus): (x := expr) used as a test
    if isinstance(node, ast.NamedExpr):
        return Truthy(term=Var(node.target.id), source_location=src)

    # -- Constant used as test
    if isinstance(node, ast.Constant):
        term = _ast_to_term(node)
        if term is not None:
            return Truthy(term=term, source_location=src)
        return None

    # -- Fallback: try to convert to a term and wrap in Truthy
    term = _ast_to_term(node)
    if term is not None:
        return Truthy(term=term, source_location=src)

    return None


def _convert_compare(
    node: ast.Compare,
    file: str = "<unknown>",
) -> Optional[Predicate]:
    """Convert a Compare node, handling chained comparisons.

    ``0 < x < n`` becomes ``And(Comparison('<', 0, x), Comparison('<', x, n))``.
    ``x is None`` and ``x is not None`` produce IsNone / IsNotNone.
    """
    src = _source_loc(node, file)
    comparators = [node.left] + node.comparators
    ops = node.ops
    preds: List[Predicate] = []

    for i, op in enumerate(ops):
        left_ast = comparators[i]
        right_ast = comparators[i + 1]

        # is None / is not None
        if isinstance(op, ast.Is):
            if isinstance(right_ast, ast.Constant) and right_ast.value is None:
                term = _ast_to_term(left_ast)
                if term is not None:
                    preds.append(IsNone(term=term, source_location=src))
                    continue
            elif isinstance(left_ast, ast.Constant) and left_ast.value is None:
                term = _ast_to_term(right_ast)
                if term is not None:
                    preds.append(IsNone(term=term, source_location=src))
                    continue
            # general 'is' -- fall through to truthiness
            left_t = _ast_to_term(left_ast)
            right_t = _ast_to_term(right_ast)
            if left_t is not None and right_t is not None:
                preds.append(Comparison(op="==", left=left_t, right=right_t, source_location=src))
            continue

        if isinstance(op, ast.IsNot):
            if isinstance(right_ast, ast.Constant) and right_ast.value is None:
                term = _ast_to_term(left_ast)
                if term is not None:
                    preds.append(IsNotNone(term=term, source_location=src))
                    continue
            elif isinstance(left_ast, ast.Constant) and left_ast.value is None:
                term = _ast_to_term(right_ast)
                if term is not None:
                    preds.append(IsNotNone(term=term, source_location=src))
                    continue
            left_t = _ast_to_term(left_ast)
            right_t = _ast_to_term(right_ast)
            if left_t is not None and right_t is not None:
                preds.append(Comparison(op="!=", left=left_t, right=right_t, source_location=src))
            continue

        # 'in' / 'not in' -- membership
        if isinstance(op, (ast.In, ast.NotIn)):
            from deppy.predicates.collection import Contains
            elem = _ast_to_term(left_ast)
            coll = _ast_to_term(right_ast)
            if elem is not None and coll is not None:
                pred = Contains(element=elem, collection=coll, source_location=src)
                if isinstance(op, ast.NotIn):
                    pred = Not(pred, source_location=src)
                preds.append(pred)
            continue

        # arithmetic comparisons
        op_str = _AST_CMP_MAP.get(type(op))
        if op_str is None:
            continue
        left_t = _ast_to_term(left_ast)
        right_t = _ast_to_term(right_ast)
        if left_t is not None and right_t is not None:
            preds.append(Comparison(op=op_str, left=left_t, right=right_t, source_location=src))

    if not preds:
        return None
    if len(preds) == 1:
        return preds[0]
    return And(preds, source_location=src)


def _convert_call_predicate(
    node: ast.Call,
    file: str = "<unknown>",
) -> Optional[Predicate]:
    """Convert a call used as a predicate: isinstance, hasattr, callable, len."""
    src = _source_loc(node, file)

    if isinstance(node.func, ast.Name):
        fname = node.func.id

        # isinstance(x, T)
        if fname == "isinstance" and len(node.args) >= 2:
            term = _ast_to_term(node.args[0])
            type_name = _extract_type_name(node.args[1])
            if term is not None and type_name is not None:
                return IsInstance(term=term, type_name=type_name, source_location=src)

        # issubclass(C, T)
        if fname == "issubclass" and len(node.args) >= 2:
            term = _ast_to_term(node.args[0])
            type_name = _extract_type_name(node.args[1])
            if term is not None and type_name is not None:
                return IsInstance(term=term, type_name=type_name, source_location=src)

        # hasattr(x, "attr")
        if fname == "hasattr" and len(node.args) >= 2:
            from deppy.predicates.heap import HasField
            obj_term = _ast_to_term(node.args[0])
            if obj_term is not None and isinstance(node.args[1], ast.Constant) and isinstance(node.args[1].value, str):
                return HasField(obj=obj_term, field_name=node.args[1].value, source_location=src)

        # callable(x)
        if fname == "callable" and len(node.args) >= 1:
            from deppy.predicates.heap import ProtocolConformance
            obj_term = _ast_to_term(node.args[0])
            if obj_term is not None:
                return ProtocolConformance(
                    obj=obj_term,
                    protocol_name="Callable",
                    required_methods=["__call__"],
                    source_location=src,
                )

        # len(x) used as truthiness: len(x) => NonEmpty
        if fname == "len" and len(node.args) >= 1:
            from deppy.predicates.collection import NonEmpty
            coll_term = _ast_to_term(node.args[0])
            if coll_term is not None:
                return NonEmpty(collection=coll_term, source_location=src)

        # bool(x)
        if fname == "bool" and len(node.args) >= 1:
            inner_term = _ast_to_term(node.args[0])
            if inner_term is not None:
                return Truthy(term=inner_term, source_location=src)

        # any(x), all(x) -- treat as truthiness of the iterable
        if fname in ("any", "all") and len(node.args) >= 1:
            inner_term = _ast_to_term(node.args[0])
            if inner_term is not None:
                return Truthy(term=Call(func=fname, args=[inner_term]), source_location=src)

    # fallback: treat the whole call as a truthy term
    term = _ast_to_term(node)
    if term is not None:
        return Truthy(term=term, source_location=src)
    return None


def _extract_type_name(node: ast.expr) -> Optional[str]:
    """Extract a type name string from an AST node used in isinstance/issubclass.

    Handles:
    - Simple names: ``int``, ``str``, ``MyClass``
    - Attribute access: ``module.Class``
    - Tuples of types: ``(int, str)`` -> ``Union[int, str]``
    """
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = _extract_type_name(node.value)
        if base is not None:
            return f"{base}.{node.attr}"
        return node.attr
    if isinstance(node, ast.Tuple):
        parts: List[str] = []
        for elt in node.elts:
            part = _extract_type_name(elt)
            if part is not None:
                parts.append(part)
        if parts:
            return "Union[" + ", ".join(parts) + "]"
    if isinstance(node, ast.Constant) and isinstance(node.value, type):
        return node.value.__name__
    return None


# ===================================================================
#  Walrus extraction helpers
# ===================================================================

def _extract_walrus_target(node: ast.expr) -> Optional[str]:
    """If the expression contains a walrus operator, return the target name."""
    if isinstance(node, ast.NamedExpr):
        return node.target.id
    for child in ast.walk(node):
        if isinstance(child, ast.NamedExpr):
            return child.target.id
    return None


def _has_walrus(node: ast.expr) -> bool:
    """Check whether an expression contains any walrus operator."""
    for child in ast.walk(node):
        if isinstance(child, ast.NamedExpr):
            return True
    return False


# ===================================================================
#  GuardHarvester visitor
# ===================================================================

class GuardHarvester(ast.NodeVisitor):
    """AST visitor that extracts guard predicates from Python source.

    Walks the AST top-down, collecting ``HarvestedGuard`` instances for
    every guard site: if/elif chains, assert statements, walrus operators
    in conditional contexts, try/except guards, while-loop tests, ternary
    expressions, and comprehension filters.

    Usage::

        harvester = GuardHarvester(file="example.py")
        harvester.visit(tree)
        guards = harvester.guards
    """

    def __init__(self, file: str = "<unknown>") -> None:
        self._file = file
        self._guards: List[HarvestedGuard] = []
        self._function_stack: List[str] = []
        self._nesting_depth: int = 0

    @property
    def guards(self) -> List[HarvestedGuard]:
        """All harvested guards collected so far."""
        return list(self._guards)

    @property
    def _current_function(self) -> Optional[str]:
        return self._function_stack[-1] if self._function_stack else None

    def _span(self, node: ast.AST) -> SourceSpan:
        return SourceSpan.from_ast(node, self._file)

    def _add_guard(
        self,
        predicate: Predicate,
        node: ast.AST,
        *,
        polarity: bool = True,
        guard_kind: GuardKind = GuardKind.IF_TEST,
        trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO,
        walrus_target: Optional[str] = None,
        associated_else: bool = False,
        extra_variables: FrozenSet[str] = frozenset(),
    ) -> None:
        """Record a harvested guard."""
        narrowed = frozenset(predicate.free_variables()) | extra_variables
        self._guards.append(HarvestedGuard(
            predicate=predicate,
            source_span=self._span(node),
            polarity=polarity,
            narrowed_variables=narrowed,
            trust_level=trust_level,
            guard_kind=guard_kind,
            parent_function=self._current_function,
            walrus_target=walrus_target,
            nesting_depth=self._nesting_depth,
            associated_else=associated_else,
        ))

    # -- Function / Class scope tracking --

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
        has_else = bool(node.orelse)
        # Determine if else is an elif
        has_elif = (
            has_else
            and len(node.orelse) == 1
            and isinstance(node.orelse[0], ast.If)
        )

        pred = _ast_test_to_predicate(node.test, self._file)
        walrus = _extract_walrus_target(node.test) if _has_walrus(node.test) else None
        extra_vars: FrozenSet[str] = frozenset()
        if walrus:
            extra_vars = frozenset({walrus})

        if pred is not None:
            # True branch
            self._add_guard(
                pred, node,
                polarity=True,
                guard_kind=GuardKind.IF_TEST,
                walrus_target=walrus,
                associated_else=has_else,
                extra_variables=extra_vars,
            )
            # False branch (negated)
            if has_else:
                neg = pred.negate()
                self._add_guard(
                    neg, node,
                    polarity=False,
                    guard_kind=GuardKind.IF_TEST,
                    walrus_target=walrus,
                    associated_else=True,
                    extra_variables=extra_vars,
                )

        # Recurse into body with increased depth
        self._nesting_depth += 1
        for child in node.body:
            self.visit(child)
        self._nesting_depth -= 1

        # Handle elif chains
        for else_node in node.orelse:
            if isinstance(else_node, ast.If):
                elif_pred = _ast_test_to_predicate(else_node.test, self._file)
                if elif_pred is not None:
                    elif_walrus = (
                        _extract_walrus_target(else_node.test)
                        if _has_walrus(else_node.test)
                        else None
                    )
                    elif_extra: FrozenSet[str] = frozenset()
                    if elif_walrus:
                        elif_extra = frozenset({elif_walrus})
                    self._add_guard(
                        elif_pred, else_node,
                        polarity=True,
                        guard_kind=GuardKind.ELIF_TEST,
                        walrus_target=elif_walrus,
                        associated_else=bool(else_node.orelse),
                        extra_variables=elif_extra,
                    )
                self._nesting_depth += 1
                for child in else_node.body:
                    self.visit(child)
                self._nesting_depth -= 1
                for child in else_node.orelse:
                    self.visit(child)
            else:
                self._nesting_depth += 1
                self.visit(else_node)
                self._nesting_depth -= 1

    # -- Assert statements --

    def visit_Assert(self, node: ast.Assert) -> None:
        pred = _ast_test_to_predicate(node.test, self._file)
        if pred is not None:
            extra_vars: FrozenSet[str] = frozenset()
            walrus = None
            if _has_walrus(node.test):
                walrus = _extract_walrus_target(node.test)
                if walrus:
                    extra_vars = frozenset({walrus})
            self._add_guard(
                pred, node,
                polarity=True,
                guard_kind=GuardKind.ASSERT_TEST,
                trust_level=TrustLevel.PROOF_BACKED,
                walrus_target=walrus,
                extra_variables=extra_vars,
            )
        self.generic_visit(node)

    # -- While loops --

    def visit_While(self, node: ast.While) -> None:
        pred = _ast_test_to_predicate(node.test, self._file)
        if pred is not None:
            self._add_guard(
                pred, node,
                polarity=True,
                guard_kind=GuardKind.WHILE_TEST,
                associated_else=bool(node.orelse),
            )
        self._nesting_depth += 1
        for child in node.body:
            self.visit(child)
        self._nesting_depth -= 1
        for child in node.orelse:
            self.visit(child)

    # -- Try/Except --

    def visit_Try(self, node: ast.Try) -> None:
        self._harvest_try_except(node)
        self.generic_visit(node)

    def visit_TryStar(self, node: ast.AST) -> None:
        """Handle Python 3.11+ try/except* (ExceptionGroup)."""
        # TryStar has similar structure; handle generically
        self._harvest_try_except(node)
        self.generic_visit(node)

    def _harvest_try_except(self, node: ast.AST) -> None:
        """Extract guards from try/except handlers."""
        handlers = getattr(node, "handlers", [])
        for handler in handlers:
            if not isinstance(handler, ast.ExceptHandler):
                continue
            if handler.type is not None:
                type_name = _extract_type_name(handler.type)
                if type_name is not None:
                    # The handler guard: the exception is an instance of the caught type
                    handler_var = handler.name or "_exc"
                    pred = IsInstance(
                        term=Var(handler_var),
                        type_name=type_name,
                        source_location=_source_loc(handler, self._file),
                    )
                    extra_vars = frozenset({handler_var}) if handler.name else frozenset()
                    self._add_guard(
                        pred, handler,
                        polarity=True,
                        guard_kind=GuardKind.TRY_EXCEPT,
                        trust_level=TrustLevel.TRUSTED_AUTO,
                        extra_variables=extra_vars,
                    )

    # -- Ternary expressions (x if cond else y) --

    def visit_IfExp(self, node: ast.IfExp) -> None:
        pred = _ast_test_to_predicate(node.test, self._file)
        if pred is not None:
            self._add_guard(
                pred, node,
                polarity=True,
                guard_kind=GuardKind.TERNARY,
                associated_else=True,
            )
        self.generic_visit(node)

    # -- Comprehension filters --

    def visit_ListComp(self, node: ast.ListComp) -> None:
        self._harvest_comprehension_ifs(node.generators)
        self.generic_visit(node)

    def visit_SetComp(self, node: ast.SetComp) -> None:
        self._harvest_comprehension_ifs(node.generators)
        self.generic_visit(node)

    def visit_DictComp(self, node: ast.DictComp) -> None:
        self._harvest_comprehension_ifs(node.generators)
        self.generic_visit(node)

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> None:
        self._harvest_comprehension_ifs(node.generators)
        self.generic_visit(node)

    def _harvest_comprehension_ifs(
        self,
        generators: List[ast.comprehension],
    ) -> None:
        """Extract guard predicates from comprehension if-clauses."""
        for gen in generators:
            for if_clause in gen.ifs:
                pred = _ast_test_to_predicate(if_clause, self._file)
                if pred is not None:
                    self._add_guard(
                        pred, if_clause,
                        polarity=True,
                        guard_kind=GuardKind.COMPREHENSION_IF,
                    )

    # -- Match statements (Python 3.10+) --

    def visit_Match(self, node: ast.AST) -> None:
        """Handle match/case statements."""
        subject = getattr(node, "subject", None)
        cases = getattr(node, "cases", [])
        if subject is None:
            self.generic_visit(node)
            return

        subject_term = _ast_to_term(subject)
        for case in cases:
            guard = getattr(case, "guard", None)
            if guard is not None:
                pred = _ast_test_to_predicate(guard, self._file)
                if pred is not None:
                    self._add_guard(
                        pred, guard,
                        polarity=True,
                        guard_kind=GuardKind.MATCH_CASE,
                    )
            # Pattern-based guards
            pattern = getattr(case, "pattern", None)
            if pattern is not None and subject_term is not None:
                self._harvest_match_pattern(subject_term, pattern)

        self.generic_visit(node)

    def _harvest_match_pattern(
        self,
        subject_term: Term,
        pattern: ast.AST,
    ) -> None:
        """Extract type narrowing from match patterns."""
        # MatchClass: case ClassName(...):
        pattern_cls = getattr(pattern, "cls", None)
        if pattern_cls is not None:
            type_name = _extract_type_name(pattern_cls)
            if type_name is not None:
                pred = IsInstance(
                    term=subject_term,
                    type_name=type_name,
                    source_location=_source_loc(pattern, self._file),
                )
                self._add_guard(
                    pred, pattern,
                    polarity=True,
                    guard_kind=GuardKind.MATCH_CASE,
                )

        # MatchValue: case 42:
        value_node = getattr(pattern, "value", None)
        if value_node is not None and isinstance(value_node, ast.Constant):
            value_term = _ast_to_term(value_node)
            if value_term is not None:
                pred = Comparison(
                    op="==",
                    left=subject_term,
                    right=value_term,
                    source_location=_source_loc(pattern, self._file),
                )
                self._add_guard(
                    pred, pattern,
                    polarity=True,
                    guard_kind=GuardKind.MATCH_CASE,
                )

    # -- BoolOp short-circuit guards (x and y, x or y) --

    def visit_BoolOp(self, node: ast.BoolOp) -> None:
        """Extract implicit guards from boolean short-circuit evaluation.

        In ``x and y``, evaluating ``y`` implies ``x`` was truthy.
        In ``x or y``, evaluating ``y`` implies ``x`` was falsy.
        """
        if isinstance(node.op, ast.And) and len(node.values) >= 2:
            for i, val in enumerate(node.values[1:], 1):
                # Every value after the first has all preceding values as guards
                for prev in node.values[:i]:
                    pred = _ast_test_to_predicate(prev, self._file)
                    if pred is not None:
                        self._add_guard(
                            pred, val,
                            polarity=True,
                            guard_kind=GuardKind.BOOLEAN_OP,
                        )

        elif isinstance(node.op, ast.Or) and len(node.values) >= 2:
            for i, val in enumerate(node.values[1:], 1):
                for prev in node.values[:i]:
                    pred = _ast_test_to_predicate(prev, self._file)
                    if pred is not None:
                        neg = pred.negate()
                        self._add_guard(
                            neg, val,
                            polarity=False,
                            guard_kind=GuardKind.BOOLEAN_OP,
                        )

        self.generic_visit(node)


# ===================================================================
#  Convenience: harvest_guards()
# ===================================================================

def harvest_guards(
    ast_tree: ast.AST,
    *,
    file: str = "<unknown>",
) -> List[HarvestedGuard]:
    """Extract all guard predicates from a Python AST.

    Args:
        ast_tree: The parsed AST (typically from ``ast.parse``).
        file: Source file name for provenance.

    Returns:
        A list of ``HarvestedGuard`` facts, one per guard site discovered.
    """
    harvester = GuardHarvester(file=file)
    harvester.visit(ast_tree)
    return harvester.guards


# ===================================================================
#  Deduplication and filtering utilities
# ===================================================================

def deduplicate_guards(
    guards: List[HarvestedGuard],
) -> List[HarvestedGuard]:
    """Remove duplicate guards with identical predicates and spans."""
    seen: Set[Tuple[str, int, int, bool]] = set()
    result: List[HarvestedGuard] = []
    for g in guards:
        key = (
            g.source_span.file,
            g.source_span.start_line,
            g.source_span.start_col,
            g.polarity,
        )
        if key not in seen:
            seen.add(key)
            result.append(g)
    return result


def filter_guards_by_function(
    guards: List[HarvestedGuard],
    function_name: str,
) -> List[HarvestedGuard]:
    """Return guards belonging to a specific function."""
    return [g for g in guards if g.parent_function == function_name]


def filter_guards_by_kind(
    guards: List[HarvestedGuard],
    kind: GuardKind,
) -> List[HarvestedGuard]:
    """Return guards of a specific syntactic kind."""
    return [g for g in guards if g.guard_kind == kind]


def filter_guards_by_variable(
    guards: List[HarvestedGuard],
    variable: str,
) -> List[HarvestedGuard]:
    """Return guards that narrow a specific variable."""
    return [g for g in guards if variable in g.narrowed_variables]


def partition_by_polarity(
    guards: List[HarvestedGuard],
) -> Tuple[List[HarvestedGuard], List[HarvestedGuard]]:
    """Split guards into (true-branch, false-branch) partitions."""
    true_guards: List[HarvestedGuard] = []
    false_guards: List[HarvestedGuard] = []
    for g in guards:
        if g.polarity:
            true_guards.append(g)
        else:
            false_guards.append(g)
    return true_guards, false_guards


def guards_for_site(
    guards: List[HarvestedGuard],
    line: int,
    col: int,
) -> List[HarvestedGuard]:
    """Return all guards dominating a given source location.

    A guard dominates a location if the guard's span starts at or before
    the target line/col and the nesting indicates the location is within
    the guard's scope.
    """
    result: List[HarvestedGuard] = []
    for g in guards:
        if g.source_span.start_line <= line:
            result.append(g)
    return result
