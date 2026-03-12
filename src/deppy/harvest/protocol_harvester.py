"""Protocol harvester -- extract protocol conformance hints from Python AST.

Walks a Python AST and identifies protocol conformance evidence from:

- Attribute access patterns: ``obj.attr`` implies ``obj`` has an ``attr`` field.
- Method call patterns: ``obj.method()`` implies a method protocol.
- Dunder usage: ``len(x)`` implies ``__len__``; ``iter(x)`` implies ``__iter__``.
- Duck-typing patterns: ``for x in obj`` implies ``Iterable`` protocol.
- Comparison operations: ``x < y`` implies ``__lt__`` / ``Comparable`` protocol.
- Context manager usage: ``with obj`` implies ``__enter__``/``__exit__``.
- Subscript access: ``obj[k]`` implies ``__getitem__``.

Each observation is recorded as a frozen ``ProtocolHint`` dataclass carrying
the required protocol name, required members, evidence source span, and a
confidence score.
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
from deppy.predicates.heap import HasField, ProtocolConformance
from deppy.static_analysis.observation_sites import SourceSpan


# ===================================================================
#  Protocol classification
# ===================================================================

class ProtocolKind(enum.Enum):
    """Classification of the protocol source."""
    ATTRIBUTE_ACCESS = "attribute_access"
    METHOD_CALL = "method_call"
    DUNDER_USAGE = "dunder_usage"
    ITERATION = "iteration"
    COMPARISON = "comparison"
    CONTEXT_MANAGER = "context_manager"
    SUBSCRIPT = "subscript"
    ARITHMETIC = "arithmetic"
    CALLABLE = "callable"
    HASHABLE = "hashable"
    AWAITABLE = "awaitable"
    ASYNC_ITERATION = "async_iteration"
    DESCRIPTOR = "descriptor"
    CONTAINER = "container"


# ===================================================================
#  Well-known protocol mappings
# ===================================================================

# Maps dunder method names to their protocol names
_DUNDER_TO_PROTOCOL: Dict[str, Tuple[str, str]] = {
    "__len__": ("Sized", "len()"),
    "__iter__": ("Iterable", "iter()"),
    "__next__": ("Iterator", "next()"),
    "__contains__": ("Container", "in operator"),
    "__getitem__": ("Subscriptable", "[] access"),
    "__setitem__": ("MutableSubscriptable", "[] assignment"),
    "__delitem__": ("MutableSubscriptable", "del []"),
    "__enter__": ("ContextManager", "with statement"),
    "__exit__": ("ContextManager", "with statement"),
    "__aenter__": ("AsyncContextManager", "async with"),
    "__aexit__": ("AsyncContextManager", "async with"),
    "__aiter__": ("AsyncIterable", "async for"),
    "__anext__": ("AsyncIterator", "async for"),
    "__call__": ("Callable", "function call"),
    "__hash__": ("Hashable", "hash()"),
    "__eq__": ("Equatable", "== operator"),
    "__ne__": ("Equatable", "!= operator"),
    "__lt__": ("Comparable", "< operator"),
    "__le__": ("Comparable", "<= operator"),
    "__gt__": ("Comparable", "> operator"),
    "__ge__": ("Comparable", ">= operator"),
    "__add__": ("Addable", "+ operator"),
    "__sub__": ("Subtractable", "- operator"),
    "__mul__": ("Multipliable", "* operator"),
    "__truediv__": ("Divisible", "/ operator"),
    "__floordiv__": ("Divisible", "// operator"),
    "__mod__": ("Modular", "% operator"),
    "__pow__": ("Exponentiable", "** operator"),
    "__neg__": ("Negatable", "unary - operator"),
    "__pos__": ("SignAware", "unary + operator"),
    "__abs__": ("AbsAware", "abs()"),
    "__bool__": ("BoolConvertible", "bool()"),
    "__int__": ("IntConvertible", "int()"),
    "__float__": ("FloatConvertible", "float()"),
    "__str__": ("StrConvertible", "str()"),
    "__repr__": ("Representable", "repr()"),
    "__bytes__": ("BytesConvertible", "bytes()"),
    "__index__": ("Indexable", "index()"),
    "__await__": ("Awaitable", "await"),
}

# Maps built-in function names to required dunder methods
_BUILTIN_TO_DUNDERS: Dict[str, List[str]] = {
    "len": ["__len__"],
    "iter": ["__iter__"],
    "next": ["__next__"],
    "hash": ["__hash__"],
    "abs": ["__abs__"],
    "bool": ["__bool__"],
    "int": ["__int__"],
    "float": ["__float__"],
    "str": ["__str__"],
    "repr": ["__repr__"],
    "bytes": ["__bytes__"],
    "reversed": ["__reversed__"],
    "sorted": ["__lt__"],
    "min": ["__lt__"],
    "max": ["__lt__"],
    "sum": ["__add__"],
}

# Maps comparison operators to dunder method names
_CMP_TO_DUNDER: Dict[type, str] = {
    ast.Lt: "__lt__",
    ast.LtE: "__le__",
    ast.Gt: "__gt__",
    ast.GtE: "__ge__",
    ast.Eq: "__eq__",
    ast.NotEq: "__ne__",
}

# Maps binary operators to dunder method names
_BINOP_TO_DUNDER: Dict[type, str] = {
    ast.Add: "__add__",
    ast.Sub: "__sub__",
    ast.Mult: "__mul__",
    ast.Div: "__truediv__",
    ast.FloorDiv: "__floordiv__",
    ast.Mod: "__mod__",
    ast.Pow: "__pow__",
    ast.BitAnd: "__and__",
    ast.BitOr: "__or__",
    ast.BitXor: "__xor__",
    ast.LShift: "__lshift__",
    ast.RShift: "__rshift__",
    ast.MatMult: "__matmul__",
}

# Maps unary operators to dunder method names
_UNARYOP_TO_DUNDER: Dict[type, str] = {
    ast.USub: "__neg__",
    ast.UAdd: "__pos__",
    ast.Invert: "__invert__",
}


# ===================================================================
#  ProtocolHint
# ===================================================================

@dataclass(frozen=True)
class ProtocolHint:
    """A protocol conformance hint extracted from the AST.

    Attributes:
        variable_name: The variable whose protocol conformance is inferred.
        protocol_name: The inferred protocol (e.g. 'Iterable', 'Sized').
        required_methods: Dunder methods required by this protocol.
        required_attributes: Non-dunder attributes accessed.
        evidence_kind: What kind of AST pattern provided the evidence.
        source_span: Location in source code.
        confidence: Confidence score in [0.0, 1.0].
        trust_level: Trust level for this hint.
        parent_function: Enclosing function name.
        evidence_description: Human-readable description of the evidence.
    """
    variable_name: str
    protocol_name: str
    required_methods: Tuple[str, ...] = ()
    required_attributes: Tuple[str, ...] = ()
    evidence_kind: ProtocolKind = ProtocolKind.ATTRIBUTE_ACCESS
    source_span: Optional[SourceSpan] = None
    confidence: float = 0.8
    trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO
    parent_function: Optional[str] = None
    evidence_description: str = ""

    @property
    def is_dunder_based(self) -> bool:
        """True if the hint is based on dunder method access."""
        return any(m.startswith("__") and m.endswith("__") for m in self.required_methods)

    @property
    def all_members(self) -> FrozenSet[str]:
        """All required members (methods + attributes)."""
        return frozenset(self.required_methods) | frozenset(self.required_attributes)

    def to_predicate(self) -> Predicate:
        """Convert to a ProtocolConformance predicate."""
        return ProtocolConformance(
            obj=Var(self.variable_name),
            protocol_name=self.protocol_name,
            required_methods=list(self.required_methods),
            source_location=SourceLocation(
                file=self.source_span.file if self.source_span else "<unknown>",
                line=self.source_span.start_line if self.source_span else 0,
                col=self.source_span.start_col if self.source_span else 0,
            ) if self.source_span else None,
        )

    def merge_with(self, other: ProtocolHint) -> ProtocolHint:
        """Merge two hints for the same variable and protocol."""
        if self.variable_name != other.variable_name:
            raise ValueError("Cannot merge hints for different variables")
        methods = frozenset(self.required_methods) | frozenset(other.required_methods)
        attrs = frozenset(self.required_attributes) | frozenset(other.required_attributes)
        conf = max(self.confidence, other.confidence)
        return ProtocolHint(
            variable_name=self.variable_name,
            protocol_name=self.protocol_name or other.protocol_name,
            required_methods=tuple(sorted(methods)),
            required_attributes=tuple(sorted(attrs)),
            evidence_kind=self.evidence_kind,
            source_span=self.source_span or other.source_span,
            confidence=conf,
            trust_level=self.trust_level,
            parent_function=self.parent_function or other.parent_function,
            evidence_description=self.evidence_description or other.evidence_description,
        )

    def pretty(self) -> str:
        methods = ", ".join(self.required_methods) if self.required_methods else ""
        attrs = ", ".join(self.required_attributes) if self.required_attributes else ""
        parts = []
        if methods:
            parts.append(f"methods=[{methods}]")
        if attrs:
            parts.append(f"attrs=[{attrs}]")
        members = ", ".join(parts)
        return (
            f"ProtocolHint({self.variable_name}: {self.protocol_name}, "
            f"{members}, conf={self.confidence:.2f})"
        )


# ===================================================================
#  AST helper: extract variable name from expression
# ===================================================================

def _extract_variable_name(node: ast.expr) -> Optional[str]:
    """Extract the root variable name from an expression."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return _extract_variable_name(node.value)
    if isinstance(node, ast.Subscript):
        return _extract_variable_name(node.value)
    if isinstance(node, ast.Starred):
        return _extract_variable_name(node.value)
    return None


def _extract_attr_chain(node: ast.expr) -> Optional[List[str]]:
    """Extract the full attribute chain: a.b.c -> ['a', 'b', 'c']."""
    if isinstance(node, ast.Name):
        return [node.id]
    if isinstance(node, ast.Attribute):
        base = _extract_attr_chain(node.value)
        if base is not None:
            return base + [node.attr]
    return None


# ===================================================================
#  ProtocolHarvester
# ===================================================================

class ProtocolHarvester(ast.NodeVisitor):
    """AST visitor that extracts protocol conformance hints.

    Walks the AST top-down, collecting ``ProtocolHint`` instances for
    every evidence site: attribute access, method calls, dunder usage,
    iteration patterns, comparisons, context managers, and subscripts.

    Usage::

        harvester = ProtocolHarvester(file="example.py")
        harvester.visit(tree)
        hints = harvester.hints
    """

    def __init__(self, file: str = "<unknown>") -> None:
        self._file = file
        self._hints: List[ProtocolHint] = []
        self._function_stack: List[str] = []

    @property
    def hints(self) -> List[ProtocolHint]:
        """All collected protocol hints."""
        return list(self._hints)

    @property
    def _current_function(self) -> Optional[str]:
        return self._function_stack[-1] if self._function_stack else None

    def _span(self, node: ast.AST) -> SourceSpan:
        return SourceSpan.from_ast(node, self._file)

    def _add_hint(
        self,
        variable_name: str,
        protocol_name: str,
        node: ast.AST,
        *,
        required_methods: Sequence[str] = (),
        required_attributes: Sequence[str] = (),
        evidence_kind: ProtocolKind = ProtocolKind.ATTRIBUTE_ACCESS,
        confidence: float = 0.8,
        evidence_description: str = "",
    ) -> None:
        """Record a protocol conformance hint."""
        if not variable_name or variable_name.startswith("_"):
            # Skip private/mangled names for cleaner output
            pass
        self._hints.append(ProtocolHint(
            variable_name=variable_name,
            protocol_name=protocol_name,
            required_methods=tuple(required_methods),
            required_attributes=tuple(required_attributes),
            evidence_kind=evidence_kind,
            source_span=self._span(node),
            confidence=confidence,
            trust_level=TrustLevel.TRUSTED_AUTO,
            parent_function=self._current_function,
            evidence_description=evidence_description,
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

    # -- Attribute access --

    def visit_Attribute(self, node: ast.Attribute) -> None:
        var_name = _extract_variable_name(node.value)
        if var_name is not None:
            self._add_hint(
                var_name,
                f"HasAttr_{node.attr}",
                node,
                required_attributes=(node.attr,),
                evidence_kind=ProtocolKind.ATTRIBUTE_ACCESS,
                confidence=0.9,
                evidence_description=f"Attribute access: {var_name}.{node.attr}",
            )
        self.generic_visit(node)

    # -- Method calls --

    def visit_Call(self, node: ast.Call) -> None:
        # Method call: obj.method(...)
        if isinstance(node.func, ast.Attribute):
            var_name = _extract_variable_name(node.func.value)
            method_name = node.func.attr
            if var_name is not None:
                self._add_hint(
                    var_name,
                    f"Has_{method_name}",
                    node,
                    required_methods=(method_name,),
                    evidence_kind=ProtocolKind.METHOD_CALL,
                    confidence=0.9,
                    evidence_description=f"Method call: {var_name}.{method_name}()",
                )

        # Built-in function call: len(x), iter(x), etc.
        if isinstance(node.func, ast.Name):
            func_name = node.func.id
            if func_name in _BUILTIN_TO_DUNDERS and node.args:
                arg_var = _extract_variable_name(node.args[0])
                if arg_var is not None:
                    dunders = _BUILTIN_TO_DUNDERS[func_name]
                    for dunder in dunders:
                        proto_info = _DUNDER_TO_PROTOCOL.get(dunder)
                        proto_name = proto_info[0] if proto_info else f"Supports_{dunder}"
                        evidence = proto_info[1] if proto_info else f"{func_name}() call"
                        self._add_hint(
                            arg_var,
                            proto_name,
                            node,
                            required_methods=(dunder,),
                            evidence_kind=ProtocolKind.DUNDER_USAGE,
                            confidence=0.95,
                            evidence_description=f"Built-in {evidence} on {arg_var}",
                        )

            # callable(x)
            if func_name == "callable" and node.args:
                arg_var = _extract_variable_name(node.args[0])
                if arg_var is not None:
                    self._add_hint(
                        arg_var,
                        "Callable",
                        node,
                        required_methods=("__call__",),
                        evidence_kind=ProtocolKind.CALLABLE,
                        confidence=0.95,
                        evidence_description=f"callable() check on {arg_var}",
                    )

        self.generic_visit(node)

    # -- Iteration: for x in obj --

    def visit_For(self, node: ast.For) -> None:
        iter_var = _extract_variable_name(node.iter)
        if iter_var is not None:
            self._add_hint(
                iter_var,
                "Iterable",
                node,
                required_methods=("__iter__",),
                evidence_kind=ProtocolKind.ITERATION,
                confidence=0.95,
                evidence_description=f"for loop iteration over {iter_var}",
            )
        self.generic_visit(node)

    def visit_AsyncFor(self, node: ast.AsyncFor) -> None:
        iter_var = _extract_variable_name(node.iter)
        if iter_var is not None:
            self._add_hint(
                iter_var,
                "AsyncIterable",
                node,
                required_methods=("__aiter__", "__anext__"),
                evidence_kind=ProtocolKind.ASYNC_ITERATION,
                confidence=0.95,
                evidence_description=f"async for iteration over {iter_var}",
            )
        self.generic_visit(node)

    # -- Comparison operators --

    def visit_Compare(self, node: ast.Compare) -> None:
        for op in node.ops:
            dunder = _CMP_TO_DUNDER.get(type(op))
            if dunder is not None:
                left_var = _extract_variable_name(node.left)
                if left_var is not None:
                    proto_info = _DUNDER_TO_PROTOCOL.get(dunder, ("Comparable", "comparison"))
                    self._add_hint(
                        left_var,
                        proto_info[0],
                        node,
                        required_methods=(dunder,),
                        evidence_kind=ProtocolKind.COMPARISON,
                        confidence=0.85,
                        evidence_description=f"{proto_info[1]} on {left_var}",
                    )

            # 'in' operator
            if isinstance(op, ast.In) and len(node.comparators) > 0:
                container_var = _extract_variable_name(node.comparators[0])
                if container_var is not None:
                    self._add_hint(
                        container_var,
                        "Container",
                        node,
                        required_methods=("__contains__",),
                        evidence_kind=ProtocolKind.CONTAINER,
                        confidence=0.95,
                        evidence_description=f"'in' check on {container_var}",
                    )

        self.generic_visit(node)

    # -- Binary operators --

    def visit_BinOp(self, node: ast.BinOp) -> None:
        dunder = _BINOP_TO_DUNDER.get(type(node.op))
        if dunder is not None:
            left_var = _extract_variable_name(node.left)
            if left_var is not None:
                proto_info = _DUNDER_TO_PROTOCOL.get(dunder, ("Arithmetic", "operator"))
                self._add_hint(
                    left_var,
                    proto_info[0],
                    node,
                    required_methods=(dunder,),
                    evidence_kind=ProtocolKind.ARITHMETIC,
                    confidence=0.85,
                    evidence_description=f"{proto_info[1]} on {left_var}",
                )
        self.generic_visit(node)

    # -- Unary operators --

    def visit_UnaryOp(self, node: ast.UnaryOp) -> None:
        dunder = _UNARYOP_TO_DUNDER.get(type(node.op))
        if dunder is not None:
            operand_var = _extract_variable_name(node.operand)
            if operand_var is not None:
                proto_info = _DUNDER_TO_PROTOCOL.get(dunder, ("UnaryOp", "operator"))
                self._add_hint(
                    operand_var,
                    proto_info[0],
                    node,
                    required_methods=(dunder,),
                    evidence_kind=ProtocolKind.ARITHMETIC,
                    confidence=0.85,
                    evidence_description=f"{proto_info[1]} on {operand_var}",
                )
        self.generic_visit(node)

    # -- Context managers: with obj --

    def visit_With(self, node: ast.With) -> None:
        for item in node.items:
            ctx_var = _extract_variable_name(item.context_expr)
            if ctx_var is not None:
                self._add_hint(
                    ctx_var,
                    "ContextManager",
                    node,
                    required_methods=("__enter__", "__exit__"),
                    evidence_kind=ProtocolKind.CONTEXT_MANAGER,
                    confidence=0.95,
                    evidence_description=f"with statement on {ctx_var}",
                )
        self.generic_visit(node)

    def visit_AsyncWith(self, node: ast.AsyncWith) -> None:
        for item in node.items:
            ctx_var = _extract_variable_name(item.context_expr)
            if ctx_var is not None:
                self._add_hint(
                    ctx_var,
                    "AsyncContextManager",
                    node,
                    required_methods=("__aenter__", "__aexit__"),
                    evidence_kind=ProtocolKind.CONTEXT_MANAGER,
                    confidence=0.95,
                    evidence_description=f"async with statement on {ctx_var}",
                )
        self.generic_visit(node)

    # -- Subscript: obj[k] --

    def visit_Subscript(self, node: ast.Subscript) -> None:
        var_name = _extract_variable_name(node.value)
        if var_name is not None:
            # Determine if reading or writing based on context
            ctx_type = type(node.ctx)
            if ctx_type == ast.Store:
                self._add_hint(
                    var_name,
                    "MutableSubscriptable",
                    node,
                    required_methods=("__getitem__", "__setitem__"),
                    evidence_kind=ProtocolKind.SUBSCRIPT,
                    confidence=0.9,
                    evidence_description=f"Subscript assignment on {var_name}",
                )
            elif ctx_type == ast.Del:
                self._add_hint(
                    var_name,
                    "MutableSubscriptable",
                    node,
                    required_methods=("__getitem__", "__delitem__"),
                    evidence_kind=ProtocolKind.SUBSCRIPT,
                    confidence=0.9,
                    evidence_description=f"Subscript deletion on {var_name}",
                )
            else:
                self._add_hint(
                    var_name,
                    "Subscriptable",
                    node,
                    required_methods=("__getitem__",),
                    evidence_kind=ProtocolKind.SUBSCRIPT,
                    confidence=0.9,
                    evidence_description=f"Subscript access on {var_name}",
                )
        self.generic_visit(node)

    # -- Await expression --

    def visit_Await(self, node: ast.Await) -> None:
        var_name = _extract_variable_name(node.value)
        if var_name is not None:
            self._add_hint(
                var_name,
                "Awaitable",
                node,
                required_methods=("__await__",),
                evidence_kind=ProtocolKind.AWAITABLE,
                confidence=0.95,
                evidence_description=f"await on {var_name}",
            )
        self.generic_visit(node)

    # -- Comprehension iteration --

    def visit_ListComp(self, node: ast.ListComp) -> None:
        self._harvest_comprehension_iters(node.generators, node)
        self.generic_visit(node)

    def visit_SetComp(self, node: ast.SetComp) -> None:
        self._harvest_comprehension_iters(node.generators, node)
        self.generic_visit(node)

    def visit_DictComp(self, node: ast.DictComp) -> None:
        self._harvest_comprehension_iters(node.generators, node)
        self.generic_visit(node)

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> None:
        self._harvest_comprehension_iters(node.generators, node)
        self.generic_visit(node)

    def _harvest_comprehension_iters(
        self,
        generators: List[ast.comprehension],
        parent_node: ast.AST,
    ) -> None:
        """Extract Iterable protocol from comprehension iterators."""
        for gen in generators:
            iter_var = _extract_variable_name(gen.iter)
            if iter_var is not None:
                self._add_hint(
                    iter_var,
                    "Iterable",
                    parent_node,
                    required_methods=("__iter__",),
                    evidence_kind=ProtocolKind.ITERATION,
                    confidence=0.95,
                    evidence_description=f"Comprehension iteration over {iter_var}",
                )


# ===================================================================
#  Convenience functions
# ===================================================================

def harvest_protocols(
    ast_tree: ast.AST,
    *,
    file: str = "<unknown>",
) -> List[ProtocolHint]:
    """Extract all protocol conformance hints from a Python AST.

    Args:
        ast_tree: The parsed AST.
        file: Source file name for provenance.

    Returns:
        A list of ProtocolHint instances.
    """
    harvester = ProtocolHarvester(file=file)
    harvester.visit(ast_tree)
    return harvester.hints


def deduplicate_hints(
    hints: List[ProtocolHint],
) -> List[ProtocolHint]:
    """Merge duplicate hints for the same variable and protocol.

    When multiple hints target the same (variable, protocol) pair,
    merge their required methods/attributes and keep the highest
    confidence.
    """
    grouped: Dict[Tuple[str, str], List[ProtocolHint]] = {}
    for h in hints:
        key = (h.variable_name, h.protocol_name)
        grouped.setdefault(key, []).append(h)

    result: List[ProtocolHint] = []
    for key, group in grouped.items():
        merged = group[0]
        for other in group[1:]:
            merged = merged.merge_with(other)
        result.append(merged)

    return result


def filter_hints_by_function(
    hints: List[ProtocolHint],
    function_name: str,
) -> List[ProtocolHint]:
    """Return hints belonging to a specific function."""
    return [h for h in hints if h.parent_function == function_name]


def filter_hints_by_variable(
    hints: List[ProtocolHint],
    variable: str,
) -> List[ProtocolHint]:
    """Return hints for a specific variable."""
    return [h for h in hints if h.variable_name == variable]


def filter_hints_by_confidence(
    hints: List[ProtocolHint],
    min_confidence: float = 0.5,
) -> List[ProtocolHint]:
    """Return hints above a confidence threshold."""
    return [h for h in hints if h.confidence >= min_confidence]


def hints_to_predicates(
    hints: List[ProtocolHint],
) -> List[Predicate]:
    """Convert all hints to ProtocolConformance predicates."""
    return [h.to_predicate() for h in hints]
