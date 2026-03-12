"""Infer structural protocols from usage patterns.

When a parameter is used with ``.append()`` and ``len()``, we can infer
it satisfies ``Sized + MutableSequence``.  This module walks function
bodies to collect method calls and attribute accesses on parameters,
then maps those usage patterns to known Python protocols.

This is bottom-up protocol inference: rather than requiring explicit type
annotations, the analysis discovers what protocols a parameter must
satisfy based on how it is used in the function body.
"""

from __future__ import annotations

import ast
from collections import defaultdict
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)


# ---------------------------------------------------------------------------
# Usage records
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MethodUsage:
    """Record of a method call on a parameter.

    Attributes:
        _method_name: Name of the called method.
        _arg_count: Number of arguments passed.
        _line: Source line number.
        _in_context: Description of the usage context (e.g., "for loop").
    """

    _method_name: str
    _arg_count: int = 0
    _line: int = 0
    _in_context: str = ""

    @property
    def method_name(self) -> str:
        return self._method_name

    @property
    def arg_count(self) -> int:
        return self._arg_count

    @property
    def line(self) -> int:
        return self._line


@dataclass(frozen=True)
class AttributeUsage:
    """Record of an attribute access on a parameter.

    Attributes:
        _attr_name: Name of the accessed attribute.
        _is_read: Whether the attribute is read.
        _is_write: Whether the attribute is written.
        _line: Source line number.
    """

    _attr_name: str
    _is_read: bool = True
    _is_write: bool = False
    _line: int = 0

    @property
    def attr_name(self) -> str:
        return self._attr_name

    @property
    def is_read(self) -> bool:
        return self._is_read

    @property
    def is_write(self) -> bool:
        return self._is_write


@dataclass(frozen=True)
class BuiltinUsage:
    """Record of a builtin function applied to a parameter.

    Attributes:
        _func_name: Name of the builtin (e.g., "len", "iter", "hash").
        _line: Source line number.
    """

    _func_name: str
    _line: int = 0

    @property
    def func_name(self) -> str:
        return self._func_name


@dataclass(frozen=True)
class OperatorUsage:
    """Record of an operator applied to a parameter.

    Attributes:
        _operator: The operator (e.g., "in", "[]", "+").
        _is_left: Whether the parameter is on the left side.
        _line: Source line number.
    """

    _operator: str
    _is_left: bool = True
    _line: int = 0

    @property
    def operator(self) -> str:
        return self._operator


# ---------------------------------------------------------------------------
# Inferred protocol
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class InferredProtocol:
    """Result of protocol inference for a single parameter.

    Attributes:
        _param_name: Name of the analyzed parameter.
        _protocols: Set of protocol names the parameter must satisfy.
        _required_methods: Set of method names used on the parameter.
        _required_attributes: Set of attribute names accessed on the parameter.
        _builtin_usages: Builtins applied to the parameter.
        _operator_usages: Operators applied to the parameter.
        _confidence: Confidence score (0.0 to 1.0).
    """

    _param_name: str
    _protocols: FrozenSet[str] = frozenset()
    _required_methods: FrozenSet[str] = frozenset()
    _required_attributes: FrozenSet[str] = frozenset()
    _builtin_usages: Tuple[BuiltinUsage, ...] = ()
    _operator_usages: Tuple[OperatorUsage, ...] = ()
    _confidence: float = 1.0

    @property
    def param_name(self) -> str:
        return self._param_name

    @property
    def protocols(self) -> FrozenSet[str]:
        return self._protocols

    @property
    def required_methods(self) -> FrozenSet[str]:
        return self._required_methods

    @property
    def required_attributes(self) -> FrozenSet[str]:
        return self._required_attributes

    @property
    def confidence(self) -> float:
        return self._confidence

    @property
    def is_empty(self) -> bool:
        return (
            len(self._protocols) == 0
            and len(self._required_methods) == 0
            and len(self._required_attributes) == 0
        )


# ---------------------------------------------------------------------------
# Protocol mapping rules
# ---------------------------------------------------------------------------

# Builtin -> protocol implications
_BUILTIN_TO_PROTOCOL: Dict[str, List[str]] = {
    "len": ["Sized"],
    "iter": ["Iterable"],
    "next": ["Iterator"],
    "hash": ["Hashable"],
    "reversed": ["Reversible"],
    "sorted": ["Iterable"],
    "list": ["Iterable"],
    "tuple": ["Iterable"],
    "set": ["Iterable"],
    "frozenset": ["Iterable"],
    "dict": ["Mapping"],
    "enumerate": ["Iterable"],
    "zip": ["Iterable"],
    "map": ["Iterable"],
    "filter": ["Iterable"],
    "sum": ["Iterable"],
    "min": ["Iterable"],
    "max": ["Iterable"],
    "any": ["Iterable"],
    "all": ["Iterable"],
    "abs": ["SupportsAbs"],
    "int": ["SupportsInt"],
    "float": ["SupportsFloat"],
    "complex": ["SupportsComplex"],
    "bytes": ["SupportsBytes"],
    "round": ["SupportsRound"],
    "repr": [],
    "str": [],
    "bool": [],
    "type": [],
}

# Method name -> protocol implications
_METHOD_TO_PROTOCOL: Dict[str, List[str]] = {
    "append": ["MutableSequence"],
    "extend": ["MutableSequence"],
    "insert": ["MutableSequence"],
    "pop": ["MutableSequence"],
    "remove": ["MutableSequence"],
    "clear": ["MutableSequence", "MutableMapping", "MutableSet"],
    "sort": ["MutableSequence"],
    "reverse": ["MutableSequence"],
    "index": ["Sequence"],
    "count": ["Sequence"],
    "keys": ["Mapping"],
    "values": ["Mapping"],
    "items": ["Mapping"],
    "get": ["Mapping"],
    "update": ["MutableMapping", "MutableSet"],
    "setdefault": ["MutableMapping"],
    "popitem": ["MutableMapping"],
    "add": ["MutableSet"],
    "discard": ["MutableSet"],
    "union": ["Set"],
    "intersection": ["Set"],
    "difference": ["Set"],
    "symmetric_difference": ["Set"],
    "issubset": ["Set"],
    "issuperset": ["Set"],
    "copy": [],
    "read": ["IO"],
    "write": ["IO"],
    "readline": ["IO"],
    "readlines": ["IO"],
    "close": ["IO", "ContextManager"],
    "seek": ["IO"],
    "tell": ["IO"],
    "flush": ["IO"],
    "__enter__": ["ContextManager"],
    "__exit__": ["ContextManager"],
    "__aenter__": ["AsyncContextManager"],
    "__aexit__": ["AsyncContextManager"],
    "__iter__": ["Iterable"],
    "__next__": ["Iterator"],
    "__len__": ["Sized"],
    "__contains__": ["Container"],
    "__getitem__": ["Sequence", "Mapping"],
    "__setitem__": ["MutableSequence", "MutableMapping"],
    "__delitem__": ["MutableSequence", "MutableMapping"],
    "__call__": ["Callable"],
    "__hash__": ["Hashable"],
    "send": ["Generator"],
    "throw": ["Generator"],
    "asend": ["AsyncGenerator"],
    "athrow": ["AsyncGenerator"],
}

# Operator -> dunder method + protocol
_OPERATOR_TO_DUNDER: Dict[str, Tuple[str, List[str]]] = {
    "in": ("__contains__", ["Container"]),
    "[]": ("__getitem__", ["Sequence", "Mapping"]),
    "[]=": ("__setitem__", ["MutableSequence", "MutableMapping"]),
    "del[]": ("__delitem__", ["MutableSequence", "MutableMapping"]),
    "+": ("__add__", []),
    "-": ("__sub__", []),
    "*": ("__mul__", []),
    "/": ("__truediv__", []),
    "//": ("__floordiv__", []),
    "%": ("__mod__", []),
    "**": ("__pow__", []),
    "==": ("__eq__", []),
    "!=": ("__ne__", []),
    "<": ("__lt__", []),
    "<=": ("__le__", []),
    ">": ("__gt__", []),
    ">=": ("__ge__", []),
    "<<": ("__lshift__", []),
    ">>": ("__rshift__", []),
    "&": ("__and__", []),
    "|": ("__or__", []),
    "^": ("__xor__", []),
    "~": ("__invert__", []),
    "neg": ("__neg__", []),
    "pos": ("__pos__", []),
}


# ---------------------------------------------------------------------------
# Usage collector (AST visitor)
# ---------------------------------------------------------------------------

class _UsageCollector(ast.NodeVisitor):
    """Walk a function body and collect usage records for a specific param."""

    def __init__(self, param_name: str) -> None:
        self._param = param_name
        self._method_usages: List[MethodUsage] = []
        self._attr_usages: List[AttributeUsage] = []
        self._builtin_usages: List[BuiltinUsage] = []
        self._operator_usages: List[OperatorUsage] = []

    @property
    def method_usages(self) -> List[MethodUsage]:
        return list(self._method_usages)

    @property
    def attr_usages(self) -> List[AttributeUsage]:
        return list(self._attr_usages)

    @property
    def builtin_usages(self) -> List[BuiltinUsage]:
        return list(self._builtin_usages)

    @property
    def operator_usages(self) -> List[OperatorUsage]:
        return list(self._operator_usages)

    def _is_param(self, node: ast.expr) -> bool:
        """Check if a node refers to our parameter."""
        return isinstance(node, ast.Name) and node.id == self._param

    def visit_Call(self, node: ast.Call) -> None:
        line = getattr(node, "lineno", 0)

        # Method call: param.method(...)
        if isinstance(node.func, ast.Attribute) and self._is_param(node.func.value):
            self._method_usages.append(MethodUsage(
                _method_name=node.func.attr,
                _arg_count=len(node.args),
                _line=line,
            ))

        # Builtin call with param as argument: len(param), iter(param), ...
        if isinstance(node.func, ast.Name):
            func_name = node.func.id
            for arg in node.args:
                if self._is_param(arg):
                    self._builtin_usages.append(BuiltinUsage(
                        _func_name=func_name,
                        _line=line,
                    ))
                    break

        self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        if self._is_param(node.value):
            # Don't double-count method calls
            # (they're handled in visit_Call)
            line = getattr(node, "lineno", 0)
            self._attr_usages.append(AttributeUsage(
                _attr_name=node.attr,
                _is_read=True,
                _line=line,
            ))
        self.generic_visit(node)

    def visit_Subscript(self, node: ast.Subscript) -> None:
        line = getattr(node, "lineno", 0)
        if self._is_param(node.value):
            self._operator_usages.append(OperatorUsage(
                _operator="[]",
                _is_left=True,
                _line=line,
            ))
        self.generic_visit(node)

    def visit_For(self, node: ast.For) -> None:
        line = getattr(node, "lineno", 0)
        if self._is_param(node.iter):
            self._builtin_usages.append(BuiltinUsage(
                _func_name="iter",
                _line=line,
            ))
        self.generic_visit(node)

    def visit_Compare(self, node: ast.Compare) -> None:
        line = getattr(node, "lineno", 0)
        for op, comparator in zip(node.ops, node.comparators):
            if isinstance(op, ast.In) and self._is_param(comparator):
                self._operator_usages.append(OperatorUsage(
                    _operator="in",
                    _is_left=False,
                    _line=line,
                ))
            elif isinstance(op, ast.NotIn) and self._is_param(comparator):
                self._operator_usages.append(OperatorUsage(
                    _operator="in",
                    _is_left=False,
                    _line=line,
                ))
        self.generic_visit(node)

    def visit_BinOp(self, node: ast.BinOp) -> None:
        line = getattr(node, "lineno", 0)
        op_map = {
            ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
            ast.Div: "/", ast.FloorDiv: "//", ast.Mod: "%",
            ast.Pow: "**", ast.LShift: "<<", ast.RShift: ">>",
            ast.BitAnd: "&", ast.BitOr: "|", ast.BitXor: "^",
        }
        op_str = op_map.get(type(node.op), "?")
        if self._is_param(node.left):
            self._operator_usages.append(OperatorUsage(
                _operator=op_str,
                _is_left=True,
                _line=line,
            ))
        if self._is_param(node.right):
            self._operator_usages.append(OperatorUsage(
                _operator=op_str,
                _is_left=False,
                _line=line,
            ))
        self.generic_visit(node)

    def visit_UnaryOp(self, node: ast.UnaryOp) -> None:
        line = getattr(node, "lineno", 0)
        if self._is_param(node.operand):
            op_map = {
                ast.UAdd: "pos", ast.USub: "neg",
                ast.Not: "not", ast.Invert: "~",
            }
            op_str = op_map.get(type(node.op), "?")
            self._operator_usages.append(OperatorUsage(
                _operator=op_str,
                _is_left=True,
                _line=line,
            ))
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        # Check for param.attr = value (write access)
        for target in node.targets:
            if (
                isinstance(target, ast.Attribute)
                and self._is_param(target.value)
            ):
                line = getattr(node, "lineno", 0)
                self._attr_usages.append(AttributeUsage(
                    _attr_name=target.attr,
                    _is_read=False,
                    _is_write=True,
                    _line=line,
                ))
            # param[key] = value
            if (
                isinstance(target, ast.Subscript)
                and self._is_param(target.value)
            ):
                line = getattr(node, "lineno", 0)
                self._operator_usages.append(OperatorUsage(
                    _operator="[]=",
                    _is_left=True,
                    _line=line,
                ))
        self.generic_visit(node)

    def visit_Delete(self, node: ast.Delete) -> None:
        for target in node.targets:
            if (
                isinstance(target, ast.Subscript)
                and self._is_param(target.value)
            ):
                line = getattr(node, "lineno", 0)
                self._operator_usages.append(OperatorUsage(
                    _operator="del[]",
                    _is_left=True,
                    _line=line,
                ))
        self.generic_visit(node)


# ---------------------------------------------------------------------------
# ProtocolInferrer
# ---------------------------------------------------------------------------

class ProtocolInferrer:
    """Infer structural protocols from parameter usage patterns.

    Walks a function body to collect method calls, attribute accesses,
    builtin applications, and operator uses on each parameter, then
    maps those patterns to known Python protocols.
    """

    def __init__(self) -> None:
        self._inference_cache: Dict[Tuple[str, str], InferredProtocol] = {}

    # -- Core inference -----------------------------------------------------

    def infer_protocol(
        self,
        func_ast: ast.FunctionDef,
        param_name: str,
    ) -> InferredProtocol:
        """Infer protocols for a single parameter from usage patterns.

        Returns an InferredProtocol with all detected protocol conformances,
        required methods, and required attributes.
        """
        cache_key = (func_ast.name, param_name)
        if cache_key in self._inference_cache:
            return self._inference_cache[cache_key]

        collector = _UsageCollector(param_name)
        for stmt in func_ast.body:
            collector.visit(stmt)

        # Collect all implied protocols
        protocols: Set[str] = set()
        methods: Set[str] = set()
        attributes: Set[str] = set()

        # From method calls
        for usage in collector.method_usages:
            methods.add(usage.method_name)
            implied = _METHOD_TO_PROTOCOL.get(usage.method_name, [])
            protocols.update(implied)

        # From builtin calls
        for usage in collector.builtin_usages:
            implied = _BUILTIN_TO_PROTOCOL.get(usage.func_name, [])
            protocols.update(implied)

        # From operator usage
        for usage in collector.operator_usages:
            op_info = _OPERATOR_TO_DUNDER.get(usage.operator)
            if op_info:
                dunder, implied = op_info
                methods.add(dunder)
                protocols.update(implied)

        # From attribute access
        for usage in collector.attr_usages:
            attributes.add(usage.attr_name)

        # Compute confidence based on evidence quantity
        evidence_count = (
            len(collector.method_usages)
            + len(collector.builtin_usages)
            + len(collector.operator_usages)
        )
        confidence = min(1.0, evidence_count / 3.0) if evidence_count > 0 else 0.0

        result = InferredProtocol(
            _param_name=param_name,
            _protocols=frozenset(protocols),
            _required_methods=frozenset(methods),
            _required_attributes=frozenset(attributes),
            _builtin_usages=tuple(collector.builtin_usages),
            _operator_usages=tuple(collector.operator_usages),
            _confidence=confidence,
        )
        self._inference_cache[cache_key] = result
        return result

    def required_methods(
        self,
        func_ast: ast.FunctionDef,
        param_name: str,
    ) -> Set[str]:
        """Return the set of method names used on a parameter."""
        protocol = self.infer_protocol(func_ast, param_name)
        return set(protocol.required_methods)

    def required_attributes(
        self,
        func_ast: ast.FunctionDef,
        param_name: str,
    ) -> Set[str]:
        """Return the set of attribute names accessed on a parameter."""
        protocol = self.infer_protocol(func_ast, param_name)
        return set(protocol.required_attributes)

    # -- Batch inference ----------------------------------------------------

    def infer_all_params(
        self,
        func_ast: ast.FunctionDef,
    ) -> Dict[str, InferredProtocol]:
        """Infer protocols for all parameters of a function."""
        results: Dict[str, InferredProtocol] = {}
        for arg in func_ast.args.args:
            if arg.arg in ("self", "cls"):
                continue
            results[arg.arg] = self.infer_protocol(func_ast, arg.arg)
        return results

    def clear_cache(self) -> None:
        """Clear the inference cache."""
        self._inference_cache.clear()
