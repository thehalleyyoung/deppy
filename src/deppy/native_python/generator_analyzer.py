"""Generator and iterator protocol analysis.

Analyzes Python generator functions to determine:
- Yield types (what values are yielded)
- Send types (what values can be sent into the generator)
- Return types (the value of the StopIteration)
- Yield-from delegation

In the sheaf-descent framework, generators create a three-part protocol:
yield type, send type, and return type, corresponding to the
Generator[YieldType, SendType, ReturnType] protocol.
"""

from __future__ import annotations

import ast
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
# Yield information
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class YieldInfo:
    """Information about a single yield expression.

    Attributes:
        _value_text: Text of the yielded value expression.
        _line: Source line number.
        _is_yield_from: Whether this is a yield-from expression.
        _delegate_text: The delegate iterable (for yield-from).
        _in_conditional: Whether the yield is inside a conditional.
        _in_loop: Whether the yield is inside a loop.
        _in_try: Whether the yield is inside a try block.
    """

    _value_text: Optional[str] = None
    _line: int = 0
    _is_yield_from: bool = False
    _delegate_text: Optional[str] = None
    _in_conditional: bool = False
    _in_loop: bool = False
    _in_try: bool = False

    @property
    def value_text(self) -> Optional[str]:
        return self._value_text

    @property
    def line(self) -> int:
        return self._line

    @property
    def is_yield_from(self) -> bool:
        return self._is_yield_from

    @property
    def delegate_text(self) -> Optional[str]:
        return self._delegate_text

    @property
    def is_bare_yield(self) -> bool:
        return self._value_text is None and not self._is_yield_from


# ---------------------------------------------------------------------------
# Send information
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SendInfo:
    """Information about how sent values are used in a generator.

    Attributes:
        _variable_name: Variable that receives the sent value.
        _line: Line where the sent value is captured.
        _is_used: Whether the sent value is actually used.
        _usage_context: Description of how the sent value is used.
    """

    _variable_name: Optional[str] = None
    _line: int = 0
    _is_used: bool = False
    _usage_context: Optional[str] = None

    @property
    def variable_name(self) -> Optional[str]:
        return self._variable_name

    @property
    def is_used(self) -> bool:
        return self._is_used


# ---------------------------------------------------------------------------
# Generator info
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class GeneratorInfo:
    """Complete analysis result for a generator function.

    Attributes:
        _func_name: Name of the generator function.
        _is_generator: Whether the function is a generator (has yield).
        _is_async_generator: Whether it's an async generator (async + yield).
        _yields: All yield expressions found.
        _sends: All places where sent values are captured.
        _return_texts: Text of all return value expressions.
        _has_yield_from: Whether the generator uses yield-from.
        _yield_from_delegates: Names of delegated generators.
        _has_return_value: Whether any return has a value.
        _total_yield_count: Total number of yield expressions.
        _is_coroutine: Whether this is a coroutine (async, no yield).
    """

    _func_name: str
    _is_generator: bool = False
    _is_async_generator: bool = False
    _yields: Tuple[YieldInfo, ...] = ()
    _sends: Tuple[SendInfo, ...] = ()
    _return_texts: Tuple[Optional[str], ...] = ()
    _has_yield_from: bool = False
    _yield_from_delegates: Tuple[str, ...] = ()
    _has_return_value: bool = False
    _total_yield_count: int = 0
    _is_coroutine: bool = False

    @property
    def func_name(self) -> str:
        return self._func_name

    @property
    def is_generator(self) -> bool:
        return self._is_generator

    @property
    def is_async_generator(self) -> bool:
        return self._is_async_generator

    @property
    def yields(self) -> Tuple[YieldInfo, ...]:
        return self._yields

    @property
    def sends(self) -> Tuple[SendInfo, ...]:
        return self._sends

    @property
    def has_yield_from(self) -> bool:
        return self._has_yield_from

    @property
    def has_return_value(self) -> bool:
        return self._has_return_value

    @property
    def total_yield_count(self) -> int:
        return self._total_yield_count

    @property
    def yield_value_texts(self) -> List[Optional[str]]:
        return [y.value_text for y in self._yields]

    @property
    def accepts_send(self) -> bool:
        return any(s.is_used for s in self._sends)


# ---------------------------------------------------------------------------
# AST visitor for generators
# ---------------------------------------------------------------------------

class _GeneratorVisitor(ast.NodeVisitor):
    """Walk a function body and collect yield/send/return information."""

    def __init__(self) -> None:
        self._yields: List[YieldInfo] = []
        self._sends: List[SendInfo] = []
        self._returns: List[Optional[str]] = []
        self._in_loop = False
        self._in_conditional = False
        self._in_try = False
        self._has_yield = False

    @property
    def yields(self) -> List[YieldInfo]:
        return list(self._yields)

    @property
    def sends(self) -> List[SendInfo]:
        return list(self._sends)

    @property
    def returns(self) -> List[Optional[str]]:
        return list(self._returns)

    @property
    def has_yield(self) -> bool:
        return self._has_yield

    def visit_Yield(self, node: ast.Yield) -> None:
        self._has_yield = True
        line = getattr(node, "lineno", 0)
        value_text = ast.unparse(node.value) if node.value is not None else None

        self._yields.append(YieldInfo(
            _value_text=value_text,
            _line=line,
            _is_yield_from=False,
            _in_conditional=self._in_conditional,
            _in_loop=self._in_loop,
            _in_try=self._in_try,
        ))
        self.generic_visit(node)

    def visit_YieldFrom(self, node: ast.YieldFrom) -> None:
        self._has_yield = True
        line = getattr(node, "lineno", 0)
        delegate_text = ast.unparse(node.value)

        self._yields.append(YieldInfo(
            _value_text=None,
            _line=line,
            _is_yield_from=True,
            _delegate_text=delegate_text,
            _in_conditional=self._in_conditional,
            _in_loop=self._in_loop,
            _in_try=self._in_try,
        ))
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        # Detect: x = yield value (send pattern)
        if isinstance(node.value, ast.Yield):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    self._sends.append(SendInfo(
                        _variable_name=target.id,
                        _line=getattr(node, "lineno", 0),
                        _is_used=True,
                        _usage_context="assignment",
                    ))
        # Detect: x = yield from gen (send delegation)
        elif isinstance(node.value, ast.YieldFrom):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    self._sends.append(SendInfo(
                        _variable_name=target.id,
                        _line=getattr(node, "lineno", 0),
                        _is_used=True,
                        _usage_context="yield_from_return",
                    ))
        self.generic_visit(node)

    def visit_Return(self, node: ast.Return) -> None:
        if node.value is not None:
            self._returns.append(ast.unparse(node.value))
        else:
            self._returns.append(None)

    def visit_For(self, node: ast.For) -> None:
        prev = self._in_loop
        self._in_loop = True
        self.generic_visit(node)
        self._in_loop = prev

    def visit_While(self, node: ast.While) -> None:
        prev = self._in_loop
        self._in_loop = True
        self.generic_visit(node)
        self._in_loop = prev

    def visit_If(self, node: ast.If) -> None:
        prev = self._in_conditional
        self._in_conditional = True
        self.generic_visit(node)
        self._in_conditional = prev

    def visit_Try(self, node: ast.Try) -> None:
        prev = self._in_try
        self._in_try = True
        self.generic_visit(node)
        self._in_try = prev

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        pass  # Don't descend into nested functions

    visit_AsyncFunctionDef = visit_FunctionDef


# ---------------------------------------------------------------------------
# GeneratorAnalyzer
# ---------------------------------------------------------------------------

class GeneratorAnalyzer:
    """Analyze generator and iterator protocols in Python functions.

    Detects yield/yield-from, tracks sent values, and determines
    the Generator[Y, S, R] type triple.
    """

    def __init__(self) -> None:
        self._analysis_cache: Dict[str, GeneratorInfo] = {}

    # -- Core analysis ------------------------------------------------------

    def analyze_generator(
        self,
        func_ast: ast.FunctionDef,
    ) -> GeneratorInfo:
        """Analyze a function for generator protocol.

        Returns a GeneratorInfo with yield types, send types, and return type.
        """
        func_name = func_ast.name
        if func_name in self._analysis_cache:
            return self._analysis_cache[func_name]

        is_async = isinstance(func_ast, ast.AsyncFunctionDef)

        visitor = _GeneratorVisitor()
        for stmt in func_ast.body:
            visitor.visit(stmt)

        is_generator = visitor.has_yield
        is_async_generator = is_async and is_generator
        is_coroutine = is_async and not is_generator

        # Collect yield-from delegates
        yield_from_delegates: List[str] = []
        has_yield_from = False
        for y in visitor.yields:
            if y.is_yield_from:
                has_yield_from = True
                if y.delegate_text:
                    yield_from_delegates.append(y.delegate_text)

        # Check return values
        has_return_value = any(r is not None for r in visitor.returns)

        result = GeneratorInfo(
            _func_name=func_name,
            _is_generator=is_generator,
            _is_async_generator=is_async_generator,
            _yields=tuple(visitor.yields),
            _sends=tuple(visitor.sends),
            _return_texts=tuple(visitor.returns),
            _has_yield_from=has_yield_from,
            _yield_from_delegates=tuple(yield_from_delegates),
            _has_return_value=has_return_value,
            _total_yield_count=len(visitor.yields),
            _is_coroutine=is_coroutine,
        )
        self._analysis_cache[func_name] = result
        return result

    def yield_types(
        self,
        func_ast: ast.FunctionDef,
    ) -> List[str]:
        """Return the text of all yield value expressions.

        Bare yields produce 'None', yield-from produces the delegate name.
        """
        info = self.analyze_generator(func_ast)
        types: List[str] = []
        for y in info.yields:
            if y.is_yield_from:
                types.append(f"yield_from({y.delegate_text})")
            elif y.value_text is not None:
                types.append(y.value_text)
            else:
                types.append("None")
        return types

    def is_generator(self, func_ast: ast.FunctionDef) -> bool:
        """Check if a function is a generator."""
        info = self.analyze_generator(func_ast)
        return info.is_generator

    def is_async_generator(self, func_ast: ast.FunctionDef) -> bool:
        """Check if a function is an async generator."""
        info = self.analyze_generator(func_ast)
        return info.is_async_generator

    # -- Batch analysis -----------------------------------------------------

    def analyze_all_in_module(
        self,
        module_ast: ast.Module,
    ) -> Dict[str, GeneratorInfo]:
        """Analyze all functions in a module for generator protocol."""
        results: Dict[str, GeneratorInfo] = {}

        class FuncVisitor(ast.NodeVisitor):
            def visit_FunctionDef(inner_self, node: ast.FunctionDef) -> None:
                results[node.name] = self.analyze_generator(node)
                inner_self.generic_visit(node)

            def visit_AsyncFunctionDef(inner_self, node: ast.AsyncFunctionDef) -> None:
                results[node.name] = self.analyze_generator(node)
                inner_self.generic_visit(node)

        FuncVisitor().visit(module_ast)
        return results

    def find_generators(
        self,
        module_ast: ast.Module,
    ) -> List[str]:
        """Find all generator function names in a module."""
        all_info = self.analyze_all_in_module(module_ast)
        return [name for name, info in all_info.items() if info.is_generator]

    def clear_cache(self) -> None:
        """Clear the analysis cache."""
        self._analysis_cache.clear()
