"""Exception flow analysis for Python functions.

Tracks which exceptions can be raised, which are caught by handlers,
and the propagation paths of uncaught exceptions.  In the sheaf-descent
framework, exception paths create ERROR sites whose viability predicates
depend on upstream argument sites.
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
# Handler information
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class HandlerInfo:
    """Information about a single except clause.

    Attributes:
        _exception_types: Caught exception type names.
        _alias: The 'as' variable name (if present).
        _line: Line number of the except clause.
        _is_bare: Whether this is a bare 'except:' clause.
        _handler_body_lines: Range of lines in the handler body.
        _reraises: Whether the handler re-raises the exception.
        _transforms_to: If the handler raises a different exception, its name.
    """

    _exception_types: Tuple[str, ...] = ()
    _alias: Optional[str] = None
    _line: int = 0
    _is_bare: bool = False
    _handler_body_lines: Tuple[int, int] = (0, 0)
    _reraises: bool = False
    _transforms_to: Optional[str] = None

    @property
    def exception_types(self) -> Tuple[str, ...]:
        return self._exception_types

    @property
    def alias(self) -> Optional[str]:
        return self._alias

    @property
    def line(self) -> int:
        return self._line

    @property
    def is_bare(self) -> bool:
        return self._is_bare

    @property
    def reraises(self) -> bool:
        return self._reraises

    @property
    def transforms_to(self) -> Optional[str]:
        return self._transforms_to

    @property
    def catches_all(self) -> bool:
        return self._is_bare or "Exception" in self._exception_types or "BaseException" in self._exception_types


# ---------------------------------------------------------------------------
# Raise information
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RaiseInfo:
    """Information about a raise statement.

    Attributes:
        _exception_type: Name of the raised exception type.
        _line: Line number.
        _is_reraise: Whether this is a bare 'raise' (re-raise).
        _is_conditional: Whether the raise is inside a conditional.
        _condition_text: Text of the guarding condition (if conditional).
        _from_exception: The 'from' clause exception type (if present).
    """

    _exception_type: Optional[str] = None
    _line: int = 0
    _is_reraise: bool = False
    _is_conditional: bool = False
    _condition_text: Optional[str] = None
    _from_exception: Optional[str] = None

    @property
    def exception_type(self) -> Optional[str]:
        return self._exception_type

    @property
    def line(self) -> int:
        return self._line

    @property
    def is_reraise(self) -> bool:
        return self._is_reraise

    @property
    def is_conditional(self) -> bool:
        return self._is_conditional


# ---------------------------------------------------------------------------
# Exception flow result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ExceptionFlowResult:
    """Complete exception flow analysis for a function.

    Attributes:
        _func_name: Name of the analyzed function.
        _raised_exceptions: All exceptions explicitly raised.
        _caught_exceptions: All exceptions caught by handlers.
        _uncaught_exceptions: Exceptions that propagate out of the function.
        _handlers: All exception handlers in the function.
        _raise_points: All raise statements.
        _implicit_exceptions: Exceptions that may be raised implicitly.
        _has_finally: Whether the function has a finally block.
        _suppresses_all: Whether a bare except suppresses all exceptions.
    """

    _func_name: str
    _raised_exceptions: FrozenSet[str] = frozenset()
    _caught_exceptions: FrozenSet[str] = frozenset()
    _uncaught_exceptions: FrozenSet[str] = frozenset()
    _handlers: Tuple[HandlerInfo, ...] = ()
    _raise_points: Tuple[RaiseInfo, ...] = ()
    _implicit_exceptions: FrozenSet[str] = frozenset()
    _has_finally: bool = False
    _suppresses_all: bool = False

    @property
    def func_name(self) -> str:
        return self._func_name

    @property
    def raised_exceptions(self) -> FrozenSet[str]:
        return self._raised_exceptions

    @property
    def caught_exceptions(self) -> FrozenSet[str]:
        return self._caught_exceptions

    @property
    def uncaught_exceptions(self) -> FrozenSet[str]:
        return self._uncaught_exceptions

    @property
    def handlers(self) -> Tuple[HandlerInfo, ...]:
        return self._handlers

    @property
    def raise_points(self) -> Tuple[RaiseInfo, ...]:
        return self._raise_points

    @property
    def has_finally(self) -> bool:
        return self._has_finally

    @property
    def is_exception_safe(self) -> bool:
        """True if no exceptions can propagate out."""
        return len(self._uncaught_exceptions) == 0 and not any(
            r.is_reraise for r in self._raise_points
        )

    @property
    def all_exception_types(self) -> FrozenSet[str]:
        """Union of all raised, caught, and implicit exception types."""
        return self._raised_exceptions | self._caught_exceptions | self._implicit_exceptions


# ---------------------------------------------------------------------------
# Implicit exception inference
# ---------------------------------------------------------------------------

# Operations and their potential implicit exceptions
_IMPLICIT_EXCEPTIONS: Dict[str, List[str]] = {
    "Subscript": ["IndexError", "KeyError"],
    "Div": ["ZeroDivisionError"],
    "FloorDiv": ["ZeroDivisionError"],
    "Mod": ["ZeroDivisionError"],
    "Attribute": ["AttributeError"],
    "Call": ["TypeError"],
    "Assert": ["AssertionError"],
    "Import": ["ImportError", "ModuleNotFoundError"],
    "Unpack": ["ValueError"],
    "StopIteration": ["StopIteration"],
    "FileOpen": ["FileNotFoundError", "PermissionError", "OSError"],
    "Conversion": ["ValueError", "TypeError"],
    "KeyLookup": ["KeyError"],
}


class _ImplicitExceptionDetector(ast.NodeVisitor):
    """Detect operations that can raise implicit exceptions."""

    def __init__(self) -> None:
        self._implicit: Set[str] = set()

    @property
    def implicit_exceptions(self) -> Set[str]:
        return set(self._implicit)

    def visit_Subscript(self, node: ast.Subscript) -> None:
        self._implicit.update(_IMPLICIT_EXCEPTIONS["Subscript"])
        self.generic_visit(node)

    def visit_BinOp(self, node: ast.BinOp) -> None:
        if isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
            self._implicit.update(_IMPLICIT_EXCEPTIONS["Div"])
        self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        self._implicit.add("AttributeError")
        self.generic_visit(node)

    def visit_Assert(self, node: ast.Assert) -> None:
        self._implicit.add("AssertionError")
        self.generic_visit(node)

    def visit_Import(self, node: ast.Import) -> None:
        self._implicit.update(_IMPLICIT_EXCEPTIONS["Import"])

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        self._implicit.update(_IMPLICIT_EXCEPTIONS["Import"])

    def visit_Call(self, node: ast.Call) -> None:
        # int(), float() etc. can raise ValueError/TypeError
        if isinstance(node.func, ast.Name):
            if node.func.id in ("int", "float", "complex"):
                self._implicit.update(_IMPLICIT_EXCEPTIONS["Conversion"])
            elif node.func.id == "open":
                self._implicit.update(_IMPLICIT_EXCEPTIONS["FileOpen"])
            elif node.func.id == "next":
                self._implicit.add("StopIteration")
        self.generic_visit(node)

    def visit_For(self, node: ast.For) -> None:
        # for loops consume iterators (StopIteration is handled internally)
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        # Unpacking: a, b = x can raise ValueError
        for target in node.targets:
            if isinstance(target, (ast.Tuple, ast.List)):
                self._implicit.add("ValueError")
        self.generic_visit(node)


# ---------------------------------------------------------------------------
# Raise / handler collector
# ---------------------------------------------------------------------------

class _ExceptionFlowVisitor(ast.NodeVisitor):
    """Collect raise statements and exception handlers from a function."""

    def __init__(self) -> None:
        self._raises: List[RaiseInfo] = []
        self._handlers: List[HandlerInfo] = []
        self._has_finally = False
        self._in_try_depth = 0
        self._in_conditional = False
        self._condition_text: Optional[str] = None
        # Track which exceptions are caught at each try-depth
        self._caught_at_depth: Dict[int, Set[str]] = {}

    @property
    def raises(self) -> List[RaiseInfo]:
        return list(self._raises)

    @property
    def handlers(self) -> List[HandlerInfo]:
        return list(self._handlers)

    @property
    def has_finally(self) -> bool:
        return self._has_finally

    def visit_Try(self, node: ast.Try) -> None:
        self._in_try_depth += 1
        depth = self._in_try_depth

        # Collect handlers for this try block
        caught_here: Set[str] = set()
        for handler in node.handlers:
            handler_info = self._process_handler(handler)
            self._handlers.append(handler_info)
            caught_here.update(handler_info.exception_types)
            if handler_info.is_bare:
                caught_here.add("*")

        self._caught_at_depth[depth] = caught_here

        # Visit try body
        for stmt in node.body:
            self.visit(stmt)

        # Visit handler bodies
        for handler in node.handlers:
            for stmt in handler.body:
                self.visit(stmt)

        # Visit else body
        for stmt in node.orelse:
            self.visit(stmt)

        # Visit finally body
        if node.finalbody:
            self._has_finally = True
            for stmt in node.finalbody:
                self.visit(stmt)

        del self._caught_at_depth[depth]
        self._in_try_depth -= 1

    # Python 3.11+ TryStar
    def visit_TryStar(self, node: Any) -> None:
        # Handle ExceptionGroup syntax if present
        self._in_try_depth += 1
        for stmt in getattr(node, "body", []):
            self.visit(stmt)
        for handler in getattr(node, "handlers", []):
            handler_info = self._process_handler(handler)
            self._handlers.append(handler_info)
            for stmt in handler.body:
                self.visit(stmt)
        if getattr(node, "finalbody", None):
            self._has_finally = True
            for stmt in node.finalbody:
                self.visit(stmt)
        self._in_try_depth -= 1

    def visit_If(self, node: ast.If) -> None:
        prev_conditional = self._in_conditional
        prev_text = self._condition_text
        self._in_conditional = True
        self._condition_text = ast.unparse(node.test)
        self.generic_visit(node)
        self._in_conditional = prev_conditional
        self._condition_text = prev_text

    def visit_Raise(self, node: ast.Raise) -> None:
        line = getattr(node, "lineno", 0)

        if node.exc is None:
            # Bare raise (re-raise)
            info = RaiseInfo(
                _is_reraise=True,
                _line=line,
                _is_conditional=self._in_conditional,
                _condition_text=self._condition_text,
            )
        else:
            exc_type = self._extract_exception_type(node.exc)
            from_exc = None
            if node.cause is not None:
                from_exc = self._extract_exception_type(node.cause)

            info = RaiseInfo(
                _exception_type=exc_type,
                _line=line,
                _is_reraise=False,
                _is_conditional=self._in_conditional,
                _condition_text=self._condition_text,
                _from_exception=from_exc,
            )

        self._raises.append(info)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        pass  # Don't descend into nested functions

    visit_AsyncFunctionDef = visit_FunctionDef

    def _process_handler(self, handler: ast.ExceptHandler) -> HandlerInfo:
        """Process a single except handler clause."""
        line = getattr(handler, "lineno", 0)
        alias = handler.name

        if handler.type is None:
            return HandlerInfo(
                _is_bare=True,
                _alias=alias,
                _line=line,
                _handler_body_lines=self._body_lines(handler.body),
                _reraises=self._body_reraises(handler.body),
                _transforms_to=self._body_raises_different(handler.body),
            )

        types = self._extract_handler_types(handler.type)
        return HandlerInfo(
            _exception_types=tuple(types),
            _alias=alias,
            _line=line,
            _is_bare=False,
            _handler_body_lines=self._body_lines(handler.body),
            _reraises=self._body_reraises(handler.body),
            _transforms_to=self._body_raises_different(handler.body),
        )

    def _extract_handler_types(self, node: ast.expr) -> List[str]:
        """Extract exception type names from a handler's type expression."""
        if isinstance(node, ast.Name):
            return [node.id]
        if isinstance(node, ast.Attribute):
            return [ast.unparse(node)]
        if isinstance(node, ast.Tuple):
            types: List[str] = []
            for elt in node.elts:
                types.extend(self._extract_handler_types(elt))
            return types
        return [ast.unparse(node)]

    def _extract_exception_type(self, node: ast.expr) -> str:
        """Extract exception type name from a raise expression."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Call):
            return self._extract_exception_type(node.func)
        if isinstance(node, ast.Attribute):
            return ast.unparse(node)
        return ast.unparse(node)

    def _body_lines(self, body: List[ast.stmt]) -> Tuple[int, int]:
        if not body:
            return (0, 0)
        start = getattr(body[0], "lineno", 0)
        end = getattr(body[-1], "end_lineno", start)
        if end is None:
            end = start
        return (start, end)

    def _body_reraises(self, body: List[ast.stmt]) -> bool:
        """Check if a handler body contains a bare raise."""
        for stmt in body:
            if isinstance(stmt, ast.Raise) and stmt.exc is None:
                return True
        return False

    def _body_raises_different(
        self, body: List[ast.stmt]
    ) -> Optional[str]:
        """Check if handler raises a different exception."""
        for stmt in body:
            if isinstance(stmt, ast.Raise) and stmt.exc is not None:
                return self._extract_exception_type(stmt.exc)
        return None


# ---------------------------------------------------------------------------
# ExceptionAnalyzer
# ---------------------------------------------------------------------------

class ExceptionAnalyzer:
    """Analyze exception flow in Python functions.

    Tracks which exceptions can be raised, which are caught, and which
    propagate out of the function.  Also detects implicit exceptions
    from operations like subscript access, division, etc.
    """

    def __init__(self, *, include_implicit: bool = True) -> None:
        self._include_implicit = include_implicit
        self._analysis_cache: Dict[str, ExceptionFlowResult] = {}

    # -- Core analysis ------------------------------------------------------

    def analyze(
        self,
        func_ast: ast.FunctionDef,
    ) -> ExceptionFlowResult:
        """Perform complete exception flow analysis on a function."""
        func_name = func_ast.name

        if func_name in self._analysis_cache:
            return self._analysis_cache[func_name]

        # Collect raises and handlers
        visitor = _ExceptionFlowVisitor()
        for stmt in func_ast.body:
            visitor.visit(stmt)

        # Collect implicit exceptions
        implicit: Set[str] = set()
        if self._include_implicit:
            detector = _ImplicitExceptionDetector()
            for stmt in func_ast.body:
                detector.visit(stmt)
            implicit = detector.implicit_exceptions

        # Compute raised, caught, uncaught
        raised: Set[str] = set()
        for info in visitor.raises:
            if info.exception_type:
                raised.add(info.exception_type)

        caught: Set[str] = set()
        catches_all = False
        for handler in visitor.handlers:
            caught.update(handler.exception_types)
            if handler.catches_all:
                catches_all = True

        # Uncaught = (raised + implicit) - caught
        all_possible = raised | implicit
        if catches_all:
            uncaught: Set[str] = set()
            # Re-raised exceptions still propagate
            for r in visitor.raises:
                if r.is_reraise:
                    uncaught.update(caught)
            # Transformed exceptions propagate
            for h in visitor.handlers:
                if h.transforms_to:
                    uncaught.add(h.transforms_to)
        else:
            uncaught = set()
            for exc in all_possible:
                if not self._is_caught(exc, visitor.handlers):
                    uncaught.add(exc)
            # Re-raised exceptions
            for h in visitor.handlers:
                if h.reraises:
                    uncaught.update(h.exception_types)
                if h.transforms_to:
                    uncaught.add(h.transforms_to)

        result = ExceptionFlowResult(
            _func_name=func_name,
            _raised_exceptions=frozenset(raised),
            _caught_exceptions=frozenset(caught),
            _uncaught_exceptions=frozenset(uncaught),
            _handlers=tuple(visitor.handlers),
            _raise_points=tuple(visitor.raises),
            _implicit_exceptions=frozenset(implicit),
            _has_finally=visitor.has_finally,
            _suppresses_all=catches_all and not any(
                h.reraises for h in visitor.handlers
            ),
        )
        self._analysis_cache[func_name] = result
        return result

    def uncaught_exceptions(
        self,
        func_ast: ast.FunctionDef,
    ) -> Set[str]:
        """Return the set of exception types that can propagate out."""
        result = self.analyze(func_ast)
        return set(result.uncaught_exceptions)

    def exception_handlers(
        self,
        func_ast: ast.FunctionDef,
    ) -> List[HandlerInfo]:
        """Return all exception handlers in the function."""
        result = self.analyze(func_ast)
        return list(result.handlers)

    # -- Internal -----------------------------------------------------------

    def _is_caught(
        self,
        exception_type: str,
        handlers: List[HandlerInfo],
    ) -> bool:
        """Check if an exception type is caught by any handler."""
        for handler in handlers:
            if handler.is_bare:
                return True
            if exception_type in handler.exception_types:
                return True
            # Check inheritance (simplified: just known base classes)
            for caught_type in handler.exception_types:
                if self._is_subexception(exception_type, caught_type):
                    return True
        return False

    def _is_subexception(self, child: str, parent: str) -> bool:
        """Simplified check for exception inheritance."""
        hierarchy: Dict[str, Set[str]] = {
            "Exception": {
                "ValueError", "TypeError", "KeyError", "IndexError",
                "AttributeError", "RuntimeError", "OSError",
                "IOError", "FileNotFoundError", "PermissionError",
                "StopIteration", "ZeroDivisionError", "AssertionError",
                "ImportError", "ModuleNotFoundError", "NameError",
                "NotImplementedError", "OverflowError", "RecursionError",
                "UnicodeError", "UnicodeDecodeError", "UnicodeEncodeError",
                "LookupError", "ArithmeticError",
            },
            "BaseException": {"Exception", "KeyboardInterrupt", "SystemExit"},
            "LookupError": {"KeyError", "IndexError"},
            "ArithmeticError": {"ZeroDivisionError", "OverflowError"},
            "OSError": {"FileNotFoundError", "PermissionError", "IOError"},
            "ImportError": {"ModuleNotFoundError"},
            "UnicodeError": {"UnicodeDecodeError", "UnicodeEncodeError"},
        }

        if child == parent:
            return True

        children = hierarchy.get(parent, set())
        if child in children:
            return True

        # Transitive check
        for c in children:
            if self._is_subexception(child, c):
                return True

        return False

    def clear_cache(self) -> None:
        """Clear the analysis cache."""
        self._analysis_cache.clear()
