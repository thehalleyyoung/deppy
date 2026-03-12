"""Exception harvester -- extract exception-guarded regions from Python AST.

Walks a Python AST and identifies try/except regions, mapping guarded
statement blocks to their caught exception types and handler actions.
Each region is recorded as a frozen ``ExceptionRegion`` dataclass.
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
from deppy.static_analysis.observation_sites import SourceSpan


# ===================================================================
#  Handler action classification
# ===================================================================

class HandlerAction(enum.Enum):
    """What the exception handler does."""
    RERAISE = "reraise"
    SUPPRESS = "suppress"
    LOG = "log"
    RETURN_DEFAULT = "return_default"
    RAISE_DIFFERENT = "raise_different"
    FALLBACK = "fallback"
    PASS = "pass"
    ASSIGN = "assign"
    BREAK = "break"
    CONTINUE = "continue"


class RegionKind(enum.Enum):
    """The kind of exception-handling region."""
    TRY_EXCEPT = "try_except"
    TRY_EXCEPT_ELSE = "try_except_else"
    TRY_FINALLY = "try_finally"
    TRY_EXCEPT_FINALLY = "try_except_finally"
    CONTEXT_MANAGER = "context_manager"
    EXCEPT_STAR = "except_star"


# ===================================================================
#  ExceptionRegion dataclass
# ===================================================================

@dataclass(frozen=True)
class ExceptionRegion:
    """An exception-guarded region extracted from the AST.

    Attributes:
        guarded_statements: Number of statements in the try body.
        caught_exceptions: Tuple of exception type names caught by handlers.
        handler_actions: Tuple of actions taken by each handler.
        region_kind: The kind of try construct.
        source_span: Source location of the try block.
        trust_level: Provenance trust.
        enclosing_function: Name of the enclosing function.
        has_else: Whether there is an else clause.
        has_finally: Whether there is a finally clause.
        handler_spans: Source spans for each handler.
        finally_span: Source span for the finally clause, if any.
        handler_variables: Tuple of bound exception variable names per handler.
        guarded_calls: Names of functions called in the try body.
        nesting_depth: How deeply nested this try is within other try blocks.
        is_bare_except: Whether any handler is a bare ``except:`` (no type).
        guarded_line_range: (start_line, end_line) of the try body.
    """
    guarded_statements: int
    caught_exceptions: Tuple[str, ...] = ()
    handler_actions: Tuple[HandlerAction, ...] = ()
    region_kind: RegionKind = RegionKind.TRY_EXCEPT
    source_span: Optional[SourceSpan] = None
    trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO
    enclosing_function: Optional[str] = None
    has_else: bool = False
    has_finally: bool = False
    handler_spans: Tuple[Optional[SourceSpan], ...] = ()
    finally_span: Optional[SourceSpan] = None
    handler_variables: Tuple[Optional[str], ...] = ()
    guarded_calls: Tuple[str, ...] = ()
    nesting_depth: int = 0
    is_bare_except: bool = False
    guarded_line_range: Optional[Tuple[int, int]] = None


# ===================================================================
#  Helpers
# ===================================================================

def _extract_type_name(node: ast.expr) -> Optional[str]:
    """Extract exception type name from AST."""
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
            name = _extract_type_name(elt)
            if name is not None:
                parts.append(name)
        return ", ".join(parts) if parts else None
    return None


def _classify_handler_action(handler: ast.ExceptHandler) -> HandlerAction:
    """Classify what an exception handler does based on its body."""
    if not handler.body:
        return HandlerAction.PASS

    # Single statement analysis
    first = handler.body[0]

    # pass
    if isinstance(first, ast.Pass):
        return HandlerAction.PASS

    # raise (bare) -> reraise
    if isinstance(first, ast.Raise) and first.exc is None:
        return HandlerAction.RERAISE

    # raise OtherException(...) -> raise_different
    if isinstance(first, ast.Raise) and first.exc is not None:
        return HandlerAction.RAISE_DIFFERENT

    # return ... -> return_default
    if isinstance(first, ast.Return):
        return HandlerAction.RETURN_DEFAULT

    # break
    if isinstance(first, ast.Break):
        return HandlerAction.BREAK

    # continue
    if isinstance(first, ast.Continue):
        return HandlerAction.CONTINUE

    # Check for logging calls
    for stmt in handler.body:
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
            call = stmt.value
            func_name = _get_call_name(call)
            if func_name is not None and any(
                log_name in func_name.lower()
                for log_name in ("log", "warning", "error", "debug", "info", "critical", "print")
            ):
                return HandlerAction.LOG

    # Assignment
    for stmt in handler.body:
        if isinstance(stmt, ast.Assign):
            return HandlerAction.ASSIGN

    return HandlerAction.FALLBACK


def _get_call_name(call: ast.Call) -> Optional[str]:
    """Get the function name from a Call node."""
    if isinstance(call.func, ast.Name):
        return call.func.id
    if isinstance(call.func, ast.Attribute):
        return call.func.attr
    return None


def _extract_guarded_calls(body: List[ast.stmt]) -> Tuple[str, ...]:
    """Extract names of functions called within the try body."""
    calls: List[str] = []
    for stmt in body:
        for node in ast.walk(stmt):
            if isinstance(node, ast.Call):
                name = _get_call_name(node)
                if name is not None:
                    calls.append(name)
    return tuple(calls)


def _line_range(body: List[ast.stmt]) -> Optional[Tuple[int, int]]:
    """Get the line range of a statement list."""
    if not body:
        return None
    start = getattr(body[0], "lineno", 0)
    end = start
    for stmt in body:
        end_line = getattr(stmt, "end_lineno", None) or getattr(stmt, "lineno", 0)
        end = max(end, end_line)
    return (start, end)


# ===================================================================
#  ExceptionHarvester visitor
# ===================================================================

class ExceptionHarvester(ast.NodeVisitor):
    """AST visitor that extracts exception-guarded regions.

    Handles:
    - try/except blocks
    - try/except/else blocks
    - try/finally blocks
    - try/except/finally blocks
    - Nested try blocks
    - with/as context managers (as implicit exception handling)
    - except* (Python 3.11+ ExceptionGroup)

    Usage::

        harvester = ExceptionHarvester(file="example.py")
        harvester.visit(tree)
        regions = harvester.regions
    """

    def __init__(self, file: str = "<unknown>") -> None:
        self._file = file
        self._regions: List[ExceptionRegion] = []
        self._function_stack: List[str] = []
        self._nesting_depth: int = 0

    @property
    def regions(self) -> List[ExceptionRegion]:
        return list(self._regions)

    @property
    def _current_function(self) -> Optional[str]:
        return self._function_stack[-1] if self._function_stack else None

    def _span(self, node: ast.AST) -> SourceSpan:
        return SourceSpan.from_ast(node, self._file)

    # -- Scope --

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

    # -- Try/Except --

    def visit_Try(self, node: ast.Try) -> None:
        self._harvest_try(node)
        self._nesting_depth += 1
        self.generic_visit(node)
        self._nesting_depth -= 1

    def visit_TryStar(self, node: ast.AST) -> None:
        """Handle Python 3.11+ try/except* (ExceptionGroup)."""
        self._harvest_try(node, is_except_star=True)
        self._nesting_depth += 1
        self.generic_visit(node)
        self._nesting_depth -= 1

    def _harvest_try(
        self,
        node: ast.AST,
        *,
        is_except_star: bool = False,
    ) -> None:
        """Extract an ExceptionRegion from a try node."""
        body = getattr(node, "body", [])
        handlers = getattr(node, "handlers", [])
        orelse = getattr(node, "orelse", [])
        finalbody = getattr(node, "finalbody", [])

        # Classify region kind
        has_except = len(handlers) > 0
        has_else = len(orelse) > 0
        has_finally = len(finalbody) > 0

        if is_except_star:
            kind = RegionKind.EXCEPT_STAR
        elif has_except and has_finally:
            kind = RegionKind.TRY_EXCEPT_FINALLY
        elif has_except and has_else:
            kind = RegionKind.TRY_EXCEPT_ELSE
        elif has_except:
            kind = RegionKind.TRY_EXCEPT
        elif has_finally:
            kind = RegionKind.TRY_FINALLY
        else:
            kind = RegionKind.TRY_EXCEPT

        # Extract caught exception types
        caught: List[str] = []
        actions: List[HandlerAction] = []
        h_spans: List[Optional[SourceSpan]] = []
        h_vars: List[Optional[str]] = []
        is_bare = False

        for handler in handlers:
            if not isinstance(handler, ast.ExceptHandler):
                continue
            if handler.type is not None:
                type_name = _extract_type_name(handler.type)
                caught.append(type_name or "Unknown")
            else:
                caught.append("BaseException")
                is_bare = True

            actions.append(_classify_handler_action(handler))
            h_spans.append(self._span(handler))
            h_vars.append(handler.name)

        guarded_calls = _extract_guarded_calls(body)
        line_range = _line_range(body)
        finally_sp = self._span(finalbody[0]) if finalbody else None

        self._regions.append(ExceptionRegion(
            guarded_statements=len(body),
            caught_exceptions=tuple(caught),
            handler_actions=tuple(actions),
            region_kind=kind,
            source_span=self._span(node),
            trust_level=TrustLevel.TRUSTED_AUTO,
            enclosing_function=self._current_function,
            has_else=has_else,
            has_finally=has_finally,
            handler_spans=tuple(h_spans),
            finally_span=finally_sp,
            handler_variables=tuple(h_vars),
            guarded_calls=guarded_calls,
            nesting_depth=self._nesting_depth,
            is_bare_except=is_bare,
            guarded_line_range=line_range,
        ))

    # -- With statements (context managers as implicit exception handling) --

    def visit_With(self, node: ast.With) -> None:
        self._harvest_with(node)
        self.generic_visit(node)

    def visit_AsyncWith(self, node: ast.AsyncWith) -> None:
        self._harvest_with(node)
        self.generic_visit(node)

    def _harvest_with(self, node: Union[ast.With, ast.AsyncWith]) -> None:
        """Extract an ExceptionRegion from a context manager."""
        guarded_calls = _extract_guarded_calls(node.body)
        line_range = _line_range(node.body)

        # Extract context manager names
        cm_names: List[str] = []
        for item in node.items:
            if isinstance(item.context_expr, ast.Call):
                name = _get_call_name(item.context_expr)
                if name is not None:
                    cm_names.append(name)
            elif isinstance(item.context_expr, ast.Name):
                cm_names.append(item.context_expr.id)

        self._regions.append(ExceptionRegion(
            guarded_statements=len(node.body),
            caught_exceptions=tuple(cm_names) if cm_names else ("contextmanager",),
            handler_actions=(HandlerAction.SUPPRESS,),
            region_kind=RegionKind.CONTEXT_MANAGER,
            source_span=self._span(node),
            trust_level=TrustLevel.TRUSTED_AUTO,
            enclosing_function=self._current_function,
            has_else=False,
            has_finally=True,
            guarded_calls=guarded_calls,
            nesting_depth=self._nesting_depth,
            guarded_line_range=line_range,
        ))


# ===================================================================
#  Convenience function
# ===================================================================

def harvest_exception_regions(
    ast_tree: ast.AST,
    *,
    file: str = "<unknown>",
) -> List[ExceptionRegion]:
    """Extract all exception-guarded regions from a Python AST.

    Args:
        ast_tree: The parsed AST (typically from ``ast.parse``).
        file: Source file name for provenance.

    Returns:
        A list of ``ExceptionRegion`` facts.
    """
    harvester = ExceptionHarvester(file=file)
    harvester.visit(ast_tree)
    return harvester.regions


# ===================================================================
#  Filtering / query utilities
# ===================================================================

def filter_by_exception(
    regions: List[ExceptionRegion],
    exception_type: str,
) -> List[ExceptionRegion]:
    """Return regions that catch a specific exception type."""
    return [r for r in regions if exception_type in r.caught_exceptions]


def filter_by_kind(
    regions: List[ExceptionRegion],
    kind: RegionKind,
) -> List[ExceptionRegion]:
    """Return regions of a specific kind."""
    return [r for r in regions if r.region_kind == kind]


def filter_by_action(
    regions: List[ExceptionRegion],
    action: HandlerAction,
) -> List[ExceptionRegion]:
    """Return regions containing a specific handler action."""
    return [r for r in regions if action in r.handler_actions]


def bare_except_regions(
    regions: List[ExceptionRegion],
) -> List[ExceptionRegion]:
    """Return regions with bare ``except:`` clauses."""
    return [r for r in regions if r.is_bare_except]


def regions_guarding_call(
    regions: List[ExceptionRegion],
    call_name: str,
) -> List[ExceptionRegion]:
    """Return regions whose try body contains a call to the given function."""
    return [r for r in regions if call_name in r.guarded_calls]


def suppressing_regions(
    regions: List[ExceptionRegion],
) -> List[ExceptionRegion]:
    """Return regions that suppress exceptions (pass handler or context manager)."""
    return [
        r for r in regions
        if HandlerAction.SUPPRESS in r.handler_actions
        or HandlerAction.PASS in r.handler_actions
    ]
