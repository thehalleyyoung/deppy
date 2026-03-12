"""Analyze wrapper chains for transparency.

A function is a "thin wrapper" if it delegates to another function while
preserving all (or most) refinements.  In sheaf-descent semantics, wrapper
transparency means the induced restriction map from the wrapper's cover
to the target's cover preserves all local section coordinates.

This module detects wrapper patterns and computes transparency chains:
if F wraps G wraps H, the chain [F, G, H] is transparent if each
wrapper preserves all refinements of its target.
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

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.interprocedural.call_graph import CallEdge, CallGraph


# ---------------------------------------------------------------------------
# Wrapper pattern data
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class WrapperPattern:
    """Description of a detected wrapper pattern.

    Attributes:
        _wrapper_name: Name of the wrapper function.
        _target_name: Name of the target function being wrapped.
        _pattern_kind: Kind of wrapper pattern detected.
        _preserves_args: Whether all arguments are passed through.
        _preserves_return: Whether the return value is passed through.
        _extra_args: Arguments added by the wrapper (not from caller).
        _dropped_args: Arguments from the caller not passed to target.
        _transforms_return: Whether the wrapper transforms the return value.
    """

    _wrapper_name: str
    _target_name: str
    _pattern_kind: str = "simple_delegate"
    _preserves_args: bool = True
    _preserves_return: bool = True
    _extra_args: Tuple[str, ...] = ()
    _dropped_args: Tuple[str, ...] = ()
    _transforms_return: bool = False

    @property
    def wrapper_name(self) -> str:
        return self._wrapper_name

    @property
    def target_name(self) -> str:
        return self._target_name

    @property
    def pattern_kind(self) -> str:
        return self._pattern_kind

    @property
    def is_transparent(self) -> bool:
        """True if the wrapper preserves all args and return."""
        return (
            self._preserves_args
            and self._preserves_return
            and not self._transforms_return
        )


@dataclass(frozen=True)
class TransparencyChainResult:
    """Result of transparency chain analysis.

    Attributes:
        _chain: Sequence of function names from outermost to innermost.
        _is_fully_transparent: Whether every link is transparent.
        _broken_links: Links where transparency is lost.
        _preserved_refinements: Refinements preserved through the chain.
        _lost_refinements: Refinements lost somewhere in the chain.
    """

    _chain: Tuple[str, ...] = ()
    _is_fully_transparent: bool = True
    _broken_links: Tuple[Tuple[str, str], ...] = ()
    _preserved_refinements: FrozenSet[str] = frozenset()
    _lost_refinements: FrozenSet[str] = frozenset()

    @property
    def chain(self) -> Tuple[str, ...]:
        return self._chain

    @property
    def is_fully_transparent(self) -> bool:
        return self._is_fully_transparent

    @property
    def depth(self) -> int:
        return len(self._chain)


# ---------------------------------------------------------------------------
# AST-level wrapper detection
# ---------------------------------------------------------------------------

def _get_function_params(func_node: ast.FunctionDef) -> List[str]:
    """Extract parameter names from a function definition."""
    params: List[str] = []
    for arg in func_node.args.args:
        params.append(arg.arg)
    return params


def _get_return_statements(func_node: ast.FunctionDef) -> List[ast.Return]:
    """Collect all return statements from a function body."""
    returns: List[ast.Return] = []

    class ReturnCollector(ast.NodeVisitor):
        def visit_Return(self, node: ast.Return) -> None:
            returns.append(node)

        def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
            pass  # Don't descend into nested functions

        visit_AsyncFunctionDef = visit_FunctionDef

    collector = ReturnCollector()
    for stmt in func_node.body:
        collector.visit(stmt)

    return returns


def _is_single_call_body(func_node: ast.FunctionDef) -> bool:
    """Check if the function body is a single call (with optional return).

    Patterns:
        def f(x): return g(x)
        def f(x): return g(x, extra=1)
        def f(x):
            result = g(x)
            return result
    """
    body = func_node.body
    # Filter out docstrings
    stmts = [
        s for s in body
        if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
                and isinstance(s.value.value, str))
    ]

    if len(stmts) == 0:
        return False

    # Pattern 1: single return with call
    if len(stmts) == 1:
        stmt = stmts[0]
        if isinstance(stmt, ast.Return) and stmt.value is not None:
            return isinstance(stmt.value, ast.Call)
        # Pattern: single expression call (no return)
        if isinstance(stmt, ast.Expr):
            return isinstance(stmt.value, ast.Call)

    # Pattern 2: assign + return
    if len(stmts) == 2:
        first, second = stmts[0], stmts[1]
        if (
            isinstance(first, ast.Assign)
            and len(first.targets) == 1
            and isinstance(first.targets[0], ast.Name)
            and isinstance(first.value, ast.Call)
            and isinstance(second, ast.Return)
            and isinstance(second.value, ast.Name)
            and second.value.id == first.targets[0].id
        ):
            return True

    return False


def _extract_call_from_body(
    func_node: ast.FunctionDef,
) -> Optional[ast.Call]:
    """Extract the single delegating call from a wrapper body."""
    body = func_node.body
    stmts = [
        s for s in body
        if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
                and isinstance(s.value.value, str))
    ]

    if len(stmts) == 1:
        stmt = stmts[0]
        if isinstance(stmt, ast.Return) and isinstance(stmt.value, ast.Call):
            return stmt.value
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
            return stmt.value

    if len(stmts) == 2:
        first = stmts[0]
        if isinstance(first, ast.Assign) and isinstance(first.value, ast.Call):
            return first.value

    return None


def _call_target_name(call_node: ast.Call) -> Optional[str]:
    """Extract the target function name from a Call node."""
    func = call_node.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        parts: List[str] = []
        current: ast.expr = func
        while isinstance(current, ast.Attribute):
            parts.append(current.attr)
            current = current.value
        if isinstance(current, ast.Name):
            parts.append(current.id)
        parts.reverse()
        return ".".join(parts)
    return None


def _check_arg_passthrough(
    func_params: List[str],
    call_node: ast.Call,
) -> Tuple[bool, Tuple[str, ...], Tuple[str, ...]]:
    """Check if call arguments are a passthrough of function parameters.

    Returns (preserves_all, extra_args, dropped_args).
    """
    call_arg_names: Set[str] = set()
    extra: List[str] = []

    for arg in call_node.args:
        if isinstance(arg, ast.Name):
            call_arg_names.add(arg.id)
        elif isinstance(arg, ast.Starred) and isinstance(arg.value, ast.Name):
            call_arg_names.add(f"*{arg.value.id}")
        else:
            extra.append("<expr>")

    for kw in call_node.keywords:
        if isinstance(kw.value, ast.Name):
            call_arg_names.add(kw.value.id)
        elif kw.arg:
            extra.append(kw.arg)

    # Check which params are passed through
    param_set = set(func_params)
    # Skip 'self' and 'cls'
    param_set.discard("self")
    param_set.discard("cls")

    passed = call_arg_names & param_set
    dropped = param_set - call_arg_names
    extra_names = call_arg_names - param_set

    preserves_all = len(dropped) == 0

    return (preserves_all, tuple(extra_names), tuple(dropped))


# ---------------------------------------------------------------------------
# WrapperAnalyzer
# ---------------------------------------------------------------------------

class WrapperAnalyzer:
    """Analyze wrapper chains for transparency.

    Detects when a function is a thin wrapper around another function,
    meaning it delegates to the target while preserving all refinements.
    Computes transparency chains through the call graph.
    """

    def __init__(self) -> None:
        self._wrapper_cache: Dict[str, Optional[WrapperPattern]] = {}

    # -- Core analysis ------------------------------------------------------

    def is_wrapper(self, func_ast: ast.FunctionDef) -> bool:
        """Detect whether a function is a thin wrapper.

        A thin wrapper has a body consisting of a single call that
        passes through its parameters.
        """
        return _is_single_call_body(func_ast)

    def wrapper_target(self, func_ast: ast.FunctionDef) -> Optional[str]:
        """Return the name of the wrapped function, or None if not a wrapper."""
        call = _extract_call_from_body(func_ast)
        if call is None:
            return None
        return _call_target_name(call)

    def analyze_wrapper(
        self, func_ast: ast.FunctionDef
    ) -> Optional[WrapperPattern]:
        """Perform full wrapper analysis on a function.

        Returns a WrapperPattern if the function is a wrapper, None otherwise.
        """
        func_name = func_ast.name

        # Check cache
        if func_name in self._wrapper_cache:
            return self._wrapper_cache[func_name]

        if not self.is_wrapper(func_ast):
            self._wrapper_cache[func_name] = None
            return None

        call = _extract_call_from_body(func_ast)
        if call is None:
            self._wrapper_cache[func_name] = None
            return None

        target_name = _call_target_name(call)
        if target_name is None:
            self._wrapper_cache[func_name] = None
            return None

        params = _get_function_params(func_ast)
        preserves_args, extra_args, dropped_args = _check_arg_passthrough(
            params, call
        )

        # Check if return value is passed through
        returns = _get_return_statements(func_ast)
        preserves_return = False
        transforms_return = False

        if len(returns) == 1 and returns[0].value is not None:
            ret_val = returns[0].value
            if isinstance(ret_val, ast.Call):
                preserves_return = True
            elif isinstance(ret_val, ast.Name):
                # Check if the name comes from the delegate call
                preserves_return = True
            else:
                transforms_return = True
        elif len(returns) == 0:
            # No return -- might be a void wrapper
            preserves_return = True

        # Determine pattern kind
        if preserves_args and preserves_return and not transforms_return:
            pattern_kind = "simple_delegate"
        elif preserves_args and transforms_return:
            pattern_kind = "transform_return"
        elif not preserves_args and preserves_return:
            pattern_kind = "modified_args"
        else:
            pattern_kind = "complex_wrapper"

        pattern = WrapperPattern(
            _wrapper_name=func_name,
            _target_name=target_name,
            _pattern_kind=pattern_kind,
            _preserves_args=preserves_args,
            _preserves_return=preserves_return,
            _extra_args=extra_args,
            _dropped_args=dropped_args,
            _transforms_return=transforms_return,
        )
        self._wrapper_cache[func_name] = pattern
        return pattern

    # -- Chain analysis -----------------------------------------------------

    def transparency_chain(
        self,
        call_graph: CallGraph,
        func: str,
        *,
        max_depth: int = 20,
    ) -> List[str]:
        """Compute the wrapper chain starting from func.

        Follows wrapper targets transitively until a non-wrapper is reached
        or the maximum depth is exceeded.

        Returns a list of function names from outermost wrapper to innermost
        target.
        """
        chain: List[str] = [func]
        visited: Set[str] = {func}
        current = func

        for _ in range(max_depth):
            func_ast = call_graph.get_function_ast(current)
            if func_ast is None:
                break

            pattern = self.analyze_wrapper(func_ast)
            if pattern is None:
                break

            target = pattern.target_name
            if target in visited:
                break  # Cycle

            chain.append(target)
            visited.add(target)
            current = target

        return chain

    def check_transparency(
        self,
        wrapper_cover: Cover,
        target_cover: Cover,
    ) -> bool:
        """Check whether a wrapper's cover is transparent w.r.t. the target.

        Transparency means:
        1. The wrapper's input boundary maps 1-1 to the target's input boundary.
        2. The target's output boundary maps 1-1 to the wrapper's output boundary.
        3. No refinements are lost in either direction.
        """
        # Check input boundary compatibility
        wrapper_inputs = {
            sid for sid in wrapper_cover.input_boundary
            if sid.kind == SiteKind.ARGUMENT_BOUNDARY
        }
        target_inputs = {
            sid for sid in target_cover.input_boundary
            if sid.kind == SiteKind.ARGUMENT_BOUNDARY
        }

        # Compare by parameter count (exact name matching is too strict)
        wrapper_param_count = len(wrapper_inputs)
        target_param_count = len(target_inputs)

        # Allow wrapper to have fewer params (e.g., dropping 'self')
        if wrapper_param_count < target_param_count - 1:
            return False

        # Check output boundary compatibility
        wrapper_outputs = {
            sid for sid in wrapper_cover.output_boundary
            if sid.kind == SiteKind.RETURN_OUTPUT_BOUNDARY
        }
        target_outputs = {
            sid for sid in target_cover.output_boundary
            if sid.kind == SiteKind.RETURN_OUTPUT_BOUNDARY
        }

        if not target_outputs:
            return True  # No outputs to check

        if not wrapper_outputs:
            return False  # Target has outputs but wrapper doesn't

        # Check that wrapper doesn't introduce new error sites not in target
        wrapper_errors = wrapper_cover.error_sites - target_cover.error_sites
        if wrapper_errors:
            return False

        return True

    def analyze_transparency_chain(
        self,
        call_graph: CallGraph,
        func: str,
        covers: Optional[Dict[str, Cover]] = None,
    ) -> TransparencyChainResult:
        """Analyze a full transparency chain with cover-level checks.

        Returns a TransparencyChainResult with detailed information about
        where transparency is preserved or lost.
        """
        chain = self.transparency_chain(call_graph, func)

        if len(chain) <= 1:
            return TransparencyChainResult(
                _chain=tuple(chain),
                _is_fully_transparent=True,
            )

        broken_links: List[Tuple[str, str]] = []
        preserved: Set[str] = set()
        lost: Set[str] = set()

        for i in range(len(chain) - 1):
            wrapper_name = chain[i]
            target_name = chain[i + 1]

            # AST-level check
            func_ast = call_graph.get_function_ast(wrapper_name)
            if func_ast is not None:
                pattern = self.analyze_wrapper(func_ast)
                if pattern is not None and not pattern.is_transparent:
                    broken_links.append((wrapper_name, target_name))
                    lost.update(pattern._dropped_args)

            # Cover-level check
            if covers is not None:
                w_cover = covers.get(wrapper_name)
                t_cover = covers.get(target_name)
                if w_cover is not None and t_cover is not None:
                    if not self.check_transparency(w_cover, t_cover):
                        if (wrapper_name, target_name) not in broken_links:
                            broken_links.append((wrapper_name, target_name))

        return TransparencyChainResult(
            _chain=tuple(chain),
            _is_fully_transparent=len(broken_links) == 0,
            _broken_links=tuple(broken_links),
            _preserved_refinements=frozenset(preserved),
            _lost_refinements=frozenset(lost),
        )

    # -- Batch analysis -----------------------------------------------------

    def find_all_wrappers(
        self,
        call_graph: CallGraph,
    ) -> Dict[str, WrapperPattern]:
        """Find all wrapper functions in the call graph."""
        wrappers: Dict[str, WrapperPattern] = {}
        for func_name, func_ast in call_graph.functions.items():
            pattern = self.analyze_wrapper(func_ast)
            if pattern is not None:
                wrappers[func_name] = pattern
        return wrappers

    def find_transparent_wrappers(
        self,
        call_graph: CallGraph,
    ) -> Dict[str, WrapperPattern]:
        """Find all transparent wrapper functions."""
        return {
            name: pattern
            for name, pattern in self.find_all_wrappers(call_graph).items()
            if pattern.is_transparent
        }

    def clear_cache(self) -> None:
        """Clear the wrapper analysis cache."""
        self._wrapper_cache.clear()
