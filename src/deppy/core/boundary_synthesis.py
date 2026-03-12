"""Input/output boundary site construction from Python AST.

Identifies function parameters as input boundary and return/raise/yield
statements as output boundary.  Produces the SiteId sets that are attached
to the Cover's ``input_boundary`` and ``output_boundary`` fields.

Key classes:

- :class:`BoundarySynthesizer` -- the top-level driver.
- :class:`InputBoundaryExtractor` -- walks the AST to find parameters.
- :class:`OutputBoundaryExtractor` -- walks the AST to find output points.
- :class:`BoundaryAnalysisResult` -- immutable result record.
"""

from __future__ import annotations

import ast
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

from deppy.core._protocols import SiteId, SiteKind
from deppy.core.site import ConcreteSite
from deppy.core.site_factory import SiteFactory


# ═══════════════════════════════════════════════════════════════════════════════
# Boundary analysis result
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ParameterInfo:
    """Information about a single function parameter.

    Attributes:
        name: Parameter name.
        index: Positional index (0-based).
        annotation: Type annotation string, if any.
        has_default: Whether the parameter has a default value.
        kind: One of 'positional', 'keyword', 'vararg', 'kwarg'.
    """

    _name: str
    _index: int
    _annotation: str = ""
    _has_default: bool = False
    _kind: str = "positional"

    @property
    def name(self) -> str:
        return self._name

    @property
    def index(self) -> int:
        return self._index

    @property
    def annotation(self) -> str:
        return self._annotation

    @property
    def has_default(self) -> bool:
        return self._has_default

    @property
    def kind(self) -> str:
        return self._kind

    def __repr__(self) -> str:
        ann = f": {self._annotation}" if self._annotation else ""
        default = " = ..." if self._has_default else ""
        return f"ParameterInfo({self._name}{ann}{default})"


@dataclass(frozen=True)
class OutputPointInfo:
    """Information about a single output point (return/raise/yield).

    Attributes:
        kind: One of 'return', 'raise', 'yield', 'yield_from'.
        line: Source line number.
        col: Source column offset.
        annotation: Return type annotation, if known.
        exception_type: For raise statements, the exception class name.
        in_try_block: Whether this output is inside a try block.
        index: Sequential index among output points.
    """

    _kind: str
    _line: int
    _col: int
    _annotation: str = ""
    _exception_type: str = ""
    _in_try_block: bool = False
    _index: int = 0

    @property
    def kind(self) -> str:
        return self._kind

    @property
    def line(self) -> int:
        return self._line

    @property
    def col(self) -> int:
        return self._col

    @property
    def annotation(self) -> str:
        return self._annotation

    @property
    def exception_type(self) -> str:
        return self._exception_type

    @property
    def in_try_block(self) -> bool:
        return self._in_try_block

    @property
    def index(self) -> int:
        return self._index

    def __repr__(self) -> str:
        loc = f"line {self._line}"
        extra = f" ({self._exception_type})" if self._exception_type else ""
        return f"OutputPointInfo({self._kind}{extra}, {loc})"


@dataclass(frozen=True)
class BoundaryAnalysisResult:
    """Result of boundary analysis for a function.

    Attributes:
        function_name: Name of the analyzed function.
        parameters: List of ParameterInfo records.
        output_points: List of OutputPointInfo records.
        input_site_ids: Set of SiteIds for the input boundary.
        output_site_ids: Set of SiteIds for the output boundary.
        return_annotation: The function's return type annotation, if any.
        is_generator: Whether the function uses yield.
        is_async: Whether the function is async.
    """

    _function_name: str
    _parameters: Tuple[ParameterInfo, ...]
    _output_points: Tuple[OutputPointInfo, ...]
    _input_site_ids: FrozenSet[SiteId]
    _output_site_ids: FrozenSet[SiteId]
    _return_annotation: str = ""
    _is_generator: bool = False
    _is_async: bool = False

    @property
    def function_name(self) -> str:
        return self._function_name

    @property
    def parameters(self) -> Tuple[ParameterInfo, ...]:
        return self._parameters

    @property
    def output_points(self) -> Tuple[OutputPointInfo, ...]:
        return self._output_points

    @property
    def input_site_ids(self) -> FrozenSet[SiteId]:
        return self._input_site_ids

    @property
    def output_site_ids(self) -> FrozenSet[SiteId]:
        return self._output_site_ids

    @property
    def return_annotation(self) -> str:
        return self._return_annotation

    @property
    def is_generator(self) -> bool:
        return self._is_generator

    @property
    def is_async(self) -> bool:
        return self._is_async

    def __repr__(self) -> str:
        return (
            f"BoundaryAnalysisResult({self._function_name}, "
            f"inputs={len(self._parameters)}, "
            f"outputs={len(self._output_points)})"
        )


# ═══════════════════════════════════════════════════════════════════════════════
# AST annotation helpers
# ═══════════════════════════════════════════════════════════════════════════════


def _annotation_to_str(node: Optional[ast.expr]) -> str:
    """Convert an AST annotation node to a string representation."""
    if node is None:
        return ""
    return ast.unparse(node)


def _exception_type_name(node: Optional[ast.expr]) -> str:
    """Extract the exception class name from a raise expression."""
    if node is None:
        return ""
    if isinstance(node, ast.Call):
        return _exception_type_name(node.func)
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return f"{_exception_type_name(node.value)}.{node.attr}"
    return ast.unparse(node)


# ═══════════════════════════════════════════════════════════════════════════════
# Input boundary extractor
# ═══════════════════════════════════════════════════════════════════════════════


class InputBoundaryExtractor(ast.NodeVisitor):
    """Extract parameter information from a function definition AST."""

    def __init__(self) -> None:
        self._parameters: List[ParameterInfo] = []

    @property
    def parameters(self) -> List[ParameterInfo]:
        return list(self._parameters)

    def extract(self, func_node: ast.FunctionDef) -> List[ParameterInfo]:
        """Extract parameters from a FunctionDef or AsyncFunctionDef."""
        self._parameters.clear()
        args = func_node.args
        idx = 0

        # Positional-only and regular positional args
        num_posonlyargs = len(args.posonlyargs) if hasattr(args, "posonlyargs") else 0
        num_defaults = len(args.defaults)
        all_positional = list(getattr(args, "posonlyargs", [])) + list(args.args)
        num_positional = len(all_positional)
        first_default_idx = num_positional - num_defaults

        for i, arg in enumerate(all_positional):
            # Skip 'self' and 'cls' for methods
            if i == 0 and arg.arg in ("self", "cls"):
                idx += 1
                continue

            has_default = i >= first_default_idx
            kind = "positional_only" if i < num_posonlyargs else "positional"
            ann = _annotation_to_str(arg.annotation)

            self._parameters.append(ParameterInfo(
                _name=arg.arg,
                _index=idx,
                _annotation=ann,
                _has_default=has_default,
                _kind=kind,
            ))
            idx += 1

        # *args
        if args.vararg:
            ann = _annotation_to_str(args.vararg.annotation)
            self._parameters.append(ParameterInfo(
                _name=args.vararg.arg,
                _index=idx,
                _annotation=ann,
                _has_default=False,
                _kind="vararg",
            ))
            idx += 1

        # Keyword-only args
        num_kw_defaults = len(args.kw_defaults)
        for i, arg in enumerate(args.kwonlyargs):
            has_default = (
                i < num_kw_defaults and args.kw_defaults[i] is not None
            )
            ann = _annotation_to_str(arg.annotation)
            self._parameters.append(ParameterInfo(
                _name=arg.arg,
                _index=idx,
                _annotation=ann,
                _has_default=has_default,
                _kind="keyword",
            ))
            idx += 1

        # **kwargs
        if args.kwarg:
            ann = _annotation_to_str(args.kwarg.annotation)
            self._parameters.append(ParameterInfo(
                _name=args.kwarg.arg,
                _index=idx,
                _annotation=ann,
                _has_default=False,
                _kind="kwarg",
            ))

        return list(self._parameters)


# ═══════════════════════════════════════════════════════════════════════════════
# Output boundary extractor
# ═══════════════════════════════════════════════════════════════════════════════


class OutputBoundaryExtractor(ast.NodeVisitor):
    """Walk a function body to find all output points."""

    def __init__(self) -> None:
        self._outputs: List[OutputPointInfo] = []
        self._try_depth: int = 0
        self._index: int = 0
        self._is_generator: bool = False
        self._return_annotation: str = ""

    @property
    def outputs(self) -> List[OutputPointInfo]:
        return list(self._outputs)

    @property
    def is_generator(self) -> bool:
        return self._is_generator

    @property
    def return_annotation(self) -> str:
        return self._return_annotation

    def extract(self, func_node: ast.FunctionDef) -> List[OutputPointInfo]:
        """Extract all output points from a function body."""
        self._outputs.clear()
        self._try_depth = 0
        self._index = 0
        self._is_generator = False
        self._return_annotation = _annotation_to_str(
            func_node.returns if hasattr(func_node, "returns") else None
        )

        # First pass: check if it's a generator
        for node in ast.walk(func_node):
            if isinstance(node, (ast.Yield, ast.YieldFrom)):
                self._is_generator = True
                break

        # Walk the body
        for stmt in func_node.body:
            self._visit_stmt(stmt)

        # If there's no explicit return and it's not a generator,
        # there's an implicit return None at the end
        has_explicit_return = any(
            o.kind == "return" for o in self._outputs
        )
        if not has_explicit_return and not self._is_generator:
            end_line = getattr(func_node, "end_lineno", func_node.lineno) or func_node.lineno
            self._outputs.append(OutputPointInfo(
                _kind="return",
                _line=end_line,
                _col=0,
                _annotation="None",
                _in_try_block=False,
                _index=self._index,
            ))
            self._index += 1

        return list(self._outputs)

    def _visit_stmt(self, node: ast.stmt) -> None:
        """Visit a statement, tracking try-block depth."""
        if isinstance(node, ast.Return):
            self._outputs.append(OutputPointInfo(
                _kind="return",
                _line=getattr(node, "lineno", 0),
                _col=getattr(node, "col_offset", 0),
                _annotation=self._return_annotation,
                _in_try_block=self._try_depth > 0,
                _index=self._index,
            ))
            self._index += 1

        elif isinstance(node, ast.Raise):
            exc_type = _exception_type_name(node.exc) if node.exc else "BaseException"
            self._outputs.append(OutputPointInfo(
                _kind="raise",
                _line=getattr(node, "lineno", 0),
                _col=getattr(node, "col_offset", 0),
                _exception_type=exc_type,
                _in_try_block=self._try_depth > 0,
                _index=self._index,
            ))
            self._index += 1

        elif isinstance(node, ast.Expr):
            if isinstance(node.value, ast.Yield):
                self._is_generator = True
                self._outputs.append(OutputPointInfo(
                    _kind="yield",
                    _line=getattr(node, "lineno", 0),
                    _col=getattr(node, "col_offset", 0),
                    _in_try_block=self._try_depth > 0,
                    _index=self._index,
                ))
                self._index += 1
            elif isinstance(node.value, ast.YieldFrom):
                self._is_generator = True
                self._outputs.append(OutputPointInfo(
                    _kind="yield_from",
                    _line=getattr(node, "lineno", 0),
                    _col=getattr(node, "col_offset", 0),
                    _in_try_block=self._try_depth > 0,
                    _index=self._index,
                ))
                self._index += 1

        elif isinstance(node, ast.Try):
            self._try_depth += 1
            for stmt in node.body:
                self._visit_stmt(stmt)
            self._try_depth -= 1
            for handler in node.handlers:
                for stmt in handler.body:
                    self._visit_stmt(stmt)
            for stmt in node.orelse:
                self._visit_stmt(stmt)
            for stmt in node.finalbody:
                self._visit_stmt(stmt)
            return  # Already visited children

        elif isinstance(node, ast.If):
            for stmt in node.body:
                self._visit_stmt(stmt)
            for stmt in node.orelse:
                self._visit_stmt(stmt)
            return

        elif isinstance(node, (ast.For, ast.While)):
            for stmt in node.body:
                self._visit_stmt(stmt)
            for stmt in node.orelse:
                self._visit_stmt(stmt)
            return

        elif isinstance(node, ast.With):
            for stmt in node.body:
                self._visit_stmt(stmt)
            return

        elif isinstance(node, ast.AsyncWith):
            for stmt in node.body:
                self._visit_stmt(stmt)
            return

        elif isinstance(node, ast.AsyncFor):
            for stmt in node.body:
                self._visit_stmt(stmt)
            for stmt in node.orelse:
                self._visit_stmt(stmt)
            return

        # Handle ast.TryStar for Python 3.11+
        elif hasattr(ast, "TryStar") and isinstance(node, ast.TryStar):
            self._try_depth += 1
            for stmt in node.body:
                self._visit_stmt(stmt)
            self._try_depth -= 1
            for handler in node.handlers:
                for stmt in handler.body:
                    self._visit_stmt(stmt)
            for stmt in node.orelse:
                self._visit_stmt(stmt)
            for stmt in node.finalbody:
                self._visit_stmt(stmt)
            return

        # For compound statements with body, recurse
        if hasattr(node, "body") and isinstance(node.body, list):
            for stmt in node.body:
                if isinstance(stmt, ast.stmt):
                    self._visit_stmt(stmt)


# ═══════════════════════════════════════════════════════════════════════════════
# Boundary synthesizer
# ═══════════════════════════════════════════════════════════════════════════════


class BoundarySynthesizer:
    """Synthesize input/output boundary sites from a function AST.

    Identifies function parameters as input boundary and return/raise/yield
    as output boundary, creating SiteId sets and ConcreteSite objects.
    """

    def __init__(
        self,
        file_path: str = "",
        site_factory: Optional[SiteFactory] = None,
    ) -> None:
        self._file_path = file_path
        self._factory = site_factory or SiteFactory(file_path=file_path)
        self._input_extractor = InputBoundaryExtractor()
        self._output_extractor = OutputBoundaryExtractor()

    # ── Main entry point ───────────────────────────────────────────────────

    def synthesize(
        self, func_ast: Union[ast.FunctionDef, ast.AsyncFunctionDef, str]
    ) -> BoundaryAnalysisResult:
        """Synthesize both input and output boundary from a function AST.

        Args:
            func_ast: Either an ``ast.FunctionDef`` / ``ast.AsyncFunctionDef``
                node or a string of Python source code.

        Returns:
            A :class:`BoundaryAnalysisResult` with all boundary information.
        """
        if isinstance(func_ast, str):
            tree = ast.parse(func_ast)
            func_node = self._find_function(tree)
            if func_node is None:
                raise ValueError("No function definition found in source")
        else:
            func_node = func_ast

        is_async = isinstance(func_node, ast.AsyncFunctionDef)
        func_name = func_node.name

        # Extract parameters
        params = self._input_extractor.extract(func_node)

        # Extract output points
        outputs = self._output_extractor.extract(func_node)
        is_generator = self._output_extractor.is_generator
        return_ann = self._output_extractor.return_annotation

        # Create input sites
        input_sites: Dict[SiteId, ConcreteSite] = {}
        for param in params:
            site = self._factory.create_argument_site(
                param_name=param.name,
                param_index=param.index,
                annotation=param.annotation or None,
                has_default=param.has_default,
                source_line=func_node.lineno,
            )
            input_sites[site.site_id] = site

        # Create output sites
        output_sites: Dict[SiteId, ConcreteSite] = {}
        for out in outputs:
            if out.kind == "return":
                site = self._factory.create_return_site(
                    return_index=out.index,
                    source_line=out.line,
                    source_col=out.col,
                )
            elif out.kind == "raise":
                site = self._factory.create_return_site(
                    return_index=out.index,
                    is_raise=True,
                    source_line=out.line,
                    source_col=out.col,
                )
            elif out.kind in ("yield", "yield_from"):
                site = self._factory.create_return_site(
                    return_index=out.index,
                    is_yield=True,
                    source_line=out.line,
                    source_col=out.col,
                )
            else:
                continue
            output_sites[site.site_id] = site

        return BoundaryAnalysisResult(
            _function_name=func_name,
            _parameters=tuple(params),
            _output_points=tuple(outputs),
            _input_site_ids=frozenset(input_sites.keys()),
            _output_site_ids=frozenset(output_sites.keys()),
            _return_annotation=return_ann,
            _is_generator=is_generator,
            _is_async=is_async,
        )

    # ── Individual boundary methods ────────────────────────────────────────

    def synthesize_input_boundary(
        self, func_ast: Union[ast.FunctionDef, ast.AsyncFunctionDef, str]
    ) -> Set[SiteId]:
        """Synthesize only the input boundary SiteIds.

        Returns:
            Set of SiteIds for function parameters.
        """
        result = self.synthesize(func_ast)
        return set(result.input_site_ids)

    def synthesize_output_boundary(
        self, func_ast: Union[ast.FunctionDef, ast.AsyncFunctionDef, str]
    ) -> Set[SiteId]:
        """Synthesize only the output boundary SiteIds.

        Returns:
            Set of SiteIds for return/raise/yield points.
        """
        result = self.synthesize(func_ast)
        return set(result.output_site_ids)

    def synthesize_sites(
        self, func_ast: Union[ast.FunctionDef, ast.AsyncFunctionDef, str]
    ) -> Tuple[List[ConcreteSite], List[ConcreteSite]]:
        """Synthesize and return actual ConcreteSite objects.

        Returns:
            A tuple of (input_sites, output_sites).
        """
        if isinstance(func_ast, str):
            tree = ast.parse(func_ast)
            func_node = self._find_function(tree)
            if func_node is None:
                raise ValueError("No function definition found in source")
        else:
            func_node = func_ast

        params = self._input_extractor.extract(func_node)
        outputs = self._output_extractor.extract(func_node)

        input_sites: List[ConcreteSite] = []
        for param in params:
            site = self._factory.create_argument_site(
                param_name=param.name,
                param_index=param.index,
                annotation=param.annotation or None,
                has_default=param.has_default,
                source_line=func_node.lineno,
            )
            input_sites.append(site)

        output_sites: List[ConcreteSite] = []
        for out in outputs:
            if out.kind == "return":
                site = self._factory.create_return_site(
                    return_index=out.index,
                    source_line=out.line,
                    source_col=out.col,
                )
            elif out.kind == "raise":
                site = self._factory.create_return_site(
                    return_index=out.index,
                    is_raise=True,
                    source_line=out.line,
                    source_col=out.col,
                )
            elif out.kind in ("yield", "yield_from"):
                site = self._factory.create_return_site(
                    return_index=out.index,
                    is_yield=True,
                    source_line=out.line,
                    source_col=out.col,
                )
            else:
                continue
            output_sites.append(site)

        return input_sites, output_sites

    # ── Helpers ────────────────────────────────────────────────────────────

    @staticmethod
    def _find_function(
        tree: ast.Module,
    ) -> Optional[Union[ast.FunctionDef, ast.AsyncFunctionDef]]:
        """Find the first function definition in a module AST."""
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                return node
        return None

    def __repr__(self) -> str:
        return f"BoundarySynthesizer(file={self._file_path!r})"
