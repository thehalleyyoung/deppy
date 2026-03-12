"""Frontend parsing stage for the sheaf-descent analysis pipeline.

Stage 0: Load source text, parse into a Python AST, and build the
intermediate representation (IR) used by subsequent stages.  The IR
maps function/class scopes to their AST nodes, type annotations, and
contract decorators.
"""

from __future__ import annotations

import ast
import hashlib
import os
import textwrap
from dataclasses import dataclass, field
from pathlib import Path
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
    Union,
)

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.pipeline.pipeline_config import PipelineConfig
from deppy.pipeline.stage_registry import Stage, StageMetadata


# ===================================================================
#  IR data structures
# ===================================================================


@dataclass(frozen=True)
class SourceInfo:
    """Metadata about the parsed source file."""

    _file_path: str
    _source_text: str
    _source_hash: str
    _encoding: str = "utf-8"
    _line_count: int = 0

    @property
    def file_path(self) -> str:
        return self._file_path

    @property
    def source_text(self) -> str:
        return self._source_text

    @property
    def source_hash(self) -> str:
        return self._source_hash

    @property
    def encoding(self) -> str:
        return self._encoding

    @property
    def line_count(self) -> int:
        return self._line_count


@dataclass(frozen=True)
class AnnotationInfo:
    """Extracted type annotation information."""

    _name: str
    _annotation_text: str
    _line: int
    _col: int

    @property
    def name(self) -> str:
        return self._name

    @property
    def annotation_text(self) -> str:
        return self._annotation_text

    @property
    def line(self) -> int:
        return self._line

    @property
    def col(self) -> int:
        return self._col


@dataclass(frozen=True)
class ParameterInfo:
    """Parameter information for a function scope."""

    _name: str
    _annotation: Optional[AnnotationInfo] = None
    _default_value: Optional[str] = None
    _is_self: bool = False
    _is_cls: bool = False
    _is_vararg: bool = False
    _is_kwarg: bool = False

    @property
    def name(self) -> str:
        return self._name

    @property
    def annotation(self) -> Optional[AnnotationInfo]:
        return self._annotation

    @property
    def default_value(self) -> Optional[str]:
        return self._default_value

    @property
    def is_self(self) -> bool:
        return self._is_self

    @property
    def is_cls(self) -> bool:
        return self._is_cls

    @property
    def has_annotation(self) -> bool:
        return self._annotation is not None


@dataclass(frozen=True)
class ScopeInfo:
    """Information about a scope (function, class, or module)."""

    _name: str
    _qualified_name: str
    _kind: str  # "function", "class", "module", "method", "async_function"
    _line_start: int
    _line_end: int
    _col_start: int = 0
    _parameters: Tuple[ParameterInfo, ...] = ()
    _return_annotation: Optional[AnnotationInfo] = None
    _decorators: Tuple[str, ...] = ()
    _docstring: Optional[str] = None
    _parent_scope: Optional[str] = None
    _is_async: bool = False
    _is_generator: bool = False
    _ast_node_type: str = "unknown"

    @property
    def name(self) -> str:
        return self._name

    @property
    def qualified_name(self) -> str:
        return self._qualified_name

    @property
    def kind(self) -> str:
        return self._kind

    @property
    def line_start(self) -> int:
        return self._line_start

    @property
    def line_end(self) -> int:
        return self._line_end

    @property
    def parameters(self) -> Tuple[ParameterInfo, ...]:
        return self._parameters

    @property
    def return_annotation(self) -> Optional[AnnotationInfo]:
        return self._return_annotation

    @property
    def decorators(self) -> Tuple[str, ...]:
        return self._decorators

    @property
    def docstring(self) -> Optional[str]:
        return self._docstring

    @property
    def parent_scope(self) -> Optional[str]:
        return self._parent_scope

    @property
    def is_async(self) -> bool:
        return self._is_async

    @property
    def has_contracts(self) -> bool:
        """True if any decorator looks like a deppy contract."""
        contract_names = {"requires", "ensures", "invariant", "witness", "theorem",
                          "lemma", "assume", "transport", "decreases", "ghost"}
        for dec in self._decorators:
            base = dec.split("(")[0].split(".")[-1]
            if base in contract_names:
                return True
        return False


@dataclass(frozen=True)
class IRModule:
    """Intermediate representation of a parsed module."""

    _source_info: SourceInfo
    _scopes: Tuple[ScopeInfo, ...]
    _imports: Tuple[str, ...]
    _global_assignments: Tuple[Tuple[str, int], ...]
    _ast_tree: Optional[Any] = field(default=None, hash=False, compare=False)

    @property
    def source_info(self) -> SourceInfo:
        return self._source_info

    @property
    def scopes(self) -> Tuple[ScopeInfo, ...]:
        return self._scopes

    @property
    def imports(self) -> Tuple[str, ...]:
        return self._imports

    @property
    def global_assignments(self) -> Tuple[Tuple[str, int], ...]:
        return self._global_assignments

    @property
    def ast_tree(self) -> Optional[Any]:
        return self._ast_tree

    def function_scopes(self) -> Tuple[ScopeInfo, ...]:
        return tuple(s for s in self._scopes if s.kind in ("function", "method", "async_function"))

    def class_scopes(self) -> Tuple[ScopeInfo, ...]:
        return tuple(s for s in self._scopes if s.kind == "class")

    def scope_by_name(self, name: str) -> Optional[ScopeInfo]:
        for s in self._scopes:
            if s.qualified_name == name or s.name == name:
                return s
        return None


# ===================================================================
#  ParseResult
# ===================================================================


@dataclass(frozen=True)
class ParseResult:
    """Result of the parse stage."""

    _ir_module: IRModule
    _warnings: Tuple[str, ...] = ()
    _errors: Tuple[str, ...] = ()

    @property
    def ir_module(self) -> IRModule:
        return self._ir_module

    @property
    def warnings(self) -> Tuple[str, ...]:
        return self._warnings

    @property
    def errors(self) -> Tuple[str, ...]:
        return self._errors

    @property
    def success(self) -> bool:
        return len(self._errors) == 0


# ===================================================================
#  AST visitor for building the IR
# ===================================================================


class _IRBuilder(ast.NodeVisitor):
    """Walk the AST and extract scope information."""

    def __init__(self, source_text: str, file_path: str) -> None:
        self._source_text = source_text
        self._source_lines = source_text.splitlines()
        self._file_path = file_path
        self._scopes: List[ScopeInfo] = []
        self._imports: List[str] = []
        self._global_assignments: List[Tuple[str, int]] = []
        self._scope_stack: List[str] = []
        self._warnings: List[str] = []

    def _current_qualified_prefix(self) -> str:
        return ".".join(self._scope_stack)

    def _qualified_name(self, name: str) -> str:
        prefix = self._current_qualified_prefix()
        return f"{prefix}.{name}" if prefix else name

    def _extract_annotation(self, node: Optional[ast.expr]) -> Optional[AnnotationInfo]:
        if node is None:
            return None
        try:
            text = ast.unparse(node)
        except Exception:
            text = "<unknown>"
        return AnnotationInfo(
            _name="",
            _annotation_text=text,
            _line=getattr(node, "lineno", 0),
            _col=getattr(node, "col_offset", 0),
        )

    def _extract_decorator_name(self, node: ast.expr) -> str:
        try:
            return ast.unparse(node)
        except Exception:
            return "<decorator>"

    def _extract_parameters(self, args: ast.arguments) -> Tuple[ParameterInfo, ...]:
        params: List[ParameterInfo] = []
        all_args = list(args.args)
        defaults_offset = len(all_args) - len(args.defaults)

        for i, arg in enumerate(all_args):
            is_self = (i == 0 and arg.arg == "self")
            is_cls = (i == 0 and arg.arg == "cls")
            default_idx = i - defaults_offset
            default_val = None
            if default_idx >= 0 and default_idx < len(args.defaults):
                try:
                    default_val = ast.unparse(args.defaults[default_idx])
                except Exception:
                    default_val = "<default>"

            params.append(ParameterInfo(
                _name=arg.arg,
                _annotation=self._extract_annotation(arg.annotation),
                _default_value=default_val,
                _is_self=is_self,
                _is_cls=is_cls,
            ))

        if args.vararg:
            params.append(ParameterInfo(
                _name=args.vararg.arg,
                _annotation=self._extract_annotation(args.vararg.annotation),
                _is_vararg=True,
            ))

        for i, arg in enumerate(args.kwonlyargs):
            default_val = None
            if i < len(args.kw_defaults) and args.kw_defaults[i] is not None:
                try:
                    default_val = ast.unparse(args.kw_defaults[i])
                except Exception:
                    default_val = "<default>"
            params.append(ParameterInfo(
                _name=arg.arg,
                _annotation=self._extract_annotation(arg.annotation),
                _default_value=default_val,
            ))

        if args.kwarg:
            params.append(ParameterInfo(
                _name=args.kwarg.arg,
                _annotation=self._extract_annotation(args.kwarg.annotation),
                _is_kwarg=True,
            ))

        return tuple(params)

    def _extract_docstring(self, body: List[ast.stmt]) -> Optional[str]:
        if body and isinstance(body[0], ast.Expr):
            value = body[0].value
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                return value.value.strip()
        return None

    def _get_end_lineno(self, node: ast.AST) -> int:
        return getattr(node, "end_lineno", getattr(node, "lineno", 0))

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._visit_function(node, is_async=False)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._visit_function(node, is_async=True)

    def _visit_function(self, node: Union[ast.FunctionDef, ast.AsyncFunctionDef], is_async: bool) -> None:
        qname = self._qualified_name(node.name)
        decorators = tuple(self._extract_decorator_name(d) for d in node.decorator_list)
        params = self._extract_parameters(node.args)
        ret_ann = self._extract_annotation(node.returns)
        docstring = self._extract_docstring(node.body)

        # Determine kind
        if is_async:
            kind = "async_function"
        elif self._scope_stack and any(
            s.kind == "class" for s in self._scopes
            if s.qualified_name == self._current_qualified_prefix()
        ):
            kind = "method"
        else:
            kind = "function"

        # Check for generators
        is_generator = False
        for child in ast.walk(node):
            if isinstance(child, (ast.Yield, ast.YieldFrom)):
                is_generator = True
                break

        scope = ScopeInfo(
            _name=node.name,
            _qualified_name=qname,
            _kind=kind,
            _line_start=node.lineno,
            _line_end=self._get_end_lineno(node),
            _col_start=node.col_offset,
            _parameters=params,
            _return_annotation=ret_ann,
            _decorators=decorators,
            _docstring=docstring,
            _parent_scope=self._current_qualified_prefix() or None,
            _is_async=is_async,
            _is_generator=is_generator,
            _ast_node_type=type(node).__name__,
        )
        self._scopes.append(scope)

        self._scope_stack.append(node.name)
        self.generic_visit(node)
        self._scope_stack.pop()

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        qname = self._qualified_name(node.name)
        decorators = tuple(self._extract_decorator_name(d) for d in node.decorator_list)
        docstring = self._extract_docstring(node.body)

        scope = ScopeInfo(
            _name=node.name,
            _qualified_name=qname,
            _kind="class",
            _line_start=node.lineno,
            _line_end=self._get_end_lineno(node),
            _col_start=node.col_offset,
            _decorators=decorators,
            _docstring=docstring,
            _parent_scope=self._current_qualified_prefix() or None,
            _ast_node_type="ClassDef",
        )
        self._scopes.append(scope)

        self._scope_stack.append(node.name)
        self.generic_visit(node)
        self._scope_stack.pop()

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            self._imports.append(alias.name)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        module = node.module or ""
        for alias in node.names:
            self._imports.append(f"{module}.{alias.name}")

    def visit_Assign(self, node: ast.Assign) -> None:
        if not self._scope_stack:
            for target in node.targets:
                if isinstance(target, ast.Name):
                    self._global_assignments.append((target.id, node.lineno))
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if not self._scope_stack and node.target and isinstance(node.target, ast.Name):
            self._global_assignments.append((node.target.id, node.lineno))
        self.generic_visit(node)


# ===================================================================
#  ParseStage
# ===================================================================


class ParseStage(Stage):
    """Stage 0: Parse source into IR.

    Accepts either a file path or source string via the pipeline context.
    Produces an IRModule containing scope information, annotations,
    contracts, and the raw AST.
    """

    def metadata(self) -> StageMetadata:
        return StageMetadata(
            _name="parse",
            _description="Parse source into intermediate representation",
            _dependencies=frozenset(),
            _order_hint=0,
        )

    def run(self, context: Dict[str, Any], config: PipelineConfig) -> ParseResult:
        """Execute parse stage.

        Expects context to contain either:
        - ``source_path``: path to a Python file
        - ``source_text``: raw source string

        Returns a ParseResult with the IR module.
        """
        source_path = context.get("source_path", "")
        source_text = context.get("source_text", "")
        file_path = str(source_path) if source_path else "<string>"

        if not source_text and source_path:
            source_text = self._load_source(str(source_path))
            if source_text is None:
                return ParseResult(
                    _ir_module=self._empty_ir(file_path),
                    _errors=(f"Could not read file: {source_path}",),
                )

        if not source_text:
            return ParseResult(
                _ir_module=self._empty_ir(file_path),
                _errors=("No source text provided",),
            )

        return self._parse_source(source_text, file_path)

    def run_file(self, file_path: str, config: PipelineConfig) -> ParseResult:
        """Parse a single file."""
        source_text = self._load_source(file_path)
        if source_text is None:
            return ParseResult(
                _ir_module=self._empty_ir(file_path),
                _errors=(f"Could not read file: {file_path}",),
            )
        return self._parse_source(source_text, file_path)

    def run_source(self, source_text: str, config: PipelineConfig) -> ParseResult:
        """Parse source text directly."""
        return self._parse_source(source_text, "<string>")

    def _parse_source(self, source_text: str, file_path: str) -> ParseResult:
        """Core parsing logic."""
        warnings: List[str] = []
        errors: List[str] = []

        # Compute source hash for incremental caching
        source_hash = hashlib.sha256(source_text.encode("utf-8")).hexdigest()[:16]

        # Parse the AST
        try:
            tree = ast.parse(source_text, filename=file_path)
        except SyntaxError as exc:
            return ParseResult(
                _ir_module=self._empty_ir(file_path),
                _errors=(f"Syntax error at line {exc.lineno}: {exc.msg}",),
            )

        # Build IR
        builder = _IRBuilder(source_text, file_path)
        builder.visit(tree)
        warnings.extend(builder._warnings)

        source_info = SourceInfo(
            _file_path=file_path,
            _source_text=source_text,
            _source_hash=source_hash,
            _line_count=len(source_text.splitlines()),
        )

        ir_module = IRModule(
            _source_info=source_info,
            _scopes=tuple(builder._scopes),
            _imports=tuple(builder._imports),
            _global_assignments=tuple(builder._global_assignments),
            _ast_tree=tree,
        )

        return ParseResult(
            _ir_module=ir_module,
            _warnings=tuple(warnings),
            _errors=tuple(errors),
        )

    @staticmethod
    def _load_source(file_path: str) -> Optional[str]:
        """Load source text from a file path."""
        path = Path(file_path)
        if not path.exists():
            return None
        try:
            return path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            try:
                return path.read_text(encoding="latin-1")
            except (OSError, UnicodeDecodeError):
                return None

    @staticmethod
    def _empty_ir(file_path: str) -> IRModule:
        """Create an empty IR module for error cases."""
        return IRModule(
            _source_info=SourceInfo(
                _file_path=file_path,
                _source_text="",
                _source_hash="",
                _line_count=0,
            ),
            _scopes=(),
            _imports=(),
            _global_assignments=(),
        )
