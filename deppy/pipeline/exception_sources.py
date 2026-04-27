"""
Exception Source Identification — AST-Level Exception Taxonomy
==============================================================

Walks a Python AST and identifies every program point that can raise
a runtime exception.  Each potential exception site is classified by
kind, annotated with the triggering condition, and located precisely
in the source.

The taxonomy covers a **restricted Python fragment** — operations on
built-in types whose exception semantics are well-defined.  Calls to
external / user-defined functions are flagged as ``CALL_PROPAGATION``
(requiring sidecar summaries or intra-module analysis to resolve).

This module is the foundation of deppy's module-level exception-freedom
verification.  It does **not** attempt to determine whether a given
exception source is safe — that is the job of the guard inference engine
and the Z3-backed prover.

Architecture
------------
  ExceptionKind       — taxonomy of Python runtime exceptions
  ExceptionSource     — one potential exception site (file, line, kind, trigger)
  ExceptionSourceFinder — AST visitor that collects all sources
  SourceSummary       — per-function / per-module aggregate
"""
from __future__ import annotations

import ast
import inspect
import textwrap
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Sequence


# ═══════════════════════════════════════════════════════════════════
# 1.  Exception Taxonomy
# ═══════════════════════════════════════════════════════════════════

class ExceptionKind(Enum):
    """Classification of Python runtime exceptions.

    Each member maps to a concrete ``BaseException`` subclass that the
    Python runtime can raise for built-in operations.  ``CALL_PROPAGATION``
    is a meta-kind representing exceptions that *may* propagate from a
    callee but whose precise kind is unknown without interprocedural
    analysis or a sidecar summary.
    """

    # ── Arithmetic ────────────────────────────────────────────────
    ZERO_DIVISION      = auto()   # x / 0, x % 0, divmod(x, 0)
    OVERFLOW           = auto()   # math.exp(1e308), int too large for C
    MATH_DOMAIN        = auto()   # math.sqrt(-1), math.log(0)

    # ── Collection access ─────────────────────────────────────────
    INDEX_ERROR        = auto()   # list[out_of_range]
    KEY_ERROR          = auto()   # dict[missing_key]
    STOP_ITERATION     = auto()   # next() on exhausted iterator

    # ── Type / value ──────────────────────────────────────────────
    TYPE_ERROR         = auto()   # wrong operand type, bad arity
    VALUE_ERROR        = auto()   # int("abc"), unpacking mismatch
    ATTRIBUTE_ERROR    = auto()   # obj.nonexistent

    # ── Name resolution ───────────────────────────────────────────
    NAME_ERROR         = auto()   # undefined variable
    IMPORT_ERROR       = auto()   # missing module / name

    # ── Assertion / explicit ──────────────────────────────────────
    ASSERTION_ERROR    = auto()   # assert False
    EXPLICIT_RAISE     = auto()   # raise SomeException(...)

    # ── OS / IO ───────────────────────────────────────────────────
    OS_ERROR           = auto()   # file I/O, network, permissions
    RUNTIME_ERROR      = auto()   # generic RuntimeError, recursion limit

    # ── Concurrency ───────────────────────────────────────────────
    TIMEOUT_ERROR      = auto()   # asyncio.wait_for timeout

    # ── Meta ──────────────────────────────────────────────────────
    CALL_PROPAGATION   = auto()   # exception propagated from callee
    UNPACK_ERROR       = auto()   # starred / tuple unpack mismatch
    ITERATION_ERROR    = auto()   # __iter__ / __next__ failure
    CUSTOM             = auto()   # user-defined exception class


# Map from Python exception class names to ExceptionKind
_EXCEPTION_NAME_MAP: dict[str, ExceptionKind] = {
    "ZeroDivisionError": ExceptionKind.ZERO_DIVISION,
    "OverflowError": ExceptionKind.OVERFLOW,
    "IndexError": ExceptionKind.INDEX_ERROR,
    "KeyError": ExceptionKind.KEY_ERROR,
    "StopIteration": ExceptionKind.STOP_ITERATION,
    "TypeError": ExceptionKind.TYPE_ERROR,
    "ValueError": ExceptionKind.VALUE_ERROR,
    "AttributeError": ExceptionKind.ATTRIBUTE_ERROR,
    "NameError": ExceptionKind.NAME_ERROR,
    "ImportError": ExceptionKind.IMPORT_ERROR,
    "ModuleNotFoundError": ExceptionKind.IMPORT_ERROR,
    "AssertionError": ExceptionKind.ASSERTION_ERROR,
    "OSError": ExceptionKind.OS_ERROR,
    "IOError": ExceptionKind.OS_ERROR,
    "FileNotFoundError": ExceptionKind.OS_ERROR,
    "PermissionError": ExceptionKind.OS_ERROR,
    "RuntimeError": ExceptionKind.RUNTIME_ERROR,
    "RecursionError": ExceptionKind.RUNTIME_ERROR,
    "TimeoutError": ExceptionKind.TIMEOUT_ERROR,
    "ArithmeticError": ExceptionKind.ZERO_DIVISION,
    "LookupError": ExceptionKind.KEY_ERROR,
    "UnicodeError": ExceptionKind.VALUE_ERROR,
    "UnicodeDecodeError": ExceptionKind.VALUE_ERROR,
    "UnicodeEncodeError": ExceptionKind.VALUE_ERROR,
    "NotImplementedError": ExceptionKind.RUNTIME_ERROR,
}


def exception_kind_from_name(name: str) -> ExceptionKind:
    """Resolve a Python exception class name to an ``ExceptionKind``."""
    return _EXCEPTION_NAME_MAP.get(name, ExceptionKind.CUSTOM)


# ═══════════════════════════════════════════════════════════════════
# 2.  Exception Source — one potential exception site
# ═══════════════════════════════════════════════════════════════════

class Severity(Enum):
    """How serious is an unhandled exception here?"""
    CRITICAL = auto()   # always raises (e.g. unconditional raise)
    HIGH     = auto()   # raises under common inputs (e.g. division)
    MEDIUM   = auto()   # raises under specific inputs (e.g. index)
    LOW      = auto()   # raises under unusual inputs (e.g. overflow)
    INFO     = auto()   # informational only (e.g. assert in tests)


@dataclass(frozen=True)
class SourceLocation:
    """Precise location of an exception source in the AST."""
    filename: str = "<unknown>"
    function: str = "<module>"
    lineno: int = 0
    col_offset: int = 0
    end_lineno: int | None = None
    end_col_offset: int | None = None

    def __str__(self) -> str:
        loc = f"{self.filename}:{self.lineno}"
        if self.col_offset:
            loc += f":{self.col_offset}"
        return f"{loc} in {self.function}"


@dataclass
class ExceptionSource:
    """A single potential exception site in Python source.

    Attributes
    ----------
    kind : ExceptionKind
        The category of exception that can be raised.
    location : SourceLocation
        Where in the source this exception can occur.
    trigger_condition : str
        A human-readable (and ideally Z3-encodable) predicate describing
        when this exception is triggered (e.g. ``"divisor == 0"``).
    ast_node : ast.AST | None
        The AST node that can raise the exception.
    severity : Severity
        How likely / important this exception source is.
    description : str
        Human-readable description.
    callee_name : str | None
        For ``CALL_PROPAGATION`` sources, the name of the callee.
    caught_by : ast.ExceptHandler | None
        If this source is inside a try/except, the handler that catches it.
    """
    kind: ExceptionKind
    location: SourceLocation
    trigger_condition: str = ""
    ast_node: ast.AST | None = None
    severity: Severity = Severity.MEDIUM
    description: str = ""
    callee_name: str | None = None
    caught_by: ast.ExceptHandler | None = None

    def __repr__(self) -> str:
        caught = " [caught]" if self.caught_by else ""
        return f"ExceptionSource({self.kind.name} @ {self.location}{caught})"


# ═══════════════════════════════════════════════════════════════════
# 3.  Source Summary
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FunctionSourceSummary:
    """All exception sources in a single function."""
    name: str
    sources: list[ExceptionSource] = field(default_factory=list)
    lineno: int = 0
    end_lineno: int = 0
    is_method: bool = False
    class_name: str | None = None
    has_try_except: bool = False
    is_generator: bool = False
    is_async: bool = False

    @property
    def total_sources(self) -> int:
        return len(self.sources)

    @property
    def uncaught_sources(self) -> list[ExceptionSource]:
        return [s for s in self.sources if s.caught_by is None]

    @property
    def caught_sources(self) -> list[ExceptionSource]:
        return [s for s in self.sources if s.caught_by is not None]

    @property
    def by_kind(self) -> dict[ExceptionKind, list[ExceptionSource]]:
        result: dict[ExceptionKind, list[ExceptionSource]] = {}
        for s in self.sources:
            result.setdefault(s.kind, []).append(s)
        return result


@dataclass
class ModuleSourceSummary:
    """All exception sources across an entire module."""
    module_path: str
    functions: list[FunctionSourceSummary] = field(default_factory=list)
    module_level_sources: list[ExceptionSource] = field(default_factory=list)

    @property
    def total_functions(self) -> int:
        return len(self.functions)

    @property
    def total_sources(self) -> int:
        return (sum(f.total_sources for f in self.functions)
                + len(self.module_level_sources))

    @property
    def total_uncaught(self) -> int:
        return (sum(len(f.uncaught_sources) for f in self.functions)
                + sum(1 for s in self.module_level_sources if s.caught_by is None))

    @property
    def functions_with_exceptions(self) -> list[FunctionSourceSummary]:
        return [f for f in self.functions if f.total_sources > 0]

    def by_kind(self) -> dict[ExceptionKind, int]:
        counts: dict[ExceptionKind, int] = {}
        for fn in self.functions:
            for src in fn.sources:
                counts[src.kind] = counts.get(src.kind, 0) + 1
        for src in self.module_level_sources:
            counts[src.kind] = counts.get(src.kind, 0) + 1
        return counts


# ═══════════════════════════════════════════════════════════════════
# 4.  AST Exception Source Finder
# ═══════════════════════════════════════════════════════════════════

# Built-in functions known to raise specific exceptions
_BUILTIN_EXCEPTION_MAP: dict[str, list[tuple[ExceptionKind, str, Severity]]] = {
    "int":     [(ExceptionKind.VALUE_ERROR, "argument not convertible to int", Severity.MEDIUM),
                (ExceptionKind.TYPE_ERROR, "argument type not supported", Severity.MEDIUM)],
    "float":   [(ExceptionKind.VALUE_ERROR, "argument not convertible to float", Severity.MEDIUM),
                (ExceptionKind.TYPE_ERROR, "argument type not supported", Severity.MEDIUM)],
    "str":     [],  # str() rarely raises
    "bool":    [],  # bool() rarely raises
    "list":    [(ExceptionKind.TYPE_ERROR, "argument not iterable", Severity.LOW)],
    "tuple":   [(ExceptionKind.TYPE_ERROR, "argument not iterable", Severity.LOW)],
    "set":     [(ExceptionKind.TYPE_ERROR, "argument not iterable", Severity.LOW)],
    "dict":    [(ExceptionKind.TYPE_ERROR, "argument not valid for dict()", Severity.LOW)],
    "len":     [(ExceptionKind.TYPE_ERROR, "object has no len()", Severity.LOW)],
    "abs":     [(ExceptionKind.TYPE_ERROR, "bad operand type for abs()", Severity.LOW)],
    "sum":     [(ExceptionKind.TYPE_ERROR, "unsummable types", Severity.LOW)],
    "min":     [(ExceptionKind.VALUE_ERROR, "min() arg is empty sequence", Severity.MEDIUM)],
    "max":     [(ExceptionKind.VALUE_ERROR, "max() arg is empty sequence", Severity.MEDIUM)],
    "sorted":  [(ExceptionKind.TYPE_ERROR, "unorderable types", Severity.LOW)],
    "next":    [(ExceptionKind.STOP_ITERATION, "iterator exhausted", Severity.MEDIUM)],
    "iter":    [(ExceptionKind.TYPE_ERROR, "object not iterable", Severity.LOW)],
    "open":    [(ExceptionKind.OS_ERROR, "file I/O error", Severity.HIGH)],
    "input":   [(ExceptionKind.OS_ERROR, "I/O error on stdin", Severity.LOW)],
    "print":   [(ExceptionKind.OS_ERROR, "I/O error on stdout", Severity.LOW)],
    "ord":     [(ExceptionKind.TYPE_ERROR, "expected string of length 1", Severity.MEDIUM)],
    "chr":     [(ExceptionKind.VALUE_ERROR, "chr() arg not in range", Severity.MEDIUM)],
    "eval":    [(ExceptionKind.RUNTIME_ERROR, "arbitrary exception from eval()", Severity.CRITICAL)],
    "exec":    [(ExceptionKind.RUNTIME_ERROR, "arbitrary exception from exec()", Severity.CRITICAL)],
    "compile": [(ExceptionKind.VALUE_ERROR, "invalid source for compile()", Severity.MEDIUM)],
    "divmod":  [(ExceptionKind.ZERO_DIVISION, "second argument is zero", Severity.HIGH)],
    "pow":     [(ExceptionKind.ZERO_DIVISION, "0 ** negative", Severity.MEDIUM),
                (ExceptionKind.VALUE_ERROR, "pow() 3rd argument not allowed", Severity.LOW)],
    "round":   [(ExceptionKind.TYPE_ERROR, "argument not numeric", Severity.LOW)],
    "hash":    [(ExceptionKind.TYPE_ERROR, "unhashable type", Severity.MEDIUM)],
    "getattr": [(ExceptionKind.ATTRIBUTE_ERROR, "attribute not found (no default)", Severity.MEDIUM)],
    "delattr": [(ExceptionKind.ATTRIBUTE_ERROR, "attribute not found", Severity.MEDIUM)],
    "setattr": [(ExceptionKind.ATTRIBUTE_ERROR, "can't set attribute", Severity.LOW)],
    "isinstance": [],
    "issubclass": [(ExceptionKind.TYPE_ERROR, "arg 2 must be a class", Severity.LOW)],
    "zip":     [],
    "map":     [],
    "filter":  [],
    "range":   [(ExceptionKind.TYPE_ERROR, "non-integer argument", Severity.LOW),
                (ExceptionKind.VALUE_ERROR, "step argument must not be zero", Severity.MEDIUM)],
    "enumerate": [],
    "reversed": [(ExceptionKind.TYPE_ERROR, "argument not reversible", Severity.LOW)],
    "super":   [(ExceptionKind.RUNTIME_ERROR, "super(): no arguments", Severity.LOW)],
    
    # ROUND 4 FIX: Add math functions that can raise MATH_DOMAIN and OVERFLOW
    "math.sqrt": [(ExceptionKind.MATH_DOMAIN, "sqrt of negative number", Severity.MEDIUM)],
    "math.log": [(ExceptionKind.MATH_DOMAIN, "log of non-positive number", Severity.MEDIUM)],
    "math.log10": [(ExceptionKind.MATH_DOMAIN, "log10 of non-positive number", Severity.MEDIUM)],
    "math.log2": [(ExceptionKind.MATH_DOMAIN, "log2 of non-positive number", Severity.MEDIUM)],
    "math.acos": [(ExceptionKind.MATH_DOMAIN, "acos domain error", Severity.MEDIUM)],
    "math.asin": [(ExceptionKind.MATH_DOMAIN, "asin domain error", Severity.MEDIUM)],
    "math.atanh": [(ExceptionKind.MATH_DOMAIN, "atanh domain error", Severity.MEDIUM)],
    "math.acosh": [(ExceptionKind.MATH_DOMAIN, "acosh domain error", Severity.MEDIUM)],
    "math.gamma": [(ExceptionKind.MATH_DOMAIN, "gamma domain error", Severity.MEDIUM)],
    "math.lgamma": [(ExceptionKind.MATH_DOMAIN, "lgamma domain error", Severity.MEDIUM)],
    "math.exp": [(ExceptionKind.OVERFLOW, "exp result too large", Severity.MEDIUM)],
    "math.exp2": [(ExceptionKind.OVERFLOW, "exp2 result too large", Severity.MEDIUM)],
    "math.expm1": [(ExceptionKind.OVERFLOW, "expm1 result too large", Severity.MEDIUM)],
    "math.pow": [(ExceptionKind.MATH_DOMAIN, "pow domain error", Severity.MEDIUM),
                 (ExceptionKind.OVERFLOW, "pow result too large", Severity.MEDIUM)],
}

# Method calls known to raise specific exceptions
_METHOD_EXCEPTION_MAP: dict[str, list[tuple[ExceptionKind, str, Severity]]] = {
    "index":    [(ExceptionKind.VALUE_ERROR, "x not in list", Severity.MEDIUM)],
    "remove":   [(ExceptionKind.VALUE_ERROR, "x not in list", Severity.MEDIUM)],
    "pop":      [(ExceptionKind.INDEX_ERROR, "pop from empty / out of range", Severity.MEDIUM),
                 (ExceptionKind.KEY_ERROR, "key not in dict", Severity.MEDIUM)],
    "sort":     [(ExceptionKind.TYPE_ERROR, "unorderable types", Severity.LOW)],
    "split":    [],
    "join":     [(ExceptionKind.TYPE_ERROR, "items must be strings", Severity.LOW)],
    "encode":   [(ExceptionKind.VALUE_ERROR, "encoding error", Severity.LOW)],
    "decode":   [(ExceptionKind.VALUE_ERROR, "decoding error", Severity.LOW)],
    "append":   [],
    "extend":   [],
    "insert":   [],
    "clear":    [],
    "copy":     [],
    "update":   [],
    "keys":     [],
    "values":   [],
    "items":    [],
    "get":      [],   # dict.get never raises
    "setdefault": [],
    "startswith": [],
    "endswith":   [],
    "strip":    [],
    "lstrip":   [],
    "rstrip":   [],
    "replace":  [],
    "lower":    [],
    "upper":    [],
    "format":   [(ExceptionKind.KEY_ERROR, "missing format key", Severity.LOW),
                 (ExceptionKind.INDEX_ERROR, "format index out of range", Severity.LOW)],
    "__getitem__": [(ExceptionKind.KEY_ERROR, "key not found", Severity.MEDIUM),
                    (ExceptionKind.INDEX_ERROR, "index out of range", Severity.MEDIUM)],
    "__setitem__": [(ExceptionKind.KEY_ERROR, "key error on set", Severity.LOW)],
    "__delitem__": [(ExceptionKind.KEY_ERROR, "key not found for deletion", Severity.MEDIUM)],
}


class ExceptionSourceFinder(ast.NodeVisitor):
    """Walk a Python AST collecting all potential exception sources.

    This visitor identifies syntactic patterns that can raise exceptions
    under Python's standard semantics for built-in types.  It does **not**
    model dynamic dispatch (``__truediv__`` overloads, descriptors, etc.)
    — such sites are flagged conservatively as ``CALL_PROPAGATION``.

    Usage
    -----
    >>> finder = ExceptionSourceFinder("mymodule.py")
    >>> tree = ast.parse(open("mymodule.py").read())
    >>> summary = finder.analyze_module(tree)
    """

    def __init__(self, filename: str = "<string>"):
        self._filename = filename
        self._current_function: str = "<module>"
        self._current_class: str | None = None
        self._try_handlers: list[list[ast.ExceptHandler]] = []
        self._sources: list[ExceptionSource] = []
        self._function_summaries: list[FunctionSourceSummary] = []
        self._module_sources: list[ExceptionSource] = []
        self._in_function: bool = False

    # ── Public API ────────────────────────────────────────────────

    def analyze_module(self, tree: ast.Module) -> ModuleSourceSummary:
        """Analyze an entire module AST, returning a complete summary."""
        self._sources = []
        self._function_summaries = []
        self._module_sources = []
        self._current_function = "<module>"
        self._in_function = False
        
        # Pre-pass: collect all function names defined in this module
        # to avoid NAME_ERROR false positives on function calls
        module_function_names = set()
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                module_function_names.add(node.name)
        self._module_function_names = module_function_names
        
        self.visit(tree)
        return ModuleSourceSummary(
            module_path=self._filename,
            functions=list(self._function_summaries),
            module_level_sources=list(self._module_sources),
        )

    def analyze_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef,
                         *, class_name: str | None = None) -> FunctionSourceSummary:
        """Analyze a single function definition."""
        saved = (self._current_function, self._current_class,
                 self._sources, self._in_function)
        self._current_function = node.name
        self._current_class = class_name
        self._sources = []
        self._in_function = True

        # Extract parameter names to avoid NAME_ERROR false positives
        param_names = set()
        if hasattr(node, 'args'):
            args = node.args
            param_names.update(arg.arg for arg in getattr(args, 'args', []))
            param_names.update(arg.arg for arg in getattr(args, 'posonlyargs', []))
            param_names.update(arg.arg for arg in getattr(args, 'kwonlyargs', []))
            if getattr(args, 'vararg', None):
                param_names.add(args.vararg.arg)
            if getattr(args, 'kwarg', None):
                param_names.add(args.kwarg.arg)
        
        # Hole 4 fix: include locally-bound names (assignments, for
        # loops, with statements, comprehensions, exception handlers)
        # alongside parameters.  Otherwise every ``let dx := ...``
        # body produces a spurious NAME_ERROR for ``dx`` later in the
        # body.
        local_names: set[str] = set()
        for sub in ast.walk(node):
            if isinstance(sub, ast.Assign):
                for tgt in sub.targets:
                    _collect_target_names(tgt, local_names)
            elif isinstance(sub, (ast.AnnAssign, ast.AugAssign)):
                _collect_target_names(sub.target, local_names)
            elif isinstance(sub, (ast.For, ast.AsyncFor)):
                _collect_target_names(sub.target, local_names)
            elif isinstance(sub, (ast.With, ast.AsyncWith)):
                for item in sub.items:
                    if item.optional_vars is not None:
                        _collect_target_names(
                            item.optional_vars, local_names,
                        )
            elif isinstance(sub, ast.ExceptHandler):
                if sub.name is not None:
                    local_names.add(sub.name)
            elif isinstance(sub, (
                ast.ListComp, ast.SetComp, ast.DictComp,
                ast.GeneratorExp,
            )):
                for gen in sub.generators:
                    _collect_target_names(gen.target, local_names)
            elif isinstance(sub, ast.Lambda):
                for arg in sub.args.args:
                    local_names.add(arg.arg)
            elif isinstance(sub, (
                ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
            )):
                # Inner def/class binds the name in the enclosing
                # scope.
                local_names.add(sub.name)
            elif isinstance(sub, ast.Import):
                for alias in sub.names:
                    name = alias.asname or alias.name.split(".")[0]
                    local_names.add(name)
            elif isinstance(sub, ast.ImportFrom):
                for alias in sub.names:
                    local_names.add(alias.asname or alias.name)

        # Store parameter + local names for NAME_ERROR visitor.
        old_params = getattr(self, '_current_function_params', set())
        self._current_function_params = param_names | local_names

        # ROUND 5 FIX: Split definition-time vs runtime hazards
        # Definition-time: decorators, defaults, annotations execute at import
        # Runtime: only the function body executes when called
        
        definition_sources = []
        runtime_sources = []
        
        # Analyze definition-time elements
        old_module_sources = list(self._module_sources)
        for decorator in node.decorator_list:
            self.visit(decorator)
        for default in getattr(node, 'args', ast.arguments()).defaults:
            self.visit(default)
        for default in getattr(node, 'args', ast.arguments()).kw_defaults:
            if default is not None:
                self.visit(default)
        if hasattr(node, 'returns') and node.returns:
            self.visit(node.returns)
        
        # Collect definition-time sources as module-level
        definition_sources = self._sources[:]
        self._module_sources.extend(definition_sources)
        self._sources = []
        
        # Analyze runtime body
        for stmt in node.body:
            self.visit(stmt)
        runtime_sources = self._sources[:]

        summary = FunctionSourceSummary(
            name=node.name,
            sources=list(runtime_sources),  # Only runtime sources in function summary
            lineno=node.lineno,
            end_lineno=getattr(node, 'end_lineno', node.lineno),
            is_method=class_name is not None,
            class_name=class_name,
            has_try_except=any(isinstance(n, ast.Try)
                              for n in ast.walk(node)),
            is_generator=any(isinstance(n, (ast.Yield, ast.YieldFrom))
                            for n in ast.walk(node)),
            is_async=isinstance(node, ast.AsyncFunctionDef),
        )

        (self._current_function, self._current_class,
         self._sources, self._in_function) = saved
        
        # Restore parameter names
        self._current_function_params = old_params
        
        return summary

    def analyze_source(self, source: str,
                       filename: str = "<string>") -> ModuleSourceSummary:
        """Analyze a source string, returning a complete module summary."""
        self._filename = filename
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return ModuleSourceSummary(module_path=filename)
        return self.analyze_module(tree)

    # ── AST Visitors ──────────────────────────────────────────────

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        summary = self.analyze_function(node, class_name=self._current_class)
        self._function_summaries.append(summary)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        summary = self.analyze_function(node, class_name=self._current_class)
        self._function_summaries.append(summary)

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        saved_class = self._current_class
        self._current_class = node.name
        self.generic_visit(node)
        self._current_class = saved_class

    def visit_BinOp(self, node: ast.BinOp) -> None:
        """Division, modulo, floor division → ZeroDivisionError.

        Hole 5 fix: when the divisor is a non-zero numeric literal
        the operation is provably safe — skip the ZERO_DIVISION
        source instead of generating an obligation that the
        downstream Z3 step will trivially discharge.
        """
        if isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
            # Constant non-zero divisor → no obligation needed.
            divisor_safe = (
                isinstance(node.right, ast.Constant)
                and isinstance(node.right.value, (int, float))
                and node.right.value != 0
            )
            if not divisor_safe:
                self._add_source(
                    ExceptionKind.ZERO_DIVISION,
                    node,
                    trigger_condition=f"divisor == 0",
                    severity=Severity.HIGH,
                    description=f"{_op_name(node.op)} by zero",
                )
        if isinstance(node.op, ast.Pow):
            self._add_source(
                ExceptionKind.ZERO_DIVISION,
                node,
                trigger_condition="base == 0 and exponent < 0",
                severity=Severity.LOW,
                description="zero raised to negative power",
            )
        self.generic_visit(node)

    def visit_Subscript(self, node: ast.Subscript) -> None:
        """Indexing → IndexError / KeyError."""
        if isinstance(node.slice, ast.Constant) and isinstance(node.slice.value, int):
            self._add_source(
                ExceptionKind.INDEX_ERROR,
                node,
                trigger_condition=f"index {node.slice.value} out of range",
                severity=Severity.MEDIUM,
                description=f"subscript access with constant index {node.slice.value}",
            )
        elif isinstance(node.slice, ast.Slice):
            pass  # slicing does not raise IndexError
        else:
            # Dynamic index — could be index or key error
            self._add_source(
                ExceptionKind.INDEX_ERROR,
                node,
                trigger_condition="index out of range",
                severity=Severity.MEDIUM,
                description="dynamic subscript access",
            )
            self._add_source(
                ExceptionKind.KEY_ERROR,
                node,
                trigger_condition="key not present",
                severity=Severity.MEDIUM,
                description="dynamic subscript access (dict key)",
            )
        self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        """Attribute access → AttributeError."""
        self._add_source(
            ExceptionKind.ATTRIBUTE_ERROR,
            node,
            trigger_condition=f"object has no attribute '{node.attr}'",
            severity=Severity.LOW,
            description=f"attribute access .{node.attr}",
        )
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        """Function / method calls → various exceptions."""
        func_name = self._resolve_call_name(node)

        if self._in_function and func_name == self._current_function:
            self._add_source(
                ExceptionKind.RUNTIME_ERROR,
                node,
                trigger_condition="recursion depth exceeded",
                severity=Severity.HIGH,
                description=f"direct recursive call to {func_name}()",
                callee_name=func_name,
            )

        if func_name in _BUILTIN_EXCEPTION_MAP:
            for kind, desc, severity in _BUILTIN_EXCEPTION_MAP[func_name]:
                self._add_source(kind, node, trigger_condition=desc,
                                 severity=severity,
                                 description=f"call to {func_name}(): {desc}")
        elif func_name and "." in func_name:
            # Method call — check method map
            method = func_name.rsplit(".", 1)[-1]
            if method in _METHOD_EXCEPTION_MAP:
                for kind, desc, severity in _METHOD_EXCEPTION_MAP[method]:
                    self._add_source(kind, node, trigger_condition=desc,
                                     severity=severity,
                                     description=f"call to .{method}(): {desc}")
            else:
                # Unknown method — flag as propagation
                self._add_source(
                    ExceptionKind.CALL_PROPAGATION,
                    node,
                    trigger_condition="callee may raise",
                    severity=Severity.MEDIUM,
                    description=f"call to {func_name}()",
                    callee_name=func_name,
                )
        elif func_name and func_name not in _BUILTIN_EXCEPTION_MAP:
            # Non-builtin function call
            self._add_source(
                ExceptionKind.CALL_PROPAGATION,
                node,
                trigger_condition="callee may raise",
                severity=Severity.MEDIUM,
                description=f"call to {func_name}()",
                callee_name=func_name,
            )

        self.generic_visit(node)

    def visit_Assert(self, node: ast.Assert) -> None:
        """Assert statement → AssertionError."""
        self._add_source(
            ExceptionKind.ASSERTION_ERROR,
            node,
            trigger_condition="assertion condition is False",
            severity=Severity.INFO,
            description="assert statement",
        )
        self.generic_visit(node)

    def visit_Raise(self, node: ast.Raise) -> None:
        """Explicit raise → classify by exception type if possible."""
        kind = ExceptionKind.EXPLICIT_RAISE
        desc = "explicit raise"
        if node.exc is not None:
            exc_name = self._resolve_exception_name(node.exc)
            if exc_name:
                kind = exception_kind_from_name(exc_name)
                desc = f"raise {exc_name}"

        if node.cause is not None:
            self._add_source(
                ExceptionKind.CALL_PROPAGATION,
                node.cause,
                trigger_condition="raise cause expression may raise",
                severity=Severity.MEDIUM,
                description="raise ... from ... cause evaluation",
            )

        self._add_source(
            kind, node,
            trigger_condition="raise executed",
            severity=Severity.CRITICAL if node.exc else Severity.HIGH,
            description=desc,
        )
        self.generic_visit(node)

    def visit_Import(self, node: ast.Import) -> None:
        """Import statement → ImportError."""
        for alias in node.names:
            self._add_source(
                ExceptionKind.IMPORT_ERROR,
                node,
                trigger_condition=f"module '{alias.name}' not found",
                severity=Severity.LOW,
                description=f"import {alias.name}",
            )
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        """From-import → ImportError."""
        mod = node.module or "<unknown>"
        for alias in (node.names or []):
            self._add_source(
                ExceptionKind.IMPORT_ERROR,
                node,
                trigger_condition=f"cannot import '{alias.name}' from '{mod}'",
                severity=Severity.LOW,
                description=f"from {mod} import {alias.name}",
            )
        self.generic_visit(node)

    def visit_For(self, node: ast.For) -> None:
        """For loop → iteration protocol exceptions."""
        # for-loops handle StopIteration internally, but __iter__ can fail
        self._add_source(
            ExceptionKind.TYPE_ERROR,
            node,
            trigger_condition="object not iterable",
            severity=Severity.LOW,
            description="for-loop iteration",
        )
        self.generic_visit(node)

    def visit_With(self, node: ast.With) -> None:
        """With statement → context manager protocol exceptions."""
        for item in node.items:
            self._add_source(
                ExceptionKind.CALL_PROPAGATION,
                item.context_expr,
                trigger_condition="context manager __enter__ may raise",
                severity=Severity.LOW,
                description="with-statement __enter__",
            )
            self._add_source(
                ExceptionKind.CALL_PROPAGATION,
                item.context_expr,
                trigger_condition="context manager __exit__ may raise",
                severity=Severity.LOW,
                description="with-statement __exit__",
            )
        self.generic_visit(node)

    def visit_AsyncWith(self, node: ast.AsyncWith) -> None:
        for item in node.items:
            self._add_source(
                ExceptionKind.CALL_PROPAGATION,
                item.context_expr,
                trigger_condition="async context manager __aenter__ may raise",
                severity=Severity.LOW,
                description="async with-statement __aenter__",
            )
            self._add_source(
                ExceptionKind.CALL_PROPAGATION,
                item.context_expr,
                trigger_condition="async context manager __aexit__ may raise",
                severity=Severity.LOW,
                description="async with-statement __aexit__",
            )
        self.generic_visit(node)

    def visit_Delete(self, node: ast.Delete) -> None:
        """Delete statement → various exceptions."""
        for target in node.targets:
            if isinstance(target, ast.Subscript):
                self._add_source(
                    ExceptionKind.KEY_ERROR,
                    node,
                    trigger_condition="key/index not found for deletion",
                    severity=Severity.MEDIUM,
                    description="del subscript",
                )
            elif isinstance(target, ast.Attribute):
                self._add_source(
                    ExceptionKind.ATTRIBUTE_ERROR,
                    node,
                    trigger_condition="attribute not found for deletion",
                    severity=Severity.MEDIUM,
                    description="del attribute",
                )
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        """Unpacking assignment → ValueError."""
        for target in node.targets:
            if isinstance(target, (ast.Tuple, ast.List)):
                self._add_source(
                    ExceptionKind.UNPACK_ERROR,
                    node,
                    trigger_condition="wrong number of values to unpack",
                    severity=Severity.MEDIUM,
                    description="tuple/list unpacking",
                )
        self.generic_visit(node)

    def visit_Try(self, node: ast.Try) -> None:
        """Track try/except scope for caught exception analysis."""
        handlers = list(node.handlers)
        self._try_handlers.append(handlers)
        for child in node.body:
            self.visit(child)
        self._try_handlers.pop()

        # Visit handlers, else, and finally normally
        for handler in node.handlers:
            self.visit(handler)
        for child in node.orelse:
            self.visit(child)
        for child in node.finalbody:
            self.visit(child)

    # Python 3.11+ TryStar (try/except*)
    def visit_TryStar(self, node: Any) -> None:
        handlers = list(getattr(node, 'handlers', []))
        self._try_handlers.append(handlers)
        for child in getattr(node, 'body', []):
            self.visit(child)
        self._try_handlers.pop()
        for handler in handlers:
            self.visit(handler)
        for child in getattr(node, 'orelse', []):
            self.visit(child)
        for child in getattr(node, 'finalbody', []):
            self.visit(child)

    def visit_ListComp(self, node: ast.ListComp) -> None:
        """Comprehension iterators can raise."""
        self._add_comprehension_iter_sources(node)
        self.generic_visit(node)

    def visit_DictComp(self, node: ast.DictComp) -> None:
        self._add_comprehension_iter_sources(node)
        self.generic_visit(node)

    def visit_SetComp(self, node: ast.SetComp) -> None:
        self._add_comprehension_iter_sources(node)
        self.generic_visit(node)

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> None:
        self._add_comprehension_iter_sources(node)
        self.generic_visit(node)

    # ROUND 4 FIX: Add missing exception source visitors
    
    def visit_Name(self, node: ast.Name) -> None:
        """Detect NAME_ERROR from undefined variable access."""
        if isinstance(node.ctx, ast.Load):
            # ROUND 4 FIX: Don't flag function parameters as NAME_ERROR
            # Parameters are guaranteed to be defined when function is called
            if hasattr(self, '_current_function_params'):
                if node.id in self._current_function_params:
                    self.generic_visit(node)
                    return
                    
            # Don't flag module-level function names as NAME_ERROR
            if hasattr(self, '_module_function_names'):
                if node.id in self._module_function_names:
                    self.generic_visit(node)
                    return
                    
            # Also skip common built-ins that are likely defined
            common_builtins = {'len', 'str', 'int', 'float', 'bool', 'list', 'dict', 'set', 'tuple'}
            if node.id in common_builtins:
                self.generic_visit(node)
                return
                
            # Variable read that could be undefined
            self._add_source(
                ExceptionKind.NAME_ERROR,
                node,
                trigger_condition=f"'{node.id}' not defined",
                description=f"name '{node.id}' is not defined",
            )
        self.generic_visit(node)
    
    def visit_Await(self, node: ast.Await) -> None:
        """Detect TIMEOUT_ERROR from async operations."""
        # await can timeout in asyncio contexts
        self._add_source(
            ExceptionKind.TIMEOUT_ERROR,
            node,
            trigger_condition="await timeout",
            description="await operation may timeout",
        )
        self.generic_visit(node)
    
    def visit_AsyncFor(self, node: ast.AsyncFor) -> None:
        """Detect TIMEOUT_ERROR and ITERATION_ERROR from async iteration."""
        self._add_source(
            ExceptionKind.TIMEOUT_ERROR,
            node,
            trigger_condition="async iteration timeout",
            description="async for loop may timeout",
        )
        self._add_source(
            ExceptionKind.ITERATION_ERROR,
            node,
            trigger_condition="async iteration failure", 
            description="async iterator may fail",
        )
        self.generic_visit(node)

    # ── Helpers ───────────────────────────────────────────────────

    def _add_source(self, kind: ExceptionKind, node: ast.AST,
                    trigger_condition: str = "",
                    severity: Severity = Severity.MEDIUM,
                    description: str = "",
                    callee_name: str | None = None) -> None:
        """Record a potential exception source."""
        location = SourceLocation(
            filename=self._filename,
            function=self._current_function,
            lineno=getattr(node, 'lineno', 0),
            col_offset=getattr(node, 'col_offset', 0),
            end_lineno=getattr(node, 'end_lineno', None),
            end_col_offset=getattr(node, 'end_col_offset', None),
        )

        # Check if this exception kind is caught by an enclosing try/except
        handler = self._find_handler(kind)

        source = ExceptionSource(
            kind=kind,
            location=location,
            trigger_condition=trigger_condition,
            ast_node=node,
            severity=severity,
            description=description,
            callee_name=callee_name,
            caught_by=handler,
        )

        self._sources.append(source)
        if not self._in_function:
            self._module_sources.append(source)

    def _add_comprehension_iter_sources(self, node: ast.AST) -> None:
        generators = getattr(node, "generators", []) or []
        for gen in generators:
            self._add_source(
                ExceptionKind.TYPE_ERROR,
                gen.iter,
                trigger_condition="object not iterable in comprehension",
                severity=Severity.LOW,
                description="comprehension/generator iteration",
            )

    def _find_handler(self, kind: ExceptionKind) -> ast.ExceptHandler | None:
        """Check if *kind* is caught by any enclosing try/except handler."""
        if not self._try_handlers:
            return None

        exc_class_name = _kind_to_class_name(kind)

        for handlers in reversed(self._try_handlers):
            for handler in handlers:
                if handler.type is None:
                    # Bare except: catches everything
                    return handler
                caught_names = self._handler_exception_names(handler)
                if exc_class_name in caught_names or "Exception" in caught_names:
                    return handler
                # Check for base class catching
                if _is_subclass_name(exc_class_name, caught_names):
                    return handler
        return None

    @staticmethod
    def _handler_exception_names(handler: ast.ExceptHandler) -> set[str]:
        """Extract exception class names from a handler."""
        if handler.type is None:
            return {"BaseException"}
        if isinstance(handler.type, ast.Name):
            return {handler.type.id}
        if isinstance(handler.type, ast.Tuple):
            names: set[str] = set()
            for elt in handler.type.elts:
                if isinstance(elt, ast.Name):
                    names.add(elt.id)
            return names
        if isinstance(handler.type, ast.Attribute):
            return {handler.type.attr}
        return set()

    @staticmethod
    def _resolve_call_name(node: ast.Call) -> str:
        """Best-effort resolution of the callable name."""
        if isinstance(node.func, ast.Name):
            return node.func.id
        if isinstance(node.func, ast.Attribute):
            base = ExceptionSourceFinder._resolve_call_name_expr(node.func.value)
            return f"{base}.{node.func.attr}" if base else node.func.attr
        return ""

    @staticmethod
    def _resolve_call_name_expr(node: ast.expr) -> str:
        """Resolve the base of an attribute chain."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            base = ExceptionSourceFinder._resolve_call_name_expr(node.value)
            return f"{base}.{node.attr}" if base else node.attr
        return ""

    @staticmethod
    def _resolve_exception_name(node: ast.expr) -> str:
        """Resolve the exception class name from a raise expression."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Call):
            return ExceptionSourceFinder._resolve_exception_name(node.func)
        if isinstance(node, ast.Attribute):
            return node.attr
        return ""


# ═══════════════════════════════════════════════════════════════════
# 5.  Helpers
# ═══════════════════════════════════════════════════════════════════

def _op_name(op: ast.operator) -> str:
    """Human-readable name for a binary operator."""
    return {
        ast.Div: "division",
        ast.FloorDiv: "floor division",
        ast.Mod: "modulo",
        ast.Pow: "exponentiation",
    }.get(type(op), type(op).__name__)


_KIND_TO_CLASS: dict[ExceptionKind, str] = {
    ExceptionKind.ZERO_DIVISION: "ZeroDivisionError",
    ExceptionKind.OVERFLOW: "OverflowError",
    ExceptionKind.MATH_DOMAIN: "ValueError",
    ExceptionKind.INDEX_ERROR: "IndexError",
    ExceptionKind.KEY_ERROR: "KeyError",
    ExceptionKind.STOP_ITERATION: "StopIteration",
    ExceptionKind.TYPE_ERROR: "TypeError",
    ExceptionKind.VALUE_ERROR: "ValueError",
    ExceptionKind.ATTRIBUTE_ERROR: "AttributeError",
    ExceptionKind.NAME_ERROR: "NameError",
    ExceptionKind.IMPORT_ERROR: "ImportError",
    ExceptionKind.ASSERTION_ERROR: "AssertionError",
    ExceptionKind.EXPLICIT_RAISE: "Exception",
    ExceptionKind.OS_ERROR: "OSError",
    ExceptionKind.RUNTIME_ERROR: "RuntimeError",
    ExceptionKind.TIMEOUT_ERROR: "TimeoutError",
    ExceptionKind.CALL_PROPAGATION: "Exception",
    ExceptionKind.UNPACK_ERROR: "ValueError",
    ExceptionKind.ITERATION_ERROR: "TypeError",
    ExceptionKind.CUSTOM: "Exception",
}


def _kind_to_class_name(kind: ExceptionKind) -> str:
    return _KIND_TO_CLASS.get(kind, "Exception")


# Python exception hierarchy for is-a checking
_EXCEPTION_HIERARCHY: dict[str, set[str]] = {
    "BaseException": {"Exception", "KeyboardInterrupt", "SystemExit",
                      "GeneratorExit"},
    "Exception": {"ArithmeticError", "LookupError", "OSError", "ValueError",
                  "TypeError", "AttributeError", "NameError", "ImportError",
                  "RuntimeError", "StopIteration", "AssertionError",
                  "UnicodeError", "BufferError", "EOFError"},
    "ArithmeticError": {"ZeroDivisionError", "OverflowError",
                        "FloatingPointError"},
    "LookupError": {"IndexError", "KeyError"},
    "OSError": {"FileNotFoundError", "PermissionError", "FileExistsError",
                "IsADirectoryError", "NotADirectoryError", "TimeoutError",
                "ConnectionError", "BrokenPipeError"},
    "RuntimeError": {"RecursionError", "NotImplementedError"},
    "ValueError": {"UnicodeError", "UnicodeDecodeError", "UnicodeEncodeError"},
    "ImportError": {"ModuleNotFoundError"},
    "ConnectionError": {"ConnectionRefusedError", "ConnectionResetError",
                        "ConnectionAbortedError"},
}


def _is_subclass_name(child: str, parents: set[str]) -> bool:
    """Check if exception class *child* is a subclass of any *parent*."""
    if child in parents:
        return True
    # Walk up the hierarchy
    for parent, children in _EXCEPTION_HIERARCHY.items():
        if child in children and parent in parents:
            return True
    # Transitive check
    for parent, children in _EXCEPTION_HIERARCHY.items():
        if child in children:
            if _is_subclass_name(parent, parents):
                return True
    return False


# ═══════════════════════════════════════════════════════════════════
# 6.  Convenience API
# ═══════════════════════════════════════════════════════════════════

def find_exception_sources(source: str,
                           filename: str = "<string>") -> ModuleSourceSummary:
    """One-shot exception source analysis for a source string."""
    finder = ExceptionSourceFinder(filename)
    return finder.analyze_source(source, filename)


def find_exception_sources_in_module(module: Any) -> ModuleSourceSummary:
    """Analyze a live Python module for exception sources."""
    try:
        source = inspect.getsource(module)
        filename = getattr(module, '__file__', module.__name__)
    except (TypeError, OSError):
        return ModuleSourceSummary(module_path=getattr(module, '__name__', '<unknown>'))
    return find_exception_sources(source, filename)


def find_exception_sources_in_function(fn: Any) -> FunctionSourceSummary:
    """Analyze a single callable for exception sources."""
    try:
        source = textwrap.dedent(inspect.getsource(fn))
        tree = ast.parse(source)
    except (TypeError, OSError, SyntaxError):
        return FunctionSourceSummary(name=getattr(fn, '__name__', '<unknown>'))

    finder = ExceptionSourceFinder(getattr(fn, '__code__', None) and
                                   fn.__code__.co_filename or "<unknown>")
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return finder.analyze_function(node)

    return FunctionSourceSummary(name=getattr(fn, '__name__', '<unknown>'))


def _collect_target_names(node: ast.expr, out: set[str]) -> None:
    """Hole 4 helper — collect names bound by an assignment target."""
    if isinstance(node, ast.Name):
        out.add(node.id)
    elif isinstance(node, (ast.Tuple, ast.List)):
        for elt in node.elts:
            _collect_target_names(elt, out)
    elif isinstance(node, ast.Starred):
        _collect_target_names(node.value, out)
    # Subscript / Attribute targets don't bind a new name.

