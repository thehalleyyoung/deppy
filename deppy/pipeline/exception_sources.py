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
# ── Safe builtin names that don't raise NAME_ERROR ──────────────────
#
# Includes Python's full builtins module + module-level dunders.
# Exhaustive list avoids whack-a-mole for missing entries.

import builtins as _builtins_mod  # noqa: E402

_SAFE_BUILTIN_NAMES: set[str] = set(dir(_builtins_mod)) | {
    "__name__", "__file__", "__doc__", "__package__", "__loader__",
    "__spec__", "__builtins__", "__path__", "__all__", "__author__",
    "__version__", "__cached__", "__dict__", "__class__", "__module__",
    "__init__", "__new__", "__del__", "__repr__", "__str__", "__hash__",
    "__eq__", "__ne__", "__lt__", "__le__", "__gt__", "__ge__",
    "__getitem__", "__setitem__", "__delitem__", "__len__",
    "__iter__", "__next__", "__contains__",
    "__add__", "__sub__", "__mul__", "__truediv__", "__floordiv__",
    "__mod__", "__pow__", "__neg__", "__pos__", "__abs__",
    "self", "cls",
}


# ── Standard methods on built-in collection types ────────────────────

_LIST_METHODS: frozenset[str] = frozenset({
    "append", "extend", "insert", "remove", "pop", "clear",
    "index", "count", "sort", "reverse", "copy",
    "__len__", "__iter__", "__contains__", "__getitem__",
    "__setitem__", "__delitem__", "__add__", "__mul__",
})

_DICT_METHODS: frozenset[str] = frozenset({
    "keys", "values", "items", "get", "pop", "popitem", "setdefault",
    "update", "clear", "copy", "fromkeys",
    "__len__", "__iter__", "__contains__", "__getitem__",
    "__setitem__", "__delitem__",
})


# ── Known-safe import roots ──────────────────────────────────────────
#
# Imports of modules in this set are not flagged as IMPORT_ERROR
# sources.  ``deppy`` itself is here (its absence would crash before
# we got to the analyzer) along with the standard-library roots that
# are guaranteed to ship with CPython.  Users can extend the set via
# the public ``register_safe_import`` helper at the bottom of this
# file.

_SAFE_IMPORT_ROOTS: set[str] = {
    "deppy",
    "__future__",
    "typing",
    "dataclasses",
    "abc",
    "collections", "itertools", "functools", "operator",
    "math", "cmath", "decimal", "fractions", "random", "statistics",
    "re", "string", "textwrap", "unicodedata",
    "os", "sys", "io", "pathlib", "shutil", "tempfile",
    "json", "csv", "pickle", "copy", "pprint",
    "datetime", "time", "calendar",
    "logging", "warnings", "traceback",
    "enum", "types", "inspect", "importlib",
    "ast", "tokenize", "symtable",
    "concurrent", "threading", "multiprocessing", "queue",
    "asyncio", "contextlib", "contextvars",
    "hashlib", "hmac", "secrets",
    "struct", "array", "weakref",
    "uuid", "ipaddress", "socket", "ssl",
    "urllib", "http", "email", "base64", "binascii",
    "subprocess",
    "z3",  # SMT solver — used by deppy's own pipeline
}


def _is_safe_import(name: str) -> bool:
    """``name`` is a known-good import root or sub-module thereof."""
    if not name:
        return False
    root = name.split(".", 1)[0]
    return root in _SAFE_IMPORT_ROOTS


def register_safe_import(name: str) -> None:
    """Register an additional module name as safe (no IMPORT_ERROR)."""
    if name:
        _SAFE_IMPORT_ROOTS.add(name)


_TYPING_SUBSCRIPT_NAMES: frozenset[str] = frozenset({
    "Optional", "Union", "List", "Dict", "Set", "FrozenSet", "Tuple",
    "Callable", "Iterable", "Iterator", "Generator", "AsyncIterator",
    "AsyncGenerator", "Awaitable", "Coroutine", "Mapping",
    "MutableMapping", "Sequence", "MutableSequence", "Collection",
    "Container", "Reversible", "AbstractSet", "MutableSet", "Type",
    "ClassVar", "Final", "Annotated", "Literal", "TypeGuard", "TypeIs",
    "Concatenate", "ParamSpec", "TypeVar", "Generic", "Protocol",
    "TypedDict", "Required", "NotRequired", "Self", "LiteralString",
    "Never", "NoReturn", "Any",
    # builtin generic aliases (Python 3.9+)
    "list", "dict", "set", "frozenset", "tuple", "type",
})


def _extract_requires_bounds(
    decorator: ast.expr,
) -> tuple[set[str], set[str]]:
    """Extract ``(bounded_names, positive_names)`` from a single
    decorator expression that looks like ``@requires(lambda ARGS:
    BODY)`` or ``@requires("X COMP Y")``.

    Returns empty sets for any decorator we can't parse.

    The bounds we recognise mirror those in
    ``ExceptionSourceFinder._extract_int_guards``: ``X < EXPR``,
    ``EXPR > X``, ``X > 0``, etc.  The caller adds these to its
    own narrowing scope, capturing the user's commitment about
    parameter validity.
    """
    bounded: set[str] = set()
    positive: set[str] = set()
    # @requires(...)  →  Call where func is "requires"
    if not isinstance(decorator, ast.Call):
        return bounded, positive
    func = decorator.func
    name = ""
    if isinstance(func, ast.Name):
        name = func.id
    elif isinstance(func, ast.Attribute):
        name = func.attr
    if name not in {"requires", "ensures", "invariant"}:
        return bounded, positive
    if not decorator.args:
        return bounded, positive
    arg = decorator.args[0]
    if isinstance(arg, ast.Lambda):
        body = arg.body
        # Use the static helper from ExceptionSourceFinder for the
        # actual bound extraction (it walks Compare / BoolOp nodes).
        b, p = ExceptionSourceFinder._extract_bounds_static(body)
        bounded |= b
        positive |= p
    elif isinstance(arg, ast.Constant) and isinstance(arg.value, str):
        # @requires("0 <= i < len(xs)")  →  parse the string.
        try:
            tree = ast.parse(arg.value, mode="eval").body
            b, p = ExceptionSourceFinder._extract_bounds_static(tree)
            bounded |= b
            positive |= p
        except SyntaxError:
            pass
    return bounded, positive


def _is_main_guard(node: ast.If) -> bool:
    """``if __name__ == "__main__":`` Python-standard script entry guard.

    Suppress exception sources within this block — it's a sanity-check
    / script invocation, not a verification target.
    """
    test = node.test
    if not isinstance(test, ast.Compare):
        return False
    if not (isinstance(test.left, ast.Name) and test.left.id == "__name__"):
        return False
    if len(test.ops) != 1 or not isinstance(test.ops[0], ast.Eq):
        return False
    if len(test.comparators) != 1:
        return False
    comp = test.comparators[0]
    if not (isinstance(comp, ast.Constant) and comp.value == "__main__"):
        return False
    return True


def _is_known_iterable(node: ast.expr) -> bool:
    """``node`` is a syntactic form known to be iterable without raising
    TypeError on ``__iter__``: literal collections, range/enumerate/zip,
    string literals, etc."""
    if isinstance(node, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
        return True
    if isinstance(node, ast.ListComp) or isinstance(node, ast.SetComp) \
            or isinstance(node, ast.DictComp) \
            or isinstance(node, ast.GeneratorExp):
        return True
    if isinstance(node, ast.Constant) and isinstance(node.value, (str, bytes)):
        return True
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
            and node.func.id in {
                "range", "enumerate", "zip", "map", "filter",
                "reversed", "sorted", "iter", "list", "tuple", "set",
                "frozenset", "dict",
            }:
        return True
    return False


def _is_typing_subscript(node: ast.Subscript) -> bool:
    """``node.value`` is a typing construct that uses ``__class_getitem__``
    rather than ``__getitem__`` — safe by construction."""
    val = node.value
    if isinstance(val, ast.Name):
        return val.id in _TYPING_SUBSCRIPT_NAMES
    if isinstance(val, ast.Attribute):
        return val.attr in _TYPING_SUBSCRIPT_NAMES
    return False


def _function_has_base_case(
    node: "ast.FunctionDef | ast.AsyncFunctionDef",
) -> bool:
    """Heuristic: does ``node`` start with a guarded early-return that
    would terminate the recursion?

    Recognised patterns at the function-body head:

      * ``if X is None: return ...``
      * ``if not X: return ...``
      * ``if X == []: return ...`` / ``if X == 0: return ...``
      * ``if len(X) == 0: return ...``  / ``if len(X) <= 0: ...``

    Walks the prefix of the body that consists of these guard-and-return
    statements.  As soon as a guard with an inner ``return`` is found,
    we declare the function has a base case.
    """
    if not getattr(node, "body", None):
        return False
    for stmt in node.body[:5]:  # check the first few statements
        if not isinstance(stmt, ast.If):
            continue
        # Inner body must contain a return.
        has_return = any(isinstance(s, ast.Return) for s in stmt.body)
        if not has_return:
            continue
        test = stmt.test
        # Pattern 1: ``X is None``
        if isinstance(test, ast.Compare) and len(test.ops) == 1 \
                and isinstance(test.ops[0], (ast.Is, ast.Eq)) \
                and len(test.comparators) == 1 \
                and isinstance(test.comparators[0], ast.Constant) \
                and test.comparators[0].value is None:
            return True
        # Pattern 2: ``not X``
        if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
            return True
        # Pattern 3: ``len(X) == 0`` / ``len(X) <= 0``
        if isinstance(test, ast.Compare) \
                and isinstance(test.left, ast.Call) \
                and isinstance(test.left.func, ast.Name) \
                and test.left.func.id == "len" \
                and len(test.ops) == 1 \
                and isinstance(test.ops[0], (ast.Eq, ast.LtE, ast.Lt)) \
                and len(test.comparators) == 1 \
                and isinstance(test.comparators[0], ast.Constant) \
                and test.comparators[0].value == 0:
            return True
        # Pattern 4: ``X == []`` / ``X == 0``
        if isinstance(test, ast.Compare) and len(test.ops) == 1 \
                and isinstance(test.ops[0], ast.Eq) \
                and len(test.comparators) == 1:
            comp = test.comparators[0]
            if isinstance(comp, ast.Constant) and comp.value == 0:
                return True
            if isinstance(comp, ast.List) and not comp.elts:
                return True
    return False


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
        # Local "definitely not None" set, populated by ``visit_If``
        # patterns like ``if x is None: return ...`` (post-if x is
        # not-None) or ``if x is not None: <body>`` (within body).
        # Suppresses spurious ATTRIBUTE_ERROR sources on x.attr
        # when x has been narrowed.
        self._definitely_not_none: set[str] = set()
        # Field annotations from the enclosing class (PC pain point):
        # used to suppress ATTRIBUTE_ERROR on ``self.<field>`` when the
        # field is declared (and thus guaranteed by Python's dataclass
        # / __init__ contract).
        self._field_annotations: dict[str, str] = {}
        # Range-loop variables in scope (PB): loop ``for i in range(n)``
        # narrows i to [0, n).  Subscript visit consults this set to
        # suppress IndexError on ``data[i]``.
        self._range_loop_vars: set[str] = set()
        # Names known to be lists (for receiver-shape detection).
        self._known_list_names: set[str] = set()
        # Flow-sensitive index narrowing.
        self._index_guarded: set[str] = set()
        self._index_positive: set[str] = set()
        # Class-instance tracking: ``h = MinHeap()`` adds h → "MinHeap"
        # to ``_var_classes``.  Method calls on h then consult
        # ``_class_members[MinHeap]`` for valid attributes/methods.
        self._var_classes: dict[str, str] = {}
        # Class members: built up by visit_ClassDef.
        self._class_members: dict[str, set[str]] = {}

    # ── Public API ────────────────────────────────────────────────

    def analyze_module(self, tree: ast.Module) -> ModuleSourceSummary:
        """Analyze an entire module AST, returning a complete summary."""
        self._sources = []
        self._function_summaries = []
        self._module_sources = []
        self._current_function = "<module>"
        self._in_function = False
        
        # Pre-pass: collect all function and class names defined in
        # this module to avoid NAME_ERROR false positives.  Classes
        # are valid call targets (``BST(value=v)``); also include
        # imported names so ``from foo import X`` is recognised.
        module_function_names = set()
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                module_function_names.add(node.name)
            elif isinstance(node, ast.ClassDef):
                module_function_names.add(node.name)
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    name = alias.asname or alias.name.split(".")[0]
                    module_function_names.add(name)
            elif isinstance(node, ast.ImportFrom):
                for alias in node.names:
                    if alias.name == "*":
                        continue
                    module_function_names.add(alias.asname or alias.name)
        self._module_function_names = module_function_names

        # Pre-pass: collect module-level *local* names (assigns, for
        # loops, with-bindings) so module-level code (e.g. ``if
        # __name__ == "__main__":``) doesn't trip NAME_ERROR on its
        # own loop / assignment variables.
        module_local_names: set[str] = set()
        for node in tree.body:
            for sub in ast.walk(node):
                if isinstance(sub, ast.Assign):
                    for tgt in sub.targets:
                        _collect_target_names(tgt, module_local_names)
                elif isinstance(sub, (ast.AnnAssign, ast.AugAssign)):
                    _collect_target_names(sub.target, module_local_names)
                elif isinstance(sub, (ast.For, ast.AsyncFor)):
                    _collect_target_names(sub.target, module_local_names)
                elif isinstance(sub, (ast.With, ast.AsyncWith)):
                    for item in sub.items:
                        if item.optional_vars is not None:
                            _collect_target_names(
                                item.optional_vars, module_local_names,
                            )
                elif isinstance(sub, ast.NamedExpr):
                    _collect_target_names(sub.target, module_local_names)
                elif isinstance(sub, (ast.ListComp, ast.SetComp,
                                       ast.DictComp, ast.GeneratorExp)):
                    for gen in sub.generators:
                        _collect_target_names(gen.target, module_local_names)
        self._module_local_names = module_local_names
        
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

        # Extract parameter names + annotations.  Param-name set used
        # for NAME_ERROR suppression; param annotations used to infer
        # whether ``len(p)`` / ``range(p)`` / etc. are safe (PA, PE).
        param_names = set()
        param_anns: dict[str, str] = {}
        if hasattr(node, 'args'):
            args = node.args
            for arg in getattr(args, 'args', []):
                param_names.add(arg.arg)
                if arg.annotation is not None:
                    param_anns[arg.arg] = ast.unparse(arg.annotation)
            for arg in getattr(args, 'posonlyargs', []):
                param_names.add(arg.arg)
                if arg.annotation is not None:
                    param_anns[arg.arg] = ast.unparse(arg.annotation)
            for arg in getattr(args, 'kwonlyargs', []):
                param_names.add(arg.arg)
                if arg.annotation is not None:
                    param_anns[arg.arg] = ast.unparse(arg.annotation)
            if getattr(args, 'vararg', None):
                param_names.add(args.vararg.arg)
            if getattr(args, 'kwarg', None):
                param_names.add(args.kwarg.arg)
        # Track param annotations on the analyzer so visit_Subscript /
        # visit_Call can consult them when deciding whether the
        # receiver / argument is provably a list / iterable / int.
        old_param_anns = getattr(self, '_current_function_param_anns', {})
        self._current_function_param_anns = param_anns
        # Names known to be lists from this function's params.
        list_param_names: set[str] = set()
        for name, ann in param_anns.items():
            if ann.startswith(("list", "List")) or "list[" in ann \
                    or "List[" in ann:
                list_param_names.add(name)
        old_known_lists = self._known_list_names
        self._known_list_names = old_known_lists | list_param_names
        
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
        # Reset the not-None narrowing scope when entering a new function.
        old_not_none = self._definitely_not_none
        self._definitely_not_none = set()
        # Detect an early-return base case for recursion termination.
        old_has_base_case = getattr(self, '_current_function_has_base_case', False)
        self._current_function_has_base_case = _function_has_base_case(node)

        # Extract guarded indices from @requires decorators.  When the
        # user has written ``@requires(lambda self, i: 0 <= i < len(...))``,
        # we read the lambda body and add any name guarded by that
        # comparison to the function's narrowing scope.  This is
        # informal — it captures the user's commitment about
        # parameter validity.
        old_guarded = set(self._index_guarded)
        old_positive = set(self._index_positive)
        old_derived = set(getattr(self, '_index_derived_guarded', set()))
        self._index_derived_guarded = old_derived
        for decorator in getattr(node, 'decorator_list', []):
            req_bounds, req_positive = _extract_requires_bounds(decorator)
            self._index_guarded |= req_bounds
            self._index_positive |= req_positive

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
        # Restore the not-None narrowing scope.
        self._definitely_not_none = old_not_none
        # Restore base-case detection.
        self._current_function_has_base_case = old_has_base_case
        # Restore param annotations + list-name set.
        self._current_function_param_anns = old_param_anns
        self._known_list_names = old_known_lists
        # Restore index narrowing.
        self._index_guarded = old_guarded
        self._index_positive = old_positive
        self._index_derived_guarded = old_derived

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
        """Visit a class — collect dataclass-style field annotations
        + method names.  Populates both ``_field_annotations`` (for
        ``self.<field>`` checks inside the class body) and
        ``_class_members`` (for instances of the class outside the
        class body, e.g. ``h.push()`` after ``h = MinHeap()``)."""
        old_fields = self._field_annotations
        old_class = self._current_class
        new_fields = dict(old_fields)
        members: set[str] = set()
        for stmt in node.body:
            if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                ann_text = ast.unparse(stmt.annotation) if stmt.annotation else ""
                new_fields[stmt.target.id] = ann_text
                members.add(stmt.target.id)
            elif isinstance(stmt, ast.Assign):
                for tgt in stmt.targets:
                    if isinstance(tgt, ast.Name):
                        new_fields[tgt.id] = ""
                        members.add(tgt.id)
            elif isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                new_fields[stmt.name] = ""
                members.add(stmt.name)
        # Add standard dunders and common Python methods that all
        # classes get for free.
        members |= {
            "__init__", "__repr__", "__str__", "__hash__",
            "__eq__", "__ne__", "__lt__", "__le__", "__gt__", "__ge__",
            "__class__", "__dict__", "__module__", "__doc__",
            "__getattribute__", "__setattr__", "__delattr__",
        }
        # Frozen / hashable dataclasses and any class with __len__
        # method explicitly: visible.
        if "__len__" in members or any(
                isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef))
                and s.name == "__len__" for s in node.body):
            members.add("__len__")
        self._class_members[node.name] = members
        self._field_annotations = new_fields
        self._current_class = node.name
        self.generic_visit(node)
        self._field_annotations = old_fields
        self._current_class = old_class

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
        """Indexing → IndexError / KeyError.

        Suppressed when the receiver is a known typing construct.

        Receiver-aware: when the analyzer can prove the receiver is a
        list (loop bound by ``range``, literal list, ``self.<field>``
        whose annotation is ``list[...]``), only ``IndexError`` is
        flagged.  When the receiver is a dict, only ``KeyError``.
        Generic case still flags both (conservative).
        """
        if _is_typing_subscript(node):
            self.generic_visit(node)
            return

        # Range-bounded loop variable narrowing (PB): ``for i in range(n):
        # ... data[i] ...`` is safe iff i ∈ [0, n) and len(data) >= n.
        # We track the in-range loop variable in ``_range_loop_vars``;
        # when the subscript index *is* a known range-loop variable AND
        # the receiver is a list-shaped value with consistent length,
        # we suppress IndexError (KeyError still suppressed because list).
        is_list_receiver = self._receiver_is_list(node.value)
        is_dict_receiver = self._receiver_is_dict(node.value)
        index_is_in_range = self._index_is_known_in_range(node.slice)

        if isinstance(node.slice, ast.Constant) and isinstance(node.slice.value, int):
            # Constant int index — always suppress KEY_ERROR (lists
            # don't raise it; dicts use string/hashable keys, not int
            # constants in this shape).
            if not is_list_receiver and not index_is_in_range:
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
            # Dynamic index — flag IndexError and/or KeyError per
            # receiver shape.  When the index is a range-loop var
            # bounded by the receiver's length, suppress IndexError too.
            if not index_is_in_range:
                if is_dict_receiver:
                    # Dict path: only KeyError.
                    self._add_source(
                        ExceptionKind.KEY_ERROR,
                        node,
                        trigger_condition="key not present",
                        severity=Severity.MEDIUM,
                        description="dynamic subscript access (dict key)",
                    )
                elif is_list_receiver:
                    # List path: only IndexError.
                    self._add_source(
                        ExceptionKind.INDEX_ERROR,
                        node,
                        trigger_condition="index out of range",
                        severity=Severity.MEDIUM,
                        description="dynamic subscript access",
                    )
                else:
                    # Unknown receiver — both possibilities.
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

    def _receiver_is_list(self, node: ast.expr) -> bool:
        """Best-effort check: the receiver is provably a list."""
        if isinstance(node, ast.List):
            return True
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
                and node.func.id in {"list", "sorted", "reversed", "range"}:
            return True
        # ``self.field`` whose annotation is list[...] or List[...].
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) \
                and node.value.id == "self":
            ann = self._field_annotations.get(node.attr, "")
            if ann and ("list[" in ann or "List[" in ann or ann == "list"
                        or ann.startswith("tuple")):
                return True
        # Loop iterable name we tracked.
        if isinstance(node, ast.Name) and node.id in getattr(
                self, '_known_list_names', set()):
            return True
        return False

    def _receiver_is_dict(self, node: ast.expr) -> bool:
        """Best-effort check: the receiver is provably a dict."""
        if isinstance(node, ast.Dict):
            return True
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
                and node.func.id == "dict":
            return True
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) \
                and node.value.id == "self":
            ann = self._field_annotations.get(node.attr, "")
            if ann and ("dict[" in ann or "Dict[" in ann or ann == "dict"):
                return True
        return False

    def _index_is_known_in_range(self, slice_node: ast.expr) -> bool:
        """The subscript index is provably non-negative AND
        bounded above.  Sources of this knowledge:

          * Range-loop variable: ``for i in range(n)`` makes ``i``
            both ≥ 0 and < n.
          * Flow-sensitive: inside ``if i < n: <body>`` (or
            ``while i < n``) i is bounded above; if also
            ``if i >= 0`` / range-loop / positive guard is in scope,
            then i is non-negative.
          * Integer literal: ``data[0]`` / ``data[5]`` etc. handled
            in the constant branch.
          * Computed expression involving a guarded name: ``data[i-1]``
            inside ``while i > 0`` is safe (i-1 ≥ 0 and i-1 < length
            iff i < length+1, which we approximate by trusting the
            programmer's guard).

        Conservative: we treat any subscript by a name in the
        ``_index_guarded`` set as in-range, since the *guard* is the
        user's commitment that the index is valid.  This is the
        standard refinement-type assumption.
        """
        if isinstance(slice_node, ast.Name):
            name = slice_node.id
            if name in getattr(self, '_range_loop_vars', set()):
                return True
            # Flow-sensitive: name was ``if X < N``-bounded OR
            # known-positive (``while i > 0`` style — the
            # programmer's commitment that the index has been kept
            # valid through the loop).
            if name in self._index_guarded:
                return True
            if name in self._index_positive:
                return True
        # Integer-arithmetic-on-guarded-name: ``i - 1`` when i is
        # positive, or ``parent`` from ``parent = (i - 1) // 2``
        # when i is positive (parent is then non-negative).  We
        # recognise the very narrow ``BinOp(Name, op, Constant)``
        # shape; broader expressions fall through.
        if isinstance(slice_node, ast.BinOp):
            # data[i - 1] / data[i + 1] / data[2*i + 1] etc. — when
            # all the names involved are guarded.
            if self._binop_indexes_in_range(slice_node):
                return True
        # Names referencing computed locals like ``parent`` / ``left``
        # / ``right`` / ``smallest`` / ``mid`` (heap-/binsearch-style
        # convention) are treated as "guarded by the prior assignment"
        # when the function has at least one length comparison guard
        # in scope — we record their guard status during visit_Assign.
        if isinstance(slice_node, ast.Name) \
                and slice_node.id in getattr(self, '_index_derived_guarded', set()):
            return True
        return False

    def _binop_indexes_in_range(self, node: ast.BinOp) -> bool:
        """Check whether a simple BinOp index expression is in range.

        Recognises ``i +/- const``, ``2*i +/- const``, ``parent +/- const``
        when the inner name is in ``_index_guarded`` or
        ``_index_positive``.
        """
        # Walk the BinOp; collect Name leaves and check all are guarded.
        names: list[str] = []
        def collect(n: ast.expr) -> bool:
            if isinstance(n, ast.Name):
                names.append(n.id)
                return True
            if isinstance(n, ast.Constant) and isinstance(n.value, int):
                return True
            if isinstance(n, ast.BinOp):
                return collect(n.left) and collect(n.right)
            return False
        if not collect(node):
            return False
        if not names:
            return False
        # All names must be guarded (under the programmer's commitment).
        guarded = self._index_guarded | self._index_positive | self._range_loop_vars
        return all(n in guarded for n in names)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        """Attribute access → AttributeError.

        Suppressed when:
          * the receiver is a name in ``_definitely_not_none``
            (narrowed by an enclosing ``is None`` check); or
          * the receiver is ``self`` and the attribute is a known
            class field (PC pain point); or
          * the receiver is ``self.<list_field>`` and the attribute
            is a known list method (e.g. ``self._data.pop``,
            ``self._data.append``); or
          * the receiver is an instance of a known class (created
            via ``h = ClassName()``) and the attribute is a known
            method/field of that class.
        """
        receiver = node.value

        if isinstance(receiver, ast.Name):
            if receiver.id in self._definitely_not_none:
                self.generic_visit(node)
                return
            # PC: self.<field> in the current class.
            if receiver.id == "self" and node.attr in self._field_annotations:
                self.generic_visit(node)
                return
            # Class-instance tracking: ``h = MinHeap()`` — h's class
            # is recorded in ``_var_classes``; methods on h are then
            # known.
            cls_name = getattr(self, '_var_classes', {}).get(receiver.id)
            if cls_name and node.attr in getattr(
                    self, '_class_members', {}).get(cls_name, set()):
                self.generic_visit(node)
                return
            # Known list / dict / str names get standard methods for free.
            if receiver.id in self._known_list_names \
                    and node.attr in _LIST_METHODS:
                self.generic_visit(node)
                return

        # Chained: ``self.field.method`` where field is a known list
        # → AttributeError unreachable for list methods.
        if isinstance(receiver, ast.Attribute) \
                and isinstance(receiver.value, ast.Name) \
                and receiver.value.id == "self":
            field_ann = self._field_annotations.get(receiver.attr, "")
            if field_ann.startswith(("list", "List")) \
                    or "list[" in field_ann or "List[" in field_ann:
                if node.attr in _LIST_METHODS:
                    self.generic_visit(node)
                    return
            if field_ann.startswith(("dict", "Dict")) or "dict[" in field_ann:
                if node.attr in _DICT_METHODS:
                    self.generic_visit(node)
                    return

        self._add_source(
            ExceptionKind.ATTRIBUTE_ERROR,
            node,
            trigger_condition=f"object has no attribute '{node.attr}'",
            severity=Severity.LOW,
            description=f"attribute access .{node.attr}",
        )
        self.generic_visit(node)

    # ── Range-loop variable tracking ───────────────────────────────

    def visit_For(self, node: ast.For) -> None:
        """For loop → iteration protocol exceptions.

        Suppressed when iterating over a *known iterable* literal:
        list, tuple, set, dict, ``range(...)``, or ``enumerate(...)``,
        ``zip(...)``, ``map(...)``, ``filter(...)``, ``reversed(...)``,
        ``sorted(...)``.  These can't raise TypeError at iteration
        start.

        Additionally tracks ``for i in range(n):`` bound variables in
        ``_range_loop_vars`` for the duration of the loop body, so
        ``data[i]`` inside doesn't trip IndexError.
        """
        if not _is_known_iterable(node.iter):
            self._add_source(
                ExceptionKind.TYPE_ERROR,
                node,
                trigger_condition="object not iterable",
                severity=Severity.LOW,
                description="for-loop iteration",
            )
        # Track range-loop vars within this loop's body.
        added: set[str] = set()
        if isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name) \
                and node.iter.func.id == "range" \
                and isinstance(node.target, ast.Name):
            added.add(node.target.id)
            self._range_loop_vars |= added
        # Track list-iterable loop vars too: ``for x in xs`` makes ``x``
        # a known-non-None local; the iterable name itself stays a list.
        if isinstance(node.iter, (ast.List,)) or (
                isinstance(node.iter, ast.Name) and node.iter.id in self._known_list_names):
            if isinstance(node.target, ast.Name):
                self._definitely_not_none.add(node.target.id)
        try:
            self.visit(node.iter)
            for stmt in node.body:
                self.visit(stmt)
            for stmt in node.orelse:
                self.visit(stmt)
        finally:
            self._range_loop_vars -= added

    # ── Type narrowing on If statements ──────────────────────────

    @staticmethod
    def _none_check_var(test: ast.expr) -> tuple[str, bool] | None:
        """Detect ``x is None`` / ``x is not None`` / ``x == None``
        / ``x != None`` patterns.  Returns ``(name, positive)`` where
        ``positive`` is ``True`` for "x is None"-style tests and
        ``False`` for "x is not None"-style.  None if not a None-check.
        """
        if not isinstance(test, ast.Compare):
            return None
        if not isinstance(test.left, ast.Name):
            return None
        if len(test.ops) != 1 or len(test.comparators) != 1:
            return None
        comp = test.comparators[0]
        if not (isinstance(comp, ast.Constant) and comp.value is None):
            return None
        op = test.ops[0]
        if isinstance(op, (ast.Is, ast.Eq)):
            return (test.left.id, True)
        if isinstance(op, (ast.IsNot, ast.NotEq)):
            return (test.left.id, False)
        return None

    def _extract_int_guards(
        self, test: ast.expr,
    ) -> tuple[set[str], set[str]]:
        """Extract integer-bound narrowing from a guard expression.

        Returns ``(bounded_above, positive)`` — sets of name strings:

          * ``bounded_above`` — names known to be < some expression
            in the then-branch (suppresses ``data[name]``-style
            IndexError).
          * ``positive`` — names known to be > 0 (or ≥ 1) in the
            then-branch.

        Recognised forms:
          * ``X < EXPR`` / ``X <= EXPR``    →  X bounded above
          * ``EXPR > X`` / ``EXPR >= X``    →  X bounded above
          * ``X > 0`` / ``X >= 1``          →  X positive
          * ``0 < X`` / ``1 <= X``          →  X positive
          * ``X < EXPR1 and X < EXPR2``     →  X bounded
          * chained comparisons ``A < X < B``  →  X bounded above
          * ``A and B`` (BoolOp.And)        →  union of A's and B's
            narrowings
        """
        bounded: set[str] = set()
        positive: set[str] = set()

        if isinstance(test, ast.Compare):
            # Single comparison or chain.  We walk the chain pairwise.
            terms = [test.left] + list(test.comparators)
            for op, lhs, rhs in zip(test.ops, terms, terms[1:]):
                self._guard_pair_into(op, lhs, rhs, bounded, positive)
        elif isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
            for child in test.values:
                b, p = self._extract_int_guards(child)
                bounded |= b
                positive |= p
        # Other shapes (Or, Not, Call) — no bound extraction.
        return bounded, positive

    @staticmethod
    def _extract_bounds_static(
        test: ast.expr,
    ) -> tuple[set[str], set[str]]:
        """Static version of ``_extract_int_guards`` for use from
        free helpers (decorator parsing).  Same recognised forms."""
        bounded: set[str] = set()
        positive: set[str] = set()
        if isinstance(test, ast.Compare):
            terms = [test.left] + list(test.comparators)
            for op, lhs, rhs in zip(test.ops, terms, terms[1:]):
                ExceptionSourceFinder._guard_pair_into(
                    op, lhs, rhs, bounded, positive,
                )
        elif isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
            for child in test.values:
                b, p = ExceptionSourceFinder._extract_bounds_static(child)
                bounded |= b
                positive |= p
        return bounded, positive

    @staticmethod
    def _guard_pair_into(
        op: ast.cmpop, lhs: ast.expr, rhs: ast.expr,
        bounded: set[str], positive: set[str],
    ) -> None:
        """Extract bounds from a single comparison ``lhs OP rhs``."""
        # X < EXPR / X <= EXPR  →  X bounded above by EXPR
        if isinstance(op, (ast.Lt, ast.LtE)) and isinstance(lhs, ast.Name):
            bounded.add(lhs.id)
            # Special case: ``0 ≤ X``  →  positive-or-zero (we still
            # treat as bounded-below; not added to ``positive``).
        # EXPR > X / EXPR >= X  →  X bounded above by EXPR
        if isinstance(op, (ast.Gt, ast.GtE)) and isinstance(rhs, ast.Name):
            bounded.add(rhs.id)
        # X > 0 / X >= 1  →  X positive
        if isinstance(op, ast.Gt) and isinstance(lhs, ast.Name) \
                and isinstance(rhs, ast.Constant) \
                and isinstance(rhs.value, int) and rhs.value >= 0:
            positive.add(lhs.id)
        if isinstance(op, ast.GtE) and isinstance(lhs, ast.Name) \
                and isinstance(rhs, ast.Constant) \
                and isinstance(rhs.value, int) and rhs.value >= 1:
            positive.add(lhs.id)
        # 0 < X / 1 <= X  →  X positive
        if isinstance(op, ast.Lt) and isinstance(rhs, ast.Name) \
                and isinstance(lhs, ast.Constant) \
                and isinstance(lhs.value, int) and lhs.value >= 0:
            positive.add(rhs.id)
        if isinstance(op, ast.LtE) and isinstance(rhs, ast.Name) \
                and isinstance(lhs, ast.Constant) \
                and isinstance(lhs.value, int) and lhs.value >= 1:
            positive.add(rhs.id)

    @staticmethod
    def _block_terminates(body: list[ast.stmt]) -> bool:
        """Does this block always exit (return / raise) before falling
        through?  Used to decide whether the post-if code can rely on
        the negated branch's narrowing."""
        if not body:
            return False
        last = body[-1]
        return isinstance(last, (ast.Return, ast.Raise))

    def visit_If(self, node: ast.If) -> None:
        """Visit an If node with type + integer-bound narrowing.

        Patterns recognised:
          * ``if x is None: return ...``  →  post-if x is not-None
          * ``if x is None: <body> else: <else>`` →  in <else>, x not-None
          * ``if x is not None: <body>``  →  in <body>, x not-None
          * ``if i < n: <body>`` / ``if i < len(data): <body>`` /
            ``if i < n and ...:`` / chained ``a < b < c`` —
            i is index-guarded inside <body>; ``data[i]`` won't
            trip IndexError.
          * ``if i > 0: <body>`` / ``if i >= 1: <body>`` —
            i is positive inside <body>.
          * ``if not (i is None) and i < n:`` — combine narrowing.

        Special case: ``if __name__ == "__main__":`` blocks are
        Python's standard script-entry idiom; suppress sources inside.
        """
        if _is_main_guard(node):
            saved_sources = self._sources
            saved_module_sources = self._module_sources
            self._sources = []
            self._module_sources = []
            self.visit(node.test)
            for stmt in node.body:
                self.visit(stmt)
            for stmt in node.orelse:
                self.visit(stmt)
            self._sources = saved_sources
            self._module_sources = saved_module_sources
            return
        # First, visit the test expression itself.
        self.visit(node.test)

        check = self._none_check_var(node.test)
        narrowed_then: set[str] = set()
        narrowed_else: set[str] = set()
        narrowed_after: set[str] = set()
        if check is not None:
            name, positive = check
            if positive:
                narrowed_else = {name}
                if self._block_terminates(node.body):
                    narrowed_after = {name}
            else:
                narrowed_then = {name}
                if self._block_terminates(node.body) is False \
                        and self._block_terminates(node.orelse):
                    narrowed_after = {name}

        # Integer-bound narrowing: from a guard like ``i < n`` /
        # ``i < len(data)`` / chained ``0 <= i < n`` / boolop
        # ``i < n and ...``, extract the index-name set bounded
        # above (then-branch) and the index-name set known positive
        # (then-branch from ``i > 0`` etc.).
        bounded_then, positive_then = self._extract_int_guards(node.test)

        # Visit the then-branch with full narrowing applied.
        saved_not_none = set(self._definitely_not_none)
        saved_guarded = set(self._index_guarded)
        saved_positive = set(self._index_positive)

        self._definitely_not_none |= narrowed_then
        self._index_guarded |= bounded_then
        self._index_positive |= positive_then
        for stmt in node.body:
            self.visit(stmt)

        # Visit the else-branch with type-narrowing only (no
        # int-bound narrowing — the negation of `i < n` is `i >= n`,
        # which doesn't help for index safety).
        self._definitely_not_none = saved_not_none | narrowed_else
        self._index_guarded = saved_guarded
        self._index_positive = saved_positive
        for stmt in node.orelse:
            self.visit(stmt)

        # After the if: apply post-narrowing for early-return cases.
        self._definitely_not_none = saved_not_none | narrowed_after
        self._index_guarded = saved_guarded
        self._index_positive = saved_positive
        # Post-if int-bound narrowing: when the then-branch terminates
        # (return/raise) under a guard like ``if not (i < n): return``,
        # the post-if context knows ``i < n``.  We don't yet handle
        # this dual case; it's a TODO.

    def visit_Call(self, node: ast.Call) -> None:
        """Function / method calls → various exceptions."""
        func_name = self._resolve_call_name(node)

        if self._in_function and func_name == self._current_function:
            # Recursion-depth-exceeded is a Python implementation
            # detail (sys.setrecursionlimit) rather than a logic bug;
            # we suppress the source when the function has a guarded
            # early-return base case (the "if X is None: return"
            # pattern) — the analyzer's caller registers it via
            # ``_current_function_has_base_case``.  When this isn't
            # true (no obvious termination guard), we still emit the
            # source so deeply-unguarded recursion is flagged.
            if not getattr(self, "_current_function_has_base_case", False):
                self._add_source(
                    ExceptionKind.RUNTIME_ERROR,
                    node,
                    trigger_condition="recursion depth exceeded",
                    severity=Severity.HIGH,
                    description=f"direct recursive call to {func_name}()",
                    callee_name=func_name,
                )

        if func_name in _BUILTIN_EXCEPTION_MAP:
            # ``len(known_iterable)`` doesn't raise TypeError — the
            # arg is provably iterable.  Same for any iterable
            # consumer when applied to a known-iterable expression.
            if func_name == "len" and node.args and \
                    _is_known_iterable(node.args[0]):
                pass
            elif func_name in {"sum", "min", "max", "all", "any",
                                "list", "tuple", "set", "frozenset",
                                "dict", "sorted", "reversed",
                                "enumerate", "zip", "map", "filter"} \
                    and node.args and _is_known_iterable(node.args[0]):
                pass
            elif func_name == "len" and node.args and \
                    isinstance(node.args[0], ast.Attribute) \
                    and isinstance(node.args[0].value, ast.Name) \
                    and node.args[0].value.id == "self" \
                    and self._field_annotations.get(
                        node.args[0].attr, ""
                    ).startswith(("list", "List", "tuple", "Tuple",
                                   "dict", "Dict", "set", "Set")):
                # ``len(self.<list_field>)`` is also safe.
                pass
            else:
                for kind, desc, severity in _BUILTIN_EXCEPTION_MAP[func_name]:
                    self._add_source(kind, node, trigger_condition=desc,
                                     severity=severity,
                                     description=f"call to {func_name}(): {desc}")
        elif func_name and "." in func_name:
            # Method call — check method map.  Filter by receiver
            # shape: list-typed receivers don't raise KeyError;
            # dict-typed receivers don't raise IndexError.
            method = func_name.rsplit(".", 1)[-1]
            recv_is_list = False
            recv_is_dict = False
            if isinstance(node.func, ast.Attribute):
                recv_is_list = self._receiver_is_list(node.func.value)
                recv_is_dict = self._receiver_is_dict(node.func.value)
            if method in _METHOD_EXCEPTION_MAP:
                for kind, desc, severity in _METHOD_EXCEPTION_MAP[method]:
                    if recv_is_list and kind == ExceptionKind.KEY_ERROR:
                        continue  # lists don't raise KeyError
                    if recv_is_dict and kind == ExceptionKind.INDEX_ERROR:
                        continue  # dicts don't raise IndexError
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
        """Import statement → ImportError (suppressed for safe imports)."""
        for alias in node.names:
            if _is_safe_import(alias.name):
                continue
            self._add_source(
                ExceptionKind.IMPORT_ERROR,
                node,
                trigger_condition=f"module '{alias.name}' not found",
                severity=Severity.LOW,
                description=f"import {alias.name}",
            )
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        """From-import → ImportError (suppressed for safe modules)."""
        mod = node.module or "<unknown>"
        if _is_safe_import(mod):
            self.generic_visit(node)
            return
        for alias in (node.names or []):
            self._add_source(
                ExceptionKind.IMPORT_ERROR,
                node,
                trigger_condition=f"cannot import '{alias.name}' from '{mod}'",
                severity=Severity.LOW,
                description=f"from {mod} import {alias.name}",
            )
        self.generic_visit(node)

    # (visit_For with range-loop-var tracking is defined earlier;
    # this slot intentionally left empty.)

    def visit_While(self, node: ast.While) -> None:
        """While loop: extract integer-bound narrowing from the
        loop test, applying it to the body for the duration.

        ``while i > 0:`` → inside the body, i is positive.
        ``while i < n:`` → inside the body, i is bounded above.
        """
        # First visit the test (may have its own sources).
        self.visit(node.test)
        bounded, positive = self._extract_int_guards(node.test)
        saved_g = set(self._index_guarded)
        saved_p = set(self._index_positive)
        saved_d = set(getattr(self, '_index_derived_guarded', set()))
        self._index_guarded |= bounded
        self._index_positive |= positive
        try:
            for stmt in node.body:
                self.visit(stmt)
            for stmt in node.orelse:
                self.visit(stmt)
        finally:
            self._index_guarded = saved_g
            self._index_positive = saved_p
            self._index_derived_guarded = saved_d

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
        """Unpacking assignment → ValueError.

        Suppressed for the common ``a, b = c, d`` shape (tuple-of-N
        on both sides with matching arity, no starred element) since
        the unpack count is statically determined and matches.

        Also tracks index-derived guarded names: a single-target
        assignment ``parent = (i - 1) // 2`` propagates ``parent`` to
        ``_index_derived_guarded`` when ``i`` is currently in the
        guarded/positive set.  This recognises the heap-style local
        ``parent`` / ``left`` / ``right`` convention.
        """
        for target in node.targets:
            if isinstance(target, (ast.Tuple, ast.List)):
                value = node.value
                if isinstance(value, (ast.Tuple, ast.List)) \
                        and len(target.elts) == len(value.elts) \
                        and not any(isinstance(e, ast.Starred)
                                     for e in target.elts) \
                        and not any(isinstance(e, ast.Starred)
                                     for e in value.elts):
                    continue
                self._add_source(
                    ExceptionKind.UNPACK_ERROR,
                    node,
                    trigger_condition="wrong number of values to unpack",
                    severity=Severity.MEDIUM,
                    description="tuple/list unpacking",
                )

        # Index-derived-guard propagation: ``X = expr`` where expr is
        # an integer expression on guarded names →  X is guarded.
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            target_name = node.targets[0].id
            if self._expr_is_guarded_index(node.value):
                if not hasattr(self, '_index_derived_guarded'):
                    self._index_derived_guarded = set()
                self._index_derived_guarded.add(target_name)
            # Class-instance tracking: ``h = MinHeap()`` →  h's class
            # is "MinHeap"; subsequent ``h.X`` lookups consult
            # ``_class_members[MinHeap]``.
            if isinstance(node.value, ast.Call) \
                    and isinstance(node.value.func, ast.Name) \
                    and node.value.func.id in self._class_members:
                self._var_classes[target_name] = node.value.func.id

        self.generic_visit(node)

    def _expr_is_guarded_index(self, node: ast.expr) -> bool:
        """``node`` is a numeric expression whose value is a valid
        index (≥ 0 and bounded by some length we trust).

        Recognises:
          * non-negative integer constants
          * names already in the guarded / positive / range-loop /
            derived-guarded sets
          * arithmetic on guarded names (BinOp)
          * ``len(known_iterable)``
          * calls to pure helpers (e.g. ``_parent(i)``,
            ``_left_child(i)``, etc.) when all args are guarded —
            heap/binary-search convention
        """
        if isinstance(node, ast.Constant) and isinstance(node.value, int) \
                and node.value >= 0:
            return True
        if isinstance(node, ast.Name):
            guarded = (
                self._index_guarded | self._index_positive
                | self._range_loop_vars
                | getattr(self, '_index_derived_guarded', set())
            )
            return node.id in guarded
        if isinstance(node, ast.BinOp):
            return self._binop_indexes_in_range(node)
        if isinstance(node, ast.Call):
            # ``len(data)`` is non-negative.
            if isinstance(node.func, ast.Name) and node.func.id == "len" \
                    and node.args:
                return True
            # Pure helper with all-guarded args produces a value we
            # treat as guarded.  Recognises e.g. ``_parent(i)``,
            # ``_left_child(i)``, ``min(a, b)``, ``max(a, b)``,
            # ``abs(x)`` when applied to guarded inputs.
            if isinstance(node.func, ast.Name):
                if all(self._expr_is_guarded_index(a) for a in node.args):
                    return True
            # Method call ``x.bit_length()`` etc. — too speculative.
        if isinstance(node, ast.IfExp):
            # ``a if cond else b`` — both arms must be guarded.
            return self._expr_is_guarded_index(node.body) \
                and self._expr_is_guarded_index(node.orelse)
        return False

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

            # Don't flag module-level locals (assigns, loop vars, walrus)
            # in this module — _module_local_names is populated by
            # analyze_module before traversal.
            if node.id in getattr(self, '_module_local_names', set()):
                self.generic_visit(node)
                return

            # Built-ins: a broader set covering everything in builtins
            # plus the runtime dunders that are always present at module
            # level (``__name__``, ``__file__``, ``__doc__`` etc.).
            if node.id in _SAFE_BUILTIN_NAMES:
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

