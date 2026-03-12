"""Error-sensitive site catalog.

Maps Python error types to viability predicates that describe under what
conditions an error site is *viable* (i.e., the error can actually be raised).
This information drives the error-path analysis in cover synthesis: only
viable error sites generate corresponding observation sites in the Cover.

Key classes:

- :class:`ErrorPattern` -- immutable descriptor of an error-raising pattern.
- :class:`ViabilityPredicate` -- describes when an error site is reachable.
- :class:`ErrorSiteEntry` -- associates a SiteId with its error metadata.
- :class:`ErrorSiteRegistry` -- the mutable registry accumulating error sites.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import SiteId, SiteKind


# ═══════════════════════════════════════════════════════════════════════════════
# Error kind taxonomy
# ═══════════════════════════════════════════════════════════════════════════════


class ErrorKind(enum.Enum):
    """Taxonomy of Python error types relevant to type analysis."""

    INDEX_ERROR = "IndexError"
    KEY_ERROR = "KeyError"
    TYPE_ERROR = "TypeError"
    VALUE_ERROR = "ValueError"
    ZERO_DIVISION_ERROR = "ZeroDivisionError"
    ATTRIBUTE_ERROR = "AttributeError"
    RUNTIME_ERROR = "RuntimeError"
    NAME_ERROR = "NameError"
    STOP_ITERATION = "StopIteration"
    OVERFLOW_ERROR = "OverflowError"
    ASSERTION_ERROR = "AssertionError"
    NOT_IMPLEMENTED_ERROR = "NotImplementedError"
    IMPORT_ERROR = "ImportError"
    OS_ERROR = "OSError"
    IO_ERROR = "IOError"
    UNICODE_ERROR = "UnicodeError"
    LOOKUP_ERROR = "LookupError"
    MEMORY_ERROR = "MemoryError"
    RECURSION_ERROR = "RecursionError"
    PERMISSION_ERROR = "PermissionError"
    FILE_NOT_FOUND_ERROR = "FileNotFoundError"
    TIMEOUT_ERROR = "TimeoutError"
    CONNECTION_ERROR = "ConnectionError"
    CUSTOM = "Custom"

    @staticmethod
    def from_exception_name(name: str) -> ErrorKind:
        """Look up an ErrorKind by Python exception class name."""
        for member in ErrorKind:
            if member.value == name:
                return member
        return ErrorKind.CUSTOM


# ═══════════════════════════════════════════════════════════════════════════════
# Operation kind taxonomy
# ═══════════════════════════════════════════════════════════════════════════════


class OperationKind(enum.Enum):
    """Kinds of operations that may raise errors."""

    SUBSCRIPT = "subscript"
    ATTRIBUTE_ACCESS = "attribute_access"
    BINARY_OP = "binary_op"
    UNARY_OP = "unary_op"
    CALL = "call"
    ITERATION = "iteration"
    COMPARISON = "comparison"
    ASSIGNMENT = "assignment"
    IMPORT = "import"
    ASSERTION = "assertion"
    CAST = "cast"
    DICT_LOOKUP = "dict_lookup"
    LIST_ACCESS = "list_access"
    DIVISION = "division"
    MODULO = "modulo"
    CONVERSION = "conversion"
    FILE_IO = "file_io"
    NETWORK_IO = "network_io"
    UNPACKING = "unpacking"
    COMPREHENSION = "comprehension"


# ═══════════════════════════════════════════════════════════════════════════════
# Viability predicate
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ViabilityPredicate:
    """Describes the condition under which an error site is reachable.

    A viability predicate is a textual + machine-checkable description of
    when a particular error can be raised.

    Attributes:
        description: Human-readable description of viability condition.
        error_kind: The kind of error this predicate applies to.
        operation: The operation that triggers the error.
        guard_variable: The variable whose value determines viability (if any).
        negation_description: Description of the condition that prevents the error.
        is_always_viable: True if the error can always happen (no guard).
        confidence: How confident we are in this predicate (0.0 to 1.0).
    """

    _description: str
    _error_kind: ErrorKind
    _operation: OperationKind
    _guard_variable: str = ""
    _negation_description: str = ""
    _is_always_viable: bool = False
    _confidence: float = 1.0

    @property
    def description(self) -> str:
        return self._description

    @property
    def error_kind(self) -> ErrorKind:
        return self._error_kind

    @property
    def operation(self) -> OperationKind:
        return self._operation

    @property
    def guard_variable(self) -> str:
        return self._guard_variable

    @property
    def negation_description(self) -> str:
        return self._negation_description or f"not({self._description})"

    @property
    def is_always_viable(self) -> bool:
        return self._is_always_viable

    @property
    def confidence(self) -> float:
        return self._confidence

    def __repr__(self) -> str:
        return (
            f"ViabilityPredicate({self._error_kind.value}: "
            f"{self._description}, confidence={self._confidence})"
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Error pattern
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ErrorPattern:
    """Describes a recognized pattern that may raise a specific error.

    Attributes:
        error_kind: The kind of error this pattern raises.
        operation: The operation kind that triggers the error.
        description: Human-readable description of the pattern.
        viability: The viability predicate for this pattern.
        example: An optional example code snippet.
    """

    _error_kind: ErrorKind
    _operation: OperationKind
    _description: str
    _viability: ViabilityPredicate
    _example: str = ""

    @property
    def error_kind(self) -> ErrorKind:
        return self._error_kind

    @property
    def operation(self) -> OperationKind:
        return self._operation

    @property
    def description(self) -> str:
        return self._description

    @property
    def viability(self) -> ViabilityPredicate:
        return self._viability

    @property
    def example(self) -> str:
        return self._example

    def __repr__(self) -> str:
        return f"ErrorPattern({self._error_kind.value}, {self._operation.value})"


# ═══════════════════════════════════════════════════════════════════════════════
# Error site entry
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ErrorSiteEntry:
    """Associates a SiteId with its error metadata.

    Attributes:
        site_id: The error site.
        error_kind: The kind of error at this site.
        viability: The viability predicate for this site.
        source_operation: Description of the operation that can fail.
        source_line: Source line number, if known.
        is_explicit_raise: True if this is an explicit ``raise`` statement.
        guarded: True if a try/except or guard condition wraps this site.
    """

    _site_id: SiteId
    _error_kind: ErrorKind
    _viability: ViabilityPredicate
    _source_operation: str = ""
    _source_line: int = 0
    _is_explicit_raise: bool = False
    _guarded: bool = False

    @property
    def site_id(self) -> SiteId:
        return self._site_id

    @property
    def error_kind(self) -> ErrorKind:
        return self._error_kind

    @property
    def viability(self) -> ViabilityPredicate:
        return self._viability

    @property
    def source_operation(self) -> str:
        return self._source_operation

    @property
    def source_line(self) -> int:
        return self._source_line

    @property
    def is_explicit_raise(self) -> bool:
        return self._is_explicit_raise

    @property
    def guarded(self) -> bool:
        return self._guarded

    @property
    def viability_description(self) -> str:
        """Short description of when this error is viable."""
        return self._viability.description

    def __repr__(self) -> str:
        return (
            f"ErrorSiteEntry({self._site_id}, "
            f"{self._error_kind.value}, "
            f"guarded={self._guarded})"
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Default error patterns
# ═══════════════════════════════════════════════════════════════════════════════


def _build_default_patterns() -> List[ErrorPattern]:
    """Build the default catalog of error patterns."""
    patterns: List[ErrorPattern] = []

    # IndexError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.INDEX_ERROR,
        _operation=OperationKind.LIST_ACCESS,
        _description="List subscript with index out of range",
        _viability=ViabilityPredicate(
            _description="index >= len(container) or index < -len(container)",
            _error_kind=ErrorKind.INDEX_ERROR,
            _operation=OperationKind.LIST_ACCESS,
            _guard_variable="index",
            _negation_description="0 <= index < len(container)",
        ),
        _example="xs[i]  # may raise IndexError",
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.INDEX_ERROR,
        _operation=OperationKind.SUBSCRIPT,
        _description="Tuple subscript with index out of range",
        _viability=ViabilityPredicate(
            _description="index >= len(tuple) or index < -len(tuple)",
            _error_kind=ErrorKind.INDEX_ERROR,
            _operation=OperationKind.SUBSCRIPT,
            _guard_variable="index",
            _negation_description="0 <= index < len(tuple)",
        ),
        _example="t[i]  # may raise IndexError",
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.INDEX_ERROR,
        _operation=OperationKind.UNPACKING,
        _description="Unpacking with wrong number of values",
        _viability=ViabilityPredicate(
            _description="len(iterable) != expected_count",
            _error_kind=ErrorKind.INDEX_ERROR,
            _operation=OperationKind.UNPACKING,
            _negation_description="len(iterable) == expected_count",
        ),
    ))

    # KeyError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.KEY_ERROR,
        _operation=OperationKind.DICT_LOOKUP,
        _description="Dictionary key not found",
        _viability=ViabilityPredicate(
            _description="key not in dictionary",
            _error_kind=ErrorKind.KEY_ERROR,
            _operation=OperationKind.DICT_LOOKUP,
            _guard_variable="key",
            _negation_description="key in dictionary",
        ),
        _example="d[k]  # may raise KeyError",
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.KEY_ERROR,
        _operation=OperationKind.SUBSCRIPT,
        _description="Generic subscript key not found",
        _viability=ViabilityPredicate(
            _description="key not in mapping",
            _error_kind=ErrorKind.KEY_ERROR,
            _operation=OperationKind.SUBSCRIPT,
            _guard_variable="key",
            _negation_description="key in mapping",
        ),
    ))

    # TypeError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.TYPE_ERROR,
        _operation=OperationKind.CALL,
        _description="Wrong argument types or count in function call",
        _viability=ViabilityPredicate(
            _description="argument types do not match parameter types",
            _error_kind=ErrorKind.TYPE_ERROR,
            _operation=OperationKind.CALL,
            _negation_description="argument types match parameter types",
        ),
        _example="f(x)  # may raise TypeError",
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.TYPE_ERROR,
        _operation=OperationKind.BINARY_OP,
        _description="Unsupported operand types for binary operator",
        _viability=ViabilityPredicate(
            _description="operand types do not support the operator",
            _error_kind=ErrorKind.TYPE_ERROR,
            _operation=OperationKind.BINARY_OP,
            _negation_description="operand types support the operator",
        ),
        _example="x + y  # may raise TypeError if types mismatch",
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.TYPE_ERROR,
        _operation=OperationKind.UNARY_OP,
        _description="Unsupported operand type for unary operator",
        _viability=ViabilityPredicate(
            _description="operand type does not support the operator",
            _error_kind=ErrorKind.TYPE_ERROR,
            _operation=OperationKind.UNARY_OP,
            _negation_description="operand type supports the operator",
        ),
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.TYPE_ERROR,
        _operation=OperationKind.ITERATION,
        _description="Attempting to iterate over non-iterable",
        _viability=ViabilityPredicate(
            _description="object is not iterable",
            _error_kind=ErrorKind.TYPE_ERROR,
            _operation=OperationKind.ITERATION,
            _negation_description="object is iterable",
        ),
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.TYPE_ERROR,
        _operation=OperationKind.SUBSCRIPT,
        _description="Object is not subscriptable",
        _viability=ViabilityPredicate(
            _description="object does not support subscript",
            _error_kind=ErrorKind.TYPE_ERROR,
            _operation=OperationKind.SUBSCRIPT,
            _negation_description="object supports subscript",
        ),
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.TYPE_ERROR,
        _operation=OperationKind.CONVERSION,
        _description="Failed type conversion",
        _viability=ViabilityPredicate(
            _description="value cannot be converted to target type",
            _error_kind=ErrorKind.TYPE_ERROR,
            _operation=OperationKind.CONVERSION,
            _negation_description="value can be converted to target type",
        ),
        _example="int('abc')  # raises TypeError/ValueError",
    ))

    # ValueError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.VALUE_ERROR,
        _operation=OperationKind.CONVERSION,
        _description="Invalid value for type conversion",
        _viability=ViabilityPredicate(
            _description="value is not a valid representation of target type",
            _error_kind=ErrorKind.VALUE_ERROR,
            _operation=OperationKind.CONVERSION,
            _guard_variable="value",
            _negation_description="value is valid for conversion",
        ),
        _example="int('abc')  # raises ValueError",
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.VALUE_ERROR,
        _operation=OperationKind.CALL,
        _description="Invalid argument value (correct type but bad value)",
        _viability=ViabilityPredicate(
            _description="argument value out of acceptable domain",
            _error_kind=ErrorKind.VALUE_ERROR,
            _operation=OperationKind.CALL,
            _negation_description="argument value in acceptable domain",
        ),
        _example="math.sqrt(-1)  # raises ValueError",
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.VALUE_ERROR,
        _operation=OperationKind.UNPACKING,
        _description="Wrong number of values to unpack",
        _viability=ViabilityPredicate(
            _description="number of values does not match targets",
            _error_kind=ErrorKind.VALUE_ERROR,
            _operation=OperationKind.UNPACKING,
            _negation_description="number of values matches targets",
        ),
    ))

    # ZeroDivisionError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.ZERO_DIVISION_ERROR,
        _operation=OperationKind.DIVISION,
        _description="Division by zero",
        _viability=ViabilityPredicate(
            _description="divisor == 0",
            _error_kind=ErrorKind.ZERO_DIVISION_ERROR,
            _operation=OperationKind.DIVISION,
            _guard_variable="divisor",
            _negation_description="divisor != 0",
        ),
        _example="x / y  # may raise ZeroDivisionError if y == 0",
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.ZERO_DIVISION_ERROR,
        _operation=OperationKind.MODULO,
        _description="Modulo by zero",
        _viability=ViabilityPredicate(
            _description="divisor == 0",
            _error_kind=ErrorKind.ZERO_DIVISION_ERROR,
            _operation=OperationKind.MODULO,
            _guard_variable="divisor",
            _negation_description="divisor != 0",
        ),
        _example="x % y  # may raise ZeroDivisionError if y == 0",
    ))

    # AttributeError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.ATTRIBUTE_ERROR,
        _operation=OperationKind.ATTRIBUTE_ACCESS,
        _description="Attribute not found on object",
        _viability=ViabilityPredicate(
            _description="object does not have the requested attribute",
            _error_kind=ErrorKind.ATTRIBUTE_ERROR,
            _operation=OperationKind.ATTRIBUTE_ACCESS,
            _negation_description="object has the requested attribute",
        ),
        _example="obj.attr  # may raise AttributeError",
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.ATTRIBUTE_ERROR,
        _operation=OperationKind.CALL,
        _description="None-type attribute access",
        _viability=ViabilityPredicate(
            _description="object is None",
            _error_kind=ErrorKind.ATTRIBUTE_ERROR,
            _operation=OperationKind.CALL,
            _guard_variable="object",
            _negation_description="object is not None",
        ),
        _example="x.method()  # x might be None",
    ))

    # RuntimeError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.RUNTIME_ERROR,
        _operation=OperationKind.CALL,
        _description="Generic runtime error from function call",
        _viability=ViabilityPredicate(
            _description="function raises RuntimeError",
            _error_kind=ErrorKind.RUNTIME_ERROR,
            _operation=OperationKind.CALL,
            _is_always_viable=True,
            _confidence=0.5,
        ),
    ))
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.RUNTIME_ERROR,
        _operation=OperationKind.ITERATION,
        _description="Dictionary changed size during iteration",
        _viability=ViabilityPredicate(
            _description="container modified during iteration",
            _error_kind=ErrorKind.RUNTIME_ERROR,
            _operation=OperationKind.ITERATION,
            _negation_description="container not modified during iteration",
            _confidence=0.7,
        ),
    ))

    # StopIteration patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.STOP_ITERATION,
        _operation=OperationKind.ITERATION,
        _description="Iterator exhausted",
        _viability=ViabilityPredicate(
            _description="iterator has no more elements",
            _error_kind=ErrorKind.STOP_ITERATION,
            _operation=OperationKind.ITERATION,
            _negation_description="iterator has remaining elements",
        ),
        _example="next(it)  # may raise StopIteration",
    ))

    # AssertionError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.ASSERTION_ERROR,
        _operation=OperationKind.ASSERTION,
        _description="Assert statement failed",
        _viability=ViabilityPredicate(
            _description="assertion condition is false",
            _error_kind=ErrorKind.ASSERTION_ERROR,
            _operation=OperationKind.ASSERTION,
            _negation_description="assertion condition is true",
        ),
        _example="assert x > 0  # may raise AssertionError",
    ))

    # OverflowError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.OVERFLOW_ERROR,
        _operation=OperationKind.BINARY_OP,
        _description="Numeric overflow in arithmetic operation",
        _viability=ViabilityPredicate(
            _description="result exceeds numeric limits",
            _error_kind=ErrorKind.OVERFLOW_ERROR,
            _operation=OperationKind.BINARY_OP,
            _negation_description="result within numeric limits",
            _confidence=0.6,
        ),
    ))

    # NotImplementedError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.NOT_IMPLEMENTED_ERROR,
        _operation=OperationKind.CALL,
        _description="Abstract method not implemented",
        _viability=ViabilityPredicate(
            _description="method body raises NotImplementedError",
            _error_kind=ErrorKind.NOT_IMPLEMENTED_ERROR,
            _operation=OperationKind.CALL,
            _negation_description="method is implemented in subclass",
        ),
    ))

    # ImportError patterns
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.IMPORT_ERROR,
        _operation=OperationKind.IMPORT,
        _description="Module or attribute import failed",
        _viability=ViabilityPredicate(
            _description="module or attribute not available",
            _error_kind=ErrorKind.IMPORT_ERROR,
            _operation=OperationKind.IMPORT,
            _negation_description="module or attribute available",
            _confidence=0.8,
        ),
    ))

    # FileNotFoundError
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.FILE_NOT_FOUND_ERROR,
        _operation=OperationKind.FILE_IO,
        _description="File not found during I/O",
        _viability=ViabilityPredicate(
            _description="file path does not exist",
            _error_kind=ErrorKind.FILE_NOT_FOUND_ERROR,
            _operation=OperationKind.FILE_IO,
            _guard_variable="path",
            _negation_description="file path exists",
        ),
    ))

    # PermissionError
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.PERMISSION_ERROR,
        _operation=OperationKind.FILE_IO,
        _description="Insufficient permissions for file operation",
        _viability=ViabilityPredicate(
            _description="process lacks required permissions",
            _error_kind=ErrorKind.PERMISSION_ERROR,
            _operation=OperationKind.FILE_IO,
            _negation_description="process has required permissions",
            _confidence=0.7,
        ),
    ))

    # TimeoutError
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.TIMEOUT_ERROR,
        _operation=OperationKind.NETWORK_IO,
        _description="Network operation timed out",
        _viability=ViabilityPredicate(
            _description="operation exceeds timeout threshold",
            _error_kind=ErrorKind.TIMEOUT_ERROR,
            _operation=OperationKind.NETWORK_IO,
            _is_always_viable=True,
            _confidence=0.5,
        ),
    ))

    # ConnectionError
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.CONNECTION_ERROR,
        _operation=OperationKind.NETWORK_IO,
        _description="Network connection failed",
        _viability=ViabilityPredicate(
            _description="network endpoint unreachable",
            _error_kind=ErrorKind.CONNECTION_ERROR,
            _operation=OperationKind.NETWORK_IO,
            _is_always_viable=True,
            _confidence=0.5,
        ),
    ))

    # RecursionError
    patterns.append(ErrorPattern(
        _error_kind=ErrorKind.RECURSION_ERROR,
        _operation=OperationKind.CALL,
        _description="Maximum recursion depth exceeded",
        _viability=ViabilityPredicate(
            _description="call stack exceeds recursion limit",
            _error_kind=ErrorKind.RECURSION_ERROR,
            _operation=OperationKind.CALL,
            _negation_description="recursion terminates within limit",
            _confidence=0.4,
        ),
    ))

    return patterns


# ═══════════════════════════════════════════════════════════════════════════════
# Error site registry
# ═══════════════════════════════════════════════════════════════════════════════


class ErrorSiteRegistry:
    """Mutable registry mapping error types to viability predicates.

    Maintains the catalog of recognized error patterns and the set of
    concrete error sites discovered during cover synthesis.
    """

    def __init__(self, load_defaults: bool = True) -> None:
        # Pattern catalog: error_kind -> list of patterns
        self._patterns: Dict[ErrorKind, List[ErrorPattern]] = {}
        # Concrete error site entries
        self._entries: Dict[SiteId, ErrorSiteEntry] = {}
        # Reverse index: error_kind -> set of site ids
        self._kind_to_sites: Dict[ErrorKind, Set[SiteId]] = {}
        # Reverse index: operation_kind -> set of site ids
        self._op_to_sites: Dict[OperationKind, Set[SiteId]] = {}
        # Custom viability overrides
        self._viability_overrides: Dict[SiteId, ViabilityPredicate] = {}

        if load_defaults:
            for pattern in _build_default_patterns():
                self.register_pattern(pattern)

    # ── Pattern registration ───────────────────────────────────────────────

    def register_pattern(self, pattern: ErrorPattern) -> None:
        """Register an error pattern in the catalog."""
        self._patterns.setdefault(pattern.error_kind, []).append(pattern)

    def register_error_pattern(
        self,
        error_kind: ErrorKind,
        viability_predicate: ViabilityPredicate,
        operation: Optional[OperationKind] = None,
        description: str = "",
    ) -> ErrorPattern:
        """Register a new error pattern by components.

        Returns the created ErrorPattern.
        """
        op = operation or viability_predicate.operation
        pattern = ErrorPattern(
            _error_kind=error_kind,
            _operation=op,
            _description=description or viability_predicate.description,
            _viability=viability_predicate,
        )
        self.register_pattern(pattern)
        return pattern

    # ── Site registration ──────────────────────────────────────────────────

    def register_error_site(
        self,
        site_id: SiteId,
        error_kind: ErrorKind,
        operation: OperationKind,
        source_operation: str = "",
        source_line: int = 0,
        is_explicit_raise: bool = False,
        guarded: bool = False,
    ) -> ErrorSiteEntry:
        """Register a concrete error site discovered during analysis.

        Automatically assigns the best-matching viability predicate
        from the pattern catalog.
        """
        viability = self._find_best_viability(error_kind, operation)

        entry = ErrorSiteEntry(
            _site_id=site_id,
            _error_kind=error_kind,
            _viability=viability,
            _source_operation=source_operation,
            _source_line=source_line,
            _is_explicit_raise=is_explicit_raise,
            _guarded=guarded,
        )

        self._entries[site_id] = entry
        self._kind_to_sites.setdefault(error_kind, set()).add(site_id)
        self._op_to_sites.setdefault(operation, set()).add(site_id)

        return entry

    def override_viability(
        self, site_id: SiteId, viability: ViabilityPredicate
    ) -> None:
        """Override the viability predicate for a specific site."""
        self._viability_overrides[site_id] = viability

    # ── Querying ───────────────────────────────────────────────────────────

    def get_viability(self, site_id: SiteId) -> str:
        """Get the viability description for a site.

        Returns the override if one exists, otherwise the entry's viability,
        or "unknown" if the site is not registered.
        """
        override = self._viability_overrides.get(site_id)
        if override is not None:
            return override.description

        entry = self._entries.get(site_id)
        if entry is not None:
            return entry.viability.description

        return "unknown"

    def get_viability_predicate(self, site_id: SiteId) -> Optional[ViabilityPredicate]:
        """Get the full viability predicate for a site."""
        override = self._viability_overrides.get(site_id)
        if override is not None:
            return override
        entry = self._entries.get(site_id)
        if entry is not None:
            return entry.viability
        return None

    def get_entry(self, site_id: SiteId) -> Optional[ErrorSiteEntry]:
        """Look up the error site entry for a site."""
        return self._entries.get(site_id)

    def get_error_sites_for_operation(
        self, op_kind: OperationKind
    ) -> List[SiteId]:
        """Get all error sites triggered by a given operation kind."""
        return list(self._op_to_sites.get(op_kind, set()))

    def get_error_sites_for_error(self, error_kind: ErrorKind) -> List[SiteId]:
        """Get all error sites for a given error kind."""
        return list(self._kind_to_sites.get(error_kind, set()))

    def get_patterns_for_error(self, error_kind: ErrorKind) -> List[ErrorPattern]:
        """Get all registered patterns for a given error kind."""
        return list(self._patterns.get(error_kind, []))

    def get_patterns_for_operation(
        self, operation: OperationKind
    ) -> List[ErrorPattern]:
        """Get all patterns that may be triggered by an operation."""
        result: List[ErrorPattern] = []
        for patterns in self._patterns.values():
            for p in patterns:
                if p.operation == operation:
                    result.append(p)
        return result

    def get_guarded_sites(self) -> List[SiteId]:
        """Get all error sites that are guarded by try/except."""
        return [
            sid for sid, entry in self._entries.items() if entry.guarded
        ]

    def get_unguarded_sites(self) -> List[SiteId]:
        """Get all error sites that are NOT guarded."""
        return [
            sid for sid, entry in self._entries.items() if not entry.guarded
        ]

    def is_registered(self, site_id: SiteId) -> bool:
        """Check whether a site is registered as an error site."""
        return site_id in self._entries

    def is_viable(self, site_id: SiteId) -> bool:
        """Check whether an error site is viable (can actually be raised).

        Sites with always_viable predicates or without override are considered
        viable.  Sites with a confidence below 0.3 are considered not viable.
        """
        pred = self.get_viability_predicate(site_id)
        if pred is None:
            return True  # Unknown sites are conservatively viable
        if pred.is_always_viable:
            return True
        return pred.confidence >= 0.3

    # ── Aggregate queries ──────────────────────────────────────────────────

    @property
    def all_error_sites(self) -> FrozenSet[SiteId]:
        """All registered error site ids."""
        return frozenset(self._entries.keys())

    @property
    def site_count(self) -> int:
        """Number of registered error sites."""
        return len(self._entries)

    @property
    def pattern_count(self) -> int:
        """Total number of registered patterns."""
        return sum(len(ps) for ps in self._patterns.values())

    def error_kind_histogram(self) -> Dict[ErrorKind, int]:
        """Histogram of error kinds across registered sites."""
        return {
            kind: len(sites)
            for kind, sites in self._kind_to_sites.items()
        }

    def operation_histogram(self) -> Dict[OperationKind, int]:
        """Histogram of operation kinds across registered sites."""
        return {
            op: len(sites) for op, sites in self._op_to_sites.items()
        }

    # ── Internal helpers ───────────────────────────────────────────────────

    def _find_best_viability(
        self, error_kind: ErrorKind, operation: OperationKind
    ) -> ViabilityPredicate:
        """Find the best matching viability predicate from the catalog.

        Prefers exact (error_kind, operation) matches.  Falls back to
        error_kind-only match, then a generic predicate.
        """
        patterns = self._patterns.get(error_kind, [])

        # Exact match on both error kind and operation
        for p in patterns:
            if p.operation == operation:
                return p.viability

        # Any pattern for the error kind
        if patterns:
            return patterns[0].viability

        # Generic fallback
        return ViabilityPredicate(
            _description=f"{error_kind.value} may be raised",
            _error_kind=error_kind,
            _operation=operation,
            _is_always_viable=True,
            _confidence=0.3,
        )

    # ── Diagnostics ────────────────────────────────────────────────────────

    def summary_report(self) -> str:
        """Generate a summary report of the registry."""
        lines: List[str] = []
        lines.append(
            f"ErrorSiteRegistry: {self.site_count} sites, "
            f"{self.pattern_count} patterns"
        )
        lines.append("")

        if self._entries:
            lines.append("Error sites by kind:")
            for kind, count in sorted(
                self.error_kind_histogram().items(),
                key=lambda kv: kv[1],
                reverse=True,
            ):
                lines.append(f"  {kind.value}: {count}")

        unguarded = self.get_unguarded_sites()
        if unguarded:
            lines.append(f"\nUnguarded error sites: {len(unguarded)}")
            for sid in unguarded[:10]:
                entry = self._entries[sid]
                lines.append(
                    f"  {sid}: {entry.error_kind.value} "
                    f"({entry.viability.description})"
                )
            if len(unguarded) > 10:
                lines.append(f"  ... and {len(unguarded) - 10} more")

        return "\n".join(lines)

    def merge(self, other: ErrorSiteRegistry) -> None:
        """Merge all entries and patterns from *other* into this registry."""
        for kind, patterns in other._patterns.items():
            existing = self._patterns.setdefault(kind, [])
            for p in patterns:
                if p not in existing:
                    existing.append(p)

        for sid, entry in other._entries.items():
            self._entries[sid] = entry
            self._kind_to_sites.setdefault(entry.error_kind, set()).add(sid)

        for op, sites in other._op_to_sites.items():
            self._op_to_sites.setdefault(op, set()).update(sites)

        for sid, v in other._viability_overrides.items():
            self._viability_overrides[sid] = v

    def clear_sites(self) -> None:
        """Clear all registered sites but keep patterns."""
        self._entries.clear()
        self._kind_to_sites.clear()
        self._op_to_sites.clear()
        self._viability_overrides.clear()

    def __repr__(self) -> str:
        return (
            f"ErrorSiteRegistry({self.site_count} sites, "
            f"{self.pattern_count} patterns)"
        )
