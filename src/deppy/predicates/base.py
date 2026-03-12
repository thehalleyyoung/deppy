"""Predicate AST / intermediate representation for DepPy.

Defines the core abstract base classes and concrete term/predicate nodes that
form the logical vocabulary of refinement types:

- **Predicate**: Boolean-valued expressions appearing in {v: τ | φ}.
- **Term**: Value-level expressions embedded inside predicates.
- **SourceLocation**: Provenance link back to Python source.

Every node is an immutable (frozen) dataclass so it can safely serve as a
dictionary key or set member inside ``LocalSection.refinements``.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import (
    Any,
    ClassVar,
    Dict,
    FrozenSet,
    Iterator,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)


# ---------------------------------------------------------------------------
# Source location
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SourceLocation:
    """Source-code location for error messages and provenance."""

    file: str
    line: int
    col: int
    end_line: Optional[int] = None
    end_col: Optional[int] = None

    def pretty(self) -> str:
        base = f"{self.file}:{self.line}:{self.col}"
        if self.end_line is not None:
            base += f"-{self.end_line}"
            if self.end_col is not None:
                base += f":{self.end_col}"
        return base

    def __repr__(self) -> str:
        return f"SourceLocation({self.pretty()!r})"


# ---------------------------------------------------------------------------
# Abstract Term
# ---------------------------------------------------------------------------

class Term(ABC):
    """Base class for value-level expressions inside predicates.

    Terms represent computations that produce values (integers, floats,
    strings, booleans, …) and appear as operands of predicates.  Every
    concrete subclass is a frozen dataclass.
    """

    @abstractmethod
    def free_variables(self) -> Set[str]:
        """Return the set of unbound variable names in this term."""

    @abstractmethod
    def substitute(self, mapping: Dict[str, Term]) -> Term:
        """Return a new term with variables replaced according to *mapping*."""

    @abstractmethod
    def pretty(self) -> str:
        """Human-readable rendering of this term."""

    @abstractmethod
    def walk_terms(self) -> Iterator[Term]:
        """Yield *self* and all sub-terms, depth-first."""

    # Convenience -------------------------------------------------------

    def contains_var(self, name: str) -> bool:
        """Return ``True`` when *name* appears free in this term."""
        return name in self.free_variables()


# ---------------------------------------------------------------------------
# Abstract Predicate
# ---------------------------------------------------------------------------

class Predicate(ABC):
    """Base class for all predicates (Boolean-valued formulas).

    Predicates form the refinement component of dependent types
    ``{v: τ | φ}`` and appear in guards, assertions, contracts, and
    verification conditions.
    """

    @abstractmethod
    def free_variables(self) -> Set[str]:
        """Return all unbound variable names."""

    @abstractmethod
    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        """Apply a simultaneous substitution of terms for variables."""

    @abstractmethod
    def negate(self) -> Predicate:
        """Return the logical negation of this predicate."""

    @abstractmethod
    def simplify(self) -> Predicate:
        """Return a (possibly) simplified equivalent predicate."""

    @abstractmethod
    def pretty(self) -> str:
        """Pretty-print to a human-readable string."""

    @abstractmethod
    def walk(self) -> Iterator[Predicate]:
        """Yield *self* followed by all sub-predicates, depth-first."""

    @abstractmethod
    def walk_terms(self) -> Iterator[Term]:
        """Yield every term embedded in this predicate (recursive)."""

    # Convenience -------------------------------------------------------

    def contains_var(self, name: str) -> bool:
        return name in self.free_variables()


# ===================================================================
#  Concrete Terms
# ===================================================================

@dataclass(frozen=True)
class Var(Term):
    """A free or bound variable reference."""

    name: str

    def free_variables(self) -> Set[str]:
        return {self.name}

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return mapping.get(self.name, self)

    def pretty(self) -> str:
        return self.name

    def walk_terms(self) -> Iterator[Term]:
        yield self

    def __repr__(self) -> str:
        return f"Var({self.name!r})"


@dataclass(frozen=True)
class IntLit(Term):
    """Integer literal."""

    value: int

    def free_variables(self) -> Set[str]:
        return set()

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return self

    def pretty(self) -> str:
        return str(self.value)

    def walk_terms(self) -> Iterator[Term]:
        yield self

    def __repr__(self) -> str:
        return f"IntLit({self.value!r})"


@dataclass(frozen=True)
class FloatLit(Term):
    """Floating-point literal."""

    value: float

    def free_variables(self) -> Set[str]:
        return set()

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return self

    def pretty(self) -> str:
        return repr(self.value)

    def walk_terms(self) -> Iterator[Term]:
        yield self

    def __repr__(self) -> str:
        return f"FloatLit({self.value!r})"


@dataclass(frozen=True)
class BoolLit(Term):
    """Boolean literal."""

    value: bool

    def free_variables(self) -> Set[str]:
        return set()

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return self

    def pretty(self) -> str:
        return str(self.value)

    def walk_terms(self) -> Iterator[Term]:
        yield self

    def __repr__(self) -> str:
        return f"BoolLit({self.value!r})"


@dataclass(frozen=True)
class StrLit(Term):
    """String literal."""

    value: str

    def free_variables(self) -> Set[str]:
        return set()

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return self

    def pretty(self) -> str:
        return repr(self.value)

    def walk_terms(self) -> Iterator[Term]:
        yield self

    def __repr__(self) -> str:
        return f"StrLit({self.value!r})"


@dataclass(frozen=True)
class NoneLit(Term):
    """The ``None`` literal."""

    def free_variables(self) -> Set[str]:
        return set()

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return self

    def pretty(self) -> str:
        return "None"

    def walk_terms(self) -> Iterator[Term]:
        yield self

    def __repr__(self) -> str:
        return "NoneLit()"


@dataclass(frozen=True)
class BinOp(Term):
    """Binary arithmetic/bitwise operation on two terms.

    Supported operators: ``+``, ``-``, ``*``, ``//``, ``%``, ``**``,
    ``&``, ``|``, ``^``, ``<<``, ``>>``.
    """

    op: str
    left: Term
    right: Term

    _VALID_OPS: ClassVar[frozenset[str]] = frozenset(
        {"+", "-", "*", "//", "%", "**", "&", "|", "^", "<<", ">>"}
    )

    def __post_init__(self) -> None:
        if self.op not in self._VALID_OPS:
            raise ValueError(f"Unknown binary operator: {self.op!r}")

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return BinOp(
            op=self.op,
            left=self.left.substitute(mapping),
            right=self.right.substitute(mapping),
        )

    def pretty(self) -> str:
        return f"({self.left.pretty()} {self.op} {self.right.pretty()})"

    def walk_terms(self) -> Iterator[Term]:
        yield self
        yield from self.left.walk_terms()
        yield from self.right.walk_terms()

    def __repr__(self) -> str:
        return f"BinOp({self.op!r}, {self.left!r}, {self.right!r})"


@dataclass(frozen=True)
class UnaryOp(Term):
    """Unary operation on a single term.

    Supported operators: ``-`` (negate), ``+`` (identity), ``~`` (bitwise not).
    """

    op: str
    operand: Term

    _VALID_OPS: ClassVar[frozenset[str]] = frozenset({"-", "+", "~"})

    def __post_init__(self) -> None:
        if self.op not in self._VALID_OPS:
            raise ValueError(f"Unknown unary operator: {self.op!r}")

    def free_variables(self) -> Set[str]:
        return self.operand.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return UnaryOp(op=self.op, operand=self.operand.substitute(mapping))

    def pretty(self) -> str:
        return f"({self.op}{self.operand.pretty()})"

    def walk_terms(self) -> Iterator[Term]:
        yield self
        yield from self.operand.walk_terms()

    def __repr__(self) -> str:
        return f"UnaryOp({self.op!r}, {self.operand!r})"


@dataclass(frozen=True)
class Call(Term):
    """Function/method call term: ``func(arg₁, arg₂, …)``.

    Models built-in calls like ``len(x)``, ``abs(x)``, ``min(a, b)``.
    """

    func: str
    args: Tuple[Term, ...] = field(default_factory=tuple)

    def __init__(self, func: str, args: Sequence[Term] = ()) -> None:
        object.__setattr__(self, "func", func)
        object.__setattr__(self, "args", tuple(args))

    def free_variables(self) -> Set[str]:
        result: Set[str] = set()
        for a in self.args:
            result |= a.free_variables()
        return result

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return Call(
            func=self.func,
            args=[a.substitute(mapping) for a in self.args],
        )

    def pretty(self) -> str:
        arg_str = ", ".join(a.pretty() for a in self.args)
        return f"{self.func}({arg_str})"

    def walk_terms(self) -> Iterator[Term]:
        yield self
        for a in self.args:
            yield from a.walk_terms()

    def __repr__(self) -> str:
        return f"Call({self.func!r}, {list(self.args)!r})"


@dataclass(frozen=True)
class Attr(Term):
    """Attribute access: ``obj.attr``."""

    obj: Term
    attr: str

    def free_variables(self) -> Set[str]:
        return self.obj.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return Attr(obj=self.obj.substitute(mapping), attr=self.attr)

    def pretty(self) -> str:
        return f"{self.obj.pretty()}.{self.attr}"

    def walk_terms(self) -> Iterator[Term]:
        yield self
        yield from self.obj.walk_terms()

    def __repr__(self) -> str:
        return f"Attr({self.obj!r}, {self.attr!r})"


@dataclass(frozen=True)
class Index(Term):
    """Subscript/index access: ``obj[idx]``."""

    obj: Term
    idx: Term

    def free_variables(self) -> Set[str]:
        return self.obj.free_variables() | self.idx.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return Index(
            obj=self.obj.substitute(mapping),
            idx=self.idx.substitute(mapping),
        )

    def pretty(self) -> str:
        return f"{self.obj.pretty()}[{self.idx.pretty()}]"

    def walk_terms(self) -> Iterator[Term]:
        yield self
        yield from self.obj.walk_terms()
        yield from self.idx.walk_terms()

    def __repr__(self) -> str:
        return f"Index({self.obj!r}, {self.idx!r})"


@dataclass(frozen=True)
class TupleLit(Term):
    """Tuple literal: ``(e₁, e₂, …)``."""

    elements: Tuple[Term, ...] = field(default_factory=tuple)

    def __init__(self, elements: Sequence[Term] = ()) -> None:
        object.__setattr__(self, "elements", tuple(elements))

    def free_variables(self) -> Set[str]:
        result: Set[str] = set()
        for e in self.elements:
            result |= e.free_variables()
        return result

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return TupleLit([e.substitute(mapping) for e in self.elements])

    def pretty(self) -> str:
        inner = ", ".join(e.pretty() for e in self.elements)
        if len(self.elements) == 1:
            inner += ","
        return f"({inner})"

    def walk_terms(self) -> Iterator[Term]:
        yield self
        for e in self.elements:
            yield from e.walk_terms()

    def __repr__(self) -> str:
        return f"TupleLit({list(self.elements)!r})"


@dataclass(frozen=True)
class IfExpr(Term):
    """Conditional expression: ``then_ if cond else else_``."""

    cond: Predicate
    then_: Term
    else_: Term

    def free_variables(self) -> Set[str]:
        return (
            self.cond.free_variables()
            | self.then_.free_variables()
            | self.else_.free_variables()
        )

    def substitute(self, mapping: Dict[str, Term]) -> Term:
        return IfExpr(
            cond=self.cond.substitute(mapping),
            then_=self.then_.substitute(mapping),
            else_=self.else_.substitute(mapping),
        )

    def pretty(self) -> str:
        return (
            f"({self.then_.pretty()} if {self.cond.pretty()} "
            f"else {self.else_.pretty()})"
        )

    def walk_terms(self) -> Iterator[Term]:
        yield self
        yield from self.cond.walk_terms()
        yield from self.then_.walk_terms()
        yield from self.else_.walk_terms()

    def __repr__(self) -> str:
        return f"IfExpr({self.cond!r}, {self.then_!r}, {self.else_!r})"


# ===================================================================
#  Helpers
# ===================================================================

def _coerce_to_term(value: Any) -> Term:
    """Best-effort coercion of a Python literal to a ``Term``."""
    if isinstance(value, Term):
        return value
    if isinstance(value, bool):
        return BoolLit(value)
    if isinstance(value, int):
        return IntLit(value)
    if isinstance(value, float):
        return FloatLit(value)
    if isinstance(value, str):
        return StrLit(value)
    if value is None:
        return NoneLit()
    if isinstance(value, (list, tuple)):
        return TupleLit([_coerce_to_term(v) for v in value])
    raise TypeError(f"Cannot coerce {type(value).__name__} to Term")
