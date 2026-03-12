"""Fluent builder API for predicate construction.

Provides:

- **PredicateBuilder**: Static methods for common predicate patterns.
- **TermBuilder**: Operator-overloaded wrapper around a ``Term`` for
  chained construction.
"""

from __future__ import annotations

from typing import Any, List, Optional, Sequence, Tuple, Union

from deppy.predicates.arithmetic import Comparison, IntRange, LinearInequality
from deppy.predicates.base import (
    Attr,
    BinOp,
    BoolLit,
    Call,
    FloatLit,
    Index,
    IntLit,
    NoneLit,
    Predicate,
    SourceLocation,
    StrLit,
    Term,
    TupleLit,
    Var,
    _coerce_to_term,
)
from deppy.predicates.boolean import And, Exists, ForAll, Iff, Implies, Not, Or
from deppy.predicates.collection import (
    Contains,
    Disjoint,
    LengthPred,
    NonEmpty,
    Permutation,
    Sorted,
    Subset,
    Unique,
)
from deppy.predicates.heap import (
    FieldValue,
    HasField,
    Initialized,
    ProtocolConformance,
)
from deppy.predicates.nullability import (
    Falsy,
    IsInstance,
    IsNone,
    IsNotNone,
    Truthy,
)
from deppy.predicates.tensor import (
    BroadcastCompatible,
    ContiguousPred,
    DevicePred,
    DtypePred,
    RankPred,
    ShapePred,
    ShapeRelation,
)


# ===================================================================
#  TermBuilder — fluent wrapper
# ===================================================================

class TermBuilder:
    """Fluent wrapper around a ``Term`` with operator overloading.

    Arithmetic and comparison operators return predicate / term nodes
    directly so that users can write::

        x = PredicateBuilder.var("x")
        pred = (x > 0) & (x < 100)
    """

    __slots__ = ("_term",)

    def __init__(self, term: Term) -> None:
        self._term = term

    @property
    def term(self) -> Term:
        """Return the underlying ``Term``."""
        return self._term

    # -- comparisons (return Comparison predicates) --------------------

    def __gt__(self, other: Any) -> Comparison:
        return Comparison(">", self._term, _as_term(other))

    def __ge__(self, other: Any) -> Comparison:
        return Comparison(">=", self._term, _as_term(other))

    def __lt__(self, other: Any) -> Comparison:
        return Comparison("<", self._term, _as_term(other))

    def __le__(self, other: Any) -> Comparison:
        return Comparison("<=", self._term, _as_term(other))

    def __eq__(self, other: Any) -> Comparison:  # type: ignore[override]
        return Comparison("==", self._term, _as_term(other))

    def __ne__(self, other: Any) -> Comparison:  # type: ignore[override]
        return Comparison("!=", self._term, _as_term(other))

    # -- arithmetic (return TermBuilder) --------------------------------

    def __add__(self, other: Any) -> TermBuilder:
        return TermBuilder(BinOp("+", self._term, _as_term(other)))

    def __radd__(self, other: Any) -> TermBuilder:
        return TermBuilder(BinOp("+", _as_term(other), self._term))

    def __sub__(self, other: Any) -> TermBuilder:
        return TermBuilder(BinOp("-", self._term, _as_term(other)))

    def __rsub__(self, other: Any) -> TermBuilder:
        return TermBuilder(BinOp("-", _as_term(other), self._term))

    def __mul__(self, other: Any) -> TermBuilder:
        return TermBuilder(BinOp("*", self._term, _as_term(other)))

    def __rmul__(self, other: Any) -> TermBuilder:
        return TermBuilder(BinOp("*", _as_term(other), self._term))

    def __floordiv__(self, other: Any) -> TermBuilder:
        return TermBuilder(BinOp("//", self._term, _as_term(other)))

    def __mod__(self, other: Any) -> TermBuilder:
        return TermBuilder(BinOp("%", self._term, _as_term(other)))

    def __pow__(self, other: Any) -> TermBuilder:
        return TermBuilder(BinOp("**", self._term, _as_term(other)))

    def __neg__(self) -> TermBuilder:
        from deppy.predicates.base import UnaryOp
        return TermBuilder(UnaryOp("-", self._term))

    def __pos__(self) -> TermBuilder:
        return self

    # -- attribute / call / index (return TermBuilder) -----------------

    def dot(self, attr: str) -> TermBuilder:
        """Attribute access: ``self.attr``."""
        return TermBuilder(Attr(self._term, attr))

    def call(self, *args: Any) -> TermBuilder:
        """Function call with the current term as the callee name.

        If the underlying term is a ``Var``, the var name becomes the
        function name.  Otherwise wraps in a generic ``Call``.
        """
        coerced = [_as_term(a) for a in args]
        if isinstance(self._term, Var):
            return TermBuilder(Call(self._term.name, coerced))
        # For attr-calls like x.dot("shape").call(), model as Call on pretty name
        return TermBuilder(Call(self._term.pretty(), coerced))

    def index(self, idx: Any) -> TermBuilder:
        """Subscript access: ``self[idx]``."""
        return TermBuilder(Index(self._term, _as_term(idx)))

    def __getitem__(self, idx: Any) -> TermBuilder:
        return self.index(idx)

    # -- convenience predicates ----------------------------------------

    def is_none(self) -> IsNone:
        """``self is None``."""
        return IsNone(self._term)

    def is_not_none(self) -> IsNotNone:
        """``self is not None``."""
        return IsNotNone(self._term)

    def is_instance(self, type_name: str) -> IsInstance:
        """``isinstance(self, type_name)``."""
        return IsInstance(self._term, type_name)

    def is_truthy(self) -> Truthy:
        """``bool(self) is True``."""
        return Truthy(self._term)

    def is_falsy(self) -> Falsy:
        """``bool(self) is False``."""
        return Falsy(self._term)

    def in_(self, collection: Any) -> Contains:
        """``self in collection``."""
        return Contains(self._term, _as_term(collection))

    def has_field(self, name: str, type_name: Optional[str] = None) -> HasField:
        """``hasattr(self, name)``."""
        return HasField(self._term, name, type_name=type_name)

    def __repr__(self) -> str:
        return f"TermBuilder({self._term!r})"


# ===================================================================
#  PredicateBuilder — static factory
# ===================================================================

class PredicateBuilder:
    """Fluent API for constructing predicates.

    Typical usage::

        P = PredicateBuilder
        x = P.var("x")
        pred = P.and_(x > 0, x < 100)
    """

    # -- Term factories ------------------------------------------------

    @staticmethod
    def var(name: str) -> TermBuilder:
        """Create a variable term wrapped in a ``TermBuilder``."""
        return TermBuilder(Var(name))

    @staticmethod
    def const(value: Any) -> Term:
        """Coerce a Python literal to a ``Term``."""
        return _coerce_to_term(value)

    @staticmethod
    def int_(value: int) -> IntLit:
        return IntLit(value)

    @staticmethod
    def float_(value: float) -> FloatLit:
        return FloatLit(value)

    @staticmethod
    def bool_(value: bool) -> BoolLit:
        return BoolLit(value)

    @staticmethod
    def str_(value: str) -> StrLit:
        return StrLit(value)

    @staticmethod
    def none() -> NoneLit:
        return NoneLit()

    @staticmethod
    def tuple_(*elems: Any) -> TupleLit:
        return TupleLit([_as_term(e) for e in elems])

    # -- Comparison factories ------------------------------------------

    @staticmethod
    def comparison(left: Any, op: str, right: Any) -> Comparison:
        """Create a comparison predicate."""
        return Comparison(op, _as_term(left), _as_term(right))

    @staticmethod
    def gt(left: Any, right: Any) -> Comparison:
        return Comparison(">", _as_term(left), _as_term(right))

    @staticmethod
    def ge(left: Any, right: Any) -> Comparison:
        return Comparison(">=", _as_term(left), _as_term(right))

    @staticmethod
    def lt(left: Any, right: Any) -> Comparison:
        return Comparison("<", _as_term(left), _as_term(right))

    @staticmethod
    def le(left: Any, right: Any) -> Comparison:
        return Comparison("<=", _as_term(left), _as_term(right))

    @staticmethod
    def eq(left: Any, right: Any) -> Comparison:
        return Comparison("==", _as_term(left), _as_term(right))

    @staticmethod
    def ne(left: Any, right: Any) -> Comparison:
        return Comparison("!=", _as_term(left), _as_term(right))

    # -- Boolean combinators -------------------------------------------

    @staticmethod
    def and_(*preds: Predicate) -> Predicate:
        """Conjunction.  Returns ``_TRUE`` for zero arguments."""
        from deppy.predicates.boolean import _TRUE
        if not preds:
            return _TRUE
        if len(preds) == 1:
            return preds[0]
        return And(list(preds))

    @staticmethod
    def or_(*preds: Predicate) -> Predicate:
        """Disjunction.  Returns ``_FALSE`` for zero arguments."""
        from deppy.predicates.boolean import _FALSE
        if not preds:
            return _FALSE
        if len(preds) == 1:
            return preds[0]
        return Or(list(preds))

    @staticmethod
    def not_(pred: Predicate) -> Predicate:
        return Not(pred)

    @staticmethod
    def implies(a: Predicate, b: Predicate) -> Implies:
        return Implies(a, b)

    @staticmethod
    def iff(a: Predicate, b: Predicate) -> Iff:
        return Iff(a, b)

    @staticmethod
    def forall(var: str, body: Predicate, domain: Any = None) -> ForAll:
        return ForAll(var=var, body=body, domain=domain)

    @staticmethod
    def exists(var: str, body: Predicate, domain: Any = None) -> Exists:
        return Exists(var=var, body=body, domain=domain)

    # -- Nullability ---------------------------------------------------

    @staticmethod
    def is_none(term: Any) -> IsNone:
        return IsNone(_as_term(term))

    @staticmethod
    def is_not_none(term: Any) -> IsNotNone:
        return IsNotNone(_as_term(term))

    @staticmethod
    def is_instance(term: Any, type_name: str) -> IsInstance:
        return IsInstance(_as_term(term), type_name)

    @staticmethod
    def truthy(term: Any) -> Truthy:
        return Truthy(_as_term(term))

    @staticmethod
    def falsy(term: Any) -> Falsy:
        return Falsy(_as_term(term))

    # -- Collection ----------------------------------------------------

    @staticmethod
    def len_gt(collection: Any, n: int) -> LengthPred:
        return LengthPred(_as_term(collection), ">", IntLit(n))

    @staticmethod
    def len_eq(collection: Any, n: int) -> LengthPred:
        return LengthPred(_as_term(collection), "==", IntLit(n))

    @staticmethod
    def non_empty(collection: Any) -> NonEmpty:
        return NonEmpty(_as_term(collection))

    @staticmethod
    def contains(element: Any, collection: Any) -> Contains:
        return Contains(_as_term(element), _as_term(collection))

    @staticmethod
    def sorted_(collection: Any, key: Optional[str] = None, reverse: bool = False) -> Sorted:
        return Sorted(_as_term(collection), key=key, reverse=reverse)

    @staticmethod
    def unique(collection: Any) -> Unique:
        return Unique(_as_term(collection))

    @staticmethod
    def subset(left: Any, right: Any) -> Subset:
        return Subset(_as_term(left), _as_term(right))

    @staticmethod
    def disjoint(left: Any, right: Any) -> Disjoint:
        return Disjoint(_as_term(left), _as_term(right))

    # -- Arithmetic ----------------------------------------------------

    @staticmethod
    def int_range(var: str, lo: Optional[int] = None, hi: Optional[int] = None) -> IntRange:
        return IntRange(variable=var, lo=lo, hi=hi)

    @staticmethod
    def linear_ineq(coefficients: dict[str, int], constant: int) -> LinearInequality:
        return LinearInequality(coefficients, constant)

    # -- Tensor --------------------------------------------------------

    @staticmethod
    def shape_eq(tensor: Any, *dims: Any) -> ShapePred:
        return ShapePred(_as_term(tensor), [_as_term(d) for d in dims])

    @staticmethod
    def rank_eq(tensor: Any, n: int) -> RankPred:
        return RankPred(_as_term(tensor), "==", n)

    @staticmethod
    def dtype_eq(tensor: Any, dtype: str) -> DtypePred:
        return DtypePred(_as_term(tensor), dtype)

    @staticmethod
    def device_eq(tensor: Any, device: str) -> DevicePred:
        return DevicePred(_as_term(tensor), device)

    @staticmethod
    def broadcast_compatible(left: Any, right: Any) -> BroadcastCompatible:
        return BroadcastCompatible(_as_term(left), _as_term(right))

    # -- Heap ----------------------------------------------------------

    @staticmethod
    def has_field(obj: Any, name: str, type_name: Optional[str] = None) -> HasField:
        return HasField(_as_term(obj), name, type_name=type_name)

    @staticmethod
    def field_value(obj: Any, name: str, pred: Predicate) -> FieldValue:
        return FieldValue(_as_term(obj), name, pred)

    @staticmethod
    def conforms_to(obj: Any, protocol: str) -> ProtocolConformance:
        return ProtocolConformance(_as_term(obj), protocol)

    @staticmethod
    def initialized(obj: Any, field_name: str) -> Initialized:
        return Initialized(_as_term(obj), field_name)


# ===================================================================
#  Internal helpers
# ===================================================================

def _as_term(value: Any) -> Term:
    """Coerce *value* to a ``Term``, accepting ``TermBuilder`` wrappers."""
    if isinstance(value, TermBuilder):
        return value.term
    if isinstance(value, Term):
        return value
    return _coerce_to_term(value)
