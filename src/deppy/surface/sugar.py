"""Syntactic sugar for dependent types — making complex types look Pythonic.

The goal: write dependent types as concisely as native Python annotations.

Instead of::

    PiType("n", RefinementType(IntType(), "v", Positive()),
           SigmaType("xs", ListType(IntType()),
                     RefinementType(IntType(), "_", Eq(Var("_"), Len(Var("xs"))))))

Write::

    Dep[int > 0, "n"] >> Pair["xs": List[int], Len("xs")]

Or with decorator sugar::

    @deppy.fn
    def sorted_head(xs: NonEmptyOf[List[int]]) -> int | Leq(Return, xs[0]):
        ...

This module provides:

- **Type-level operators**: ``>>`` for Pi, ``&`` for Sigma/Pair, ``|`` for
  refinement predicates, ``[]`` for indexed families
- **Short aliases**: ``Nat``, ``Pos``, ``NonEmptyOf``, ``BoundedInt``, ``Sized``
- **Predicate combinators**: ``Eq``, ``Neq``, ``Lt``, ``Gt``, ``Leq``, ``Geq``,
  ``And``, ``Or``, ``Not``, ``In``, ``Len``, ``Shape``
- **Builder DSL**: ``Fn[...]``, ``Pair[...]``, ``Ref[τ, φ]``, ``Dep[τ, "x"]``
- **Decorator integration**: ``@deppy.fn``, ``@deppy.checked``
"""

from __future__ import annotations

import functools
import inspect
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterator,
    List as TypingList,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    TypeVar,
    Union,
    overload,
)

from deppy.types.base import TypeBase, AnyType, NeverType, ANY_TYPE, NEVER_TYPE
from deppy.types.dependent import (
    PiType,
    SigmaType,
    MultiPiType,
    IndexedFamily,
    ForallType,
    ExistsType,
    IdentityType,
    WitnessType,
)
from deppy.types.refinement import (
    RefinementType,
    Predicate,
    ComparisonPred,
    ComparisonOp,
    ConjunctionPred,
    DisjunctionPred,
    NotPred,
    MembershipPred,
    QualifiedType,
    Qualifier,
    NonNull,
)

T = TypeVar("T")


# ═══════════════════════════════════════════════════════════════════════════════
# Lightweight type aliases
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class _SimpleType(TypeBase):
    """A named type for use in sugar expressions."""

    _name: str

    @property
    def name(self) -> str:
        return self._name

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        return mapping.get(self._name, self)

    def free_variables(self) -> FrozenSet[str]:
        return frozenset()

    def __repr__(self) -> str:
        return self._name


@dataclass(frozen=True)
class _ParametricType(TypeBase):
    """A parameterized type like List[int], Dict[str, int]."""

    _base: str
    _args: Tuple[TypeBase, ...]

    @property
    def base(self) -> str:
        return self._base

    @property
    def args(self) -> Tuple[TypeBase, ...]:
        return self._args

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_args = tuple(a.substitute(mapping) for a in self._args)
        if all(n is o for n, o in zip(new_args, self._args)):
            return self
        return _ParametricType(self._base, new_args)

    def free_variables(self) -> FrozenSet[str]:
        fv: set[str] = set()
        for a in self._args:
            fv |= a.free_variables()
        return frozenset(fv)

    def __repr__(self) -> str:
        args_str = ", ".join(repr(a) for a in self._args)
        return f"{self._base}[{args_str}]"


# Primitive type shortcuts
Int = _SimpleType("int")
Float = _SimpleType("float")
Str = _SimpleType("str")
Bool = _SimpleType("bool")
NoneType = _SimpleType("None")
Bytes = _SimpleType("bytes")


# ═══════════════════════════════════════════════════════════════════════════════
# Predicate variable references
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class Var:
    """A variable reference in a predicate expression.

    Usage::

        Var("x")           # reference to x
        Var("x") > 0       # x > 0  (produces a Predicate)
        Var("x") + 1       # x + 1  (produces a TermExpr)
    """

    _name: str

    @property
    def name(self) -> str:
        return self._name

    # Comparison operators → Predicate
    def __gt__(self, other: Any) -> _SugarPred:
        return _SugarPred("gt", self, other)

    def __ge__(self, other: Any) -> _SugarPred:
        return _SugarPred("ge", self, other)

    def __lt__(self, other: Any) -> _SugarPred:
        return _SugarPred("lt", self, other)

    def __le__(self, other: Any) -> _SugarPred:
        return _SugarPred("le", self, other)

    def __eq__(self, other: Any) -> _SugarPred:  # type: ignore[override]
        return _SugarPred("eq", self, other)

    def __ne__(self, other: Any) -> _SugarPred:  # type: ignore[override]
        return _SugarPred("ne", self, other)

    # Arithmetic operators → TermExpr
    def __add__(self, other: Any) -> _TermExpr:
        return _TermExpr("add", self, other)

    def __sub__(self, other: Any) -> _TermExpr:
        return _TermExpr("sub", self, other)

    def __mul__(self, other: Any) -> _TermExpr:
        return _TermExpr("mul", self, other)

    def __mod__(self, other: Any) -> _TermExpr:
        return _TermExpr("mod", self, other)

    def __repr__(self) -> str:
        return self._name


# A few common variable names
v = Var("v")
x = Var("x")
y = Var("y")
n = Var("n")
Return = Var("__return__")


@dataclass(frozen=True)
class _TermExpr:
    """An arithmetic term expression (not yet a predicate)."""

    _op: str
    _left: Any
    _right: Any

    @property
    def op(self) -> str:
        return self._op

    @property
    def left(self) -> Any:
        return self._left

    @property
    def right(self) -> Any:
        return self._right

    def __gt__(self, other: Any) -> _SugarPred:
        return _SugarPred("gt", self, other)

    def __ge__(self, other: Any) -> _SugarPred:
        return _SugarPred("ge", self, other)

    def __lt__(self, other: Any) -> _SugarPred:
        return _SugarPred("lt", self, other)

    def __le__(self, other: Any) -> _SugarPred:
        return _SugarPred("le", self, other)

    def __eq__(self, other: Any) -> _SugarPred:  # type: ignore[override]
        return _SugarPred("eq", self, other)

    def __ne__(self, other: Any) -> _SugarPred:  # type: ignore[override]
        return _SugarPred("ne", self, other)

    def __repr__(self) -> str:
        return f"({self._left} {self._op} {self._right})"


# ═══════════════════════════════════════════════════════════════════════════════
# Sugar predicates
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class _SugarPred:
    """A lightweight predicate produced by operator overloading.

    Converts to a real :class:`Predicate` via :func:`to_predicate`.
    """

    _op: str
    _left: Any
    _right: Any

    @property
    def op(self) -> str:
        return self._op

    @property
    def left(self) -> Any:
        return self._left

    @property
    def right(self) -> Any:
        return self._right

    # Logical combinators
    def __and__(self, other: _SugarPred) -> _SugarPred:
        return _SugarPred("and", self, other)

    def __or__(self, other: _SugarPred) -> _SugarPred:
        return _SugarPred("or", self, other)

    def __invert__(self) -> _SugarPred:
        return _SugarPred("not", self, None)

    def __repr__(self) -> str:
        if self._op == "not":
            return f"¬({self._left})"
        op_symbols = {
            "gt": ">", "ge": "≥", "lt": "<", "le": "≤",
            "eq": "=", "ne": "≠", "and": "∧", "or": "∨",
        }
        sym = op_symbols.get(self._op, self._op)
        return f"({self._left} {sym} {self._right})"


def _term_to_str(t: Any) -> str:
    """Convert a term/var/literal to string form for predicates."""
    if isinstance(t, Var):
        return t.name
    if isinstance(t, _TermExpr):
        return f"({_term_to_str(t.left)} {t.op} {_term_to_str(t.right)})"
    return str(t)


def to_predicate(sp: _SugarPred, binder: str = "v") -> Predicate:
    """Convert a sugar predicate to a real :class:`Predicate`."""
    op_map = {
        "gt": ComparisonOp.GT, "ge": ComparisonOp.GE, "lt": ComparisonOp.LT,
        "le": ComparisonOp.LE, "eq": ComparisonOp.EQ, "ne": ComparisonOp.NE,
    }

    if sp.op in op_map:
        lhs = _term_to_str(sp.left)
        rhs = _term_to_str(sp.right)
        return ComparisonPred(lhs, op_map[sp.op], rhs)

    if sp.op == "and":
        left_p = to_predicate(sp.left, binder) if isinstance(sp.left, _SugarPred) else sp.left
        right_p = to_predicate(sp.right, binder) if isinstance(sp.right, _SugarPred) else sp.right
        return ConjunctionPred((left_p, right_p))

    if sp.op == "or":
        left_p = to_predicate(sp.left, binder) if isinstance(sp.left, _SugarPred) else sp.left
        right_p = to_predicate(sp.right, binder) if isinstance(sp.right, _SugarPred) else sp.right
        return DisjunctionPred((left_p, right_p))

    if sp.op == "not":
        inner = to_predicate(sp.left, binder) if isinstance(sp.left, _SugarPred) else sp.left
        return NotPred(inner)

    raise ValueError(f"Unknown sugar predicate operator: {sp.op}")


# ═══════════════════════════════════════════════════════════════════════════════
# Predicate shorthand functions
# ═══════════════════════════════════════════════════════════════════════════════


def Eq(a: Any, b: Any) -> _SugarPred:
    """Equality predicate: ``a == b``."""
    return _SugarPred("eq", a, b)


def Neq(a: Any, b: Any) -> _SugarPred:
    """Inequality predicate: ``a != b``."""
    return _SugarPred("ne", a, b)


def Lt(a: Any, b: Any) -> _SugarPred:
    """Strict less-than: ``a < b``."""
    return _SugarPred("lt", a, b)


def Gt(a: Any, b: Any) -> _SugarPred:
    """Strict greater-than: ``a > b``."""
    return _SugarPred("gt", a, b)


def Leq(a: Any, b: Any) -> _SugarPred:
    """Less-or-equal: ``a <= b``."""
    return _SugarPred("le", a, b)


def Geq(a: Any, b: Any) -> _SugarPred:
    """Greater-or-equal: ``a >= b``."""
    return _SugarPred("ge", a, b)


def And(*preds: _SugarPred) -> _SugarPred:
    """Conjunction of predicates."""
    if not preds:
        raise ValueError("And() requires at least one predicate")
    result = preds[0]
    for p in preds[1:]:
        result = result & p
    return result


def Or(*preds: _SugarPred) -> _SugarPred:
    """Disjunction of predicates."""
    if not preds:
        raise ValueError("Or() requires at least one predicate")
    result = preds[0]
    for p in preds[1:]:
        result = result | p
    return result


def Not(pred: _SugarPred) -> _SugarPred:
    """Negation of a predicate."""
    return ~pred


def Len(var_name: Any) -> _TermExpr:
    """Length term: ``len(var)``."""
    return _TermExpr("len", var_name, None)


def Shape(var_name: Any, dim: int = -1) -> _TermExpr:
    """Tensor shape term: ``shape(var)`` or ``shape(var, dim)``."""
    return _TermExpr("shape", var_name, dim)


def Rank(var_name: Any) -> _TermExpr:
    """Tensor rank term: ``rank(var)``."""
    return _TermExpr("rank", var_name, None)


def Idx(var_name: Any, index: Any) -> _TermExpr:
    """Indexing term: ``var[index]``."""
    return _TermExpr("idx", var_name, index)


# ═══════════════════════════════════════════════════════════════════════════════
# Refined type builder: Ref[τ, φ]
# ═══════════════════════════════════════════════════════════════════════════════


class _RefMeta:
    """Metaclass-like builder for ``Ref[int, v > 0]`` syntax.

    Usage::

        Ref[int, v > 0]              → {v: int | v > 0}
        Ref[int, (v > 0) & (v < 100)] → {v: int | v > 0 ∧ v < 100}
    """

    def __getitem__(self, key: Any) -> RefinementType:
        if not isinstance(key, tuple) or len(key) != 2:
            raise TypeError("Ref requires Ref[type, predicate]")
        base_type, pred = key
        base = _resolve_type(base_type)
        real_pred = to_predicate(pred) if isinstance(pred, _SugarPred) else pred
        return RefinementType(base, "v", real_pred)

    def __repr__(self) -> str:
        return "Ref"


Ref = _RefMeta()
"""Refinement type builder: ``Ref[int, v > 0]``."""


# ═══════════════════════════════════════════════════════════════════════════════
# Dependent function builder: Fn[...]
# ═══════════════════════════════════════════════════════════════════════════════


class _FnMeta:
    """Builder for dependent function types.

    Usage::

        Fn["n": Pos, List[int]]              → Π(n: Pos). List[int]
        Fn[int, str]                          → int → str
        Fn[("n", Nat), ("xs", Vec(n)), int]  → Π(n:Nat, xs:Vec(n)). int
    """

    def __getitem__(self, key: Any) -> TypeBase:
        if not isinstance(key, tuple):
            raise TypeError("Fn requires Fn[param_types..., return_type]")

        items = list(key)
        if len(items) < 2:
            raise TypeError("Fn requires at least one parameter and a return type")

        return_type = _resolve_type(items[-1])
        params = items[:-1]

        # Collect (name, type) pairs
        param_pairs: TypingList[Tuple[str, TypeBase]] = []
        for i, p in enumerate(params):
            if isinstance(p, tuple) and len(p) == 2:
                name, ty = p
                param_pairs.append((str(name), _resolve_type(ty)))
            elif isinstance(p, slice):
                # Fn["n": int, ...]  →  slice(name, type, None)
                name = p.start
                ty = p.stop
                param_pairs.append((str(name), _resolve_type(ty)))
            else:
                param_pairs.append((f"_p{i}", _resolve_type(p)))

        if len(param_pairs) == 1:
            name, ty = param_pairs[0]
            return PiType(name, ty, return_type)

        return MultiPiType(tuple(param_pairs), return_type)

    def __repr__(self) -> str:
        return "Fn"


Fn = _FnMeta()
"""Dependent function type builder: ``Fn[("n", Nat), Vec("n")]``."""


# ═══════════════════════════════════════════════════════════════════════════════
# Dependent pair builder: Pair[...]
# ═══════════════════════════════════════════════════════════════════════════════


class _PairMeta:
    """Builder for dependent pair (Sigma) types.

    Usage::

        Pair[("n", Nat), Vec("n")]    → Σ(n: Nat). Vec(n)
        Pair[int, str]                → int × str (non-dependent)
    """

    def __getitem__(self, key: Any) -> TypeBase:
        if not isinstance(key, tuple) or len(key) != 2:
            raise TypeError("Pair requires Pair[first, second]")

        fst, snd = key
        if isinstance(fst, tuple) and len(fst) == 2:
            name, ty = fst
            return SigmaType(str(name), _resolve_type(ty), _resolve_type(snd))
        if isinstance(fst, slice):
            name = fst.start
            ty = fst.stop
            return SigmaType(str(name), _resolve_type(ty), _resolve_type(snd))

        return SigmaType("_fst", _resolve_type(fst), _resolve_type(snd))

    def __repr__(self) -> str:
        return "Pair"


Pair = _PairMeta()
"""Dependent pair type builder: ``Pair[("n", Nat), Vec("n")]``."""


# ═══════════════════════════════════════════════════════════════════════════════
# Dep[...] — generic dependent type binding
# ═══════════════════════════════════════════════════════════════════════════════


class _DepMeta:
    """Generic dependent binding: attach a name to a type for downstream use.

    Usage::

        Dep["n", int]       → a binding (n : int) for use in Pi/Sigma
        Dep["xs", List[int], Len("xs") > 0]  → refined binding
    """

    def __getitem__(self, key: Any) -> Tuple[str, TypeBase]:
        if not isinstance(key, tuple):
            raise TypeError("Dep requires Dep[name, type] or Dep[name, type, predicate]")

        if len(key) == 2:
            name, ty = key
            return (str(name), _resolve_type(ty))

        if len(key) == 3:
            name, ty, pred = key
            base = _resolve_type(ty)
            real_pred = to_predicate(pred) if isinstance(pred, _SugarPred) else pred
            refined = RefinementType(base, str(name), real_pred)
            return (str(name), refined)

        raise TypeError("Dep requires 2 or 3 arguments: Dep[name, type] or Dep[name, type, pred]")

    def __repr__(self) -> str:
        return "Dep"


Dep = _DepMeta()
"""Dependent binding builder: ``Dep["n", int]``."""


# ═══════════════════════════════════════════════════════════════════════════════
# Common refined type shortcuts
# ═══════════════════════════════════════════════════════════════════════════════


# Nat = {v: int | v >= 0}
Nat = RefinementType(Int, "v", ComparisonPred("v", ComparisonOp.GE, "0"))
"""Non-negative integer: ``{v: int | v >= 0}``."""

# Pos = {v: int | v > 0}
Pos = RefinementType(Int, "v", ComparisonPred("v", ComparisonOp.GT, "0"))
"""Positive integer: ``{v: int | v > 0}``."""


def BoundedInt(lo: Any, hi: Any, base: Any = None) -> RefinementType:
    """Bounded integer: ``{v: int | lo <= v <= hi}``.

    Usage::

        BoundedInt(0, 255)         → {v: int | 0 <= v <= 255}
        BoundedInt(0.0, 1.0, float) → {v: float | 0.0 <= v <= 1.0}
    """
    base_type = _resolve_type(base) if base is not None else Int
    lo_pred = ComparisonPred("v", ComparisonOp.GE, str(lo))
    hi_pred = ComparisonPred("v", ComparisonOp.LE, str(hi))
    combined = ConjunctionPred((lo_pred, hi_pred))
    return RefinementType(base_type, "v", combined)


def Sized(size_pred: _SugarPred, element_type: Any = None) -> RefinementType:
    """Collection with a size constraint.

    Usage::

        Sized(Var("v") > 0)                  → non-empty collection
        Sized(Eq(Len(Var("v")), Var("n")))   → collection of length n
    """
    from deppy.types.base import ListType
    if element_type is not None:
        base = ListType(_resolve_type(element_type))
    else:
        base = _SimpleType("Sequence")
    real_pred = to_predicate(size_pred) if isinstance(size_pred, _SugarPred) else size_pred
    return RefinementType(base, "v", real_pred)


class _NonEmptyOfMeta:
    """``NonEmptyOf[List[int]]`` — a non-empty collection type.

    Usage::

        NonEmptyOf[List[int]]    → {v: List[int] | len(v) > 0}
        NonEmptyOf[str]          → {v: str | len(v) > 0}
    """

    def __getitem__(self, base: Any) -> RefinementType:
        resolved = _resolve_type(base)
        pred = ComparisonPred("len(v)", ComparisonOp.GT, "0")
        return RefinementType(resolved, "v", pred)

    def __repr__(self) -> str:
        return "NonEmptyOf"


NonEmptyOf = _NonEmptyOfMeta()
"""Non-empty collection: ``NonEmptyOf[List[int]]``."""


class _VecMeta:
    """Length-indexed vector: ``Vec[int, "n"]`` → ``{v: List[int] | len(v) == n}``.

    Usage::

        Vec[int, 3]            → {v: List[int] | len(v) == 3}
        Vec[int, "n"]          → {v: List[int] | len(v) == n}  (dependent)
        Vec[float]             → List[float]  (no length constraint)
    """

    def __getitem__(self, key: Any) -> TypeBase:
        from deppy.types.base import ListType
        if isinstance(key, tuple):
            if len(key) == 2:
                elem, length = key
                base = ListType(_resolve_type(elem))
                pred = ComparisonPred("len(v)", ComparisonOp.EQ, str(length))
                return RefinementType(base, "v", pred)
            raise TypeError("Vec requires Vec[elem_type] or Vec[elem_type, length]")
        return ListType(_resolve_type(key))

    def __repr__(self) -> str:
        return "Vec"


Vec = _VecMeta()
"""Length-indexed vector: ``Vec[int, 3]``."""


class _TensorMeta:
    """Shaped tensor: ``Tensor[float32, (3, 4)]`` or ``Tensor[float32, "n", "m"]``.

    Usage::

        Tensor[float, 3, 4]              → Tensor(float, shape=(3,4))
        Tensor[float, "batch", "hidden"] → dependent shape tensor
    """

    def __getitem__(self, key: Any) -> RefinementType:
        if not isinstance(key, tuple) or len(key) < 2:
            raise TypeError("Tensor requires Tensor[dtype, dim1, dim2, ...]")

        dtype = key[0]
        dims = key[1:]

        base = _SimpleType("Tensor")
        shape_str = "(" + ", ".join(str(d) for d in dims) + ")"
        pred = ComparisonPred("shape(v)", ComparisonOp.EQ, shape_str)
        return RefinementType(base, "v", pred)

    def __repr__(self) -> str:
        return "Tensor"


Tensor = _TensorMeta()
"""Shaped tensor: ``Tensor[float, 3, 4]``."""


class _OptMeta:
    """Nullable type shorthand: ``Opt[int]`` = ``Optional[int]``.

    Carries a nullability qualifier for the sheaf system.
    """

    def __getitem__(self, base: Any) -> QualifiedType:
        resolved = _resolve_type(base)
        return QualifiedType(resolved, (NonNull(),))

    def __repr__(self) -> str:
        return "Opt"


Opt = _OptMeta()
"""Optional/nullable: ``Opt[int]``."""


# ═══════════════════════════════════════════════════════════════════════════════
# Type resolution
# ═══════════════════════════════════════════════════════════════════════════════


_PYTHON_TYPE_MAP: Dict[Any, TypeBase] = {
    int: Int,
    float: Float,
    str: Str,
    bool: Bool,
    type(None): NoneType,
    bytes: Bytes,
}


def _resolve_type(t: Any) -> TypeBase:
    """Resolve a Python type or sugar type to a :class:`TypeBase`."""
    if isinstance(t, TypeBase):
        return t
    if t in _PYTHON_TYPE_MAP:
        return _PYTHON_TYPE_MAP[t]
    if isinstance(t, type):
        return _SimpleType(t.__name__)
    if isinstance(t, str):
        # String types become type variables (forward references)
        return _SimpleType(t)
    return _SimpleType(repr(t))


# ═══════════════════════════════════════════════════════════════════════════════
# Decorator sugar
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class FunctionSpec:
    """Specification extracted from a decorated function's annotations.

    Attributes:
        name: Function name.
        params: List of (name, type) pairs.
        return_type: Return type (resolved).
        predicates: Extracted predicates from refinement types.
        is_dependent: Whether any parameter type mentions another parameter.
    """

    _name: str
    _params: Tuple[Tuple[str, TypeBase], ...]
    _return_type: TypeBase
    _predicates: Tuple[_SugarPred, ...]
    _is_dependent: bool

    @property
    def name(self) -> str:
        return self._name

    @property
    def params(self) -> Tuple[Tuple[str, TypeBase], ...]:
        return self._params

    @property
    def return_type(self) -> TypeBase:
        return self._return_type

    @property
    def predicates(self) -> Tuple[_SugarPred, ...]:
        return self._predicates

    @property
    def is_dependent(self) -> bool:
        return self._is_dependent

    def to_pi_type(self) -> TypeBase:
        """Convert this spec to a Pi type."""
        if len(self._params) == 0:
            return self._return_type
        if len(self._params) == 1:
            name, ty = self._params[0]
            return PiType(name, ty, self._return_type)
        return MultiPiType(self._params, self._return_type)

    def __repr__(self) -> str:
        params = ", ".join(f"{n}: {t!r}" for n, t in self._params)
        return f"FunctionSpec({self._name}({params}) -> {self._return_type!r})"


def extract_spec(func: Callable[..., Any]) -> FunctionSpec:
    """Extract a :class:`FunctionSpec` from a function's type annotations.

    Resolves Python annotations to deppy types, detects refinement types
    and dependent parameters.

    Usage::

        def foo(x: int, y: int) -> int: ...
        spec = extract_spec(foo)
        # spec.params == (("x", Int), ("y", Int))
        # spec.return_type == Int
    """
    sig = inspect.signature(func)
    hints = {}
    try:
        hints = func.__annotations__
    except AttributeError:
        pass

    params: TypingList[Tuple[str, TypeBase]] = []
    predicates: TypingList[_SugarPred] = []

    for name, param in sig.parameters.items():
        if name == "self" or name == "cls":
            continue
        ann = hints.get(name)
        if ann is None:
            params.append((name, ANY_TYPE))
        elif isinstance(ann, RefinementType):
            params.append((name, ann))
        elif isinstance(ann, _SugarPred):
            # If the annotation is a predicate, wrap the param in a refinement
            params.append((name, Ref[Any, ann]))
            predicates.append(ann)
        else:
            params.append((name, _resolve_type(ann)))

    ret_ann = hints.get("return")
    return_type = _resolve_type(ret_ann) if ret_ann is not None else ANY_TYPE

    # Check dependence
    param_names = {n for n, _ in params}
    is_dep = False
    for _, ty in params:
        if ty.free_variables() & param_names:
            is_dep = True
            break
    if return_type.free_variables() & param_names:
        is_dep = True

    return FunctionSpec(
        _name=func.__name__,
        _params=tuple(params),
        _return_type=return_type,
        _predicates=tuple(predicates),
        _is_dependent=is_dep,
    )


def fn(func: Callable[..., T]) -> Callable[..., T]:
    """Decorator that extracts a dependent type spec from annotations.

    The spec is attached as ``func.__deppy_spec__``.

    Usage::

        @fn
        def head(xs: NonEmptyOf[list]) -> int:
            return xs[0]

        head.__deppy_spec__.params   # (("xs", {v: list | len(v) > 0}),)
    """
    spec = extract_spec(func)
    func.__deppy_spec__ = spec  # type: ignore[attr-defined]
    return func


def checked(func: Callable[..., T]) -> Callable[..., T]:
    """Decorator that extracts spec AND wraps with runtime checks.

    Usage::

        @checked
        def divide(a: int, b: Ref[int, v != 0]) -> float:
            return a / b

        divide(10, 0)  # raises ContractViolation
    """
    spec = extract_spec(func)
    func.__deppy_spec__ = spec  # type: ignore[attr-defined]

    @functools.wraps(func)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        # Bind arguments
        sig = inspect.signature(func)
        bound = sig.bind(*args, **kwargs)
        bound.apply_defaults()

        # Check refinement predicates on params
        for (param_name, param_type), (_, arg_val) in zip(
            spec.params, bound.arguments.items()
        ):
            if isinstance(param_type, RefinementType):
                _runtime_check_refinement(param_name, arg_val, param_type)

        result = func(*args, **kwargs)

        # Check return type refinements
        if isinstance(spec.return_type, RefinementType):
            _runtime_check_refinement("__return__", result, spec.return_type)

        return result

    wrapper.__deppy_spec__ = spec  # type: ignore[attr-defined]
    return wrapper  # type: ignore[return-value]


class ContractViolation(Exception):
    """Raised when a runtime refinement check fails."""

    def __init__(self, param: str, value: Any, refinement: RefinementType) -> None:
        self.param = param
        self.value = value
        self.refinement = refinement
        super().__init__(
            f"Contract violation: {param}={value!r} does not satisfy {refinement!r}"
        )


def _runtime_check_refinement(
    name: str, value: Any, rtype: RefinementType
) -> None:
    """Best-effort runtime check of a refinement predicate."""
    pred = rtype.predicate
    if isinstance(pred, ComparisonPred):
        _check_comparison(name, value, pred, rtype)
    elif isinstance(pred, ConjunctionPred):
        _check_conjunction(name, value, pred, rtype)


def _check_comparison(
    name: str, value: Any, pred: ComparisonPred, rtype: RefinementType
) -> None:
    """Runtime check for comparison predicates."""
    lhs_val = _eval_term(pred.lhs, rtype.binder, value)
    rhs_val = _eval_term(pred.rhs, rtype.binder, value)

    if lhs_val is None or rhs_val is None:
        return  # Cannot evaluate, skip

    op_checks = {
        ComparisonOp.GT: lambda a, b: a > b,
        ComparisonOp.GE: lambda a, b: a >= b,
        ComparisonOp.LT: lambda a, b: a < b,
        ComparisonOp.LE: lambda a, b: a <= b,
        ComparisonOp.EQ: lambda a, b: a == b,
        ComparisonOp.NE: lambda a, b: a != b,
    }

    check = op_checks.get(pred.op)
    if check is not None:
        try:
            if not check(lhs_val, rhs_val):
                raise ContractViolation(name, value, rtype)
        except TypeError:
            pass  # Incomparable types, skip


def _check_conjunction(
    name: str, value: Any, pred: ConjunctionPred, rtype: RefinementType
) -> None:
    """Runtime check for conjunction predicates (AND)."""
    for sub in pred.conjuncts:
        if isinstance(sub, ComparisonPred):
            _check_comparison(name, value, sub, rtype)
        elif isinstance(sub, ConjunctionPred):
            _check_conjunction(name, value, sub, rtype)


def _eval_term(term_str: Any, binder: str, value: Any) -> Any:
    """Evaluate a term string against a bound value."""
    if not isinstance(term_str, str):
        return term_str
    if term_str == binder:
        return value
    if term_str == f"len({binder})":
        try:
            return len(value)
        except TypeError:
            return None
    try:
        return int(term_str)
    except ValueError:
        pass
    try:
        return float(term_str)
    except ValueError:
        pass
    return None


# ═══════════════════════════════════════════════════════════════════════════════
# Pretty-printing
# ═══════════════════════════════════════════════════════════════════════════════


def pretty(ty: TypeBase) -> str:
    """Render a type in concise Pythonic notation.

    Usage::

        pretty(PiType("n", Nat, Vec[int, "n"]))
        # → "(n: Nat) -> Vec[int, n]"
    """
    if isinstance(ty, PiType):
        param = f"{ty.param_name}: {pretty(ty.param_type)}"
        ret = pretty(ty.return_type)
        return f"({param}) -> {ret}"

    if isinstance(ty, MultiPiType):
        params = ", ".join(f"{n}: {pretty(t)}" for n, t in ty.params)
        ret = pretty(ty.return_type)
        return f"({params}) -> {ret}"

    if isinstance(ty, SigmaType):
        fst = f"{ty.fst_name}: {pretty(ty.fst_type)}"
        snd = pretty(ty.snd_type)
        if ty.fst_name == "_fst":
            return f"{pretty(ty.fst_type)} × {snd}"
        return f"({fst}, {snd})"

    if isinstance(ty, RefinementType):
        base = pretty(ty.base)
        pred_str = str(ty.predicate)
        return f"{{{ty.binder}: {base} | {pred_str}}}"

    if isinstance(ty, QualifiedType):
        base = pretty(ty.base)
        quals = ", ".join(q.name() for q in ty.qualifiers)
        return f"{base}[{quals}]"

    if isinstance(ty, ForallType):
        return f"∀{ty.var_name}. {pretty(ty.body)}"

    if isinstance(ty, ExistsType):
        return f"∃{ty.var_name}. {pretty(ty.body)}"

    if isinstance(ty, IdentityType):
        return f"Id({pretty(ty.base_type)}, {ty.lhs!r}, {ty.rhs!r})"

    if isinstance(ty, _ParametricType):
        args = ", ".join(pretty(a) for a in ty.args)
        return f"{ty.base}[{args}]"

    if isinstance(ty, _SimpleType):
        return ty.name

    return repr(ty)
