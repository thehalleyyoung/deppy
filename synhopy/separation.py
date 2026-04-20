"""
synhopy.separation — Separation logic constructs for SynHoPy.

Re-exports separation logic primitives so that
``from synhopy.separation import pts_to, emp`` works as shown in the book.
"""
from __future__ import annotations
from typing import Any, TypeVar, Generic

T = TypeVar("T")


class SLProp:
    """Base class for separation logic propositions."""
    def __and__(self, other: "SLProp") -> "SepConj":
        return SepConj(self, other)
    def __mul__(self, other: "SLProp") -> "SepConj":
        return SepConj(self, other)
    def __pow__(self, other: "SLProp") -> "SepConj":
        """p ** q — separating conjunction."""
        return SepConj(self, other)


class Emp(SLProp):
    """The trivial/empty separation logic proposition."""
    def __repr__(self): return "emp"

emp = Emp()


class Pure(SLProp):
    """A pure (heap-independent) proposition."""
    def __init__(self, prop):
        self.prop = prop
    def __repr__(self): return f"pure({self.prop})"


class PointsTo(SLProp):
    """pts_to(ref, value) — reference points to value."""
    def __init__(self, ref, value, perm: float = 1.0):
        self.ref = ref
        self.value = value
        self.perm = perm
    def __repr__(self): return f"pts_to({self.ref}, {self.value})"


def pts_to(ref, value, perm: float = 1.0) -> PointsTo:
    """Create a points-to proposition."""
    return PointsTo(ref, value, perm)


def pts_to_frac(ref, value, perm: float) -> PointsTo:
    """Create a fractional points-to proposition."""
    return PointsTo(ref, value, perm)


class AttrTo(SLProp):
    """attr_to(obj, attr, value) — object attribute points to value."""
    def __init__(self, obj, attr: str, value):
        self.obj = obj
        self.attr = attr
        self.value = value
    def __repr__(self): return f"attr_to({self.obj}, {self.attr!r}, {self.value})"


def attr_to(obj, attr: str, value) -> AttrTo:
    """Create an attribute points-to proposition."""
    return AttrTo(obj, attr, value)


class DictEntry(SLProp):
    """dict_entry(d, key, value) — dict entry points to value."""
    def __init__(self, d, key, value):
        self.d = d
        self.key = key
        self.value = value


def dict_entry(d, key, value) -> DictEntry:
    return DictEntry(d, key, value)


class ElemAt(SLProp):
    """elem_at(lst, idx, value) — list element at index."""
    def __init__(self, lst, idx: int, value):
        self.lst = lst
        self.idx = idx
        self.value = value


def elem_at(lst, idx: int, value) -> ElemAt:
    return ElemAt(lst, idx, value)


class ArrayPtsTo(SLProp):
    """array_pts_to(arr, contents) — entire array contents."""
    def __init__(self, arr, contents):
        self.arr = arr
        self.contents = contents


def array_pts_to(arr, contents) -> ArrayPtsTo:
    return ArrayPtsTo(arr, contents)


class SepConj(SLProp):
    """Separating conjunction: p ** q."""
    def __init__(self, left: SLProp, right: SLProp):
        self.left = left
        self.right = right
    def __repr__(self): return f"({self.left} ** {self.right})"


class Wand(SLProp):
    """Separating implication (magic wand): p -* q."""
    def __init__(self, pre: SLProp, post: SLProp):
        self.pre = pre
        self.post = post


def wand(pre: SLProp, post: SLProp) -> Wand:
    return Wand(pre, post)


class Exists(SLProp):
    """Existential quantification over slprops."""
    def __init__(self, var_name: str, body):
        self.var_name = var_name
        self.body = body


def exists(var_name: str, body) -> Exists:
    return Exists(var_name, body)


class Ref(Generic[T]):
    """A mutable reference cell."""
    def __init__(self, value: T):
        self._value = value
    @property
    def value(self) -> T:
        return self._value
    @value.setter
    def value(self, v: T):
        self._value = v
    def __repr__(self): return f"Ref({self._value!r})"
