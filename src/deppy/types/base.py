"""Base type hierarchy for DepPy's sheaf-descent semantic typing system.

This module defines the fundamental type representations used throughout DepPy.
Types are modeled as carriers for local sections in a sheaf-descent framework,
providing a rich type language that covers Python's type system and extends it
with refinement, dependent, and indexed types.
"""
from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Dict,
    FrozenSet,
    Iterator,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Abstract root
# ═══════════════════════════════════════════════════════════════════════════════


class TypeBase(ABC):
    """Abstract root of the DepPy type hierarchy.

    Every type in the system inherits from TypeBase and must implement:
    - substitute: Apply a type-variable substitution mapping.
    - free_variables: Return the set of free type-variable names.
    - contains: Check if another type appears as a sub-expression.
    - walk: Recursive pre-order traversal yielding all sub-types.
    """

    @abstractmethod
    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        """Apply *mapping* from variable names to types, returning a new type."""
        ...

    @abstractmethod
    def free_variables(self) -> FrozenSet[str]:
        """Return names of all free type variables occurring in this type."""
        ...

    def contains(self, other: TypeBase) -> bool:
        """Return ``True`` if *other* appears anywhere inside this type."""
        for t in self.walk():
            if t == other:
                return True
        return False

    def walk(self) -> Iterator[TypeBase]:
        """Yield this type and every sub-type in pre-order."""
        yield self

    @abstractmethod
    def __eq__(self, other: object) -> bool: ...

    @abstractmethod
    def __hash__(self) -> int: ...

    @abstractmethod
    def __repr__(self) -> str: ...

    def is_ground(self) -> bool:
        """``True`` when the type contains no free type variables."""
        return len(self.free_variables()) == 0


# ═══════════════════════════════════════════════════════════════════════════════
# Primitive types
# ═══════════════════════════════════════════════════════════════════════════════


class PrimitiveKind(Enum):
    """Enumeration of Python's built-in primitive types."""

    INT = "int"
    FLOAT = "float"
    STR = "str"
    BOOL = "bool"
    BYTES = "bytes"
    NONE = "NoneType"
    COMPLEX = "complex"


@dataclass(frozen=True)
class PrimitiveType(TypeBase):
    """A primitive Python type: int, float, str, bool, bytes, NoneType, complex."""

    kind: PrimitiveKind

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        return self

    def free_variables(self) -> FrozenSet[str]:
        return frozenset()

    def __repr__(self) -> str:
        return self.kind.value


# Singleton instances for common usage
INT_TYPE = PrimitiveType(PrimitiveKind.INT)
FLOAT_TYPE = PrimitiveType(PrimitiveKind.FLOAT)
STR_TYPE = PrimitiveType(PrimitiveKind.STR)
BOOL_TYPE = PrimitiveType(PrimitiveKind.BOOL)
BYTES_TYPE = PrimitiveType(PrimitiveKind.BYTES)
NONE_TYPE = PrimitiveType(PrimitiveKind.NONE)
COMPLEX_TYPE = PrimitiveType(PrimitiveKind.COMPLEX)


# ═══════════════════════════════════════════════════════════════════════════════
# Top and bottom types
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class AnyType(TypeBase):
    """Top type — every type is a subtype of ``Any``."""

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        return self

    def free_variables(self) -> FrozenSet[str]:
        return frozenset()

    def __repr__(self) -> str:
        return "Any"


ANY_TYPE = AnyType()


@dataclass(frozen=True)
class NeverType(TypeBase):
    """Bottom type — subtype of every type.  Represents unreachable code."""

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        return self

    def free_variables(self) -> FrozenSet[str]:
        return frozenset()

    def __repr__(self) -> str:
        return "Never"


NEVER_TYPE = NeverType()


# ═══════════════════════════════════════════════════════════════════════════════
# Container types
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ListType(TypeBase):
    """Homogeneous list type ``List[element]``."""

    element: TypeBase

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_elem = self.element.substitute(mapping)
        if new_elem is self.element:
            return self
        return ListType(new_elem)

    def free_variables(self) -> FrozenSet[str]:
        return self.element.free_variables()

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.element.walk()

    def __repr__(self) -> str:
        return f"List[{self.element!r}]"


@dataclass(frozen=True)
class DictType(TypeBase):
    """Dictionary type ``Dict[key, value]``."""

    key: TypeBase
    value: TypeBase

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_k = self.key.substitute(mapping)
        new_v = self.value.substitute(mapping)
        if new_k is self.key and new_v is self.value:
            return self
        return DictType(new_k, new_v)

    def free_variables(self) -> FrozenSet[str]:
        return self.key.free_variables() | self.value.free_variables()

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.key.walk()
        yield from self.value.walk()

    def __repr__(self) -> str:
        return f"Dict[{self.key!r}, {self.value!r}]"


@dataclass(frozen=True)
class TupleType(TypeBase):
    """Tuple type.

    When *variadic* is ``False`` (default): fixed-length ``Tuple[T1, T2, ...]``.
    When *variadic* is ``True``: homogeneous ``Tuple[T, ...]`` with a single element type.
    """

    elements: Tuple[TypeBase, ...]
    variadic: bool = False

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_elems = tuple(e.substitute(mapping) for e in self.elements)
        if all(n is o for n, o in zip(new_elems, self.elements)):
            return self
        return TupleType(new_elems, self.variadic)

    def free_variables(self) -> FrozenSet[str]:
        result: set[str] = set()
        for e in self.elements:
            result |= e.free_variables()
        return frozenset(result)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        for e in self.elements:
            yield from e.walk()

    def __repr__(self) -> str:
        if self.variadic and len(self.elements) == 1:
            return f"Tuple[{self.elements[0]!r}, ...]"
        inner = ", ".join(repr(e) for e in self.elements)
        return f"Tuple[{inner}]"


@dataclass(frozen=True)
class SetType(TypeBase):
    """Set type ``Set[element]``."""

    element: TypeBase

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_elem = self.element.substitute(mapping)
        if new_elem is self.element:
            return self
        return SetType(new_elem)

    def free_variables(self) -> FrozenSet[str]:
        return self.element.free_variables()

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.element.walk()

    def __repr__(self) -> str:
        return f"Set[{self.element!r}]"


@dataclass(frozen=True)
class FrozenSetType(TypeBase):
    """FrozenSet type ``FrozenSet[element]``."""

    element: TypeBase

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_elem = self.element.substitute(mapping)
        if new_elem is self.element:
            return self
        return FrozenSetType(new_elem)

    def free_variables(self) -> FrozenSet[str]:
        return self.element.free_variables()

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.element.walk()

    def __repr__(self) -> str:
        return f"FrozenSet[{self.element!r}]"


# ═══════════════════════════════════════════════════════════════════════════════
# Optional and Union types
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class OptionalType(TypeBase):
    """Optional type ``Optional[inner]`` ≡ ``Union[inner, None]``."""

    inner: TypeBase

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_inner = self.inner.substitute(mapping)
        if new_inner is self.inner:
            return self
        return OptionalType(new_inner)

    def free_variables(self) -> FrozenSet[str]:
        return self.inner.free_variables()

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.inner.walk()

    def to_union(self) -> UnionType:
        """Convert to canonical ``Union[inner, NoneType]`` form."""
        return UnionType((self.inner, NONE_TYPE))

    def __repr__(self) -> str:
        return f"Optional[{self.inner!r}]"


def _flatten_union(types: Sequence[TypeBase]) -> Tuple[TypeBase, ...]:
    """Flatten nested unions and deduplicate while preserving insertion order."""
    seen: set[TypeBase] = set()
    result: list[TypeBase] = []

    def _collect(t: TypeBase) -> None:
        if isinstance(t, UnionType):
            for m in t.members:
                _collect(m)
        elif isinstance(t, OptionalType):
            _collect(t.inner)
            _collect(NONE_TYPE)
        else:
            if t not in seen:
                seen.add(t)
                result.append(t)

    for t in types:
        _collect(t)
    return tuple(result)


@dataclass(frozen=True, eq=False)
class UnionType(TypeBase):
    """Union type ``Union[T1, T2, ...]``.

    Members are stored in a canonical flattened, deduplicated form.
    Equality is order-independent (set semantics).
    """

    members: Tuple[TypeBase, ...]

    def __post_init__(self) -> None:
        canonical = _flatten_union(self.members)
        object.__setattr__(self, "members", canonical)

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_members = tuple(m.substitute(mapping) for m in self.members)
        if all(n is o for n, o in zip(new_members, self.members)):
            return self
        return UnionType(new_members)

    def free_variables(self) -> FrozenSet[str]:
        result: set[str] = set()
        for m in self.members:
            result |= m.free_variables()
        return frozenset(result)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        for m in self.members:
            yield from m.walk()

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, UnionType):
            return NotImplemented
        return frozenset(self.members) == frozenset(other.members)

    def __hash__(self) -> int:
        return hash(("Union", frozenset(self.members)))

    def __repr__(self) -> str:
        inner = ", ".join(repr(m) for m in self.members)
        return f"Union[{inner}]"

    @staticmethod
    def build(types: Sequence[TypeBase]) -> TypeBase:
        """Build a union, simplifying singleton / empty / Any cases."""
        flat = _flatten_union(types)
        if len(flat) == 0:
            return NEVER_TYPE
        if len(flat) == 1:
            return flat[0]
        if any(isinstance(t, AnyType) for t in flat):
            return ANY_TYPE
        return UnionType(flat)


# ═══════════════════════════════════════════════════════════════════════════════
# Intersection type
# ═══════════════════════════════════════════════════════════════════════════════


def _flatten_intersection(types: Sequence[TypeBase]) -> Tuple[TypeBase, ...]:
    """Flatten nested intersections and deduplicate."""
    seen: set[TypeBase] = set()
    result: list[TypeBase] = []

    def _collect(t: TypeBase) -> None:
        if isinstance(t, IntersectionType):
            for m in t.members:
                _collect(m)
        else:
            if t not in seen:
                seen.add(t)
                result.append(t)

    for t in types:
        _collect(t)
    return tuple(result)


@dataclass(frozen=True, eq=False)
class IntersectionType(TypeBase):
    """Intersection type ``T1 & T2 & ...``.

    Equality is order-independent.
    """

    members: Tuple[TypeBase, ...]

    def __post_init__(self) -> None:
        canonical = _flatten_intersection(self.members)
        object.__setattr__(self, "members", canonical)

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_members = tuple(m.substitute(mapping) for m in self.members)
        if all(n is o for n, o in zip(new_members, self.members)):
            return self
        return IntersectionType(new_members)

    def free_variables(self) -> FrozenSet[str]:
        result: set[str] = set()
        for m in self.members:
            result |= m.free_variables()
        return frozenset(result)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        for m in self.members:
            yield from m.walk()

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, IntersectionType):
            return NotImplemented
        return frozenset(self.members) == frozenset(other.members)

    def __hash__(self) -> int:
        return hash(("Intersection", frozenset(self.members)))

    def __repr__(self) -> str:
        inner = " & ".join(repr(m) for m in self.members)
        return f"({inner})"

    @staticmethod
    def build(types: Sequence[TypeBase]) -> TypeBase:
        """Build an intersection, simplifying edge cases."""
        flat = _flatten_intersection(types)
        if len(flat) == 0:
            return ANY_TYPE
        if len(flat) == 1:
            return flat[0]
        if any(isinstance(t, NeverType) for t in flat):
            return NEVER_TYPE
        return IntersectionType(tuple(flat))


# ═══════════════════════════════════════════════════════════════════════════════
# Callable type
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class CallableType(TypeBase):
    """Callable type ``Callable[[A1, ...], R]``.

    Supports positional parameters with optional names and async callables.
    """

    param_types: Tuple[TypeBase, ...]
    return_type: TypeBase
    param_names: Tuple[str, ...] = ()
    is_async: bool = False

    def __post_init__(self) -> None:
        if self.param_names and len(self.param_names) != len(self.param_types):
            raise ValueError(
                f"param_names length ({len(self.param_names)}) must match "
                f"param_types length ({len(self.param_types)})"
            )

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_params = tuple(p.substitute(mapping) for p in self.param_types)
        new_ret = self.return_type.substitute(mapping)
        if (
            all(n is o for n, o in zip(new_params, self.param_types))
            and new_ret is self.return_type
        ):
            return self
        return CallableType(new_params, new_ret, self.param_names, self.is_async)

    def free_variables(self) -> FrozenSet[str]:
        result: set[str] = set()
        for p in self.param_types:
            result |= p.free_variables()
        result |= self.return_type.free_variables()
        return frozenset(result)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        for p in self.param_types:
            yield from p.walk()
        yield from self.return_type.walk()

    def __repr__(self) -> str:
        prefix = "async " if self.is_async else ""
        params = ", ".join(repr(p) for p in self.param_types)
        return f"{prefix}Callable[[{params}], {self.return_type!r}]"

    @property
    def arity(self) -> int:
        """Number of positional parameters."""
        return len(self.param_types)


# ═══════════════════════════════════════════════════════════════════════════════
# Class, Protocol, and Module types
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ClassType(TypeBase):
    """A user-defined class type.

    Stores the fully-qualified class name, type arguments (for generics),
    and references to base classes.
    """

    name: str
    module: str = ""
    type_args: Tuple[TypeBase, ...] = ()
    bases: Tuple[TypeBase, ...] = ()

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_args = tuple(a.substitute(mapping) for a in self.type_args)
        new_bases = tuple(b.substitute(mapping) for b in self.bases)
        if all(n is o for n, o in zip(new_args, self.type_args)) and all(
            n is o for n, o in zip(new_bases, self.bases)
        ):
            return self
        return ClassType(self.name, self.module, new_args, new_bases)

    def free_variables(self) -> FrozenSet[str]:
        result: set[str] = set()
        for a in self.type_args:
            result |= a.free_variables()
        for b in self.bases:
            result |= b.free_variables()
        return frozenset(result)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        for a in self.type_args:
            yield from a.walk()
        for b in self.bases:
            yield from b.walk()

    @property
    def qualified_name(self) -> str:
        """Fully-qualified class name."""
        if self.module:
            return f"{self.module}.{self.name}"
        return self.name

    def __repr__(self) -> str:
        if self.type_args:
            args = ", ".join(repr(a) for a in self.type_args)
            return f"{self.qualified_name}[{args}]"
        return self.qualified_name


class ProtocolMember:
    """A single member (method or attribute) required by a protocol."""

    __slots__ = ("name", "type", "is_method", "is_property")

    def __init__(
        self,
        name: str,
        type: TypeBase,
        *,
        is_method: bool = False,
        is_property: bool = False,
    ) -> None:
        self.name = name
        self.type = type
        self.is_method = is_method
        self.is_property = is_property

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ProtocolMember):
            return NotImplemented
        return (
            self.name == other.name
            and self.type == other.type
            and self.is_method == other.is_method
            and self.is_property == other.is_property
        )

    def __hash__(self) -> int:
        return hash((self.name, self.type, self.is_method, self.is_property))

    def __repr__(self) -> str:
        kind = (
            "method"
            if self.is_method
            else ("property" if self.is_property else "attr")
        )
        return f"ProtocolMember({self.name}: {self.type!r}, {kind})"


@dataclass(frozen=True)
class ProtocolType(TypeBase):
    """Structural protocol type.

    Defines required members (methods and attributes) that a type must
    implement to satisfy the protocol.
    """

    name: str
    members: Tuple[ProtocolMember, ...]
    is_runtime_checkable: bool = False

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_members = tuple(
            ProtocolMember(
                m.name,
                m.type.substitute(mapping),
                is_method=m.is_method,
                is_property=m.is_property,
            )
            for m in self.members
        )
        if all(n.type is o.type for n, o in zip(new_members, self.members)):
            return self
        return ProtocolType(self.name, new_members, self.is_runtime_checkable)

    def free_variables(self) -> FrozenSet[str]:
        result: set[str] = set()
        for m in self.members:
            result |= m.type.free_variables()
        return frozenset(result)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        for m in self.members:
            yield from m.type.walk()

    def member_dict(self) -> Dict[str, ProtocolMember]:
        """Return members indexed by name."""
        return {m.name: m for m in self.members}

    def __repr__(self) -> str:
        members_str = ", ".join(f"{m.name}: {m.type!r}" for m in self.members)
        return f"Protocol[{self.name}({members_str})]"


@dataclass(frozen=True)
class ModuleType(TypeBase):
    """Type representing a Python module."""

    module_name: str
    exports: Tuple[Tuple[str, TypeBase], ...] = ()

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_exports = tuple(
            (name, t.substitute(mapping)) for name, t in self.exports
        )
        if all(n[1] is o[1] for n, o in zip(new_exports, self.exports)):
            return self
        return ModuleType(self.module_name, new_exports)

    def free_variables(self) -> FrozenSet[str]:
        result: set[str] = set()
        for _, t in self.exports:
            result |= t.free_variables()
        return frozenset(result)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        for _, t in self.exports:
            yield from t.walk()

    def get_export(self, name: str) -> Optional[TypeBase]:
        """Look up a module export by name."""
        for n, t in self.exports:
            if n == name:
                return t
        return None

    def __repr__(self) -> str:
        return f"Module[{self.module_name}]"


# ═══════════════════════════════════════════════════════════════════════════════
# Literal, TypeAlias, and Tensor types
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True, eq=False)
class LiteralType(TypeBase):
    """Literal type ``Literal[v1, v2, ...]``.

    Values must be ``int``, ``str``, ``bool``, ``bytes``, or ``None``.
    """

    values: Tuple[Union[int, str, bool, bytes, None], ...]

    _ALLOWED: Tuple[type, ...] = field(
        default=(int, str, bool, bytes, type(None)),
        init=False,
        repr=False,
        compare=False,
        hash=False,
    )

    def __post_init__(self) -> None:
        for v in self.values:
            if not isinstance(v, self._ALLOWED):
                raise TypeError(
                    f"Literal values must be int, str, bool, bytes, or None; "
                    f"got {type(v).__name__}"
                )

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        return self

    def free_variables(self) -> FrozenSet[str]:
        return frozenset()

    def inferred_base_type(self) -> TypeBase:
        """Infer the widest primitive type covering all literal values."""
        types_present: set[type] = {type(v) for v in self.values}
        if types_present == {bool}:
            return BOOL_TYPE
        if types_present <= {int, bool}:
            return INT_TYPE
        if types_present == {str}:
            return STR_TYPE
        if types_present == {bytes}:
            return BYTES_TYPE
        if types_present == {type(None)}:
            return NONE_TYPE
        type_map: dict[type, PrimitiveKind] = {
            int: PrimitiveKind.INT,
            bool: PrimitiveKind.BOOL,
            str: PrimitiveKind.STR,
            bytes: PrimitiveKind.BYTES,
            type(None): PrimitiveKind.NONE,
        }
        seen: set[PrimitiveKind] = set()
        bases: list[TypeBase] = []
        for v in self.values:
            kind = type_map.get(type(v))
            if kind is not None and kind not in seen:
                seen.add(kind)
                bases.append(PrimitiveType(kind))
        return UnionType.build(bases)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, LiteralType):
            return NotImplemented
        return frozenset(self.values) == frozenset(other.values)

    def __hash__(self) -> int:
        return hash(("Literal", frozenset(self.values)))

    def __repr__(self) -> str:
        vals = ", ".join(repr(v) for v in self.values)
        return f"Literal[{vals}]"


@dataclass(frozen=True)
class TypeAliasType(TypeBase):
    """A named type alias wrapping an underlying type."""

    name: str
    underlying: TypeBase
    type_params: Tuple[str, ...] = ()

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_underlying = self.underlying.substitute(mapping)
        if new_underlying is self.underlying:
            return self
        return TypeAliasType(self.name, new_underlying, self.type_params)

    def free_variables(self) -> FrozenSet[str]:
        return self.underlying.free_variables() - frozenset(self.type_params)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.underlying.walk()

    def resolve(self) -> TypeBase:
        """Unwrap the alias chain to the innermost non-alias type."""
        t = self.underlying
        while isinstance(t, TypeAliasType):
            t = t.underlying
        return t

    def __repr__(self) -> str:
        if self.type_params:
            params = ", ".join(self.type_params)
            return f"TypeAlias[{self.name}[{params}] = {self.underlying!r}]"
        return f"TypeAlias[{self.name} = {self.underlying!r}]"


@dataclass(frozen=True)
class TensorType(TypeBase):
    """Tensor type with optional shape, dtype, and device annotations.

    Designed for ``torch.Tensor`` / ``numpy.ndarray`` compatibility.
    Shape dimensions may be concrete ``int`` or symbolic ``str`` names.
    """

    shape: Optional[Tuple[Union[int, str], ...]] = None
    dtype: Optional[str] = None
    device: Optional[str] = None
    framework: str = "torch"

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        if self.shape is None:
            return self
        new_shape: list[Union[int, str]] = []
        changed = False
        for dim in self.shape:
            if isinstance(dim, str) and dim in mapping:
                target = mapping[dim]
                if isinstance(target, LiteralType) and len(target.values) == 1:
                    val = target.values[0]
                    if isinstance(val, int):
                        new_shape.append(val)
                        changed = True
                        continue
                new_shape.append(dim)
            else:
                new_shape.append(dim)
        if not changed:
            return self
        return TensorType(tuple(new_shape), self.dtype, self.device, self.framework)

    def free_variables(self) -> FrozenSet[str]:
        if self.shape is None:
            return frozenset()
        return frozenset(d for d in self.shape if isinstance(d, str))

    def __repr__(self) -> str:
        parts: list[str] = [f"{self.framework}.Tensor"]
        annotations: list[str] = []
        if self.shape is not None:
            annotations.append(f"shape={self.shape}")
        if self.dtype is not None:
            annotations.append(f"dtype={self.dtype}")
        if self.device is not None:
            annotations.append(f"device={self.device}")
        if annotations:
            parts.append("[" + ", ".join(annotations) + "]")
        return "".join(parts)

    @property
    def ndim(self) -> Optional[int]:
        """Number of dimensions, if shape is known."""
        return len(self.shape) if self.shape is not None else None


# ═══════════════════════════════════════════════════════════════════════════════
# Utility functions
# ═══════════════════════════════════════════════════════════════════════════════

_NUMERIC_ORDER: Dict[PrimitiveKind, int] = {
    PrimitiveKind.BOOL: 0,
    PrimitiveKind.INT: 1,
    PrimitiveKind.FLOAT: 2,
    PrimitiveKind.COMPLEX: 3,
}


def type_from_python(py_type: type) -> TypeBase:
    """Convert a Python runtime type to a :class:`TypeBase` representation."""
    _type_map: dict[type, TypeBase] = {
        int: INT_TYPE,
        float: FLOAT_TYPE,
        str: STR_TYPE,
        bool: BOOL_TYPE,
        bytes: BYTES_TYPE,
        complex: COMPLEX_TYPE,
        type(None): NONE_TYPE,
    }
    result = _type_map.get(py_type)
    if result is not None:
        return result
    return ClassType(py_type.__name__, getattr(py_type, "__module__", ""))


def type_join(a: TypeBase, b: TypeBase) -> TypeBase:
    """Compute the join (least upper bound) of two types.

    This is a best-effort structural join used during type inference.
    """
    if a == b:
        return a
    if isinstance(a, NeverType):
        return b
    if isinstance(b, NeverType):
        return a
    if isinstance(a, AnyType) or isinstance(b, AnyType):
        return ANY_TYPE
    # Numeric widening: bool < int < float < complex
    if isinstance(a, PrimitiveType) and isinstance(b, PrimitiveType):
        oa = _NUMERIC_ORDER.get(a.kind)
        ob = _NUMERIC_ORDER.get(b.kind)
        if oa is not None and ob is not None:
            return a if oa >= ob else b
    # Covariant container join
    if isinstance(a, ListType) and isinstance(b, ListType):
        return ListType(type_join(a.element, b.element))
    if isinstance(a, SetType) and isinstance(b, SetType):
        return SetType(type_join(a.element, b.element))
    if isinstance(a, FrozenSetType) and isinstance(b, FrozenSetType):
        return FrozenSetType(type_join(a.element, b.element))
    if isinstance(a, DictType) and isinstance(b, DictType):
        return DictType(type_join(a.key, b.key), type_join(a.value, b.value))
    if isinstance(a, OptionalType) and isinstance(b, OptionalType):
        return OptionalType(type_join(a.inner, b.inner))
    if isinstance(a, OptionalType):
        return OptionalType(type_join(a.inner, b))
    if isinstance(b, OptionalType):
        return OptionalType(type_join(a, b.inner))
    # Fallback: form a union
    return UnionType.build([a, b])


def type_meet(a: TypeBase, b: TypeBase) -> TypeBase:
    """Compute the meet (greatest lower bound) of two types.

    Best-effort structural meet for type inference.
    """
    if a == b:
        return a
    if isinstance(a, AnyType):
        return b
    if isinstance(b, AnyType):
        return a
    if isinstance(a, NeverType) or isinstance(b, NeverType):
        return NEVER_TYPE
    # Numeric narrowing
    if isinstance(a, PrimitiveType) and isinstance(b, PrimitiveType):
        oa = _NUMERIC_ORDER.get(a.kind)
        ob = _NUMERIC_ORDER.get(b.kind)
        if oa is not None and ob is not None:
            return a if oa <= ob else b
    # Covariant container meet
    if isinstance(a, ListType) and isinstance(b, ListType):
        return ListType(type_meet(a.element, b.element))
    if isinstance(a, SetType) and isinstance(b, SetType):
        return SetType(type_meet(a.element, b.element))
    if isinstance(a, DictType) and isinstance(b, DictType):
        return DictType(type_meet(a.key, b.key), type_meet(a.value, b.value))
    # Fallback: intersection
    return IntersectionType.build([a, b])
