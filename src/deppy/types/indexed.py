"""Indexed type families for DepPy.

Provides constructs for working with families of types parameterised by
index terms, including:

- :class:`TypeFamily` — a family of types indexed by some domain, with a
  callable fiber mapping indices to types.
- :class:`FamilyApplication` — the result of applying a type family to a
  concrete index.
- :class:`DependentRecord` — a record type where field types may depend on
  the values of earlier fields (ordered dependency).
- :class:`TypeFamilyComposition` — composition of two type families.
- :class:`ConstantFamily` — a degenerate family that ignores its index.
"""
from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterator,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from .base import TypeBase, AnyType, NeverType, ANY_TYPE, NEVER_TYPE


# ═══════════════════════════════════════════════════════════════════════════════
# Type family
# ═══════════════════════════════════════════════════════════════════════════════


class TypeFamily:
    """A family of types indexed by some domain.

    Mathematically, this is a functor ``F : D → Type`` mapping indices from
    the domain *index_domain* to DepPy types via *fiber*.

    Attributes:
        name: Human-readable family name.
        index_domain: The type of valid indices.
        fiber: A callable mapping an index value to the type at that index.
    """

    __slots__ = ("name", "index_domain", "fiber", "_cache")

    def __init__(
        self,
        name: str,
        index_domain: TypeBase,
        fiber: Callable[[Any], TypeBase],
    ) -> None:
        self.name = name
        self.index_domain = index_domain
        self.fiber = fiber
        self._cache: Dict[Any, TypeBase] = {}

    def apply(self, index: Any) -> TypeBase:
        """Evaluate the family at *index*, returning the fiber type.

        Results are cached for repeated lookups.
        """
        key = index
        try:
            key_hash = hash(index)
        except TypeError:
            # Unhashable index — compute without caching
            return self.fiber(index)
        cached = self._cache.get(key)
        if cached is not None:
            return cached
        result = self.fiber(index)
        self._cache[key] = result
        return result

    def map(self, transform: Callable[[TypeBase], TypeBase]) -> TypeFamily:
        """Return a new family with *transform* applied to each fiber."""
        original_fiber = self.fiber
        return TypeFamily(
            f"{self.name}.map",
            self.index_domain,
            lambda i: transform(original_fiber(i)),
        )

    def restrict(
        self,
        new_domain: TypeBase,
        index_map: Callable[[Any], Any],
    ) -> TypeFamily:
        """Restrict (pull back) the family along *index_map*.

        ``restrict(D', f)`` produces a family over ``D'`` with fiber
        ``i ↦ F(f(i))``.
        """
        original_fiber = self.fiber
        return TypeFamily(
            f"{self.name}.restrict",
            new_domain,
            lambda i: original_fiber(index_map(i)),
        )

    def compose(self, other: TypeFamily) -> TypeFamilyComposition:
        """Compose ``self ∘ other``: first apply *other*, then use its
        result as index into *self*."""
        return TypeFamilyComposition(outer=self, inner=other)

    def __repr__(self) -> str:
        return f"TypeFamily({self.name}, {self.index_domain!r})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, TypeFamily):
            return NotImplemented
        return self.name == other.name and self.index_domain == other.index_domain

    def __hash__(self) -> int:
        return hash((self.name, self.index_domain))


# ═══════════════════════════════════════════════════════════════════════════════
# Family application
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class FamilyApplication(TypeBase):
    """The type obtained by applying a :class:`TypeFamily` to a specific index.

    Attributes:
        family: The type family being applied.
        index: The concrete index value.
    """

    family: TypeFamily
    index: Any

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        # If the index is a type variable name that appears in the mapping,
        # recompute the family application
        if isinstance(self.index, str) and self.index in mapping:
            new_index = mapping[self.index]
            return FamilyApplication(self.family, new_index)
        return self

    def free_variables(self) -> FrozenSet[str]:
        if isinstance(self.index, str):
            return frozenset({self.index})
        if isinstance(self.index, TypeBase):
            return self.index.free_variables()
        return frozenset()

    def walk(self) -> Iterator[TypeBase]:
        yield self
        if isinstance(self.index, TypeBase):
            yield from self.index.walk()

    def evaluate(self) -> TypeBase:
        """Evaluate the family at the stored index, returning the fiber type."""
        return self.family.apply(self.index)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, FamilyApplication):
            return NotImplemented
        return self.family == other.family and self.index == other.index

    def __hash__(self) -> int:
        try:
            return hash(("FamilyApp", self.family, self.index))
        except TypeError:
            return hash(("FamilyApp", self.family, id(self.index)))

    def __repr__(self) -> str:
        return f"{self.family.name}({self.index!r})"


# ═══════════════════════════════════════════════════════════════════════════════
# Constant family
# ═══════════════════════════════════════════════════════════════════════════════


class ConstantFamily(TypeFamily):
    """A degenerate type family that returns the same type for every index.

    ``ConstantFamily("C", D, T)`` represents ``F : D → Type`` where
    ``F(i) = T`` for all ``i``.
    """

    def __init__(self, name: str, index_domain: TypeBase, constant_type: TypeBase) -> None:
        self._constant_type = constant_type
        super().__init__(name, index_domain, lambda _i: constant_type)

    @property
    def constant_type(self) -> TypeBase:
        """The fixed type returned at every index."""
        return self._constant_type

    def __repr__(self) -> str:
        return f"ConstantFamily({self.name}, {self._constant_type!r})"


# ═══════════════════════════════════════════════════════════════════════════════
# Type family composition
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class TypeFamilyComposition:
    """Composition of two type families ``outer ∘ inner``.

    Applying this composition to an index ``i`` first evaluates ``inner(i)``
    to get an intermediate value, then evaluates ``outer(intermediate)``.

    Attributes:
        outer: The outer family.
        inner: The inner family.
    """

    outer: TypeFamily
    inner: TypeFamily

    def apply(self, index: Any) -> TypeBase:
        """Evaluate the composed family at *index*."""
        intermediate = self.inner.apply(index)
        return self.outer.apply(intermediate)

    def to_family(self) -> TypeFamily:
        """Convert to a plain :class:`TypeFamily`."""
        return TypeFamily(
            f"{self.outer.name}∘{self.inner.name}",
            self.inner.index_domain,
            self.apply,
        )

    def __repr__(self) -> str:
        return f"({self.outer.name} ∘ {self.inner.name})"


# ═══════════════════════════════════════════════════════════════════════════════
# Dependent record
# ═══════════════════════════════════════════════════════════════════════════════


class DependentRecord:
    """A record where later field types may depend on earlier field values.

    This is a value-level construct (compared to :class:`DependentRecordType`
    in ``dependent.py`` which is a type-level construct).  ``DependentRecord``
    carries both the field types *and* the dependency information needed
    to resolve types at instantiation time.

    Attributes:
        fields: Ordered mapping from field names to their types.
        dependencies: For each field, the list of earlier fields its type depends on.
    """

    __slots__ = ("fields", "dependencies")

    def __init__(
        self,
        fields: Optional[OrderedDict[str, TypeBase]] = None,
        dependencies: Optional[Dict[str, List[str]]] = None,
    ) -> None:
        self.fields: OrderedDict[str, TypeBase] = fields if fields is not None else OrderedDict()
        self.dependencies: Dict[str, List[str]] = dependencies if dependencies is not None else {}

    def add_field(
        self,
        name: str,
        ty: TypeBase,
        depends_on: Optional[List[str]] = None,
    ) -> None:
        """Add a field to the record.

        Args:
            name: Field name.
            ty: The field's type (may contain references to earlier field names).
            depends_on: List of earlier field names this field depends on.
        """
        if depends_on is not None:
            for dep in depends_on:
                if dep not in self.fields:
                    raise ValueError(
                        f"dependency '{dep}' for field '{name}' has not been declared yet"
                    )
        self.fields[name] = ty
        if depends_on:
            self.dependencies[name] = depends_on

    def field_type(self, name: str) -> Optional[TypeBase]:
        """Look up a field's type."""
        return self.fields.get(name)

    def field_names(self) -> List[str]:
        """Return field names in declaration order."""
        return list(self.fields.keys())

    def resolve_field(
        self,
        name: str,
        bindings: Mapping[str, TypeBase],
    ) -> TypeBase:
        """Resolve a field's type given *bindings* for its dependencies.

        Substitutes bound values into the field's type.
        """
        ty = self.fields.get(name)
        if ty is None:
            raise KeyError(f"unknown field '{name}'")
        deps = self.dependencies.get(name, [])
        if not deps:
            return ty
        mapping = {d: bindings[d] for d in deps if d in bindings}
        return ty.substitute(mapping)

    def instantiate(self, bindings: Mapping[str, TypeBase]) -> OrderedDict[str, TypeBase]:
        """Instantiate all field types given *bindings*.

        Processes fields in order, using each resolved type as a binding for
        subsequent dependent fields.
        """
        result: OrderedDict[str, TypeBase] = OrderedDict()
        running_bindings = dict(bindings)
        for name in self.fields:
            resolved = self.resolve_field(name, running_bindings)
            result[name] = resolved
            running_bindings[name] = resolved
        return result

    def to_type(self) -> TypeBase:
        """Convert to a :class:`DependentRecordType`."""
        from .dependent import DependentRecordType
        return DependentRecordType(tuple(self.fields.items()))

    def free_variables(self) -> FrozenSet[str]:
        """Return free type variables across all fields."""
        bound: set[str] = set()
        fv: set[str] = set()
        for name, ty in self.fields.items():
            fv |= ty.free_variables() - bound
            bound.add(name)
        return frozenset(fv)

    def is_independent(self) -> bool:
        """``True`` when no field depends on any other field."""
        return len(self.dependencies) == 0

    def dependency_order(self) -> List[str]:
        """Return field names in topological (dependency) order.

        For a well-formed record this is just declaration order.
        """
        return list(self.fields.keys())

    def project(self, names: Sequence[str]) -> DependentRecord:
        """Project onto a subset of fields, preserving dependencies."""
        name_set = set(names)
        new_fields: OrderedDict[str, TypeBase] = OrderedDict()
        new_deps: Dict[str, List[str]] = {}
        for name in self.fields:
            if name in name_set:
                new_fields[name] = self.fields[name]
                if name in self.dependencies:
                    new_deps[name] = [
                        d for d in self.dependencies[name] if d in name_set
                    ]
        return DependentRecord(new_fields, new_deps)

    def __repr__(self) -> str:
        fields_str = ", ".join(f"{k}: {v!r}" for k, v in self.fields.items())
        if self.dependencies:
            deps_str = ", ".join(
                f"{k} depends on [{', '.join(v)}]"
                for k, v in self.dependencies.items()
            )
            return f"DependentRecord({{{fields_str}}}, deps={{{deps_str}}})"
        return f"DependentRecord({{{fields_str}}})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, DependentRecord):
            return NotImplemented
        return self.fields == other.fields and self.dependencies == other.dependencies

    def __hash__(self) -> int:
        return hash((
            tuple(self.fields.items()),
            tuple(sorted(
                (k, tuple(v)) for k, v in self.dependencies.items()
            )),
        ))


# ═══════════════════════════════════════════════════════════════════════════════
# Indexed union and intersection
# ═══════════════════════════════════════════════════════════════════════════════


class IndexedUnion(TypeFamily):
    """A union (coproduct) of a type family: ``⊔_{i ∈ D} F(i)``.

    Represents the disjoint union of all fibers.
    """

    def __init__(self, base_family: TypeFamily) -> None:
        self._base_family = base_family
        super().__init__(
            f"⊔({base_family.name})",
            base_family.index_domain,
            base_family.fiber,
        )

    @property
    def base_family(self) -> TypeFamily:
        return self._base_family

    def evaluate_at(self, indices: Sequence[Any]) -> TypeBase:
        """Evaluate the indexed union at a finite set of indices."""
        from .base import UnionType
        members = [self.apply(i) for i in indices]
        return UnionType.build(members)

    def __repr__(self) -> str:
        return f"⊔({self._base_family.name})"


class IndexedIntersection(TypeFamily):
    """An intersection (product) of a type family: ``⊓_{i ∈ D} F(i)``.

    Represents the intersection of all fibers.
    """

    def __init__(self, base_family: TypeFamily) -> None:
        self._base_family = base_family
        super().__init__(
            f"⊓({base_family.name})",
            base_family.index_domain,
            base_family.fiber,
        )

    @property
    def base_family(self) -> TypeFamily:
        return self._base_family

    def evaluate_at(self, indices: Sequence[Any]) -> TypeBase:
        """Evaluate the indexed intersection at a finite set of indices."""
        from .base import IntersectionType
        members = [self.apply(i) for i in indices]
        return IntersectionType.build(members)

    def __repr__(self) -> str:
        return f"⊓({self._base_family.name})"
