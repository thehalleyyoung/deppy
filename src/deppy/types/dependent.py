"""Dependent types for DepPy.

This module provides:
- :class:`PiType` — dependent function type Π(x:τ₁).τ₂
- :class:`SigmaType` — dependent pair type Σ(x:τ₁).τ₂
- :class:`IndexedFamily` — type family parameterised by a term
- :class:`WitnessType` — result carrying a proof witness
- :class:`IdentityType` — identity / equality type Id_A(a, b)
- :class:`ForallType` — universally quantified type
- :class:`ExistsType` — existentially quantified type
"""
from __future__ import annotations

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
    Tuple,
)

from .base import TypeBase, AnyType, NeverType, ANY_TYPE, NEVER_TYPE


# ═══════════════════════════════════════════════════════════════════════════════
# Pi type (dependent function)
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class PiType(TypeBase):
    """Dependent function type ``Π(x:τ₁).τ₂``.

    The return type *return_type* may mention *param_name*.  When *param_name*
    does not appear free in *return_type* this degenerates to a simple function
    type ``τ₁ → τ₂``.

    Attributes:
        param_name: The binding variable name *x*.
        param_type: The domain type *τ₁*.
        return_type: The codomain type *τ₂*, possibly dependent on *x*.
    """

    param_name: str
    param_type: TypeBase
    return_type: TypeBase

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        # Avoid capturing the bound variable
        filtered = {k: v for k, v in mapping.items() if k != self.param_name}
        new_param = self.param_type.substitute(mapping)
        new_ret = self.return_type.substitute(filtered)
        if new_param is self.param_type and new_ret is self.return_type:
            return self
        return PiType(self.param_name, new_param, new_ret)

    def free_variables(self) -> FrozenSet[str]:
        param_fv = self.param_type.free_variables()
        ret_fv = self.return_type.free_variables() - {self.param_name}
        return param_fv | ret_fv

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.param_type.walk()
        yield from self.return_type.walk()

    def is_dependent(self) -> bool:
        """``True`` when the return type actually mentions *param_name*."""
        return self.param_name in self.return_type.free_variables()

    def apply(self, arg: TypeBase) -> TypeBase:
        """Substitute *arg* for *param_name* in the return type."""
        return self.return_type.substitute({self.param_name: arg})

    def alpha_rename(self, new_name: str) -> PiType:
        """Alpha-rename the binder."""
        if new_name == self.param_name:
            return self
        new_ret = self.return_type.substitute({self.param_name: _NamePlaceholder(new_name)})
        # The placeholder is never a real type — we abuse substitute to rename
        # free occurrences.  A cleaner approach uses a dedicated rename, but
        # since our TypeBase.substitute already handles the plumbing we
        # reconstruct with the right variable.
        from .variables import TypeVariable
        tv = TypeVariable(new_name)
        new_ret = self.return_type.substitute({self.param_name: tv})
        return PiType(new_name, self.param_type, new_ret)

    def to_callable(self) -> TypeBase:
        """Convert to a non-dependent :class:`CallableType` when possible."""
        from .base import CallableType
        if self.is_dependent():
            return self
        return CallableType((self.param_type,), self.return_type)

    def __repr__(self) -> str:
        return f"Π({self.param_name}: {self.param_type!r}).{self.return_type!r}"


class _NamePlaceholder(TypeBase):
    """Internal placeholder used during alpha-renaming."""

    def __init__(self, name: str) -> None:
        self._name = name

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        return mapping.get(self._name, self)

    def free_variables(self) -> FrozenSet[str]:
        return frozenset({self._name})

    def __eq__(self, other: object) -> bool:
        if isinstance(other, _NamePlaceholder):
            return self._name == other._name
        return NotImplemented

    def __hash__(self) -> int:
        return hash(("_placeholder", self._name))

    def __repr__(self) -> str:
        return self._name


# ═══════════════════════════════════════════════════════════════════════════════
# Multi-parameter Pi
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class MultiPiType(TypeBase):
    """Multi-parameter dependent function type ``Π(x₁:τ₁, ..., xₙ:τₙ).τ``.

    Desugars to nested :class:`PiType` via :meth:`to_nested`.
    """

    params: Tuple[Tuple[str, TypeBase], ...]
    return_type: TypeBase

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        bound_names = {name for name, _ in self.params}
        filtered = {k: v for k, v in mapping.items() if k not in bound_names}
        new_params = tuple(
            (name, ty.substitute(mapping)) for name, ty in self.params
        )
        new_ret = self.return_type.substitute(filtered)
        if (
            all(n[1] is o[1] for n, o in zip(new_params, self.params))
            and new_ret is self.return_type
        ):
            return self
        return MultiPiType(new_params, new_ret)

    def free_variables(self) -> FrozenSet[str]:
        bound = {name for name, _ in self.params}
        fv: set[str] = set()
        for _, ty in self.params:
            fv |= ty.free_variables()
        fv |= self.return_type.free_variables() - bound
        return frozenset(fv)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        for _, ty in self.params:
            yield from ty.walk()
        yield from self.return_type.walk()

    def to_nested(self) -> TypeBase:
        """Desugar into nested :class:`PiType` instances."""
        result: TypeBase = self.return_type
        for name, ty in reversed(self.params):
            result = PiType(name, ty, result)
        return result

    def __repr__(self) -> str:
        params_str = ", ".join(f"{n}: {t!r}" for n, t in self.params)
        return f"Π({params_str}).{self.return_type!r}"


# ═══════════════════════════════════════════════════════════════════════════════
# Sigma type (dependent pair)
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class SigmaType(TypeBase):
    """Dependent pair type ``Σ(x:τ₁).τ₂``.

    The second component's type may depend on the value of the first.

    Attributes:
        fst_name: The binder for the first component.
        fst_type: Type of the first component.
        snd_type: Type of the second component, possibly dependent on *fst_name*.
    """

    fst_name: str
    fst_type: TypeBase
    snd_type: TypeBase

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        filtered = {k: v for k, v in mapping.items() if k != self.fst_name}
        new_fst = self.fst_type.substitute(mapping)
        new_snd = self.snd_type.substitute(filtered)
        if new_fst is self.fst_type and new_snd is self.snd_type:
            return self
        return SigmaType(self.fst_name, new_fst, new_snd)

    def free_variables(self) -> FrozenSet[str]:
        fst_fv = self.fst_type.free_variables()
        snd_fv = self.snd_type.free_variables() - {self.fst_name}
        return fst_fv | snd_fv

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.fst_type.walk()
        yield from self.snd_type.walk()

    def is_dependent(self) -> bool:
        """``True`` when the second type mentions *fst_name*."""
        return self.fst_name in self.snd_type.free_variables()

    def project_snd(self, fst_value: TypeBase) -> TypeBase:
        """Compute the second component's type given a first-component value."""
        return self.snd_type.substitute({self.fst_name: fst_value})

    def to_tuple(self) -> TypeBase:
        """Convert to a non-dependent tuple type when possible."""
        from .base import TupleType
        if self.is_dependent():
            return self
        return TupleType((self.fst_type, self.snd_type))

    def __repr__(self) -> str:
        return f"Σ({self.fst_name}: {self.fst_type!r}).{self.snd_type!r}"


# ═══════════════════════════════════════════════════════════════════════════════
# Indexed type family
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class IndexedFamily(TypeBase):
    """A type family indexed by a term: ``F(i)``.

    Attributes:
        family_name: Human-readable family name.
        index_type: The type of the index parameter.
        body: The type expression parameterised by the index.
        index_binder: The variable name used in *body* for the index.
    """

    family_name: str
    index_type: TypeBase
    body: TypeBase
    index_binder: str = "i"

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        filtered = {k: v for k, v in mapping.items() if k != self.index_binder}
        new_idx = self.index_type.substitute(mapping)
        new_body = self.body.substitute(filtered)
        if new_idx is self.index_type and new_body is self.body:
            return self
        return IndexedFamily(self.family_name, new_idx, new_body, self.index_binder)

    def free_variables(self) -> FrozenSet[str]:
        idx_fv = self.index_type.free_variables()
        body_fv = self.body.free_variables() - {self.index_binder}
        return idx_fv | body_fv

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.index_type.walk()
        yield from self.body.walk()

    def apply(self, index: TypeBase) -> TypeBase:
        """Instantiate the family at a specific index."""
        return self.body.substitute({self.index_binder: index})

    def __repr__(self) -> str:
        return f"{self.family_name}({self.index_binder}: {self.index_type!r}) = {self.body!r}"


# ═══════════════════════════════════════════════════════════════════════════════
# Witness type
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class WitnessType(TypeBase):
    """Result carrying a proof witness.

    Packages a value type with a proposition that has been proven about it.

    Attributes:
        value_type: The type of the value.
        witness_prop: A description of the proposition witnessed.
    """

    value_type: TypeBase
    witness_prop: Any

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_val = self.value_type.substitute(mapping)
        if new_val is self.value_type:
            return self
        return WitnessType(new_val, self.witness_prop)

    def free_variables(self) -> FrozenSet[str]:
        return self.value_type.free_variables()

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.value_type.walk()

    def forget_witness(self) -> TypeBase:
        """Erase the witness, returning just the value type."""
        return self.value_type

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, WitnessType):
            return NotImplemented
        return self.value_type == other.value_type and self.witness_prop == other.witness_prop

    def __hash__(self) -> int:
        try:
            return hash(("Witness", self.value_type, self.witness_prop))
        except TypeError:
            return hash(("Witness", self.value_type, id(self.witness_prop)))

    def __repr__(self) -> str:
        return f"Witness[{self.value_type!r}, {self.witness_prop!r}]"


# ═══════════════════════════════════════════════════════════════════════════════
# Identity type
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class IdentityType(TypeBase):
    """Identity type ``Id_A(a, b)``.

    Inhabited when *lhs* and *rhs* are (propositionally) equal at type *carrier*.

    Attributes:
        carrier: The type at which equality is asserted.
        lhs: Left-hand side of the equality.
        rhs: Right-hand side of the equality.
    """

    carrier: TypeBase
    lhs: Any
    rhs: Any

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        new_carrier = self.carrier.substitute(mapping)
        new_lhs = self.lhs.substitute(mapping) if isinstance(self.lhs, TypeBase) else self.lhs
        new_rhs = self.rhs.substitute(mapping) if isinstance(self.rhs, TypeBase) else self.rhs
        if (
            new_carrier is self.carrier
            and new_lhs is self.lhs
            and new_rhs is self.rhs
        ):
            return self
        return IdentityType(new_carrier, new_lhs, new_rhs)

    def free_variables(self) -> FrozenSet[str]:
        fv = self.carrier.free_variables()
        if isinstance(self.lhs, TypeBase):
            fv = fv | self.lhs.free_variables()
        if isinstance(self.rhs, TypeBase):
            fv = fv | self.rhs.free_variables()
        return fv

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.carrier.walk()
        if isinstance(self.lhs, TypeBase):
            yield from self.lhs.walk()
        if isinstance(self.rhs, TypeBase):
            yield from self.rhs.walk()

    def is_reflexive(self) -> bool:
        """``True`` when *lhs* and *rhs* are syntactically equal."""
        return self.lhs == self.rhs

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, IdentityType):
            return NotImplemented
        return (
            self.carrier == other.carrier
            and self.lhs == other.lhs
            and self.rhs == other.rhs
        )

    def __hash__(self) -> int:
        try:
            return hash(("Id", self.carrier, self.lhs, self.rhs))
        except TypeError:
            return hash(("Id", self.carrier, id(self.lhs), id(self.rhs)))

    def __repr__(self) -> str:
        return f"Id_{{{self.carrier!r}}}({self.lhs!r}, {self.rhs!r})"


# ═══════════════════════════════════════════════════════════════════════════════
# Universally and existentially quantified types
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ForallType(TypeBase):
    """Universally quantified type ``∀α.τ``.

    Attributes:
        var_name: The quantified type variable.
        bound: An optional upper bound on the variable.
        body: The body type, which may mention *var_name*.
    """

    var_name: str
    body: TypeBase
    bound: Optional[TypeBase] = None

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        filtered = {k: v for k, v in mapping.items() if k != self.var_name}
        new_body = self.body.substitute(filtered)
        new_bound = self.bound.substitute(mapping) if self.bound is not None else None
        if new_body is self.body and (new_bound is self.bound):
            return self
        return ForallType(self.var_name, new_body, new_bound)

    def free_variables(self) -> FrozenSet[str]:
        fv = self.body.free_variables() - {self.var_name}
        if self.bound is not None:
            fv = fv | self.bound.free_variables()
        return fv

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.body.walk()
        if self.bound is not None:
            yield from self.bound.walk()

    def instantiate(self, ty: TypeBase) -> TypeBase:
        """Instantiate the universally quantified variable with *ty*."""
        return self.body.substitute({self.var_name: ty})

    def __repr__(self) -> str:
        bound_str = f" <: {self.bound!r}" if self.bound is not None else ""
        return f"∀{self.var_name}{bound_str}.{self.body!r}"


@dataclass(frozen=True)
class ExistsType(TypeBase):
    """Existentially quantified type ``∃α.τ``.

    Attributes:
        var_name: The quantified type variable.
        body: The body type.
        bound: An optional upper bound.
    """

    var_name: str
    body: TypeBase
    bound: Optional[TypeBase] = None

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        filtered = {k: v for k, v in mapping.items() if k != self.var_name}
        new_body = self.body.substitute(filtered)
        new_bound = self.bound.substitute(mapping) if self.bound is not None else None
        if new_body is self.body and (new_bound is self.bound):
            return self
        return ExistsType(self.var_name, new_body, new_bound)

    def free_variables(self) -> FrozenSet[str]:
        fv = self.body.free_variables() - {self.var_name}
        if self.bound is not None:
            fv = fv | self.bound.free_variables()
        return fv

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.body.walk()
        if self.bound is not None:
            yield from self.bound.walk()

    def open(self, witness: TypeBase) -> TypeBase:
        """Open the existential with a concrete witness type."""
        return self.body.substitute({self.var_name: witness})

    def __repr__(self) -> str:
        bound_str = f" <: {self.bound!r}" if self.bound is not None else ""
        return f"∃{self.var_name}{bound_str}.{self.body!r}"


# ═══════════════════════════════════════════════════════════════════════════════
# Dependent record type
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class DependentRecordType(TypeBase):
    """Record type where later fields may depend on earlier fields.

    Fields are ordered; each field's type may reference earlier field names.

    Attributes:
        fields: Ordered sequence of ``(name, type)`` pairs.
    """

    fields: Tuple[Tuple[str, TypeBase], ...]

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        bound_names: set[str] = set()
        new_fields: list[Tuple[str, TypeBase]] = []
        for name, ty in self.fields:
            filtered = {k: v for k, v in mapping.items() if k not in bound_names}
            new_ty = ty.substitute(filtered)
            new_fields.append((name, new_ty))
            bound_names.add(name)
        if all(n[1] is o[1] for n, o in zip(new_fields, self.fields)):
            return self
        return DependentRecordType(tuple(new_fields))

    def free_variables(self) -> FrozenSet[str]:
        bound: set[str] = set()
        fv: set[str] = set()
        for name, ty in self.fields:
            fv |= ty.free_variables() - bound
            bound.add(name)
        return frozenset(fv)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        for _, ty in self.fields:
            yield from ty.walk()

    def field_type(self, name: str) -> Optional[TypeBase]:
        """Look up a field type by name."""
        for n, t in self.fields:
            if n == name:
                return t
        return None

    def field_names(self) -> Tuple[str, ...]:
        """Return the ordered field names."""
        return tuple(n for n, _ in self.fields)

    def dependencies(self) -> Dict[str, List[str]]:
        """Compute which fields each field depends on.

        Returns a mapping from field name to a list of earlier field names
        that appear free in its type.
        """
        all_names = {n for n, _ in self.fields}
        deps: Dict[str, List[str]] = {}
        seen: set[str] = set()
        for name, ty in self.fields:
            ty_fv = ty.free_variables()
            deps[name] = sorted(ty_fv & seen)
            seen.add(name)
        return deps

    def project(self, fst_values: Mapping[str, TypeBase]) -> DependentRecordType:
        """Partially instantiate the record given values for some fields."""
        new_fields: list[Tuple[str, TypeBase]] = []
        for name, ty in self.fields:
            if name in fst_values:
                continue
            new_ty = ty.substitute(fst_values)
            new_fields.append((name, new_ty))
        return DependentRecordType(tuple(new_fields))

    def __repr__(self) -> str:
        fields_str = ", ".join(f"{n}: {t!r}" for n, t in self.fields)
        return f"Record{{{fields_str}}}"


# ═══════════════════════════════════════════════════════════════════════════════
# Utility: telescope
# ═══════════════════════════════════════════════════════════════════════════════


def telescope_to_pi(params: Sequence[Tuple[str, TypeBase]], ret: TypeBase) -> TypeBase:
    """Build a nested Pi type from a telescope of parameters.

    ``telescope_to_pi([("x", A), ("y", B)], C)`` produces ``Π(x:A).Π(y:B).C``.
    """
    result = ret
    for name, ty in reversed(params):
        result = PiType(name, ty, result)
    return result


def telescope_to_sigma(fields: Sequence[Tuple[str, TypeBase]]) -> TypeBase:
    """Build a nested Sigma type from a telescope.

    ``telescope_to_sigma([("x", A), ("y", B)])`` produces ``Σ(x:A).B``.
    For single-field telescopes, returns just the field type.
    """
    if len(fields) == 0:
        from .base import TupleType
        return TupleType(())
    if len(fields) == 1:
        return fields[0][1]
    *init, (last_name, last_ty) = fields
    result: TypeBase = last_ty
    for name, ty in reversed(init):
        result = SigmaType(name, ty, result)
    return result
