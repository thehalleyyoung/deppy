"""Type variables, row variables, and unification state for DepPy.

This module provides:
- :class:`TypeVariable` — standard unification variables with optional bounds.
- :class:`RowVariable` — row polymorphism variables for open record / kwargs types.
- :class:`SkolemVariable` — rigid (Skolem) constants introduced when checking
  universally-quantified types.
- :class:`ExistentialVariable` — existential type variables.
- :class:`UnificationState` — mutable state that tracks variable bindings during
  type inference and supports path-compressed union-find.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass, field
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
)

from .base import TypeBase, AnyType, NeverType, ANY_TYPE, NEVER_TYPE


# ═══════════════════════════════════════════════════════════════════════════════
# Type variables
# ═══════════════════════════════════════════════════════════════════════════════


class Variance:
    """Variance annotation for type parameters."""

    COVARIANT = "covariant"
    CONTRAVARIANT = "contravariant"
    INVARIANT = "invariant"
    BIVARIANT = "bivariant"


@dataclass(frozen=True)
class TypeVariable(TypeBase):
    """A type variable ``α`` used during type inference and polymorphism.

    Attributes:
        name: Unique name such as ``'T'``, ``'α'``, or ``'_t0'``.
        upper_bound: The upper bound (supertype constraint).  Defaults to ``Any``.
        lower_bound: The lower bound (subtype constraint).  Defaults to ``Never``.
        variance: One of ``Variance.COVARIANT``, etc.
        constraints: If non-empty, the variable is constrained to exactly one of
            these types (like ``TypeVar('T', int, str)``).
        level: Binding level for let-polymorphism (higher = more local).
    """

    name: str
    upper_bound: TypeBase = field(default_factory=lambda: ANY_TYPE)
    lower_bound: TypeBase = field(default_factory=lambda: NEVER_TYPE)
    variance: str = Variance.INVARIANT
    constraints: Tuple[TypeBase, ...] = ()
    level: int = 0

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        replacement = mapping.get(self.name)
        if replacement is not None:
            return replacement
        new_upper = self.upper_bound.substitute(mapping)
        new_lower = self.lower_bound.substitute(mapping)
        new_constraints = tuple(c.substitute(mapping) for c in self.constraints)
        if (
            new_upper is self.upper_bound
            and new_lower is self.lower_bound
            and all(n is o for n, o in zip(new_constraints, self.constraints))
        ):
            return self
        return TypeVariable(
            self.name,
            new_upper,
            new_lower,
            self.variance,
            new_constraints,
            self.level,
        )

    def free_variables(self) -> FrozenSet[str]:
        result: set[str] = {self.name}
        result |= self.upper_bound.free_variables()
        result |= self.lower_bound.free_variables()
        for c in self.constraints:
            result |= c.free_variables()
        return frozenset(result)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        yield from self.upper_bound.walk()
        yield from self.lower_bound.walk()
        for c in self.constraints:
            yield from c.walk()

    def is_unconstrained(self) -> bool:
        """``True`` when the variable has no bounds or constraints."""
        return (
            isinstance(self.upper_bound, AnyType)
            and isinstance(self.lower_bound, NeverType)
            and len(self.constraints) == 0
        )

    def with_upper_bound(self, bound: TypeBase) -> TypeVariable:
        """Return a copy with *bound* as the new upper bound."""
        return TypeVariable(
            self.name, bound, self.lower_bound,
            self.variance, self.constraints, self.level,
        )

    def with_lower_bound(self, bound: TypeBase) -> TypeVariable:
        """Return a copy with *bound* as the new lower bound."""
        return TypeVariable(
            self.name, self.upper_bound, bound,
            self.variance, self.constraints, self.level,
        )

    def __repr__(self) -> str:
        parts = [self.name]
        if not isinstance(self.upper_bound, AnyType):
            parts.append(f" <: {self.upper_bound!r}")
        if not isinstance(self.lower_bound, NeverType):
            parts.append(f" :> {self.lower_bound!r}")
        if self.constraints:
            constrs = ", ".join(repr(c) for c in self.constraints)
            parts.append(f" in {{{constrs}}}")
        return "".join(parts)


# ═══════════════════════════════════════════════════════════════════════════════
# Row variable
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class RowVariable(TypeBase):
    """Row polymorphism variable ``ρ``.

    Used for open records (e.g. ``TypedDict`` with extra keys) and
    ``**kwargs`` typing.  A row variable represents "the rest of the fields".

    Attributes:
        name: Unique identifier for this row variable.
        known_fields: Fields already known to be present in the row.
        rest: An optional inner row variable representing further extension.
    """

    name: str
    known_fields: Tuple[Tuple[str, TypeBase], ...] = ()
    rest: Optional[TypeBase] = None

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        replacement = mapping.get(self.name)
        if replacement is not None:
            return replacement
        new_fields = tuple(
            (k, v.substitute(mapping)) for k, v in self.known_fields
        )
        new_rest = self.rest.substitute(mapping) if self.rest is not None else None
        if (
            all(n[1] is o[1] for n, o in zip(new_fields, self.known_fields))
            and (new_rest is self.rest)
        ):
            return self
        return RowVariable(self.name, new_fields, new_rest)

    def free_variables(self) -> FrozenSet[str]:
        result: set[str] = {self.name}
        for _, v in self.known_fields:
            result |= v.free_variables()
        if self.rest is not None:
            result |= self.rest.free_variables()
        return frozenset(result)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        for _, v in self.known_fields:
            yield from v.walk()
        if self.rest is not None:
            yield from self.rest.walk()

    def field_dict(self) -> Dict[str, TypeBase]:
        """Known fields as a dictionary."""
        return dict(self.known_fields)

    def extend(self, field_name: str, field_type: TypeBase) -> RowVariable:
        """Return a new row with an additional known field."""
        new_fields = self.known_fields + ((field_name, field_type),)
        return RowVariable(self.name, new_fields, self.rest)

    def __repr__(self) -> str:
        parts = [f"ρ.{self.name}"]
        if self.known_fields:
            fields_str = ", ".join(
                f"{k}: {v!r}" for k, v in self.known_fields
            )
            parts.append(f"({fields_str})")
        if self.rest is not None:
            parts.append(f" | {self.rest!r}")
        return "".join(parts)


# ═══════════════════════════════════════════════════════════════════════════════
# Skolem and existential variables
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class SkolemVariable(TypeBase):
    """A Skolem constant introduced when checking universally-quantified types.

    Skolem variables are *rigid*: they cannot be unified with other types.
    They represent "an arbitrary but fixed" type chosen by the environment.

    Attributes:
        name: Unique name, typically generated (e.g. ``'sk_0'``).
        origin: Optional human-readable description of why this Skolem was created.
        scope_level: Nesting depth at which the Skolem was introduced.
    """

    name: str
    origin: str = ""
    scope_level: int = 0

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        return mapping.get(self.name, self)

    def free_variables(self) -> FrozenSet[str]:
        return frozenset({self.name})

    def __repr__(self) -> str:
        if self.origin:
            return f"sk({self.name}, {self.origin})"
        return f"sk({self.name})"


@dataclass(frozen=True)
class ExistentialVariable(TypeBase):
    """An existential type variable ``∃α.τ`` in unpacked form.

    Represents a type that is known to exist but whose concrete identity is
    hidden — the dual of universal (Skolem) quantification.

    Attributes:
        name: The existential variable's name.
        witness_type: The *hidden* type, if it has been opened.
        scope_level: Nesting depth.
    """

    name: str
    witness_type: Optional[TypeBase] = None
    scope_level: int = 0

    def substitute(self, mapping: Mapping[str, TypeBase]) -> TypeBase:
        replacement = mapping.get(self.name)
        if replacement is not None:
            return replacement
        if self.witness_type is not None:
            new_witness = self.witness_type.substitute(mapping)
            if new_witness is not self.witness_type:
                return ExistentialVariable(self.name, new_witness, self.scope_level)
        return self

    def free_variables(self) -> FrozenSet[str]:
        result: set[str] = {self.name}
        if self.witness_type is not None:
            result |= self.witness_type.free_variables()
        return frozenset(result)

    def walk(self) -> Iterator[TypeBase]:
        yield self
        if self.witness_type is not None:
            yield from self.witness_type.walk()

    def is_opened(self) -> bool:
        """``True`` when a witness type has been revealed."""
        return self.witness_type is not None

    def open(self, witness: TypeBase) -> ExistentialVariable:
        """Return a copy with the existential opened to *witness*."""
        return ExistentialVariable(self.name, witness, self.scope_level)

    def __repr__(self) -> str:
        if self.witness_type is not None:
            return f"∃{self.name}(={self.witness_type!r})"
        return f"∃{self.name}"


# ═══════════════════════════════════════════════════════════════════════════════
# Unification state
# ═══════════════════════════════════════════════════════════════════════════════


class UnificationError(Exception):
    """Raised when two types cannot be unified."""

    def __init__(self, lhs: TypeBase, rhs: TypeBase, reason: str = "") -> None:
        self.lhs = lhs
        self.rhs = rhs
        self.reason = reason
        msg = f"Cannot unify {lhs!r} with {rhs!r}"
        if reason:
            msg += f": {reason}"
        super().__init__(msg)


class UnificationState:
    """Manages type-variable bindings during inference.

    Implements a union-find with path compression so that chains of
    ``α = β = γ = int`` are resolved efficiently.
    """

    def __init__(self) -> None:
        self._bindings: Dict[str, TypeBase] = {}
        self._parent: Dict[str, str] = {}
        self._rank: Dict[str, int] = {}
        self._level: int = 0
        self._counter = itertools.count()

    # ── Fresh variable generation ──────────────────────────────────────────

    def fresh(
        self,
        prefix: str = "_t",
        upper_bound: TypeBase | None = None,
        lower_bound: TypeBase | None = None,
    ) -> TypeVariable:
        """Create a fresh type variable that is tracked by this state."""
        idx = next(self._counter)
        name = f"{prefix}{idx}"
        self._parent[name] = name
        self._rank[name] = 0
        ub = upper_bound if upper_bound is not None else ANY_TYPE
        lb = lower_bound if lower_bound is not None else NEVER_TYPE
        return TypeVariable(name, ub, lb, Variance.INVARIANT, (), self._level)

    def fresh_row(self, prefix: str = "_r") -> RowVariable:
        """Create a fresh row variable tracked by this state."""
        idx = next(self._counter)
        name = f"{prefix}{idx}"
        self._parent[name] = name
        self._rank[name] = 0
        return RowVariable(name)

    def fresh_skolem(self, prefix: str = "sk", origin: str = "") -> SkolemVariable:
        """Create a fresh Skolem constant."""
        idx = next(self._counter)
        name = f"{prefix}_{idx}"
        return SkolemVariable(name, origin, self._level)

    def fresh_existential(self, prefix: str = "ex") -> ExistentialVariable:
        """Create a fresh existential variable."""
        idx = next(self._counter)
        name = f"{prefix}_{idx}"
        self._parent[name] = name
        self._rank[name] = 0
        return ExistentialVariable(name, scope_level=self._level)

    # ── Union-find ─────────────────────────────────────────────────────────

    def _find(self, name: str) -> str:
        """Find the representative of *name* with path compression."""
        root = name
        while self._parent.get(root, root) != root:
            root = self._parent[root]
        # Path compression
        current = name
        while current != root:
            parent = self._parent[current]
            self._parent[current] = root
            current = parent
        return root

    def _union(self, a: str, b: str) -> str:
        """Merge equivalence classes of *a* and *b*, returning new root."""
        ra = self._find(a)
        rb = self._find(b)
        if ra == rb:
            return ra
        rank_a = self._rank.get(ra, 0)
        rank_b = self._rank.get(rb, 0)
        if rank_a < rank_b:
            self._parent[ra] = rb
            return rb
        elif rank_a > rank_b:
            self._parent[rb] = ra
            return ra
        else:
            self._parent[rb] = ra
            self._rank[ra] = rank_a + 1
            return ra

    # ── Binding operations ─────────────────────────────────────────────────

    def bind(self, var_name: str, ty: TypeBase) -> None:
        """Bind type variable *var_name* to *ty*.

        Raises :class:`UnificationError` if an occurs-check fails.
        """
        rep = self._find(var_name)
        if isinstance(ty, TypeVariable):
            ty_rep = self._find(ty.name)
            if rep == ty_rep:
                return
            existing = self._bindings.get(rep)
            if existing is not None:
                # Already bound — unify existing binding with ty
                self.unify(existing, ty)
                return
            root = self._union(rep, ty_rep)
            # If the other side has a binding, propagate
            other = rep if root == ty_rep else ty_rep
            other_binding = self._bindings.pop(other, None)
            if other_binding is not None:
                self._bindings[root] = other_binding
            return
        # Occurs check
        resolved = self.resolve(ty)
        if var_name in resolved.free_variables():
            raise UnificationError(
                TypeVariable(var_name), ty, "occurs check failed"
            )
        rep = self._find(var_name)
        existing = self._bindings.get(rep)
        if existing is not None:
            self.unify(existing, resolved)
        else:
            self._bindings[rep] = resolved

    def resolve(self, ty: TypeBase) -> TypeBase:
        """Fully resolve all bound variables in *ty*."""
        if isinstance(ty, TypeVariable):
            rep = self._find(ty.name)
            bound = self._bindings.get(rep)
            if bound is not None:
                return self.resolve(bound)
            if rep != ty.name:
                return TypeVariable(
                    rep, ty.upper_bound, ty.lower_bound,
                    ty.variance, ty.constraints, ty.level,
                )
            return ty
        if isinstance(ty, RowVariable):
            rep = self._find(ty.name)
            bound = self._bindings.get(rep)
            if bound is not None:
                return self.resolve(bound)
            new_fields = tuple(
                (k, self.resolve(v)) for k, v in ty.known_fields
            )
            new_rest = self.resolve(ty.rest) if ty.rest is not None else None
            return RowVariable(rep, new_fields, new_rest)
        if isinstance(ty, ExistentialVariable):
            rep = self._find(ty.name)
            bound = self._bindings.get(rep)
            if bound is not None:
                return self.resolve(bound)
            return ty
        # For compound types, apply resolution through substitution
        return ty.substitute(self.as_mapping())

    def as_mapping(self) -> Dict[str, TypeBase]:
        """Return the current bindings as a substitution mapping.

        Keys are representative names; values are recursively resolved.
        """
        result: Dict[str, TypeBase] = {}
        visited: Set[str] = set()
        for name in list(self._parent.keys()):
            rep = self._find(name)
            if rep in visited:
                if rep in result:
                    result[name] = result[rep]
                continue
            visited.add(rep)
            bound = self._bindings.get(rep)
            if bound is not None:
                resolved = self._resolve_no_loop(bound, set())
                result[rep] = resolved
                if name != rep:
                    result[name] = resolved
        return result

    def _resolve_no_loop(self, ty: TypeBase, seen: Set[str]) -> TypeBase:
        """Resolve without infinite loops on cycles."""
        if isinstance(ty, TypeVariable):
            rep = self._find(ty.name)
            if rep in seen:
                return TypeVariable(rep, ty.upper_bound, ty.lower_bound,
                                    ty.variance, ty.constraints, ty.level)
            bound = self._bindings.get(rep)
            if bound is not None:
                return self._resolve_no_loop(bound, seen | {rep})
            return TypeVariable(rep, ty.upper_bound, ty.lower_bound,
                                ty.variance, ty.constraints, ty.level)
        if isinstance(ty, RowVariable):
            rep = self._find(ty.name)
            if rep in seen:
                return ty
            bound = self._bindings.get(rep)
            if bound is not None:
                return self._resolve_no_loop(bound, seen | {rep})
            return ty
        return ty

    # ── Unification ────────────────────────────────────────────────────────

    def unify(self, a: TypeBase, b: TypeBase) -> None:
        """Unify types *a* and *b*, updating bindings.

        Raises :class:`UnificationError` on failure.
        """
        a = self.resolve(a)
        b = self.resolve(b)

        if a == b:
            return

        # Variable cases
        if isinstance(a, TypeVariable):
            self.bind(a.name, b)
            return
        if isinstance(b, TypeVariable):
            self.bind(b.name, a)
            return
        if isinstance(a, RowVariable):
            self.bind(a.name, b)
            return
        if isinstance(b, RowVariable):
            self.bind(b.name, a)
            return
        if isinstance(a, ExistentialVariable):
            self.bind(a.name, b)
            return
        if isinstance(b, ExistentialVariable):
            self.bind(b.name, a)
            return

        # Skolem variables are rigid
        if isinstance(a, SkolemVariable) or isinstance(b, SkolemVariable):
            raise UnificationError(a, b, "Skolem variable is rigid")

        # AnyType unifies with anything
        if isinstance(a, AnyType) or isinstance(b, AnyType):
            return

        # NeverType unifies with anything (bottom is subtype of all)
        if isinstance(a, NeverType) or isinstance(b, NeverType):
            return

        # Structural unification of matching constructors
        from .base import (
            PrimitiveType, ListType, DictType, TupleType,
            SetType, FrozenSetType, OptionalType, UnionType,
            CallableType, ClassType, LiteralType, TensorType,
        )

        if isinstance(a, PrimitiveType) and isinstance(b, PrimitiveType):
            if a.kind == b.kind:
                return
            raise UnificationError(a, b, "different primitive types")

        if isinstance(a, ListType) and isinstance(b, ListType):
            self.unify(a.element, b.element)
            return

        if isinstance(a, DictType) and isinstance(b, DictType):
            self.unify(a.key, b.key)
            self.unify(a.value, b.value)
            return

        if isinstance(a, SetType) and isinstance(b, SetType):
            self.unify(a.element, b.element)
            return

        if isinstance(a, FrozenSetType) and isinstance(b, FrozenSetType):
            self.unify(a.element, b.element)
            return

        if isinstance(a, TupleType) and isinstance(b, TupleType):
            if a.variadic != b.variadic:
                raise UnificationError(a, b, "variadic mismatch")
            if not a.variadic and len(a.elements) != len(b.elements):
                raise UnificationError(a, b, "tuple length mismatch")
            for ea, eb in zip(a.elements, b.elements):
                self.unify(ea, eb)
            return

        if isinstance(a, OptionalType) and isinstance(b, OptionalType):
            self.unify(a.inner, b.inner)
            return

        if isinstance(a, CallableType) and isinstance(b, CallableType):
            if len(a.param_types) != len(b.param_types):
                raise UnificationError(a, b, "callable arity mismatch")
            # Parameters are contravariant, but for unification we unify directly
            for pa, pb in zip(a.param_types, b.param_types):
                self.unify(pa, pb)
            self.unify(a.return_type, b.return_type)
            return

        if isinstance(a, ClassType) and isinstance(b, ClassType):
            if a.name != b.name or a.module != b.module:
                raise UnificationError(a, b, "different class types")
            if len(a.type_args) != len(b.type_args):
                raise UnificationError(a, b, "type argument count mismatch")
            for ta, tb in zip(a.type_args, b.type_args):
                self.unify(ta, tb)
            return

        if isinstance(a, TensorType) and isinstance(b, TensorType):
            if a.framework != b.framework:
                raise UnificationError(a, b, "different tensor frameworks")
            if a.dtype is not None and b.dtype is not None and a.dtype != b.dtype:
                raise UnificationError(a, b, "tensor dtype mismatch")
            if a.device is not None and b.device is not None and a.device != b.device:
                raise UnificationError(a, b, "tensor device mismatch")
            if a.shape is not None and b.shape is not None:
                if len(a.shape) != len(b.shape):
                    raise UnificationError(a, b, "tensor rank mismatch")
                for da, db in zip(a.shape, b.shape):
                    if isinstance(da, int) and isinstance(db, int) and da != db:
                        raise UnificationError(a, b, f"tensor dim mismatch: {da} vs {db}")
            return

        raise UnificationError(a, b, "incompatible type constructors")

    # ── Scope management ───────────────────────────────────────────────────

    def enter_scope(self) -> int:
        """Enter a new binding scope, returning the previous level."""
        prev = self._level
        self._level += 1
        return prev

    def exit_scope(self, saved_level: int) -> None:
        """Exit a binding scope, restoring the level."""
        self._level = saved_level

    @property
    def current_level(self) -> int:
        """Current nesting level."""
        return self._level

    # ── Snapshot / rollback ────────────────────────────────────────────────

    def snapshot(self) -> _UnificationSnapshot:
        """Take a snapshot of the current state for backtracking."""
        return _UnificationSnapshot(
            bindings=dict(self._bindings),
            parent=dict(self._parent),
            rank=dict(self._rank),
            level=self._level,
            counter_value=next(self._counter),
        )

    def rollback(self, snap: _UnificationSnapshot) -> None:
        """Restore state from a previous snapshot."""
        self._bindings = dict(snap.bindings)
        self._parent = dict(snap.parent)
        self._rank = dict(snap.rank)
        self._level = snap.level
        self._counter = itertools.count(snap.counter_value)

    def __repr__(self) -> str:
        bindings = ", ".join(
            f"{k} → {v!r}" for k, v in sorted(self._bindings.items())
        )
        return f"UnificationState({bindings})"


@dataclass(frozen=True)
class _UnificationSnapshot:
    """Immutable snapshot of :class:`UnificationState` for backtracking."""

    bindings: Dict[str, TypeBase]
    parent: Dict[str, str]
    rank: Dict[str, int]
    level: int
    counter_value: int
