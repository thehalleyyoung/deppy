"""Carrier types for sheaf sections in DepPy.

In the sheaf-descent framework, a **carrier** describes what a local section's
value is typed as at a particular site.  This module provides:

- :class:`CarrierType` — the type assigned to a section at a specific site,
  together with site-specific refinements.
- :class:`CarrierSchema` — a schema describing the structure of carriers
  across a family of sites.
- :class:`CarrierProjection` — projects a carrier type along a morphism
  (restriction map) from one site to another.
- :class:`CarrierMerger` — merges compatible carrier types from overlapping
  sites into a single carrier for a global section.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
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

from .base import (
    TypeBase,
    AnyType,
    NeverType,
    UnionType,
    IntersectionType,
    ANY_TYPE,
    NEVER_TYPE,
    type_join,
    type_meet,
)
from .refinement import (
    RefinementType,
    QualifiedType,
    Predicate,
    TruePred,
    ConjunctionPred,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Carrier type
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class CarrierType:
    """The type of a local section's value at a given site.

    Attributes:
        base: The underlying DepPy type (e.g. ``int``, ``List[str]``).
        site_refinements: A mapping from refinement names to site-specific
            predicate values (e.g. ``{"positive": True, "max": 100}``).
        provenance: Optional tag describing where this carrier was derived from.
    """

    base: TypeBase
    site_refinements: Dict[str, Any] = field(default_factory=dict, hash=False)
    provenance: str = ""

    def __post_init__(self) -> None:
        # Freeze the refinements dict for safety in hashing contexts
        if not isinstance(self.site_refinements, dict):
            object.__setattr__(self, "site_refinements", dict(self.site_refinements))

    def with_refinement(self, name: str, value: Any) -> CarrierType:
        """Return a copy with an additional site refinement."""
        new_refs = dict(self.site_refinements)
        new_refs[name] = value
        return CarrierType(self.base, new_refs, self.provenance)

    def without_refinement(self, name: str) -> CarrierType:
        """Return a copy with the named refinement removed."""
        new_refs = {k: v for k, v in self.site_refinements.items() if k != name}
        return CarrierType(self.base, new_refs, self.provenance)

    def strip_refinements(self) -> CarrierType:
        """Return a copy with all site refinements removed."""
        return CarrierType(self.base, {}, self.provenance)

    def has_refinement(self, name: str) -> bool:
        """Check whether a site refinement with *name* is present."""
        return name in self.site_refinements

    def to_type(self) -> TypeBase:
        """Convert to a plain :class:`TypeBase`, embedding refinements as a
        :class:`QualifiedType` or :class:`RefinementType` if possible."""
        if not self.site_refinements:
            return self.base
        # Attempt to build a refinement type from known refinement patterns
        predicates: list[Predicate] = []
        from .refinement import ComparisonPred, ComparisonOp, LengthPred
        for name, value in self.site_refinements.items():
            if name == "positive" and value:
                predicates.append(ComparisonPred("v", ComparisonOp.GT, 0))
            elif name == "non_negative" and value:
                predicates.append(ComparisonPred("v", ComparisonOp.GE, 0))
            elif name == "max" and isinstance(value, (int, float)):
                predicates.append(ComparisonPred("v", ComparisonOp.LE, value))
            elif name == "min" and isinstance(value, (int, float)):
                predicates.append(ComparisonPred("v", ComparisonOp.GE, value))
            elif name == "non_empty" and value:
                predicates.append(LengthPred("v", ComparisonOp.GT, 0))
            elif name == "max_length" and isinstance(value, int):
                predicates.append(LengthPred("v", ComparisonOp.LE, value))
            # Unknown refinements are kept as opaque
        if not predicates:
            return self.base
        if len(predicates) == 1:
            combined = predicates[0]
        else:
            combined = ConjunctionPred(tuple(predicates))
        return RefinementType(self.base, "v", combined)

    def is_compatible_with(self, other: CarrierType) -> bool:
        """Check basic structural compatibility (same base type)."""
        return self.base == other.base

    def __repr__(self) -> str:
        if self.site_refinements:
            refs = ", ".join(f"{k}={v!r}" for k, v in self.site_refinements.items())
            return f"Carrier({self.base!r}, {refs})"
        return f"Carrier({self.base!r})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CarrierType):
            return NotImplemented
        return self.base == other.base and self.site_refinements == other.site_refinements

    def __hash__(self) -> int:
        return hash((self.base, tuple(sorted(self.site_refinements.items()))))


# ═══════════════════════════════════════════════════════════════════════════════
# Carrier schema
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class SchemaConstraint:
    """A constraint on carrier schema fields.

    Attributes:
        description: Human-readable description of the constraint.
        field_names: Fields involved in this constraint.
        check: A callable that validates field types. Returns ``True`` if satisfied.
    """

    description: str
    field_names: Tuple[str, ...]
    check: Optional[Callable[[Dict[str, TypeBase]], bool]] = field(
        default=None, hash=False, compare=False
    )

    def validate(self, fields: Dict[str, TypeBase]) -> bool:
        """Evaluate this constraint against *fields*."""
        if self.check is None:
            return True
        relevant = {k: v for k, v in fields.items() if k in self.field_names}
        return self.check(relevant)

    def __repr__(self) -> str:
        return f"Constraint({self.description}, fields={self.field_names})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, SchemaConstraint):
            return NotImplemented
        return self.description == other.description and self.field_names == other.field_names

    def __hash__(self) -> int:
        return hash((self.description, self.field_names))


@dataclass(frozen=True)
class CarrierSchema:
    """Schema describing the carrier structure at a family of sites.

    Attributes:
        fields: Mapping from field names to their types.
        constraints: A list of inter-field constraints.
        name: Optional schema name for identification.
    """

    fields: Dict[str, TypeBase] = field(default_factory=dict, hash=False)
    constraints: Tuple[SchemaConstraint, ...] = ()
    name: str = ""

    def field_type(self, name: str) -> Optional[TypeBase]:
        """Look up a field type."""
        return self.fields.get(name)

    def field_names(self) -> FrozenSet[str]:
        """Return all field names in the schema."""
        return frozenset(self.fields.keys())

    def with_field(self, name: str, ty: TypeBase) -> CarrierSchema:
        """Return a new schema with an additional field."""
        new_fields = dict(self.fields)
        new_fields[name] = ty
        return CarrierSchema(new_fields, self.constraints, self.name)

    def without_field(self, name: str) -> CarrierSchema:
        """Return a new schema with the named field removed."""
        new_fields = {k: v for k, v in self.fields.items() if k != name}
        # Drop constraints that reference the removed field
        new_constraints = tuple(
            c for c in self.constraints if name not in c.field_names
        )
        return CarrierSchema(new_fields, new_constraints, self.name)

    def add_constraint(self, constraint: SchemaConstraint) -> CarrierSchema:
        """Return a new schema with an additional constraint."""
        return CarrierSchema(
            self.fields,
            self.constraints + (constraint,),
            self.name,
        )

    def validate(self) -> List[str]:
        """Validate all constraints.  Returns list of violation messages."""
        violations: list[str] = []
        for c in self.constraints:
            if not c.validate(self.fields):
                violations.append(f"constraint violated: {c.description}")
        return violations

    def is_subschema_of(self, other: CarrierSchema) -> bool:
        """Check whether this schema has at least the fields of *other*
        (width subtyping for records)."""
        for name, ty in other.fields.items():
            if name not in self.fields:
                return False
        return True

    def project_to(self, field_names: FrozenSet[str]) -> CarrierSchema:
        """Project the schema onto a subset of fields."""
        new_fields = {k: v for k, v in self.fields.items() if k in field_names}
        new_constraints = tuple(
            c for c in self.constraints
            if all(f in field_names for f in c.field_names)
        )
        return CarrierSchema(new_fields, new_constraints, self.name)

    def merge_with(self, other: CarrierSchema) -> CarrierSchema:
        """Merge two schemas, taking the join of overlapping field types."""
        merged_fields: Dict[str, TypeBase] = dict(self.fields)
        for name, ty in other.fields.items():
            if name in merged_fields:
                merged_fields[name] = type_join(merged_fields[name], ty)
            else:
                merged_fields[name] = ty
        merged_constraints = self.constraints + other.constraints
        return CarrierSchema(merged_fields, merged_constraints, self.name or other.name)

    def __repr__(self) -> str:
        fields_str = ", ".join(f"{k}: {v!r}" for k, v in self.fields.items())
        name_str = f"{self.name}: " if self.name else ""
        return f"Schema({name_str}{{{fields_str}}})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CarrierSchema):
            return NotImplemented
        return self.fields == other.fields and self.constraints == other.constraints

    def __hash__(self) -> int:
        return hash((tuple(sorted(self.fields.items())), self.constraints))


# ═══════════════════════════════════════════════════════════════════════════════
# Carrier projection
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class CarrierProjection:
    """Projects a carrier type along a morphism between sites.

    Represents how carrier information is restricted or reindexed when
    moving from a source site to a target site.

    Attributes:
        source_schema: The schema at the source site.
        target_schema: The schema at the target site.
        projection_map: Maps target field names to source field names.
    """

    source_schema: CarrierSchema
    target_schema: CarrierSchema
    projection_map: Dict[str, str] = field(default_factory=dict, hash=False)

    def project_carrier(self, carrier: CarrierType) -> CarrierType:
        """Project a carrier from source to target, mapping refinements."""
        new_refinements: Dict[str, Any] = {}
        for target_name, source_name in self.projection_map.items():
            if source_name in carrier.site_refinements:
                new_refinements[target_name] = carrier.site_refinements[source_name]
        return CarrierType(
            carrier.base,
            new_refinements,
            provenance=f"projected from {carrier.provenance}" if carrier.provenance else "projected",
        )

    def project_type(self, ty: TypeBase) -> TypeBase:
        """Project a type from source to target schema.

        This applies the field mapping as a substitution on type variables
        that correspond to field names.
        """
        mapping: Dict[str, TypeBase] = {}
        from .variables import TypeVariable
        for target_name, source_name in self.projection_map.items():
            source_ty = self.source_schema.field_type(source_name)
            if source_ty is not None:
                mapping[source_name] = source_ty
        if not mapping:
            return ty
        return ty.substitute(mapping)

    def is_identity(self) -> bool:
        """Check if this is an identity projection (no field remapping)."""
        return all(k == v for k, v in self.projection_map.items())

    def compose(self, other: CarrierProjection) -> CarrierProjection:
        """Compose this projection with *other* (self ∘ other).

        ``self`` maps source → intermediate, *other* maps intermediate → target.
        Result maps source → target.
        """
        composed_map: Dict[str, str] = {}
        for target_name, intermediate_name in other.projection_map.items():
            source_name = self.projection_map.get(intermediate_name, intermediate_name)
            composed_map[target_name] = source_name
        return CarrierProjection(
            self.source_schema,
            other.target_schema,
            composed_map,
        )

    def validate(self) -> List[str]:
        """Validate that the projection is well-formed."""
        issues: list[str] = []
        for target_name, source_name in self.projection_map.items():
            if source_name not in self.source_schema.fields:
                issues.append(
                    f"source field '{source_name}' not in source schema"
                )
            if target_name not in self.target_schema.fields:
                issues.append(
                    f"target field '{target_name}' not in target schema"
                )
        return issues

    def __repr__(self) -> str:
        mapping_str = ", ".join(
            f"{t} ← {s}" for t, s in self.projection_map.items()
        )
        return f"Projection({mapping_str})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CarrierProjection):
            return NotImplemented
        return (
            self.source_schema == other.source_schema
            and self.target_schema == other.target_schema
            and self.projection_map == other.projection_map
        )

    def __hash__(self) -> int:
        return hash((
            self.source_schema,
            self.target_schema,
            tuple(sorted(self.projection_map.items())),
        ))


# ═══════════════════════════════════════════════════════════════════════════════
# Carrier merger
# ═══════════════════════════════════════════════════════════════════════════════


class MergeStrategy(Enum):
    """Strategy for merging overlapping carrier types."""

    JOIN = auto()       # Take the join (least upper bound)
    MEET = auto()       # Take the meet (greatest lower bound)
    UNION = auto()      # Form a union type
    INTERSECT = auto()  # Form an intersection type
    STRICT = auto()     # Require exact equality


@dataclass
class CarrierMerger:
    """Merges carrier types from overlapping sites into a unified carrier.

    Used during global section assembly to reconcile carriers that describe
    the same value at different observation sites.

    Attributes:
        strategy: The merge strategy to use.
    """

    strategy: MergeStrategy = MergeStrategy.JOIN

    def merge(self, carriers: Sequence[CarrierType]) -> CarrierType:
        """Merge multiple carriers into one.

        Raises ``ValueError`` if merging fails under the strict strategy.
        """
        if not carriers:
            return CarrierType(ANY_TYPE)
        if len(carriers) == 1:
            return carriers[0]

        base = self._merge_bases([c.base for c in carriers])
        merged_refs = self._merge_refinements([c.site_refinements for c in carriers])
        provenance = "merged(" + ", ".join(
            c.provenance for c in carriers if c.provenance
        ) + ")"
        return CarrierType(base, merged_refs, provenance)

    def _merge_bases(self, bases: Sequence[TypeBase]) -> TypeBase:
        """Merge base types according to the strategy."""
        if self.strategy == MergeStrategy.JOIN:
            result = bases[0]
            for b in bases[1:]:
                result = type_join(result, b)
            return result

        if self.strategy == MergeStrategy.MEET:
            result = bases[0]
            for b in bases[1:]:
                result = type_meet(result, b)
            return result

        if self.strategy == MergeStrategy.UNION:
            return UnionType.build(list(bases))

        if self.strategy == MergeStrategy.INTERSECT:
            return IntersectionType.build(list(bases))

        if self.strategy == MergeStrategy.STRICT:
            first = bases[0]
            for b in bases[1:]:
                if b != first:
                    raise ValueError(
                        f"strict merge requires equal base types: "
                        f"{first!r} vs {b!r}"
                    )
            return first

        raise ValueError(f"unknown merge strategy: {self.strategy}")

    def _merge_refinements(
        self,
        refinement_dicts: Sequence[Dict[str, Any]],
    ) -> Dict[str, Any]:
        """Merge site refinement dictionaries.

        Takes the intersection of keys and uses the first value for each key
        (under the assumption that compatible carriers agree on refinement values).
        """
        if not refinement_dicts:
            return {}
        all_keys = set(refinement_dicts[0].keys())
        for rd in refinement_dicts[1:]:
            all_keys &= set(rd.keys())
        merged: Dict[str, Any] = {}
        for key in all_keys:
            values = [rd[key] for rd in refinement_dicts if key in rd]
            if values:
                merged[key] = values[0]
        return merged

    def merge_schemas(self, schemas: Sequence[CarrierSchema]) -> CarrierSchema:
        """Merge multiple schemas."""
        if not schemas:
            return CarrierSchema()
        result = schemas[0]
        for s in schemas[1:]:
            result = result.merge_with(s)
        return result


# ═══════════════════════════════════════════════════════════════════════════════
# Carrier compatibility check
# ═══════════════════════════════════════════════════════════════════════════════


def carriers_compatible(a: CarrierType, b: CarrierType) -> bool:
    """Check whether two carriers are compatible on their overlap.

    Two carriers are compatible if their base types have a common supertype
    and their shared refinements agree.
    """
    from .subtyping import is_subtype
    if not (is_subtype(a.base, b.base) or is_subtype(b.base, a.base)):
        # Check if they share a common upper bound via join
        joined = type_join(a.base, b.base)
        if isinstance(joined, AnyType) and not (
            isinstance(a.base, AnyType) or isinstance(b.base, AnyType)
        ):
            return False
    # Check shared refinements
    shared_keys = set(a.site_refinements.keys()) & set(b.site_refinements.keys())
    for key in shared_keys:
        if a.site_refinements[key] != b.site_refinements[key]:
            return False
    return True


def carrier_from_type(ty: TypeBase, provenance: str = "") -> CarrierType:
    """Create a :class:`CarrierType` from a plain :class:`TypeBase`."""
    if isinstance(ty, RefinementType):
        # Extract refinements from the predicate if possible
        refs: Dict[str, Any] = {}
        from .refinement import ComparisonPred, ComparisonOp, LengthPred
        pred = ty.predicate
        preds = [pred]
        if isinstance(pred, ConjunctionPred):
            preds = list(pred.conjuncts)
        for p in preds:
            if isinstance(p, ComparisonPred):
                if p.op == ComparisonOp.GT and p.rhs == 0:
                    refs["positive"] = True
                elif p.op == ComparisonOp.GE and p.rhs == 0:
                    refs["non_negative"] = True
                elif p.op == ComparisonOp.LE and isinstance(p.rhs, (int, float)):
                    refs["max"] = p.rhs
                elif p.op == ComparisonOp.GE and isinstance(p.rhs, (int, float)):
                    refs["min"] = p.rhs
            elif isinstance(p, LengthPred):
                if p.op == ComparisonOp.GT and p.value == 0:
                    refs["non_empty"] = True
                elif p.op == ComparisonOp.LE:
                    refs["max_length"] = p.value
        return CarrierType(ty.base, refs, provenance)
    if isinstance(ty, QualifiedType):
        refs_q: Dict[str, Any] = {}
        for q in ty.qualifiers:
            refs_q[q.name().lower()] = True
        return CarrierType(ty.base, refs_q, provenance)
    return CarrierType(ty, {}, provenance)
