"""Theory Family 4: Heap & Protocol Theory.

Handles object field access, protocol conformance, structural subtyping,
and initialization tracking.
Forward: track which fields are initialized.
Backward: require protocol conformance at call sites.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism

from .theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    TheoryPackBase,
    merge_refinements,
    narrow_section,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Field initialization state
# ═══════════════════════════════════════════════════════════════════════════════


class FieldState(Enum):
    """Initialization state of a field."""
    UNINITIALIZED = "uninitialized"
    INITIALIZED = "initialized"
    MAYBE_INITIALIZED = "maybe_initialized"
    READONLY = "readonly"
    DELETED = "deleted"


@dataclass(frozen=True)
class FieldInfo:
    """Information about a single field of an object."""
    name: str
    field_type: Any = None
    state: FieldState = FieldState.UNINITIALIZED
    is_method: bool = False
    is_property: bool = False
    is_class_var: bool = False
    default_value: Any = None
    has_default: bool = False

    def is_accessible(self) -> bool:
        return self.state in (FieldState.INITIALIZED, FieldState.READONLY)

    def is_assignable(self) -> bool:
        return self.state != FieldState.READONLY and self.state != FieldState.DELETED


@dataclass
class ObjectLayout:
    """Tracks the field layout and initialization state of an object.

    This is the primary data structure for heap-protocol analysis.
    """
    class_name: str = ""
    fields: Dict[str, FieldInfo] = field(default_factory=dict)
    bases: List[str] = field(default_factory=list)
    mro: List[str] = field(default_factory=list)
    is_frozen: bool = False
    has_slots: bool = False
    slot_names: Set[str] = field(default_factory=set)

    def get_field(self, name: str) -> Optional[FieldInfo]:
        return self.fields.get(name)

    def set_field(self, name: str, info: FieldInfo) -> None:
        if self.is_frozen and name in self.fields:
            return
        if self.has_slots and name not in self.slot_names:
            return
        self.fields[name] = info

    def mark_initialized(self, name: str, field_type: Any = None) -> None:
        existing = self.fields.get(name)
        if existing:
            self.fields[name] = FieldInfo(
                name=name, field_type=field_type or existing.field_type,
                state=FieldState.INITIALIZED,
                is_method=existing.is_method, is_property=existing.is_property,
                is_class_var=existing.is_class_var,
            )
        else:
            self.fields[name] = FieldInfo(
                name=name, field_type=field_type, state=FieldState.INITIALIZED,
            )

    def mark_deleted(self, name: str) -> None:
        if name in self.fields:
            old = self.fields[name]
            self.fields[name] = FieldInfo(
                name=name, field_type=old.field_type, state=FieldState.DELETED,
            )

    def initialized_fields(self) -> Set[str]:
        return {n for n, f in self.fields.items() if f.is_accessible()}

    def uninitialized_fields(self) -> Set[str]:
        return {n for n, f in self.fields.items() if f.state == FieldState.UNINITIALIZED}

    def all_field_names(self) -> Set[str]:
        return set(self.fields.keys())

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {
            "_class_name": self.class_name,
            "_initialized_fields": self.initialized_fields(),
            "_uninitialized_fields": self.uninitialized_fields(),
            "_field_types": {n: f.field_type for n, f in self.fields.items()},
            "_is_frozen": self.is_frozen,
        }
        if self.has_slots:
            refs["_has_slots"] = True
            refs["_slot_names"] = self.slot_names
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> ObjectLayout:
        layout = ObjectLayout(class_name=refs.get("_class_name", ""))
        layout.is_frozen = refs.get("_is_frozen", False)
        layout.has_slots = refs.get("_has_slots", False)
        layout.slot_names = refs.get("_slot_names", set())
        initialized = refs.get("_initialized_fields", set())
        field_types = refs.get("_field_types", {})
        for name in initialized:
            layout.fields[name] = FieldInfo(
                name=name, field_type=field_types.get(name),
                state=FieldState.INITIALIZED,
            )
        uninitialized = refs.get("_uninitialized_fields", set())
        for name in uninitialized:
            if name not in layout.fields:
                layout.fields[name] = FieldInfo(
                    name=name, field_type=field_types.get(name),
                    state=FieldState.UNINITIALIZED,
                )
        return layout


# ═══════════════════════════════════════════════════════════════════════════════
# Protocol specification
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ProtocolMemberSpec:
    """A member required by a protocol."""
    name: str
    member_type: Any = None
    is_method: bool = False
    is_property: bool = False
    is_optional: bool = False


@dataclass(frozen=True)
class ProtocolSpec:
    """A structural protocol specification."""
    name: str
    members: Tuple[ProtocolMemberSpec, ...] = ()
    is_runtime_checkable: bool = False

    def required_member_names(self) -> FrozenSet[str]:
        return frozenset(m.name for m in self.members if not m.is_optional)

    def all_member_names(self) -> FrozenSet[str]:
        return frozenset(m.name for m in self.members)

    def check_conformance(self, layout: ObjectLayout) -> Tuple[bool, List[str]]:
        violations: List[str] = []
        for member in self.members:
            if member.is_optional:
                continue
            fi = layout.get_field(member.name)
            if fi is None:
                violations.append(f"missing member '{member.name}'")
            elif not fi.is_accessible():
                violations.append(f"member '{member.name}' is not initialized")
            elif member.is_method and not fi.is_method:
                violations.append(f"'{member.name}' should be a method")
        return len(violations) == 0, violations


# ═══════════════════════════════════════════════════════════════════════════════
# Common protocols
# ═══════════════════════════════════════════════════════════════════════════════

ITERABLE_PROTOCOL = ProtocolSpec("Iterable", (
    ProtocolMemberSpec("__iter__", is_method=True),
))

ITERATOR_PROTOCOL = ProtocolSpec("Iterator", (
    ProtocolMemberSpec("__iter__", is_method=True),
    ProtocolMemberSpec("__next__", is_method=True),
))

SIZED_PROTOCOL = ProtocolSpec("Sized", (
    ProtocolMemberSpec("__len__", is_method=True),
))

CONTAINER_PROTOCOL = ProtocolSpec("Container", (
    ProtocolMemberSpec("__contains__", is_method=True),
))

HASHABLE_PROTOCOL = ProtocolSpec("Hashable", (
    ProtocolMemberSpec("__hash__", is_method=True),
))

CALLABLE_PROTOCOL = ProtocolSpec("Callable", (
    ProtocolMemberSpec("__call__", is_method=True),
))

CONTEXT_MANAGER_PROTOCOL = ProtocolSpec("ContextManager", (
    ProtocolMemberSpec("__enter__", is_method=True),
    ProtocolMemberSpec("__exit__", is_method=True),
))

ASYNC_ITERABLE_PROTOCOL = ProtocolSpec("AsyncIterable", (
    ProtocolMemberSpec("__aiter__", is_method=True),
))

SUPPORTS_INT_PROTOCOL = ProtocolSpec("SupportsInt", (
    ProtocolMemberSpec("__int__", is_method=True),
))

SUPPORTS_FLOAT_PROTOCOL = ProtocolSpec("SupportsFloat", (
    ProtocolMemberSpec("__float__", is_method=True),
))

SUPPORTS_BYTES_PROTOCOL = ProtocolSpec("SupportsBytes", (
    ProtocolMemberSpec("__bytes__", is_method=True),
))

SUPPORTS_ABS_PROTOCOL = ProtocolSpec("SupportsAbs", (
    ProtocolMemberSpec("__abs__", is_method=True),
))

_COMMON_PROTOCOLS: Dict[str, ProtocolSpec] = {
    "Iterable": ITERABLE_PROTOCOL,
    "Iterator": ITERATOR_PROTOCOL,
    "Sized": SIZED_PROTOCOL,
    "Container": CONTAINER_PROTOCOL,
    "Hashable": HASHABLE_PROTOCOL,
    "Callable": CALLABLE_PROTOCOL,
    "ContextManager": CONTEXT_MANAGER_PROTOCOL,
    "AsyncIterable": ASYNC_ITERABLE_PROTOCOL,
    "SupportsInt": SUPPORTS_INT_PROTOCOL,
    "SupportsFloat": SUPPORTS_FLOAT_PROTOCOL,
    "SupportsBytes": SUPPORTS_BYTES_PROTOCOL,
    "SupportsAbs": SUPPORTS_ABS_PROTOCOL,
}


def lookup_protocol(name: str) -> Optional[ProtocolSpec]:
    return _COMMON_PROTOCOLS.get(name)


# ═══════════════════════════════════════════════════════════════════════════════
# Structural subtyping
# ═══════════════════════════════════════════════════════════════════════════════


def structural_subtype_check(
    layout: ObjectLayout,
    required_fields: Set[str],
) -> Tuple[bool, Set[str]]:
    """Check structural subtyping: layout has all required fields initialized."""
    initialized = layout.initialized_fields()
    missing = required_fields - initialized
    return len(missing) == 0, missing


def protocol_conformance_check(
    layout: ObjectLayout,
    protocol: ProtocolSpec,
) -> Tuple[bool, List[str]]:
    """Full protocol conformance check."""
    return protocol.check_conformance(layout)


# ═══════════════════════════════════════════════════════════════════════════════
# HeapProtocolTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class HeapProtocolTheoryPack(TheoryPackBase):
    """Theory Family 4: Heap & Protocol Theory.

    Handles HEAP_PROTOCOL, SSA_VALUE, ARGUMENT_BOUNDARY, and ERROR sites
    involving object layout, field access, and protocol conformance.
    """

    pack_name = "heap_protocol"
    pack_priority = 30

    _APPLICABLE = frozenset({
        SiteKind.HEAP_PROTOCOL,
        SiteKind.SSA_VALUE,
        SiteKind.ARGUMENT_BOUNDARY,
        SiteKind.RETURN_OUTPUT_BOUNDARY,
        SiteKind.CALL_RESULT,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        """Resolve field initialization and protocol conformance."""
        refs = section.refinements

        if "_class_name" not in refs and "_initialized_fields" not in refs:
            if not self._looks_like_object_section(section):
                return SolverResult(
                    status=SolverStatus.UNCHANGED,
                    section=section,
                    explanation="not a heap/protocol section",
                )

        layout = ObjectLayout.from_refinements(refs)

        required_protocol = refs.get("_required_protocol")
        if required_protocol is not None:
            if isinstance(required_protocol, str):
                proto = lookup_protocol(required_protocol)
            elif isinstance(required_protocol, ProtocolSpec):
                proto = required_protocol
            else:
                proto = None

            if proto is not None:
                conforms, violations = proto.check_conformance(layout)
                new_refs = dict(refs)
                new_refs["_protocol_conforms"] = conforms
                new_refs["_protocol_violations"] = violations
                new_refs.update(layout.to_refinements())

                if not conforms:
                    return SolverResult(
                        status=SolverStatus.REFINED,
                        section=LocalSection(
                            site_id=section.site_id,
                            carrier_type=section.carrier_type,
                            refinements=new_refs,
                            trust=section.trust,
                            provenance=f"protocol check: {len(violations)} violation(s)",
                            witnesses=dict(section.witnesses),
                        ),
                        constraints_remaining=[
                            f"protocol violation: {v}" for v in violations
                        ],
                        explanation=f"protocol {proto.name}: {len(violations)} violation(s)",
                    )
                return SolverResult(
                    status=SolverStatus.SOLVED,
                    section=LocalSection(
                        site_id=section.site_id,
                        carrier_type=section.carrier_type,
                        refinements=new_refs,
                        trust=TrustLevel.BOUNDED_AUTO,
                        provenance=f"protocol {proto.name}: conforms",
                        witnesses=dict(section.witnesses),
                    ),
                    explanation=f"protocol {proto.name}: conforms",
                )

        field_access = refs.get("_field_access")
        if field_access is not None:
            fi = layout.get_field(str(field_access))
            new_refs = dict(refs)
            if fi is not None and fi.is_accessible():
                new_refs["_field_accessible"] = True
                new_refs["_field_type"] = fi.field_type
                new_refs.update(layout.to_refinements())
                return SolverResult(
                    status=SolverStatus.SOLVED,
                    section=LocalSection(
                        site_id=section.site_id,
                        carrier_type=fi.field_type or section.carrier_type,
                        refinements=new_refs,
                        trust=TrustLevel.BOUNDED_AUTO,
                        provenance=f"field access: {field_access} accessible",
                        witnesses=dict(section.witnesses),
                    ),
                    explanation=f"field {field_access} is initialized",
                )
            else:
                new_refs["_field_accessible"] = False
                new_refs.update(layout.to_refinements())
                return SolverResult(
                    status=SolverStatus.REFINED,
                    section=LocalSection(
                        site_id=section.site_id,
                        carrier_type=section.carrier_type,
                        refinements=new_refs,
                        trust=section.trust,
                        provenance=f"field access: {field_access} not accessible",
                        witnesses=dict(section.witnesses),
                    ),
                    constraints_remaining=[
                        f"field '{field_access}' not initialized",
                    ],
                    explanation=f"field {field_access} not initialized",
                )

        new_refs = dict(refs)
        new_refs.update(layout.to_refinements())
        return SolverResult(
            status=SolverStatus.REFINED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=section.trust,
                provenance="heap layout resolved",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"layout: {len(layout.initialized_fields())} initialized fields",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Propagate field initialization forward."""
        restricted = morphism.restrict(section)
        refs = section.refinements

        init_fields = refs.get("_initialized_fields", set())
        field_types = refs.get("_field_types", {})

        if morphism.metadata:
            new_field = morphism.metadata.get("field_write")
            if new_field is not None:
                init_fields = set(init_fields) | {new_field}
                write_type = morphism.metadata.get("field_write_type")
                if write_type is not None:
                    field_types = dict(field_types)
                    field_types[new_field] = write_type

            deleted_field = morphism.metadata.get("field_delete")
            if deleted_field is not None:
                init_fields = set(init_fields) - {deleted_field}

        new_refs = dict(restricted.refinements)
        new_refs["_initialized_fields"] = init_fields
        new_refs["_field_types"] = field_types

        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance="heap forward: field state propagated",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Infer required fields/protocol from downstream usage."""
        refs = section.refinements
        required_refs: Dict[str, Any] = {}

        field_access = refs.get("_field_access")
        if field_access is not None:
            required_refs[f"_requires_field_{field_access}"] = True
            required_init = set(refs.get("_initialized_fields", set()))
            required_init.add(str(field_access))
            required_refs["_required_initialized_fields"] = required_init

        protocol = refs.get("_required_protocol")
        if protocol is not None:
            required_refs["_required_protocol"] = protocol

        violations = refs.get("_protocol_violations", [])
        for v in violations:
            required_refs[f"_fix_violation_{v}"] = True

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="heap pullback: field/protocol requirements",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name
        if "attr" in name.lower():
            return f"object has attribute '{name.split('.')[-1]}'"
        if "protocol" in name.lower():
            return f"object conforms to required protocol"
        if "init" in name.lower():
            return f"field is initialized before access"
        return f"heap safety for {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        refs = section.refinements
        if refs.get("_protocol_conforms") is True:
            return BoundaryClassification.FULLY_PROVEN
        if refs.get("_field_accessible") is True:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        if refs.get("_protocol_violations"):
            return BoundaryClassification.INCONSISTENT
        if section.trust == TrustLevel.ASSUMED:
            return BoundaryClassification.ASSUMED
        return BoundaryClassification.REQUIRES_PROOF

    # ── Internal helpers ──────────────────────────────────────────────────

    def _looks_like_object_section(self, section: LocalSection) -> bool:
        refs = section.refinements
        heap_keys = {
            "_class_name", "_initialized_fields", "_field_access",
            "_required_protocol", "_field_types", "_is_frozen",
        }
        return bool(heap_keys & set(refs.keys()))
