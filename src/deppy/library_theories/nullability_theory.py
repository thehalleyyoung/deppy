"""Theory Family 3: Nullability & Optionality.

Handles None checks, Optional types, and nullability narrowing.
Forward: narrow Optional[T] to T after ``is not None``.
Backward: require non-None when accessing attributes.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
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
# Nullability state
# ═══════════════════════════════════════════════════════════════════════════════


class NullState(Enum):
    """Nullability state of a value."""
    DEFINITELY_NULL = "null"
    DEFINITELY_NON_NULL = "non_null"
    POSSIBLY_NULL = "nullable"
    UNKNOWN = "unknown"

    @property
    def is_safe(self) -> bool:
        return self == NullState.DEFINITELY_NON_NULL

    @property
    def is_dangerous(self) -> bool:
        return self in (NullState.POSSIBLY_NULL, NullState.UNKNOWN)


def null_state_from_refinements(refs: Dict[str, Any]) -> NullState:
    """Extract nullability state from refinements."""
    if refs.get("non_null") or refs.get("is_not_none"):
        return NullState.DEFINITELY_NON_NULL
    if refs.get("is_none"):
        return NullState.DEFINITELY_NULL
    if refs.get("nullable") or refs.get("optional"):
        return NullState.POSSIBLY_NULL
    return NullState.UNKNOWN


def null_state_to_refinements(state: NullState) -> Dict[str, Any]:
    """Convert nullability state to refinements."""
    if state == NullState.DEFINITELY_NON_NULL:
        return {"non_null": True, "is_not_none": True}
    if state == NullState.DEFINITELY_NULL:
        return {"is_none": True}
    if state == NullState.POSSIBLY_NULL:
        return {"nullable": True}
    return {}


# ═══════════════════════════════════════════════════════════════════════════════
# Nullability lattice operations
# ═══════════════════════════════════════════════════════════════════════════════


def null_meet(a: NullState, b: NullState) -> NullState:
    """Meet in the nullability lattice (intersection/tightest)."""
    if a == b:
        return a
    if a == NullState.DEFINITELY_NULL and b == NullState.DEFINITELY_NON_NULL:
        return NullState.DEFINITELY_NULL  # contradiction -> bottom
    if b == NullState.DEFINITELY_NULL and a == NullState.DEFINITELY_NON_NULL:
        return NullState.DEFINITELY_NULL
    if a == NullState.UNKNOWN:
        return b
    if b == NullState.UNKNOWN:
        return a
    if a == NullState.POSSIBLY_NULL:
        return b
    if b == NullState.POSSIBLY_NULL:
        return a
    return NullState.UNKNOWN


def null_join(a: NullState, b: NullState) -> NullState:
    """Join in the nullability lattice (union/loosest)."""
    if a == b:
        return a
    if a == NullState.UNKNOWN or b == NullState.UNKNOWN:
        return NullState.UNKNOWN
    if (a == NullState.DEFINITELY_NULL and b == NullState.DEFINITELY_NON_NULL) or \
       (b == NullState.DEFINITELY_NULL and a == NullState.DEFINITELY_NON_NULL):
        return NullState.POSSIBLY_NULL
    if NullState.POSSIBLY_NULL in (a, b):
        return NullState.POSSIBLY_NULL
    return NullState.POSSIBLY_NULL


# ═══════════════════════════════════════════════════════════════════════════════
# Optional type analysis
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class OptionalInfo:
    """Information about an Optional[T] type."""
    inner_type: Any = None
    null_state: NullState = NullState.UNKNOWN
    guard_variable: str = ""
    guard_checked: bool = False

    def narrow_non_null(self) -> OptionalInfo:
        return OptionalInfo(
            self.inner_type, NullState.DEFINITELY_NON_NULL,
            self.guard_variable, True,
        )

    def narrow_null(self) -> OptionalInfo:
        return OptionalInfo(
            self.inner_type, NullState.DEFINITELY_NULL,
            self.guard_variable, True,
        )

    def is_safe_to_access(self) -> bool:
        return self.null_state == NullState.DEFINITELY_NON_NULL


def extract_optional_info(section: LocalSection) -> OptionalInfo:
    """Extract optional/nullable info from a section."""
    refs = section.refinements
    inner_type = refs.get("inner_type", refs.get("unwrapped_type", section.carrier_type))
    state = null_state_from_refinements(refs)
    guard_var = refs.get("guard_variable", "")
    guard_checked = refs.get("null_checked", False)
    return OptionalInfo(inner_type, state, guard_var, guard_checked)


# ═══════════════════════════════════════════════════════════════════════════════
# Null-safety operations catalog
# ═══════════════════════════════════════════════════════════════════════════════


_NULL_PRODUCING_OPS: Set[str] = {
    "dict.get", "list.pop", "next", "re.match", "re.search",
    "os.getenv", "getattr_default", "weakref.deref",
}

_NULL_CONSUMING_OPS: Set[str] = {
    "attr_access", "method_call", "subscript", "iter",
    "len", "bool", "str.format",
}

_NULL_SAFE_OPS: Set[str] = {
    "is_none_check", "is_not_none_check", "type_check",
    "id", "repr",
}


def operation_null_safety(op_name: str) -> str:
    """Classify an operation's null safety.

    Returns:
        'safe' - operation handles None
        'produces_null' - operation may produce None
        'requires_non_null' - operation requires non-None input
    """
    if op_name in _NULL_SAFE_OPS:
        return "safe"
    if op_name in _NULL_PRODUCING_OPS:
        return "produces_null"
    if op_name in _NULL_CONSUMING_OPS:
        return "requires_non_null"
    return "unknown"


# ═══════════════════════════════════════════════════════════════════════════════
# NullabilityTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class NullabilityTheoryPack(TheoryPackBase):
    """Theory Family 3: Nullability & Optionality.

    Handles SSA_VALUE, BRANCH_GUARD, ARGUMENT_BOUNDARY, CALL_RESULT, and
    ERROR sites involving Optional types and None checks.
    """

    pack_name = "nullability"
    pack_priority = 20

    _APPLICABLE = frozenset({
        SiteKind.SSA_VALUE,
        SiteKind.BRANCH_GUARD,
        SiteKind.ARGUMENT_BOUNDARY,
        SiteKind.RETURN_OUTPUT_BOUNDARY,
        SiteKind.CALL_RESULT,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        """Resolve nullability at a site."""
        info = extract_optional_info(section)
        refs = section.refinements

        if info.null_state == NullState.DEFINITELY_NON_NULL:
            new_refs = dict(refs)
            new_refs["non_null"] = True
            new_refs.pop("nullable", None)
            new_refs.pop("is_none", None)
            if info.inner_type is not None:
                new_carrier = info.inner_type
            else:
                new_carrier = section.carrier_type

            refined = LocalSection(
                site_id=section.site_id,
                carrier_type=new_carrier,
                refinements=new_refs,
                trust=TrustLevel.TRUSTED_AUTO,
                provenance="nullability: confirmed non-null",
                witnesses=dict(section.witnesses),
            )
            return SolverResult(
                status=SolverStatus.SOLVED,
                section=refined,
                explanation="confirmed non-null",
            )

        if info.null_state == NullState.DEFINITELY_NULL:
            new_refs = dict(refs)
            new_refs["is_none"] = True
            new_refs.pop("non_null", None)
            new_refs.pop("nullable", None)
            refined = LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=TrustLevel.TRUSTED_AUTO,
                provenance="nullability: confirmed null",
                witnesses=dict(section.witnesses),
            )
            return SolverResult(
                status=SolverStatus.SOLVED,
                section=refined,
                explanation="confirmed null",
            )

        op_name = refs.get("operation")
        if op_name is not None:
            safety = operation_null_safety(str(op_name))
            if safety == "requires_non_null" and info.null_state != NullState.DEFINITELY_NON_NULL:
                return SolverResult(
                    status=SolverStatus.REFINED,
                    section=section,
                    constraints_remaining=["requires non-null check"],
                    explanation=f"operation {op_name} requires non-null input",
                    proof_obligations=[f"prove {site.name} is not None"],
                )
            if safety == "produces_null":
                new_refs = dict(refs)
                new_refs["nullable"] = True
                refined = LocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    refinements=new_refs,
                    trust=section.trust,
                    provenance=f"nullability: {op_name} may produce None",
                    witnesses=dict(section.witnesses),
                )
                return SolverResult(
                    status=SolverStatus.REFINED,
                    section=refined,
                    explanation=f"{op_name} produces nullable result",
                )

        if self._is_optional_type(section.carrier_type):
            new_refs = dict(refs)
            new_refs["nullable"] = True
            inner = self._unwrap_optional(section.carrier_type)
            if inner is not None:
                new_refs["inner_type"] = inner
            refined = LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=section.trust,
                provenance="nullability: Optional type detected",
                witnesses=dict(section.witnesses),
            )
            return SolverResult(
                status=SolverStatus.REFINED,
                section=refined,
                explanation="Optional type detected",
            )

        return SolverResult(
            status=SolverStatus.UNCHANGED,
            section=section,
            explanation="no nullability information to refine",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Propagate nullability forward."""
        restricted = morphism.restrict(section)
        info = extract_optional_info(section)

        null_refs = null_state_to_refinements(info.null_state)
        if info.inner_type is not None and info.null_state == NullState.DEFINITELY_NON_NULL:
            null_refs["inner_type"] = info.inner_type
            new_carrier = info.inner_type
        else:
            new_carrier = restricted.carrier_type

        new_refs = merge_refinements(restricted.refinements, null_refs, "meet")

        op_name = None
        if morphism.metadata:
            op_name = morphism.metadata.get("operation")
        if op_name is not None:
            safety = operation_null_safety(str(op_name))
            if safety == "produces_null":
                new_refs["nullable"] = True
                new_refs.pop("non_null", None)
            elif safety == "safe" and info.null_state == NullState.DEFINITELY_NON_NULL:
                new_refs["non_null"] = True

        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=new_carrier,
            refinements=new_refs,
            trust=restricted.trust,
            provenance=f"nullability forward: {info.null_state.value}",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Infer non-null requirements from downstream usage."""
        refs = section.refinements

        required_refs: Dict[str, Any] = {}

        op_name = refs.get("operation")
        if op_name is not None:
            safety = operation_null_safety(str(op_name))
            if safety == "requires_non_null":
                required_refs["non_null"] = True
                required_refs["requires_non_null"] = True

        if refs.get("attr_access") or refs.get("method_call"):
            required_refs["non_null"] = True
            required_refs["requires_non_null"] = True

        if refs.get("subscript") or refs.get("iteration"):
            required_refs["non_null"] = True

        target_null_state = null_state_from_refinements(refs)
        if target_null_state == NullState.DEFINITELY_NON_NULL:
            required_refs["non_null"] = True

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="nullability pullback: requires non-null",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        """Describe the null-safety condition."""
        name = error_site.name
        if "attr" in name.lower():
            return f"{name}: object is not None before attribute access"
        if "call" in name.lower():
            return f"{name}: callable is not None before invocation"
        if "subscript" in name.lower() or "index" in name.lower():
            return f"{name}: container is not None before indexing"
        return f"{name} is not None"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        """Classify a section for null-safety proof purposes."""
        info = extract_optional_info(section)
        if info.null_state == NullState.DEFINITELY_NON_NULL:
            if section.trust == TrustLevel.PROOF_BACKED:
                return BoundaryClassification.FULLY_PROVEN
            if info.guard_checked:
                return BoundaryClassification.CONDITIONALLY_PROVEN
            return BoundaryClassification.RUNTIME_GUARDED
        if info.null_state == NullState.DEFINITELY_NULL:
            return BoundaryClassification.FULLY_PROVEN
        if info.null_state == NullState.POSSIBLY_NULL:
            return BoundaryClassification.REQUIRES_PROOF
        return BoundaryClassification.ASSUMED

    # ── Internal helpers ──────────────────────────────────────────────────

    def _is_optional_type(self, carrier_type: Any) -> bool:
        """Check if a carrier type is Optional."""
        if carrier_type is None:
            return False
        type_str = str(carrier_type)
        return "Optional" in type_str or "NoneType" in type_str

    def _unwrap_optional(self, carrier_type: Any) -> Any:
        """Extract the inner type from Optional[T]."""
        if hasattr(carrier_type, "inner"):
            return carrier_type.inner
        if hasattr(carrier_type, "members"):
            members = carrier_type.members
            if isinstance(members, tuple):
                non_none = [m for m in members if "None" not in str(m)]
                if len(non_none) == 1:
                    return non_none[0]
        return None
