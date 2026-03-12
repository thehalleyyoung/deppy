"""Theory Family 2: Boolean Guard Theory.

Handles guard predicates from if/assert/while conditions.
Forward: narrow types along true/false branches.
Backward: determine which guards are needed for safety.
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
    make_section,
    merge_refinements,
    narrow_section,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Guard representation
# ═══════════════════════════════════════════════════════════════════════════════


class GuardKind(Enum):
    """Classification of guard predicates."""
    IS_NONE = "is_none"
    IS_NOT_NONE = "is_not_none"
    IS_INSTANCE = "isinstance"
    COMPARISON = "comparison"
    TRUTHINESS = "truthiness"
    HAS_ATTR = "hasattr"
    IN_COLLECTION = "in"
    NOT_IN = "not_in"
    CALLABLE_CHECK = "callable"
    BOOLEAN_LITERAL = "literal"
    CONJUNCTION = "and"
    DISJUNCTION = "or"
    NEGATION = "not"


@dataclass(frozen=True)
class Guard:
    """A guard predicate observed at a BRANCH_GUARD site.

    Attributes:
        kind: The kind of guard (isinstance, comparison, etc.)
        variable: The primary variable being tested.
        parameters: Additional data (type name, comparison value, etc.)
        negated: Whether this guard is negated.
    """
    kind: GuardKind
    variable: str
    parameters: Any = None
    negated: bool = False

    def negate(self) -> Guard:
        """Return the negation of this guard."""
        if self.kind == GuardKind.IS_NONE:
            return Guard(GuardKind.IS_NOT_NONE, self.variable, self.parameters)
        if self.kind == GuardKind.IS_NOT_NONE:
            return Guard(GuardKind.IS_NONE, self.variable, self.parameters)
        if self.kind == GuardKind.IN_COLLECTION:
            return Guard(GuardKind.NOT_IN, self.variable, self.parameters)
        if self.kind == GuardKind.NOT_IN:
            return Guard(GuardKind.IN_COLLECTION, self.variable, self.parameters)
        return Guard(self.kind, self.variable, self.parameters, not self.negated)

    def to_refinements(self) -> Dict[str, Any]:
        """Convert guard to refinement entries for the true branch."""
        refs: Dict[str, Any] = {}
        if self.kind == GuardKind.IS_NOT_NONE:
            refs["non_null"] = True
        elif self.kind == GuardKind.IS_NONE:
            refs["is_none"] = True
        elif self.kind == GuardKind.IS_INSTANCE:
            refs["narrowed_type"] = self.parameters
        elif self.kind == GuardKind.TRUTHINESS:
            refs["truthy"] = True
        elif self.kind == GuardKind.HAS_ATTR:
            refs[f"has_attr_{self.parameters}"] = True
        elif self.kind == GuardKind.IN_COLLECTION:
            refs["in_collection"] = self.parameters
        elif self.kind == GuardKind.CALLABLE_CHECK:
            refs["is_callable"] = True
        elif self.kind == GuardKind.COMPARISON:
            if isinstance(self.parameters, dict):
                op = self.parameters.get("op", "")
                value = self.parameters.get("value")
                if op == "==" and value is not None:
                    refs["exact_value"] = value
                elif op == "!=" and value is not None:
                    refs["excluded_value"] = value
                elif op == "<" and isinstance(value, (int, float)):
                    refs["upper_bound"] = value - 1
                elif op == "<=" and isinstance(value, (int, float)):
                    refs["upper_bound"] = value
                elif op == ">" and isinstance(value, (int, float)):
                    refs["lower_bound"] = value + 1
                elif op == ">=" and isinstance(value, (int, float)):
                    refs["lower_bound"] = value
        elif self.kind == GuardKind.BOOLEAN_LITERAL:
            refs["exact_value"] = self.parameters
        if self.negated:
            refs = _negate_refinements(refs)
        return refs

    def false_branch_refinements(self) -> Dict[str, Any]:
        """Refinements for the false branch (guard negation)."""
        return self.negate().to_refinements()


def _negate_refinements(refs: Dict[str, Any]) -> Dict[str, Any]:
    """Negate a set of guard-derived refinements."""
    negated: Dict[str, Any] = {}
    for key, value in refs.items():
        if key == "non_null":
            negated["is_none"] = True
        elif key == "is_none":
            negated["non_null"] = True
        elif key == "truthy":
            negated["falsy"] = True
        elif key == "falsy":
            negated["truthy"] = True
        elif key == "lower_bound" and isinstance(value, (int, float)):
            negated["upper_bound"] = value - 1
        elif key == "upper_bound" and isinstance(value, (int, float)):
            negated["lower_bound"] = value + 1
        elif key == "exact_value":
            negated["excluded_value"] = value
        elif key == "excluded_value":
            negated["exact_value"] = value
        elif key == "in_collection":
            negated["not_in_collection"] = value
        else:
            negated[f"not_{key}"] = value
    return negated


# ═══════════════════════════════════════════════════════════════════════════════
# Guard extraction
# ═══════════════════════════════════════════════════════════════════════════════


def extract_guard(section: LocalSection) -> Optional[Guard]:
    """Extract a Guard from a section's refinements."""
    refs = section.refinements
    guard_kind = refs.get("guard_kind")
    if guard_kind is None:
        if refs.get("non_null"):
            return Guard(GuardKind.IS_NOT_NONE, section.site_id.name)
        if refs.get("is_none"):
            return Guard(GuardKind.IS_NONE, section.site_id.name)
        if refs.get("narrowed_type"):
            return Guard(
                GuardKind.IS_INSTANCE,
                section.site_id.name,
                refs["narrowed_type"],
            )
        return None

    try:
        kind = GuardKind(guard_kind)
    except ValueError:
        return None

    variable = refs.get("guard_variable", section.site_id.name)
    parameters = refs.get("guard_parameters")
    negated = refs.get("guard_negated", False)
    return Guard(kind, variable, parameters, negated)


def guard_to_section(
    guard: Guard,
    site_id: SiteId,
    branch: bool = True,
    trust: TrustLevel = TrustLevel.TRUSTED_AUTO,
) -> LocalSection:
    """Create a section from a guard for the given branch."""
    if branch:
        refs = guard.to_refinements()
    else:
        refs = guard.false_branch_refinements()
    refs["guard_kind"] = guard.kind.value
    refs["guard_variable"] = guard.variable
    refs["guard_parameters"] = guard.parameters
    refs["guard_branch"] = branch
    return LocalSection(
        site_id=site_id,
        carrier_type=None,
        refinements=refs,
        trust=trust,
        provenance=f"guard: {guard.variable} {guard.kind.value} (branch={branch})",
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Compound guard logic
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class CompoundGuard:
    """A compound guard made of multiple sub-guards."""
    op: GuardKind  # CONJUNCTION, DISJUNCTION, or NEGATION
    children: Tuple[Any, ...] = ()  # Guard or CompoundGuard

    def to_refinements(self, branch: bool = True) -> Dict[str, Any]:
        """Flatten compound guard to refinements."""
        if self.op == GuardKind.CONJUNCTION and branch:
            refs: Dict[str, Any] = {}
            for child in self.children:
                if isinstance(child, Guard):
                    refs = merge_refinements(refs, child.to_refinements(), "meet")
                elif isinstance(child, CompoundGuard):
                    refs = merge_refinements(refs, child.to_refinements(True), "meet")
            return refs
        elif self.op == GuardKind.DISJUNCTION and branch:
            all_refs: List[Dict[str, Any]] = []
            for child in self.children:
                if isinstance(child, Guard):
                    all_refs.append(child.to_refinements())
                elif isinstance(child, CompoundGuard):
                    all_refs.append(child.to_refinements(True))
            if all_refs:
                joined: Dict[str, Any] = {}
                for r in all_refs:
                    for k, v in r.items():
                        if k not in joined:
                            joined[k] = v
                return joined
            return {}
        elif self.op == GuardKind.NEGATION:
            if self.children:
                child = self.children[0]
                if isinstance(child, Guard):
                    return child.false_branch_refinements() if branch else child.to_refinements()
                elif isinstance(child, CompoundGuard):
                    return child.to_refinements(not branch)
        return {}


# ═══════════════════════════════════════════════════════════════════════════════
# Required guards analysis
# ═══════════════════════════════════════════════════════════════════════════════


def required_guards_for_safety(error_refs: Dict[str, Any]) -> List[Guard]:
    """Determine which guards would make an error site safe."""
    guards: List[Guard] = []
    if error_refs.get("requires_non_null"):
        var = error_refs.get("variable", "x")
        guards.append(Guard(GuardKind.IS_NOT_NONE, var))
    if error_refs.get("requires_type"):
        var = error_refs.get("variable", "x")
        type_name = error_refs["requires_type"]
        guards.append(Guard(GuardKind.IS_INSTANCE, var, type_name))
    if error_refs.get("requires_non_empty"):
        var = error_refs.get("variable", "x")
        guards.append(Guard(GuardKind.TRUTHINESS, var))
    if error_refs.get("requires_bound"):
        var = error_refs.get("variable", "x")
        bound = error_refs["requires_bound"]
        guards.append(Guard(
            GuardKind.COMPARISON, var,
            {"op": "<", "value": bound},
        ))
    if error_refs.get("requires_in_collection"):
        var = error_refs.get("variable", "x")
        collection = error_refs["requires_in_collection"]
        guards.append(Guard(GuardKind.IN_COLLECTION, var, collection))
    return guards


# ═══════════════════════════════════════════════════════════════════════════════
# BooleanGuardTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class BooleanGuardTheoryPack(TheoryPackBase):
    """Theory Family 2: Boolean Guard Theory.

    Handles BRANCH_GUARD sites. Forward: narrow types along true/false
    branches. Backward: determine which guards are needed for safety.
    """

    pack_name = "boolean_guard"
    pack_priority = 15

    _APPLICABLE = frozenset({
        SiteKind.BRANCH_GUARD,
        SiteKind.SSA_VALUE,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        """Resolve guard information at a branch guard site."""
        guard = extract_guard(section)
        if guard is None:
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="no guard information found",
            )

        branch = section.refinements.get("guard_branch", True)
        if branch:
            new_refs = merge_refinements(
                section.refinements, guard.to_refinements(), "meet"
            )
        else:
            new_refs = merge_refinements(
                section.refinements, guard.false_branch_refinements(), "meet"
            )

        new_refs["_guard_resolved"] = True
        new_refs["_guard_obj"] = guard

        refined = LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=new_refs,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance=f"guard resolved: {guard.kind.value} (branch={branch})",
            witnesses=dict(section.witnesses),
        )
        return SolverResult(
            status=SolverStatus.SOLVED,
            section=refined,
            explanation=f"guard {guard.variable} {guard.kind.value} -> branch={branch}",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Narrow the target section based on the guard at the source."""
        restricted = morphism.restrict(section)

        guard = extract_guard(section)
        if guard is None:
            return restricted

        branch = section.refinements.get("guard_branch", True)
        guard_refs = guard.to_refinements() if branch else guard.false_branch_refinements()

        target_variable = guard.variable
        if morphism.projection:
            for tgt, src in morphism.projection.items():
                if src == target_variable:
                    remapped_refs: Dict[str, Any] = {}
                    for k, v in guard_refs.items():
                        remapped_refs[k] = v
                    guard_refs = remapped_refs
                    break

        new_refs = merge_refinements(restricted.refinements, guard_refs, "meet")

        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance=f"guard narrowed: {guard.kind.value} branch={branch}",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        """Determine required guards from error site requirements."""
        required = required_guards_for_safety(section.refinements)

        pulled_refs: Dict[str, Any] = {}
        for guard in required:
            guard_refs = guard.to_refinements()
            pulled_refs = merge_refinements(pulled_refs, guard_refs, "meet")
            pulled_refs[f"_required_guard_{guard.variable}"] = guard.kind.value

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=pulled_refs,
            trust=TrustLevel.RESIDUAL,
            provenance=f"requires {len(required)} guard(s) for safety",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        """Describe the guard needed for safety."""
        name = error_site.name
        if "none" in name.lower() or "null" in name.lower():
            return f"{name} is not None"
        if "type" in name.lower() or "isinstance" in name.lower():
            return f"isinstance({name}, expected_type)"
        if "bound" in name.lower() or "index" in name.lower():
            return f"0 <= {name} < limit"
        return f"guard condition for {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        """Classify guard-site sections."""
        if section.refinements.get("_guard_resolved"):
            return BoundaryClassification.FULLY_PROVEN
        if section.trust == TrustLevel.TRUSTED_AUTO:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        if section.trust == TrustLevel.ASSUMED:
            return BoundaryClassification.ASSUMED
        guard = extract_guard(section)
        if guard is not None:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        return BoundaryClassification.REQUIRES_PROOF
