"""Subtyping checker for DepPy's type system.

Implements a complete subtyping relation covering:
- Primitive types (with numeric widening).
- Container types (covariance, contravariance, invariance).
- Union and intersection types.
- Refinement types (generating verification conditions).
- Dependent function (Pi) and pair (Sigma) types.
- Structural (protocol) subtyping.
- Tensor subtyping (shape, dtype, device compatibility).
- Top (Any) and bottom (Never) types.
"""
from __future__ import annotations

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
)

from .base import (
    TypeBase,
    PrimitiveType,
    PrimitiveKind,
    AnyType,
    NeverType,
    ListType,
    DictType,
    TupleType,
    SetType,
    FrozenSetType,
    OptionalType,
    UnionType,
    IntersectionType,
    CallableType,
    ClassType,
    ProtocolType,
    ProtocolMember,
    ModuleType,
    LiteralType,
    TypeAliasType,
    TensorType,
    ANY_TYPE,
    NEVER_TYPE,
    NONE_TYPE,
    _NUMERIC_ORDER,
)
from .refinement import (
    RefinementType,
    QualifiedType,
    Predicate,
    TruePred,
    FalsePred,
    ComparisonPred,
    ConjunctionPred,
    ImplicationPred,
    ComparisonOp,
)
from .dependent import (
    PiType,
    SigmaType,
    IndexedFamily,
    WitnessType,
    IdentityType,
    ForallType,
    ExistsType,
    DependentRecordType,
    MultiPiType,
)
from .variables import (
    TypeVariable,
    RowVariable,
    SkolemVariable,
    ExistentialVariable,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Verification conditions
# ═══════════════════════════════════════════════════════════════════════════════


class VCKind(Enum):
    """Kind of verification condition."""

    PREDICATE_IMPLICATION = auto()
    TYPE_EQUALITY = auto()
    SUBTYPE_OBLIGATION = auto()
    WELL_FORMEDNESS = auto()


@dataclass(frozen=True)
class VerificationCondition:
    """A proof obligation generated during subtype checking.

    Attributes:
        kind: The category of the VC.
        description: Human-readable description.
        antecedent: Assumed predicates (context).
        consequent: What must be proven.
        source_sub: The sub-type that generated this VC.
        source_sup: The super-type.
    """

    kind: VCKind
    description: str
    antecedent: Optional[Predicate] = None
    consequent: Optional[Predicate] = None
    source_sub: Optional[TypeBase] = None
    source_sup: Optional[TypeBase] = None

    def __repr__(self) -> str:
        return f"VC({self.kind.name}: {self.description})"


# ═══════════════════════════════════════════════════════════════════════════════
# Subtyping result
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class SubtypingResult:
    """Result of a subtype check.

    Attributes:
        is_subtype: ``True`` when sub <: sup holds (possibly modulo VCs).
        evidence: An optional explanation or coercion witness.
        verification_conditions: Proof obligations that must be discharged
            externally (e.g. by an SMT solver) for the result to hold.
        trace: Human-readable derivation trace.
    """

    is_subtype: bool
    evidence: Optional[Any] = None
    verification_conditions: List[VerificationCondition] = field(default_factory=list)
    trace: List[str] = field(default_factory=list)

    @staticmethod
    def yes(evidence: Any = None, trace: str = "") -> SubtypingResult:
        """Construct a successful result."""
        return SubtypingResult(
            is_subtype=True,
            evidence=evidence,
            trace=[trace] if trace else [],
        )

    @staticmethod
    def no(reason: str = "") -> SubtypingResult:
        """Construct a failed result."""
        return SubtypingResult(
            is_subtype=False,
            evidence=reason,
            trace=[reason] if reason else [],
        )

    @staticmethod
    def conditional(
        vcs: List[VerificationCondition],
        trace: str = "",
    ) -> SubtypingResult:
        """Result that holds if all VCs are discharged."""
        return SubtypingResult(
            is_subtype=True,
            verification_conditions=vcs,
            trace=[trace] if trace else [],
        )

    def and_then(self, other: SubtypingResult) -> SubtypingResult:
        """Combine two results conjunctively."""
        if not self.is_subtype:
            return self
        if not other.is_subtype:
            return other
        return SubtypingResult(
            is_subtype=True,
            evidence=(self.evidence, other.evidence),
            verification_conditions=self.verification_conditions + other.verification_conditions,
            trace=self.trace + other.trace,
        )

    def __bool__(self) -> bool:
        return self.is_subtype


# ═══════════════════════════════════════════════════════════════════════════════
# Subtyping checker
# ═══════════════════════════════════════════════════════════════════════════════


class SubtypingChecker:
    """Complete subtyping checker for the DepPy type system.

    Usage::

        checker = SubtypingChecker()
        result = checker.check(sub_type, super_type)
        if result:
            print("sub <: sup")
    """

    def __init__(self, *, max_depth: int = 100) -> None:
        self._max_depth = max_depth
        self._assumption_stack: List[Tuple[TypeBase, TypeBase]] = []

    # ── Main entry point ───────────────────────────────────────────────────

    def check(self, sub: TypeBase, sup: TypeBase, *, depth: int = 0) -> SubtypingResult:
        """Check whether *sub* <: *sup*.

        Returns a :class:`SubtypingResult` describing the outcome.
        """
        if depth > self._max_depth:
            return SubtypingResult.no("max subtyping depth exceeded")

        # Reflexivity
        if sub == sup:
            return SubtypingResult.yes(trace=f"{sub!r} <: {sup!r} by reflexivity")

        # Assumption (co-inductive hypothesis for recursive types)
        for s, t in self._assumption_stack:
            if s == sub and t == sup:
                return SubtypingResult.yes(trace="by assumption (co-induction)")

        # Top and bottom
        if isinstance(sup, AnyType):
            return SubtypingResult.yes(trace=f"{sub!r} <: Any")
        if isinstance(sub, NeverType):
            return SubtypingResult.yes(trace=f"Never <: {sup!r}")
        if isinstance(sub, AnyType) and not isinstance(sup, AnyType):
            return SubtypingResult.no(f"Any is not a subtype of {sup!r}")
        if isinstance(sup, NeverType) and not isinstance(sub, NeverType):
            return SubtypingResult.no(f"{sub!r} is not a subtype of Never")

        # Resolve aliases
        if isinstance(sub, TypeAliasType):
            return self.check(sub.resolve(), sup, depth=depth + 1)
        if isinstance(sup, TypeAliasType):
            return self.check(sub, sup.resolve(), depth=depth + 1)

        # Type variables
        if isinstance(sub, TypeVariable):
            return self.check(sub.upper_bound, sup, depth=depth + 1)
        if isinstance(sup, TypeVariable):
            return self.check(sub, sup.lower_bound, depth=depth + 1)

        # Union: sub <: Union[...] if sub <: any member
        if isinstance(sup, UnionType):
            return self._check_sub_union_sup(sub, sup, depth)

        # Union: Union[...] <: sup if every member <: sup
        if isinstance(sub, UnionType):
            return self._check_union_sub(sub, sup, depth)

        # Intersection: sub <: T1 & T2 if sub <: T1 and sub <: T2
        if isinstance(sup, IntersectionType):
            return self._check_sub_intersection_sup(sub, sup, depth)

        # Intersection: T1 & T2 <: sup if T1 <: sup or T2 <: sup
        if isinstance(sub, IntersectionType):
            return self._check_intersection_sub(sub, sup, depth)

        # Optional
        if isinstance(sub, OptionalType) and isinstance(sup, OptionalType):
            return self.check(sub.inner, sup.inner, depth=depth + 1)
        if isinstance(sup, OptionalType):
            # T <: Optional[U] if T <: U or T <: NoneType
            r = self.check(sub, sup.inner, depth=depth + 1)
            if r:
                return r
            return self.check(sub, NONE_TYPE, depth=depth + 1)

        # Refinement types
        if isinstance(sub, RefinementType) or isinstance(sup, RefinementType):
            return self._check_refinement(sub, sup, depth)

        # Qualified types
        if isinstance(sub, QualifiedType) or isinstance(sup, QualifiedType):
            return self._check_qualified(sub, sup, depth)

        # Dependent types
        if isinstance(sub, PiType) and isinstance(sup, PiType):
            return self._check_pi(sub, sup, depth)
        if isinstance(sub, SigmaType) and isinstance(sup, SigmaType):
            return self._check_sigma(sub, sup, depth)
        if isinstance(sub, ForallType) and isinstance(sup, ForallType):
            return self._check_forall(sub, sup, depth)
        if isinstance(sub, ExistsType) and isinstance(sup, ExistsType):
            return self._check_exists(sub, sup, depth)

        # Witness / Identity
        if isinstance(sub, WitnessType) and isinstance(sup, WitnessType):
            return self.check(sub.value_type, sup.value_type, depth=depth + 1)
        if isinstance(sub, WitnessType):
            return self.check(sub.value_type, sup, depth=depth + 1)
        if isinstance(sub, IdentityType) and isinstance(sup, IdentityType):
            return self._check_identity(sub, sup, depth)

        # Literal <: base
        if isinstance(sub, LiteralType):
            return self.check(sub.inferred_base_type(), sup, depth=depth + 1)

        # Primitives
        if isinstance(sub, PrimitiveType) and isinstance(sup, PrimitiveType):
            return self._check_primitive(sub, sup)

        # Containers
        if isinstance(sub, ListType) and isinstance(sup, ListType):
            return self.check(sub.element, sup.element, depth=depth + 1)
        if isinstance(sub, SetType) and isinstance(sup, SetType):
            return self.check(sub.element, sup.element, depth=depth + 1)
        if isinstance(sub, FrozenSetType) and isinstance(sup, FrozenSetType):
            return self.check(sub.element, sup.element, depth=depth + 1)
        if isinstance(sub, DictType) and isinstance(sup, DictType):
            return self._check_dict(sub, sup, depth)
        if isinstance(sub, TupleType) and isinstance(sup, TupleType):
            return self._check_tuple(sub, sup, depth)

        # Callable
        if isinstance(sub, CallableType) and isinstance(sup, CallableType):
            return self._check_callable(sub, sup, depth)

        # Pi <-> Callable interop
        if isinstance(sub, PiType) and isinstance(sup, CallableType):
            return self._check_pi_callable(sub, sup, depth)
        if isinstance(sub, CallableType) and isinstance(sup, PiType):
            return self._check_callable_pi(sub, sup, depth)

        # Protocol structural subtyping
        if isinstance(sup, ProtocolType):
            return self._check_structural(sub, sup, depth)

        # ClassType subtyping via bases
        if isinstance(sub, ClassType) and isinstance(sup, ClassType):
            return self._check_class(sub, sup, depth)

        # Tensor subtyping
        if isinstance(sub, TensorType) and isinstance(sup, TensorType):
            return self._check_tensor(sub, sup, depth)

        # Dependent record subtyping
        if isinstance(sub, DependentRecordType) and isinstance(sup, DependentRecordType):
            return self._check_dep_record(sub, sup, depth)

        # Indexed family subtyping
        if isinstance(sub, IndexedFamily) and isinstance(sup, IndexedFamily):
            return self._check_indexed_family(sub, sup, depth)

        # MultiPiType: desugar
        if isinstance(sub, MultiPiType):
            return self.check(sub.to_nested(), sup, depth=depth + 1)
        if isinstance(sup, MultiPiType):
            return self.check(sub, sup.to_nested(), depth=depth + 1)

        return SubtypingResult.no(
            f"no subtyping rule for {type(sub).__name__} <: {type(sup).__name__}"
        )

    # ── Primitive subtyping ────────────────────────────────────────────────

    def _check_primitive(
        self, sub: PrimitiveType, sup: PrimitiveType
    ) -> SubtypingResult:
        if sub.kind == sup.kind:
            return SubtypingResult.yes(trace=f"{sub!r} == {sup!r}")
        # bool <: int <: float <: complex
        os = _NUMERIC_ORDER.get(sub.kind)
        ot = _NUMERIC_ORDER.get(sup.kind)
        if os is not None and ot is not None and os <= ot:
            return SubtypingResult.yes(
                trace=f"{sub!r} <: {sup!r} by numeric widening"
            )
        return SubtypingResult.no(f"{sub!r} is not a subtype of {sup!r}")

    # ── Container subtyping ────────────────────────────────────────────────

    def _check_dict(
        self, sub: DictType, sup: DictType, depth: int
    ) -> SubtypingResult:
        # Dicts are invariant in key, covariant in value for read-only
        # We model as covariant for both in a read-only context
        key_result = self.check(sub.key, sup.key, depth=depth + 1)
        if not key_result:
            return SubtypingResult.no(
                f"Dict key: {sub.key!r} is not a subtype of {sup.key!r}"
            )
        val_result = self.check(sub.value, sup.value, depth=depth + 1)
        if not val_result:
            return SubtypingResult.no(
                f"Dict value: {sub.value!r} is not a subtype of {sup.value!r}"
            )
        return key_result.and_then(val_result)

    def _check_tuple(
        self, sub: TupleType, sup: TupleType, depth: int
    ) -> SubtypingResult:
        # Both variadic
        if sub.variadic and sup.variadic:
            return self.check(sub.elements[0], sup.elements[0], depth=depth + 1)
        # Fixed <: variadic: each element must be subtype of the variadic element
        if not sub.variadic and sup.variadic and len(sup.elements) == 1:
            result = SubtypingResult.yes()
            for i, elem in enumerate(sub.elements):
                r = self.check(elem, sup.elements[0], depth=depth + 1)
                result = result.and_then(r)
                if not result:
                    return result
            return result
        # Both fixed: lengths must match, element-wise
        if not sub.variadic and not sup.variadic:
            if len(sub.elements) != len(sup.elements):
                return SubtypingResult.no(
                    f"tuple length mismatch: {len(sub.elements)} vs {len(sup.elements)}"
                )
            result = SubtypingResult.yes()
            for i, (se, te) in enumerate(zip(sub.elements, sup.elements)):
                r = self.check(se, te, depth=depth + 1)
                result = result.and_then(r)
                if not result:
                    return result
            return result
        return SubtypingResult.no("variadic tuple is not a subtype of fixed tuple")

    # ── Callable subtyping ─────────────────────────────────────────────────

    def _check_callable(
        self, sub: CallableType, sup: CallableType, depth: int
    ) -> SubtypingResult:
        if len(sub.param_types) != len(sup.param_types):
            return SubtypingResult.no(
                f"callable arity mismatch: {len(sub.param_types)} vs {len(sup.param_types)}"
            )
        result = SubtypingResult.yes()
        # Parameters are contravariant: sup.param <: sub.param
        for i, (sp, tp) in enumerate(zip(sub.param_types, sup.param_types)):
            r = self.check(tp, sp, depth=depth + 1)
            if not r:
                return SubtypingResult.no(
                    f"callable param {i}: contravariance check failed"
                )
            result = result.and_then(r)
        # Return type is covariant
        r = self.check(sub.return_type, sup.return_type, depth=depth + 1)
        return result.and_then(r)

    # ── Pi type subtyping ──────────────────────────────────────────────────

    def _check_pi(
        self, sub: PiType, sup: PiType, depth: int
    ) -> SubtypingResult:
        # Contravariant in domain: sup.param_type <: sub.param_type
        dom_result = self.check(sup.param_type, sub.param_type, depth=depth + 1)
        if not dom_result:
            return SubtypingResult.no("Pi domain: contravariance check failed")
        # Covariant in codomain (under the assumption x : sup.param_type)
        # We assume the parameter and check the return types
        self._assumption_stack.append((sub, sup))
        try:
            cod_result = self.check(sub.return_type, sup.return_type, depth=depth + 1)
        finally:
            self._assumption_stack.pop()
        return dom_result.and_then(cod_result)

    def _check_pi_callable(
        self, sub: PiType, sup: CallableType, depth: int
    ) -> SubtypingResult:
        if sup.arity != 1:
            return SubtypingResult.no("Pi type has one parameter; callable arity mismatch")
        # Domain contravariant
        dom = self.check(sup.param_types[0], sub.param_type, depth=depth + 1)
        if not dom:
            return dom
        # Codomain covariant (non-dependent approximation)
        cod = self.check(sub.return_type, sup.return_type, depth=depth + 1)
        return dom.and_then(cod)

    def _check_callable_pi(
        self, sub: CallableType, sup: PiType, depth: int
    ) -> SubtypingResult:
        if sub.arity != 1:
            return SubtypingResult.no("callable arity != 1 for Pi comparison")
        dom = self.check(sup.param_type, sub.param_types[0], depth=depth + 1)
        if not dom:
            return dom
        cod = self.check(sub.return_type, sup.return_type, depth=depth + 1)
        return dom.and_then(cod)

    # ── Sigma type subtyping ───────────────────────────────────────────────

    def _check_sigma(
        self, sub: SigmaType, sup: SigmaType, depth: int
    ) -> SubtypingResult:
        # Covariant in both components
        fst = self.check(sub.fst_type, sup.fst_type, depth=depth + 1)
        if not fst:
            return fst
        snd = self.check(sub.snd_type, sup.snd_type, depth=depth + 1)
        return fst.and_then(snd)

    # ── Forall / Exists subtyping ──────────────────────────────────────────

    def _check_forall(
        self, sub: ForallType, sup: ForallType, depth: int
    ) -> SubtypingResult:
        # ∀α.A <: ∀β.B  when  [β/α]A <: B  (up to alpha renaming)
        renamed = sub.body.substitute({sub.var_name: TypeVariable(sup.var_name)})
        return self.check(renamed, sup.body, depth=depth + 1)

    def _check_exists(
        self, sub: ExistsType, sup: ExistsType, depth: int
    ) -> SubtypingResult:
        renamed = sub.body.substitute({sub.var_name: TypeVariable(sup.var_name)})
        return self.check(renamed, sup.body, depth=depth + 1)

    # ── Identity type subtyping ────────────────────────────────────────────

    def _check_identity(
        self, sub: IdentityType, sup: IdentityType, depth: int
    ) -> SubtypingResult:
        carrier = self.check(sub.carrier, sup.carrier, depth=depth + 1)
        if not carrier:
            return carrier
        if sub.lhs != sup.lhs or sub.rhs != sup.rhs:
            return SubtypingResult.no("identity type endpoints differ")
        return carrier

    # ── Union / Intersection helpers ───────────────────────────────────────

    def _check_sub_union_sup(
        self, sub: TypeBase, sup: UnionType, depth: int
    ) -> SubtypingResult:
        for member in sup.members:
            r = self.check(sub, member, depth=depth + 1)
            if r:
                return r
        return SubtypingResult.no(
            f"{sub!r} is not a subtype of any member of {sup!r}"
        )

    def _check_union_sub(
        self, sub: UnionType, sup: TypeBase, depth: int
    ) -> SubtypingResult:
        result = SubtypingResult.yes()
        for member in sub.members:
            r = self.check(member, sup, depth=depth + 1)
            if not r:
                return SubtypingResult.no(
                    f"union member {member!r} is not a subtype of {sup!r}"
                )
            result = result.and_then(r)
        return result

    def _check_sub_intersection_sup(
        self, sub: TypeBase, sup: IntersectionType, depth: int
    ) -> SubtypingResult:
        result = SubtypingResult.yes()
        for member in sup.members:
            r = self.check(sub, member, depth=depth + 1)
            if not r:
                return SubtypingResult.no(
                    f"{sub!r} is not a subtype of intersection member {member!r}"
                )
            result = result.and_then(r)
        return result

    def _check_intersection_sub(
        self, sub: IntersectionType, sup: TypeBase, depth: int
    ) -> SubtypingResult:
        for member in sub.members:
            r = self.check(member, sup, depth=depth + 1)
            if r:
                return r
        return SubtypingResult.no(
            f"no member of {sub!r} is a subtype of {sup!r}"
        )

    # ── Refinement subtyping ──────────────────────────────────────────────

    def _check_refinement(
        self, sub: TypeBase, sup: TypeBase, depth: int
    ) -> SubtypingResult:
        sub_base: TypeBase
        sub_pred: Optional[Predicate]
        sup_base: TypeBase
        sup_pred: Optional[Predicate]

        if isinstance(sub, RefinementType):
            sub_base = sub.base
            sub_pred = sub.predicate
        else:
            sub_base = sub
            sub_pred = None

        if isinstance(sup, RefinementType):
            sup_base = sup.base
            sup_pred = sup.predicate
        else:
            sup_base = sup
            sup_pred = None

        # Base type must be a subtype
        base_result = self.check(sub_base, sup_base, depth=depth + 1)
        if not base_result:
            return base_result

        # If sup has no predicate, any sub is fine
        if sup_pred is None:
            return base_result

        # If sup has a predicate but sub doesn't, we generate a VC
        if sub_pred is None:
            vc = VerificationCondition(
                kind=VCKind.PREDICATE_IMPLICATION,
                description=f"must prove {sup_pred!r} without refinement on sub",
                antecedent=TruePred(),
                consequent=sup_pred,
                source_sub=sub,
                source_sup=sup,
            )
            return SubtypingResult.conditional([vc],
                trace=f"refinement VC: True ⇒ {sup_pred!r}")

        # Both have predicates: sub_pred ⇒ sup_pred
        # Try syntactic implication check first
        if sub_pred == sup_pred:
            return base_result

        # Trivial cases
        if isinstance(sup_pred, TruePred):
            return base_result
        if isinstance(sub_pred, FalsePred):
            return base_result  # vacuously true

        # Generate a VC
        vc = VerificationCondition(
            kind=VCKind.PREDICATE_IMPLICATION,
            description=f"must prove {sub_pred!r} ⇒ {sup_pred!r}",
            antecedent=sub_pred,
            consequent=sup_pred,
            source_sub=sub,
            source_sup=sup,
        )
        result = base_result.and_then(
            SubtypingResult.conditional(
                [vc],
                trace=f"refinement VC: {sub_pred!r} ⇒ {sup_pred!r}",
            )
        )
        return result

    def check_refinement(
        self, sub: RefinementType, sup: RefinementType
    ) -> SubtypingResult:
        """Public API for refinement subtype checking."""
        return self._check_refinement(sub, sup, depth=0)

    # ── Qualified type subtyping ──────────────────────────────────────────

    def _check_qualified(
        self, sub: TypeBase, sup: TypeBase, depth: int
    ) -> SubtypingResult:
        # Strip qualifiers and convert to refinement for checking
        if isinstance(sub, QualifiedType) and isinstance(sup, QualifiedType):
            base_r = self.check(sub.base, sup.base, depth=depth + 1)
            if not base_r:
                return base_r
            # Check that sub has at least all qualifiers of sup
            sup_quals = set(sup.qualifiers)
            sub_quals = set(sub.qualifiers)
            missing = sup_quals - sub_quals
            if not missing:
                return base_r
            # Convert missing qualifiers to VCs
            vcs: list[VerificationCondition] = []
            for q in missing:
                vcs.append(VerificationCondition(
                    kind=VCKind.PREDICATE_IMPLICATION,
                    description=f"sub must satisfy qualifier {q.name()}",
                    source_sub=sub,
                    source_sup=sup,
                ))
            return base_r.and_then(SubtypingResult.conditional(vcs))

        if isinstance(sub, QualifiedType):
            return self.check(sub.base, sup, depth=depth + 1)

        if isinstance(sup, QualifiedType):
            base_r = self.check(sub, sup.base, depth=depth + 1)
            if not base_r:
                return base_r
            vcs = [
                VerificationCondition(
                    kind=VCKind.PREDICATE_IMPLICATION,
                    description=f"must prove qualifier {q.name()} for {sub!r}",
                    source_sub=sub,
                    source_sup=sup,
                )
                for q in sup.qualifiers
            ]
            return base_r.and_then(SubtypingResult.conditional(vcs))

        return SubtypingResult.no("qualified type check: unreachable")

    # ── Structural (protocol) subtyping ────────────────────────────────────

    def _check_structural(
        self, sub: TypeBase, sup: ProtocolType, depth: int
    ) -> SubtypingResult:
        """Check whether *sub* structurally satisfies protocol *sup*."""
        # Gather the members of sub
        sub_members: Dict[str, TypeBase] = {}
        if isinstance(sub, ProtocolType):
            sub_members = {m.name: m.type for m in sub.members}
        elif isinstance(sub, ClassType):
            # For ClassType, we'd need method/attribute info — approximate
            # by checking if it's a known subclass
            # In a full system this would consult a class hierarchy table
            return SubtypingResult.no(
                f"structural check of ClassType against Protocol "
                f"requires member information"
            )
        elif isinstance(sub, DependentRecordType):
            sub_members = {n: t for n, t in sub.fields}
        else:
            return SubtypingResult.no(
                f"{type(sub).__name__} cannot structurally satisfy Protocol"
            )

        result = SubtypingResult.yes()
        sup_dict = sup.member_dict()
        for name, required in sup_dict.items():
            provided = sub_members.get(name)
            if provided is None:
                return SubtypingResult.no(
                    f"protocol member '{name}' not found in {sub!r}"
                )
            r = self.check(provided, required.type, depth=depth + 1)
            if not r:
                return SubtypingResult.no(
                    f"protocol member '{name}': {provided!r} is not a subtype of {required.type!r}"
                )
            result = result.and_then(r)
        return result

    def check_structural(
        self, sub: TypeBase, sup: ProtocolType
    ) -> SubtypingResult:
        """Public API for structural subtype checking."""
        return self._check_structural(sub, sup, depth=0)

    # ── Class subtyping ────────────────────────────────────────────────────

    def _check_class(
        self, sub: ClassType, sup: ClassType, depth: int
    ) -> SubtypingResult:
        # Same name (and module)
        if sub.name == sup.name and sub.module == sup.module:
            if len(sub.type_args) != len(sup.type_args):
                return SubtypingResult.no("class type argument count mismatch")
            result = SubtypingResult.yes()
            for sa, ta in zip(sub.type_args, sup.type_args):
                r = self.check(sa, ta, depth=depth + 1)
                result = result.and_then(r)
                if not result:
                    return result
            return result
        # Check base classes transitively
        for base in sub.bases:
            r = self.check(base, sup, depth=depth + 1)
            if r:
                return r
        return SubtypingResult.no(
            f"{sub.qualified_name} is not a subclass of {sup.qualified_name}"
        )

    # ── Tensor subtyping ──────────────────────────────────────────────────

    def _check_tensor(
        self, sub: TensorType, sup: TensorType, depth: int
    ) -> SubtypingResult:
        if sub.framework != sup.framework:
            return SubtypingResult.no(
                f"tensor framework mismatch: {sub.framework} vs {sup.framework}"
            )
        # dtype: if sup specifies, sub must match
        if sup.dtype is not None and sub.dtype is not None:
            if sub.dtype != sup.dtype:
                return SubtypingResult.no(
                    f"tensor dtype mismatch: {sub.dtype} vs {sup.dtype}"
                )
        # device: if sup specifies, sub must match
        if sup.device is not None and sub.device is not None:
            if sub.device != sup.device:
                return SubtypingResult.no(
                    f"tensor device mismatch: {sub.device} vs {sup.device}"
                )
        # shape: if sup specifies, sub must be compatible
        if sup.shape is not None:
            if sub.shape is None:
                return SubtypingResult.no(
                    "sub tensor has unknown shape, sup requires known shape"
                )
            if len(sub.shape) != len(sup.shape):
                return SubtypingResult.no(
                    f"tensor rank mismatch: {len(sub.shape)} vs {len(sup.shape)}"
                )
            vcs: list[VerificationCondition] = []
            for i, (sd, td) in enumerate(zip(sub.shape, sup.shape)):
                if isinstance(sd, int) and isinstance(td, int):
                    if sd != td:
                        return SubtypingResult.no(
                            f"tensor dim {i} mismatch: {sd} vs {td}"
                        )
                elif isinstance(td, str):
                    # Symbolic dim in sup — always ok (sup is more general)
                    pass
                elif isinstance(sd, str):
                    # sub is symbolic, sup is concrete — needs VC
                    vcs.append(VerificationCondition(
                        kind=VCKind.TYPE_EQUALITY,
                        description=f"tensor dim {i}: {sd} must equal {td}",
                        source_sub=sub,
                        source_sup=sup,
                    ))
            if vcs:
                return SubtypingResult.conditional(
                    vcs, trace="tensor shape VCs"
                )
        return SubtypingResult.yes(trace="tensor subtype OK")

    def check_dependent(self, sub: PiType, sup: PiType) -> SubtypingResult:
        """Public API for dependent function subtype checking."""
        return self._check_pi(sub, sup, depth=0)

    # ── Dependent record subtyping ─────────────────────────────────────────

    def _check_dep_record(
        self, sub: DependentRecordType, sup: DependentRecordType, depth: int,
    ) -> SubtypingResult:
        # Width subtyping: sub must have at least the fields of sup
        sub_fields = dict(sub.fields)
        result = SubtypingResult.yes()
        for name, sup_ty in sup.fields:
            sub_ty = sub_fields.get(name)
            if sub_ty is None:
                return SubtypingResult.no(
                    f"record field '{name}' missing in sub"
                )
            r = self.check(sub_ty, sup_ty, depth=depth + 1)
            if not r:
                return SubtypingResult.no(
                    f"record field '{name}': {sub_ty!r} not <: {sup_ty!r}"
                )
            result = result.and_then(r)
        return result

    # ── Indexed family subtyping ───────────────────────────────────────────

    def _check_indexed_family(
        self, sub: IndexedFamily, sup: IndexedFamily, depth: int,
    ) -> SubtypingResult:
        # Index domains must be compatible, bodies must be subtypes
        idx = self.check(sub.index_type, sup.index_type, depth=depth + 1)
        if not idx:
            return idx
        body = self.check(sub.body, sup.body, depth=depth + 1)
        return idx.and_then(body)


# ═══════════════════════════════════════════════════════════════════════════════
# Convenience functions
# ═══════════════════════════════════════════════════════════════════════════════

_DEFAULT_CHECKER = SubtypingChecker()


def is_subtype(sub: TypeBase, sup: TypeBase) -> bool:
    """Quick check: is *sub* a subtype of *sup*?"""
    return _DEFAULT_CHECKER.check(sub, sup).is_subtype


def check_subtype(sub: TypeBase, sup: TypeBase) -> SubtypingResult:
    """Full check returning a :class:`SubtypingResult`."""
    return _DEFAULT_CHECKER.check(sub, sup)


def are_equivalent(a: TypeBase, b: TypeBase) -> bool:
    """Check type equivalence: *a* <: *b* and *b* <: *a*."""
    return is_subtype(a, b) and is_subtype(b, a)
