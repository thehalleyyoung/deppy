"""Generate contract suggestions from solved sections.

ContractGenerator converts boundary sections (the solved input/output
assignments from the frontier search) into ``@requires`` / ``@ensures``
/ ``@raises`` contract annotations.  These contracts are the user-facing
output of the analysis pipeline.
"""

from __future__ import annotations

import textwrap
from dataclasses import dataclass, field
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
    BoundarySection,
    Cover,
    GlobalSection,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.types.base import (
    ANY_TYPE,
    NEVER_TYPE,
    AnyType,
    CallableType,
    ClassType,
    DictType,
    ListType,
    NeverType,
    OptionalType,
    PrimitiveType,
    SetType,
    TupleType,
    TypeBase,
    UnionType,
)
from deppy.types.refinement import (
    ComparisonOp,
    ComparisonPred,
    ConjunctionPred,
    IsNotNonePred,
    IsNonePred,
    LengthPred,
    Predicate,
    QualifiedType,
    RefinementType,
    TruePred,
)


# ---------------------------------------------------------------------------
# Generated contract data
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ContractClause:
    """A single clause in a generated contract.

    Attributes:
        kind: 'requires', 'ensures', or 'raises'.
        expression: The predicate expression as a string.
        site_id: The site this clause was derived from.
        trust: Trust level of the underlying section.
        is_inferred: Whether this was inferred (vs user-supplied).
    """

    _kind: str
    _expression: str
    _site_id: Optional[SiteId] = None
    _trust: TrustLevel = TrustLevel.TRUSTED_AUTO
    _is_inferred: bool = True

    @property
    def kind(self) -> str:
        return self._kind

    @property
    def expression(self) -> str:
        return self._expression

    @property
    def site_id(self) -> Optional[SiteId]:
        return self._site_id

    @property
    def trust(self) -> TrustLevel:
        return self._trust

    @property
    def is_inferred(self) -> bool:
        return self._is_inferred


@dataclass(frozen=True)
class GeneratedContract:
    """A complete contract for a function or code region.

    Attributes:
        function_name: The function this contract applies to.
        requires: Precondition clauses.
        ensures: Postcondition clauses.
        raises: Exception condition clauses.
        provenance: Where this contract was derived from.
        confidence: Confidence in the correctness of this contract.
    """

    _function_name: str
    _requires: Tuple[ContractClause, ...]
    _ensures: Tuple[ContractClause, ...]
    _raises: Tuple[ContractClause, ...]
    _provenance: str = ""
    _confidence: float = 1.0

    @property
    def function_name(self) -> str:
        return self._function_name

    @property
    def requires(self) -> Tuple[ContractClause, ...]:
        return self._requires

    @property
    def ensures(self) -> Tuple[ContractClause, ...]:
        return self._ensures

    @property
    def raises(self) -> Tuple[ContractClause, ...]:
        return self._raises

    @property
    def provenance(self) -> str:
        return self._provenance

    @property
    def confidence(self) -> float:
        return self._confidence

    @property
    def is_trivial(self) -> bool:
        """True if the contract has no non-trivial clauses."""
        return not self._requires and not self._ensures and not self._raises


# ---------------------------------------------------------------------------
# Type-to-string formatting
# ---------------------------------------------------------------------------

def _type_to_str(t: Any) -> str:
    """Convert a type object to a readable string."""
    if t is None:
        return "Any"
    if isinstance(t, TypeBase):
        return repr(t)
    return str(t)


def _predicate_to_str(pred: Any) -> str:
    """Convert a predicate to a readable string."""
    if pred is None:
        return "True"
    if isinstance(pred, Predicate):
        return repr(pred)
    return str(pred)


def _refinement_to_expr(key: str, value: Any) -> str:
    """Convert a single refinement key-value to an expression string."""
    if key == "non_null" and value:
        return "value is not None"
    if key == "positive" and value:
        return "value > 0"
    if key == "non_negative" and value:
        return "value >= 0"
    if key == "non_empty" and value:
        return "len(value) > 0"
    if key == "sorted" and value:
        return "is_sorted(value)"
    if key == "bounded" and isinstance(value, (list, tuple)) and len(value) == 2:
        return f"{value[0]} <= value <= {value[1]}"
    if key == "max_length" and isinstance(value, int):
        return f"len(value) <= {value}"
    if key == "min_length" and isinstance(value, int):
        return f"len(value) >= {value}"
    if key == "isinstance" and isinstance(value, str):
        return f"isinstance(value, {value})"
    if key == "predicate" and isinstance(value, Predicate):
        return _predicate_to_str(value)
    if isinstance(value, bool):
        return f"{key}" if value else f"not {key}"
    return f"{key} == {value!r}"


def _section_to_type_str(section: LocalSection) -> str:
    """Convert a section's carrier type to a type string."""
    carrier = section.carrier_type
    if carrier is None or isinstance(carrier, AnyType):
        return "Any"
    if isinstance(carrier, RefinementType):
        base_str = _type_to_str(carrier.base)
        pred_str = repr(carrier.predicate)
        return f"{{{carrier.binder}: {base_str} | {pred_str}}}"
    if isinstance(carrier, QualifiedType):
        base_str = _type_to_str(carrier.base)
        quals = ", ".join(q.name() for q in carrier.qualifiers)
        return f"{base_str} @[{quals}]"
    return _type_to_str(carrier)


# ---------------------------------------------------------------------------
# Formatting helpers for @requires, @ensures, @raises
# ---------------------------------------------------------------------------

def _format_requires(
    input_section: LocalSection,
    param_name: Optional[str] = None,
) -> List[str]:
    """Convert an input section to @requires expression strings.

    Extracts type constraints and refinements from the section and
    formats them as precondition expressions.
    """
    expressions: List[str] = []
    name = param_name or _extract_param_name(input_section.site_id)

    carrier = input_section.carrier_type
    if carrier is not None and not isinstance(carrier, AnyType):
        if isinstance(carrier, PrimitiveType):
            expressions.append(f"isinstance({name}, {carrier.kind.value})")
        elif isinstance(carrier, ClassType):
            expressions.append(f"isinstance({name}, {carrier.name})")
        elif isinstance(carrier, UnionType):
            types_str = ", ".join(_type_to_str(m) for m in carrier.members)
            expressions.append(f"isinstance({name}, ({types_str}))")
        elif isinstance(carrier, OptionalType):
            pass
        elif isinstance(carrier, ListType):
            expressions.append(f"isinstance({name}, list)")
        elif isinstance(carrier, DictType):
            expressions.append(f"isinstance({name}, dict)")
        elif isinstance(carrier, RefinementType):
            pred_str = repr(carrier.predicate).replace(
                carrier.binder, name
            )
            expressions.append(pred_str)

    for key, value in sorted(input_section.refinements.items()):
        expr = _refinement_to_expr(key, value).replace("value", name)
        expressions.append(expr)

    return expressions


def _format_ensures(
    output_section: LocalSection,
    return_name: str = "result",
) -> List[str]:
    """Convert an output section to @ensures expression strings."""
    expressions: List[str] = []

    carrier = output_section.carrier_type
    if carrier is not None and not isinstance(carrier, (AnyType, NeverType)):
        if isinstance(carrier, PrimitiveType):
            expressions.append(
                f"isinstance({return_name}, {carrier.kind.value})"
            )
        elif isinstance(carrier, ClassType):
            expressions.append(
                f"isinstance({return_name}, {carrier.name})"
            )
        elif isinstance(carrier, RefinementType):
            pred_str = repr(carrier.predicate).replace(
                carrier.binder, return_name
            )
            expressions.append(pred_str)

    for key, value in sorted(output_section.refinements.items()):
        expr = _refinement_to_expr(key, value).replace(
            "value", return_name
        )
        expressions.append(expr)

    return expressions


def _format_raises(
    error_sections: List[LocalSection],
) -> List[str]:
    """Convert error sections to @raises expression strings."""
    expressions: List[str] = []

    for sec in error_sections:
        if sec.site_id.kind != SiteKind.ERROR:
            continue

        error_name = _extract_error_name(sec)
        condition = _extract_error_condition(sec)

        if condition:
            expressions.append(f"raises {error_name} when {condition}")
        else:
            expressions.append(f"raises {error_name}")

    return expressions


def _extract_param_name(site_id: SiteId) -> str:
    """Extract parameter name from a site ID."""
    name = site_id.name
    parts = name.rsplit(".", 1)
    result = parts[-1] if len(parts) > 1 else name
    parts = result.rsplit(":", 1)
    return parts[-1] if len(parts) > 1 else result


def _extract_error_name(section: LocalSection) -> str:
    """Extract error class name from an error section."""
    carrier = section.carrier_type
    if isinstance(carrier, ClassType):
        return carrier.name
    name = section.site_id.name
    if "Error" in name or "Exception" in name:
        parts = name.split(".")
        for p in parts:
            if "Error" in p or "Exception" in p:
                return p
    return "Exception"


def _extract_error_condition(section: LocalSection) -> str:
    """Extract the condition under which an error is raised."""
    conditions: List[str] = []
    for key, value in section.refinements.items():
        if key == "condition":
            conditions.append(str(value))
        elif key == "predicate" and isinstance(value, Predicate):
            conditions.append(repr(value))
    return " and ".join(conditions) if conditions else ""


def _extract_function_name(cover: Cover) -> str:
    """Extract the function name from a cover's metadata."""
    for sid in cover.input_boundary:
        name = sid.name
        parts = name.split(".")
        if len(parts) >= 2:
            return parts[-2]
        return parts[0]
    for sid in cover.output_boundary:
        name = sid.name
        parts = name.split(".")
        if len(parts) >= 2:
            return parts[-2]
        return parts[0]
    return "unknown_function"


# ---------------------------------------------------------------------------
# ContractGenerator
# ---------------------------------------------------------------------------

class ContractGenerator:
    """Generate contract suggestions from solved boundary sections.

    Converts the solved input/output sections from the frontier search
    into @requires/@ensures/@raises contract annotations.

    Usage::

        gen = ContractGenerator()
        contracts = gen.generate(cover, sections)
        for c in contracts:
            print(c.function_name)
            for r in c.requires:
                print(f"  @requires {r.expression}")
    """

    def __init__(
        self,
        *,
        include_trivial: bool = False,
        min_trust: TrustLevel = TrustLevel.BOUNDED_AUTO,
        include_inferred: bool = True,
    ) -> None:
        self._include_trivial = include_trivial
        self._min_trust = min_trust
        self._include_inferred = include_inferred
        self._trust_order = {
            TrustLevel.PROOF_BACKED: 5,
            TrustLevel.TRUSTED_AUTO: 4,
            TrustLevel.TRACE_BACKED: 3,
            TrustLevel.BOUNDED_AUTO: 2,
            TrustLevel.ASSUMED: 1,
            TrustLevel.RESIDUAL: 0,
        }

    def generate(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[GeneratedContract]:
        """Generate contracts from a cover and its sections.

        Processes each function's input, output, and error sections to
        produce a GeneratedContract.
        """
        func_name = _extract_function_name(cover)

        requires_clauses: List[ContractClause] = []
        for sid in sorted(cover.input_boundary, key=str):
            sec = sections.get(sid)
            if sec is None:
                continue
            if not self._meets_trust(sec.trust):
                continue
            param_name = _extract_param_name(sid)
            exprs = _format_requires(sec, param_name)
            for expr in exprs:
                clause = ContractClause(
                    _kind="requires",
                    _expression=expr,
                    _site_id=sid,
                    _trust=sec.trust,
                    _is_inferred=True,
                )
                requires_clauses.append(clause)

        ensures_clauses: List[ContractClause] = []
        for sid in sorted(cover.output_boundary, key=str):
            sec = sections.get(sid)
            if sec is None:
                continue
            if not self._meets_trust(sec.trust):
                continue
            exprs = _format_ensures(sec)
            for expr in exprs:
                clause = ContractClause(
                    _kind="ensures",
                    _expression=expr,
                    _site_id=sid,
                    _trust=sec.trust,
                    _is_inferred=True,
                )
                ensures_clauses.append(clause)

        error_sections = [
            sections[sid]
            for sid in cover.error_sites
            if sid in sections
        ]
        raises_clauses: List[ContractClause] = []
        raises_exprs = _format_raises(error_sections)
        for expr in raises_exprs:
            clause = ContractClause(
                _kind="raises",
                _expression=expr,
                _is_inferred=True,
            )
            raises_clauses.append(clause)

        contract = GeneratedContract(
            _function_name=func_name,
            _requires=tuple(requires_clauses),
            _ensures=tuple(ensures_clauses),
            _raises=tuple(raises_clauses),
            _provenance=f"generated from cover with {len(cover.sites)} sites",
            _confidence=self._compute_confidence(
                requires_clauses + ensures_clauses + raises_clauses
            ),
        )

        if contract.is_trivial and not self._include_trivial:
            return []

        return [contract]

    def generate_from_global(
        self,
        cover: Cover,
        global_section: GlobalSection,
    ) -> List[GeneratedContract]:
        """Generate contracts from a GlobalSection."""
        return self.generate(cover, global_section.local_sections)

    def _format_requires(
        self,
        input_section: LocalSection,
    ) -> str:
        """Format a single input section as a @requires string."""
        param_name = _extract_param_name(input_section.site_id)
        exprs = _format_requires(input_section, param_name)
        return " and ".join(exprs) if exprs else "True"

    def _format_ensures(
        self,
        output_section: LocalSection,
    ) -> str:
        """Format a single output section as an @ensures string."""
        exprs = _format_ensures(output_section)
        return " and ".join(exprs) if exprs else "True"

    def _format_raises(
        self,
        error_sections: List[LocalSection],
    ) -> str:
        """Format error sections as a @raises string."""
        exprs = _format_raises(error_sections)
        return "; ".join(exprs) if exprs else ""

    def _meets_trust(self, trust: TrustLevel) -> bool:
        """Check if a trust level meets the minimum threshold."""
        return (
            self._trust_order.get(trust, 0)
            >= self._trust_order.get(self._min_trust, 0)
        )

    def _compute_confidence(
        self,
        clauses: List[ContractClause],
    ) -> float:
        """Compute overall confidence from clause trust levels."""
        if not clauses:
            return 1.0
        total = sum(
            self._trust_order.get(c.trust, 0) for c in clauses
        )
        max_possible = len(clauses) * 5
        return total / max(max_possible, 1)

    def format_contract_text(
        self,
        contract: GeneratedContract,
    ) -> str:
        """Format a contract as a human-readable string."""
        lines: List[str] = []
        lines.append(f"Contract for {contract.function_name}:")

        if contract.requires:
            lines.append("  Preconditions:")
            for r in contract.requires:
                trust_str = f" [{r.trust.value}]" if r.trust else ""
                lines.append(f"    @requires {r.expression}{trust_str}")

        if contract.ensures:
            lines.append("  Postconditions:")
            for e in contract.ensures:
                trust_str = f" [{e.trust.value}]" if e.trust else ""
                lines.append(f"    @ensures {e.expression}{trust_str}")

        if contract.raises:
            lines.append("  Exceptions:")
            for x in contract.raises:
                lines.append(f"    @raises {x.expression}")

        lines.append(f"  Confidence: {contract.confidence:.0%}")
        return "\n".join(lines)
