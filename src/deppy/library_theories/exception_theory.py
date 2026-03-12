"""Theory Family 10: Exception Theory.

Error-site viability for each exception type.
Maps operations to potential exceptions.
Forward: propagate error possibility.
Backward: require preconditions to prevent errors.
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
)


# ═══════════════════════════════════════════════════════════════════════════════
# Exception taxonomy
# ═══════════════════════════════════════════════════════════════════════════════


class ExceptionCategory(Enum):
    """High-level categories of Python exceptions."""
    TYPE_ERROR = "TypeError"
    VALUE_ERROR = "ValueError"
    INDEX_ERROR = "IndexError"
    KEY_ERROR = "KeyError"
    ATTRIBUTE_ERROR = "AttributeError"
    NAME_ERROR = "NameError"
    RUNTIME_ERROR = "RuntimeError"
    ZERO_DIVISION = "ZeroDivisionError"
    OVERFLOW_ERROR = "OverflowError"
    STOP_ITERATION = "StopIteration"
    FILE_NOT_FOUND = "FileNotFoundError"
    PERMISSION_ERROR = "PermissionError"
    IMPORT_ERROR = "ImportError"
    OS_ERROR = "OSError"
    ASSERTION_ERROR = "AssertionError"
    NOT_IMPLEMENTED = "NotImplementedError"
    MEMORY_ERROR = "MemoryError"
    RECURSION_ERROR = "RecursionError"
    UNICODE_ERROR = "UnicodeError"
    TIMEOUT_ERROR = "TimeoutError"


@dataclass(frozen=True)
class ExceptionSpec:
    """Specification of a potential exception."""
    category: ExceptionCategory
    message_template: str = ""
    precondition: str = ""
    operation: str = ""
    severity: str = "error"

    def viability_predicate(self) -> str:
        if self.precondition:
            return f"NOT ({self.precondition})"
        return f"no {self.category.value}"


# ═══════════════════════════════════════════════════════════════════════════════
# Operation-to-exception mapping
# ═══════════════════════════════════════════════════════════════════════════════

_OP_EXCEPTIONS: Dict[str, List[ExceptionSpec]] = {
    "__getitem__": [
        ExceptionSpec(ExceptionCategory.INDEX_ERROR, "index out of range",
                     "index >= len(obj) or index < -len(obj)", "__getitem__"),
        ExceptionSpec(ExceptionCategory.KEY_ERROR, "key not found",
                     "key not in dict", "__getitem__"),
        ExceptionSpec(ExceptionCategory.TYPE_ERROR, "unhashable type",
                     "key is not hashable", "__getitem__"),
    ],
    "__setitem__": [
        ExceptionSpec(ExceptionCategory.INDEX_ERROR, "assignment index out of range",
                     "index >= len(obj) or index < -len(obj)", "__setitem__"),
        ExceptionSpec(ExceptionCategory.TYPE_ERROR, "unhashable type",
                     "key is not hashable", "__setitem__"),
    ],
    "__delitem__": [
        ExceptionSpec(ExceptionCategory.INDEX_ERROR, "index out of range",
                     "index >= len(obj)", "__delitem__"),
        ExceptionSpec(ExceptionCategory.KEY_ERROR, "key not found",
                     "key not in dict", "__delitem__"),
    ],
    "__truediv__": [
        ExceptionSpec(ExceptionCategory.ZERO_DIVISION, "division by zero",
                     "divisor == 0", "__truediv__"),
    ],
    "__floordiv__": [
        ExceptionSpec(ExceptionCategory.ZERO_DIVISION, "integer division by zero",
                     "divisor == 0", "__floordiv__"),
    ],
    "__mod__": [
        ExceptionSpec(ExceptionCategory.ZERO_DIVISION, "modulo by zero",
                     "divisor == 0", "__mod__"),
    ],
    "int": [
        ExceptionSpec(ExceptionCategory.VALUE_ERROR, "invalid literal for int()",
                     "string is not a valid integer", "int"),
        ExceptionSpec(ExceptionCategory.TYPE_ERROR, "argument must be string or number",
                     "argument is not numeric or string", "int"),
    ],
    "float": [
        ExceptionSpec(ExceptionCategory.VALUE_ERROR, "could not convert string to float",
                     "string is not a valid float", "float"),
    ],
    "next": [
        ExceptionSpec(ExceptionCategory.STOP_ITERATION, "iterator exhausted",
                     "iterator has no more elements", "next"),
    ],
    "getattr": [
        ExceptionSpec(ExceptionCategory.ATTRIBUTE_ERROR, "object has no attribute",
                     "attribute does not exist on object", "getattr"),
    ],
    "open": [
        ExceptionSpec(ExceptionCategory.FILE_NOT_FOUND, "file not found",
                     "file path does not exist", "open"),
        ExceptionSpec(ExceptionCategory.PERMISSION_ERROR, "permission denied",
                     "insufficient file permissions", "open"),
    ],
    "import": [
        ExceptionSpec(ExceptionCategory.IMPORT_ERROR, "no module named",
                     "module does not exist", "import"),
    ],
    "assert": [
        ExceptionSpec(ExceptionCategory.ASSERTION_ERROR, "assertion failed",
                     "assertion condition is False", "assert"),
    ],
    "list.index": [
        ExceptionSpec(ExceptionCategory.VALUE_ERROR, "is not in list",
                     "element not found in list", "list.index"),
    ],
    "list.remove": [
        ExceptionSpec(ExceptionCategory.VALUE_ERROR, "not in list",
                     "element not found in list", "list.remove"),
    ],
    "dict.pop": [
        ExceptionSpec(ExceptionCategory.KEY_ERROR, "key not found",
                     "key not in dict and no default", "dict.pop"),
    ],
    "list.pop": [
        ExceptionSpec(ExceptionCategory.INDEX_ERROR, "pop from empty list",
                     "list is empty", "list.pop"),
    ],
    "str.index": [
        ExceptionSpec(ExceptionCategory.VALUE_ERROR, "substring not found",
                     "substring not in string", "str.index"),
    ],
    "json.loads": [
        ExceptionSpec(ExceptionCategory.VALUE_ERROR, "invalid JSON",
                     "string is not valid JSON", "json.loads"),
    ],
    "torch.matmul": [
        ExceptionSpec(ExceptionCategory.RUNTIME_ERROR, "shape mismatch",
                     "inner dimensions don't match", "torch.matmul"),
    ],
    "torch.reshape": [
        ExceptionSpec(ExceptionCategory.RUNTIME_ERROR, "shape not compatible",
                     "numel doesn't match", "torch.reshape"),
    ],
}


def exceptions_for_operation(op_name: str) -> List[ExceptionSpec]:
    """Get potential exceptions for a given operation."""
    return _OP_EXCEPTIONS.get(op_name, [])


def precondition_for_exception(spec: ExceptionSpec) -> Dict[str, Any]:
    """Convert an exception's precondition to refinement requirements."""
    refs: Dict[str, Any] = {}
    cat = spec.category

    if cat == ExceptionCategory.INDEX_ERROR:
        refs["requires_bounds_check"] = True
        refs["non_empty"] = True
    elif cat == ExceptionCategory.KEY_ERROR:
        refs["requires_key_check"] = True
    elif cat == ExceptionCategory.ATTRIBUTE_ERROR:
        refs["requires_hasattr_check"] = True
    elif cat == ExceptionCategory.ZERO_DIVISION:
        refs["requires_nonzero_divisor"] = True
        refs["divisor_lower_bound"] = 1
    elif cat == ExceptionCategory.TYPE_ERROR:
        refs["requires_type_check"] = True
    elif cat == ExceptionCategory.VALUE_ERROR:
        refs["requires_value_validation"] = True
    elif cat == ExceptionCategory.STOP_ITERATION:
        refs["requires_has_next_check"] = True
    elif cat == ExceptionCategory.FILE_NOT_FOUND:
        refs["requires_path_exists_check"] = True
    elif cat == ExceptionCategory.ASSERTION_ERROR:
        refs["assertion_condition_required"] = True
    elif cat == ExceptionCategory.OVERFLOW_ERROR:
        refs["requires_overflow_check"] = True

    return refs


# ═══════════════════════════════════════════════════════════════════════════════
# Exception flow tracking
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class ExceptionFlow:
    """Tracks possible exceptions through a computation."""
    possible_exceptions: List[ExceptionSpec] = field(default_factory=list)
    caught_exceptions: Set[str] = field(default_factory=set)
    propagated_exceptions: List[ExceptionSpec] = field(default_factory=list)

    @property
    def uncaught(self) -> List[ExceptionSpec]:
        return [
            e for e in self.possible_exceptions
            if e.category.value not in self.caught_exceptions
        ]

    @property
    def is_safe(self) -> bool:
        return len(self.uncaught) == 0

    def add_exception(self, spec: ExceptionSpec) -> None:
        self.possible_exceptions.append(spec)

    def catch(self, category: str) -> None:
        self.caught_exceptions.add(category)

    def catch_all(self) -> None:
        for e in self.possible_exceptions:
            self.caught_exceptions.add(e.category.value)

    def to_refinements(self) -> Dict[str, Any]:
        return {
            "possible_exceptions": [
                {"category": e.category.value, "operation": e.operation,
                 "precondition": e.precondition}
                for e in self.possible_exceptions
            ],
            "caught_exceptions": list(self.caught_exceptions),
            "is_exception_safe": self.is_safe,
        }

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> ExceptionFlow:
        flow = ExceptionFlow()
        for e in refs.get("possible_exceptions", []):
            if isinstance(e, dict):
                try:
                    cat = ExceptionCategory(e.get("category", "RuntimeError"))
                except ValueError:
                    cat = ExceptionCategory.RUNTIME_ERROR
                flow.add_exception(ExceptionSpec(
                    category=cat,
                    operation=e.get("operation", ""),
                    precondition=e.get("precondition", ""),
                ))
        flow.caught_exceptions = set(refs.get("caught_exceptions", []))
        return flow


# ═══════════════════════════════════════════════════════════════════════════════
# ExceptionTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class ExceptionTheoryPack(TheoryPackBase):
    """Theory Family 10: Exception Theory.

    Maps operations to potential exceptions and determines viability
    predicates for error sites.
    """

    pack_name = "exception"
    pack_priority = 40

    _APPLICABLE = frozenset({
        SiteKind.ERROR,
        SiteKind.SSA_VALUE,
        SiteKind.CALL_RESULT,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        refs = section.refinements
        flow = ExceptionFlow.from_refinements(refs)

        op_name = refs.get("operation") or refs.get("call_target")
        if op_name is not None:
            new_exceptions = exceptions_for_operation(str(op_name))
            for spec in new_exceptions:
                if spec.category.value not in {e.category.value for e in flow.possible_exceptions}:
                    flow.add_exception(spec)

        try_block = refs.get("in_try_block", False)
        except_handlers = refs.get("except_handlers", [])
        if try_block:
            for handler in except_handlers:
                if handler == "Exception" or handler == "BaseException":
                    flow.catch_all()
                else:
                    flow.catch(str(handler))

        new_refs = dict(refs)
        new_refs.update(flow.to_refinements())

        if flow.is_safe:
            return SolverResult(
                status=SolverStatus.SOLVED,
                section=LocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    refinements=new_refs,
                    trust=TrustLevel.BOUNDED_AUTO,
                    provenance="exception: all exceptions handled",
                    witnesses=dict(section.witnesses),
                ),
                explanation="all potential exceptions are caught or prevented",
            )

        uncaught = flow.uncaught
        return SolverResult(
            status=SolverStatus.REFINED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=section.trust,
                provenance=f"exception: {len(uncaught)} uncaught exception(s)",
                witnesses=dict(section.witnesses),
            ),
            constraints_remaining=[
                f"uncaught {e.category.value} from {e.operation}: {e.precondition}"
                for e in uncaught
            ],
            explanation=f"{len(uncaught)} uncaught exception(s)",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        restricted = morphism.restrict(section)
        flow = ExceptionFlow.from_refinements(section.refinements)

        if morphism.metadata:
            try_block = morphism.metadata.get("enters_try", False)
            if try_block:
                handlers = morphism.metadata.get("except_handlers", [])
                for h in handlers:
                    flow.catch(str(h))

        new_refs = merge_refinements(restricted.refinements, flow.to_refinements(), "meet")
        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance="exception forward",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        flow = ExceptionFlow.from_refinements(section.refinements)
        required_refs: Dict[str, Any] = {}

        for exc in flow.uncaught:
            prereqs = precondition_for_exception(exc)
            required_refs = merge_refinements(required_refs, prereqs, "meet")

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="exception pullback: preconditions",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name
        for op_name, specs in _OP_EXCEPTIONS.items():
            if op_name.lower() in name.lower():
                conditions = [s.viability_predicate() for s in specs]
                return " AND ".join(conditions)
        return f"no uncaught exception at {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        flow = ExceptionFlow.from_refinements(section.refinements)
        if flow.is_safe:
            return BoundaryClassification.FULLY_PROVEN
        if flow.uncaught:
            return BoundaryClassification.REQUIRES_PROOF
        return BoundaryClassification.ASSUMED
