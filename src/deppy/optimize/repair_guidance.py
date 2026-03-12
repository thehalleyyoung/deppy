"""Suggest code repairs for obstructions.

Given the obstruction basis (non-trivial H^1 classes), RepairGuidance
analyzes each obstruction and produces actionable repair suggestions:

- **Missing guard**: a branch guard is needed to narrow types.
- **Type mismatch**: two sites carry incompatible types on an overlap.
- **Bounds violation**: a refinement predicate (e.g. x > 0) is violated.

Each suggestion includes a code snippet, confidence score, and source location.
"""

from __future__ import annotations

import re
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
    Cover,
    LocalSection,
    ObstructionData,
    RepairSuggestion as CoreRepairSuggestion,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.types.base import (
    ANY_TYPE,
    NEVER_TYPE,
    AnyType,
    NeverType,
    OptionalType,
    TypeBase,
    UnionType,
)


# ---------------------------------------------------------------------------
# Data types for repair guidance
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SourceLocation:
    """Location in source code for a repair suggestion."""

    _file: str
    _line: int
    _col: int
    _end_line: Optional[int] = None
    _end_col: Optional[int] = None

    @property
    def file(self) -> str:
        return self._file

    @property
    def line(self) -> int:
        return self._line

    @property
    def col(self) -> int:
        return self._col

    @property
    def end_line(self) -> Optional[int]:
        return self._end_line

    @property
    def end_col(self) -> Optional[int]:
        return self._end_col

    def pretty(self) -> str:
        base = f"{self._file}:{self._line}:{self._col}"
        if self._end_line is not None:
            base += f"-{self._end_line}"
            if self._end_col is not None:
                base += f":{self._end_col}"
        return base


@dataclass(frozen=True)
class RepairSuggestion:
    """A concrete repair suggestion for an obstruction.

    Attributes:
        description: Human-readable explanation of the fix.
        code_snippet: Example code that would resolve the issue.
        confidence: Confidence score in [0, 1].
        location: Optional source-code location for the fix.
        category: Classification of the repair type.
        affected_sites: Sites that this repair would modify.
        priority: Ordering priority (lower = more urgent).
    """

    _description: str
    _code_snippet: str
    _confidence: float
    _location: Optional[SourceLocation] = None
    _category: str = "general"
    _affected_sites: FrozenSet[SiteId] = field(default_factory=frozenset)
    _priority: int = 5

    @property
    def description(self) -> str:
        return self._description

    @property
    def code_snippet(self) -> str:
        return self._code_snippet

    @property
    def confidence(self) -> float:
        return self._confidence

    @property
    def location(self) -> Optional[SourceLocation]:
        return self._location

    @property
    def category(self) -> str:
        return self._category

    @property
    def affected_sites(self) -> FrozenSet[SiteId]:
        return self._affected_sites

    @property
    def priority(self) -> int:
        return self._priority


# ---------------------------------------------------------------------------
# Classification of obstruction kinds
# ---------------------------------------------------------------------------

class _ObstructionKind:
    """Classification labels for obstruction root causes."""

    MISSING_GUARD = "missing_guard"
    TYPE_MISMATCH = "type_mismatch"
    BOUNDS_VIOLATION = "bounds_violation"
    NONE_SAFETY = "none_safety"
    MISSING_ANNOTATION = "missing_annotation"
    UNREACHABLE_ERROR = "unreachable_error"
    SHAPE_MISMATCH = "shape_mismatch"
    PROTOCOL_VIOLATION = "protocol_violation"
    UNKNOWN = "unknown"


def _classify_obstruction(obs: ObstructionData) -> str:
    """Classify an obstruction by analyzing its explanation and sections."""
    explanation = obs.explanation.lower()

    if "guard" in explanation or "branch" in explanation or "narrowing" in explanation:
        return _ObstructionKind.MISSING_GUARD

    if "none" in explanation or "optional" in explanation or "nullable" in explanation:
        return _ObstructionKind.NONE_SAFETY

    if "bound" in explanation or "range" in explanation or "overflow" in explanation:
        return _ObstructionKind.BOUNDS_VIOLATION

    if "shape" in explanation or "dimension" in explanation or "tensor" in explanation:
        return _ObstructionKind.SHAPE_MISMATCH

    if "protocol" in explanation or "interface" in explanation or "method" in explanation:
        return _ObstructionKind.PROTOCOL_VIOLATION

    if "unreachable" in explanation or "dead" in explanation:
        return _ObstructionKind.UNREACHABLE_ERROR

    if "annotation" in explanation or "missing type" in explanation:
        return _ObstructionKind.MISSING_ANNOTATION

    if "mismatch" in explanation or "incompatible" in explanation or "conflict" in explanation:
        return _ObstructionKind.TYPE_MISMATCH

    return _ObstructionKind.UNKNOWN


def _extract_variable_name(site_id: SiteId) -> str:
    """Extract a likely variable name from a site identifier."""
    name = site_id.name
    parts = name.split(".")
    if len(parts) >= 2:
        return parts[-1]
    parts = name.split(":")
    if len(parts) >= 2:
        return parts[-1]
    return name


def _extract_location(obs: ObstructionData) -> Optional[SourceLocation]:
    """Extract the best source location from an obstruction's conflict data."""
    for overlap_a, overlap_b in obs.conflicting_overlaps:
        if overlap_a.source_location is not None:
            loc = overlap_a.source_location
            return SourceLocation(
                _file=loc[0], _line=loc[1], _col=loc[2]
            )
        if overlap_b.source_location is not None:
            loc = overlap_b.source_location
            return SourceLocation(
                _file=loc[0], _line=loc[1], _col=loc[2]
            )
    return None


def _type_name(t: Any) -> str:
    """Get a readable name from a carrier type."""
    if t is None:
        return "Unknown"
    if isinstance(t, TypeBase):
        return repr(t)
    return str(t)


# ---------------------------------------------------------------------------
# Individual repair strategies
# ---------------------------------------------------------------------------

def _fix_missing_guard(obs: ObstructionData) -> RepairSuggestion:
    """Suggest adding a type guard to resolve a missing-guard obstruction.

    Analyzes the conflicting overlaps to determine what guard condition
    would prevent the type error.
    """
    var_names: List[str] = []
    type_names: List[str] = []
    affected: Set[SiteId] = set()

    for a_id, b_id in obs.conflicting_overlaps:
        var_names.append(_extract_variable_name(a_id))
        affected.add(a_id)
        affected.add(b_id)

    if not var_names:
        var_names = ["x"]

    primary_var = var_names[0]

    guard_conditions: List[str] = []
    for a_id, b_id in obs.conflicting_overlaps:
        if a_id.kind == SiteKind.BRANCH_GUARD:
            guard_conditions.append(
                f"isinstance({primary_var}, expected_type)"
            )
        elif a_id.kind == SiteKind.ARGUMENT_BOUNDARY:
            guard_conditions.append(f"{primary_var} is not None")
        else:
            guard_conditions.append(
                f"isinstance({primary_var}, expected_type)"
            )

    if not guard_conditions:
        guard_conditions = [f"isinstance({primary_var}, expected_type)"]

    guard = guard_conditions[0]
    snippet = (
        f"if {guard}:\n"
        f"    # handle the guarded case\n"
        f"    ...\n"
        f"else:\n"
        f"    raise TypeError(f\"Expected appropriate type for {primary_var}\")"
    )

    confidence = 0.75
    if len(obs.conflicting_overlaps) == 1:
        confidence = 0.85

    return RepairSuggestion(
        _description=(
            f"Add a type guard for '{primary_var}' to disambiguate "
            f"the conflicting type assignments at the overlap."
        ),
        _code_snippet=snippet,
        _confidence=confidence,
        _location=_extract_location(obs),
        _category=_ObstructionKind.MISSING_GUARD,
        _affected_sites=frozenset(affected),
        _priority=2,
    )


def _fix_type_mismatch(obs: ObstructionData) -> RepairSuggestion:
    """Suggest a fix for a type mismatch between overlapping sites."""
    affected: Set[SiteId] = set()
    type_details: List[str] = []

    for a_id, b_id in obs.conflicting_overlaps:
        affected.add(a_id)
        affected.add(b_id)
        type_details.append(f"  Site {a_id.name} vs {b_id.name}")

    details_str = "\n".join(type_details) if type_details else "  (unknown sites)"

    if obs.conflicting_overlaps:
        first_a, first_b = obs.conflicting_overlaps[0]
        var_a = _extract_variable_name(first_a)
        var_b = _extract_variable_name(first_b)
    else:
        var_a = "x"
        var_b = "y"

    has_return = any(
        sid.kind == SiteKind.RETURN_OUTPUT_BOUNDARY
        for pair in obs.conflicting_overlaps
        for sid in pair
    )

    if has_return:
        snippet = (
            f"# Ensure consistent return types across all branches:\n"
            f"def function(...) -> ExpectedReturnType:\n"
            f"    if condition:\n"
            f"        return value_a  # type: ExpectedReturnType\n"
            f"    else:\n"
            f"        return value_b  # type: ExpectedReturnType"
        )
        description = (
            "Ensure all return paths produce the same type. "
            "The current code returns different types on different branches."
        )
    else:
        snippet = (
            f"# Ensure '{var_a}' has a consistent type:\n"
            f"if isinstance({var_a}, TypeA):\n"
            f"    {var_a} = convert_to_common({var_a})  # normalize type\n"
            f"# or use a Union type annotation:\n"
            f"# {var_a}: Union[TypeA, TypeB] = ..."
        )
        description = (
            f"Resolve the type mismatch for '{var_a}' by either "
            f"normalizing to a common type or widening the annotation "
            f"to a Union."
        )

    confidence = 0.70
    if len(obs.conflicting_overlaps) <= 2:
        confidence = 0.80

    return RepairSuggestion(
        _description=description,
        _code_snippet=snippet,
        _confidence=confidence,
        _location=_extract_location(obs),
        _category=_ObstructionKind.TYPE_MISMATCH,
        _affected_sites=frozenset(affected),
        _priority=3,
    )


def _fix_bounds_violation(obs: ObstructionData) -> RepairSuggestion:
    """Suggest a fix for a bounds/range violation."""
    affected: Set[SiteId] = set()
    for a_id, b_id in obs.conflicting_overlaps:
        affected.add(a_id)
        affected.add(b_id)

    var_name = "value"
    if obs.conflicting_overlaps:
        var_name = _extract_variable_name(obs.conflicting_overlaps[0][0])

    bound_info = _extract_bound_info(obs.explanation)
    lower = bound_info.get("lower", "MIN")
    upper = bound_info.get("upper", "MAX")

    snippet = (
        f"# Clamp {var_name} to valid range [{lower}, {upper}]:\n"
        f"if {var_name} < {lower}:\n"
        f"    raise ValueError(f\"{var_name} must be >= {lower}, got {{{var_name}}}\")\n"
        f"if {var_name} > {upper}:\n"
        f"    raise ValueError(f\"{var_name} must be <= {upper}, got {{{var_name}}}\")\n"
        f"# Or clamp: {var_name} = max({lower}, min({var_name}, {upper}))"
    )

    return RepairSuggestion(
        _description=(
            f"Add bounds checking for '{var_name}'. The value may "
            f"exceed the expected range [{lower}, {upper}]."
        ),
        _code_snippet=snippet,
        _confidence=0.80,
        _location=_extract_location(obs),
        _category=_ObstructionKind.BOUNDS_VIOLATION,
        _affected_sites=frozenset(affected),
        _priority=2,
    )


def _fix_none_safety(obs: ObstructionData) -> RepairSuggestion:
    """Suggest a fix for None-safety violations."""
    affected: Set[SiteId] = set()
    for a_id, b_id in obs.conflicting_overlaps:
        affected.add(a_id)
        affected.add(b_id)

    var_name = "value"
    if obs.conflicting_overlaps:
        var_name = _extract_variable_name(obs.conflicting_overlaps[0][0])

    snippet = (
        f"# Guard against None before use:\n"
        f"if {var_name} is None:\n"
        f"    raise ValueError(\"{var_name} must not be None\")\n"
        f"# Now {var_name} is narrowed to non-None type\n"
        f"result = {var_name}.method()  # safe to call"
    )

    return RepairSuggestion(
        _description=(
            f"Add a None check for '{var_name}' before use. "
            f"The value may be None at this point, but is used "
            f"as if it were non-None."
        ),
        _code_snippet=snippet,
        _confidence=0.90,
        _location=_extract_location(obs),
        _category=_ObstructionKind.NONE_SAFETY,
        _affected_sites=frozenset(affected),
        _priority=1,
    )


def _fix_shape_mismatch(obs: ObstructionData) -> RepairSuggestion:
    """Suggest a fix for tensor shape mismatches."""
    affected: Set[SiteId] = set()
    for a_id, b_id in obs.conflicting_overlaps:
        affected.add(a_id)
        affected.add(b_id)

    snippet = (
        "# Reshape tensors to compatible shapes:\n"
        "tensor_a = tensor_a.reshape(expected_shape)\n"
        "# Or verify shapes match:\n"
        "assert tensor_a.shape == tensor_b.shape, \\\n"
        '    f"Shape mismatch: {tensor_a.shape} vs {tensor_b.shape}"'
    )

    return RepairSuggestion(
        _description=(
            "Resolve tensor shape mismatch by reshaping or "
            "verifying that shapes are compatible before the operation."
        ),
        _code_snippet=snippet,
        _confidence=0.65,
        _location=_extract_location(obs),
        _category=_ObstructionKind.SHAPE_MISMATCH,
        _affected_sites=frozenset(affected),
        _priority=3,
    )


def _fix_protocol_violation(obs: ObstructionData) -> RepairSuggestion:
    """Suggest a fix for protocol/interface violations."""
    affected: Set[SiteId] = set()
    for a_id, b_id in obs.conflicting_overlaps:
        affected.add(a_id)
        affected.add(b_id)

    snippet = (
        "# Implement the required protocol methods:\n"
        "class MyClass:\n"
        "    def required_method(self, ...) -> ReturnType:\n"
        "        ...\n"
        "\n"
        "# Or use a Protocol type hint:\n"
        "from typing import Protocol\n"
        "\n"
        "class MyProtocol(Protocol):\n"
        "    def required_method(self, ...) -> ReturnType: ..."
    )

    return RepairSuggestion(
        _description=(
            "Implement the required protocol methods. The object does "
            "not satisfy the structural protocol expected at this site."
        ),
        _code_snippet=snippet,
        _confidence=0.60,
        _location=_extract_location(obs),
        _category=_ObstructionKind.PROTOCOL_VIOLATION,
        _affected_sites=frozenset(affected),
        _priority=4,
    )


def _fix_missing_annotation(obs: ObstructionData) -> RepairSuggestion:
    """Suggest adding a type annotation."""
    affected: Set[SiteId] = set()
    for a_id, b_id in obs.conflicting_overlaps:
        affected.add(a_id)
        affected.add(b_id)

    var_name = "x"
    if obs.conflicting_overlaps:
        var_name = _extract_variable_name(obs.conflicting_overlaps[0][0])

    snippet = (
        f"# Add explicit type annotation:\n"
        f"{var_name}: ExpectedType = ...  # specify the type\n"
        f"\n"
        f"# For function parameters:\n"
        f"def func({var_name}: ExpectedType) -> ReturnType:\n"
        f"    ..."
    )

    return RepairSuggestion(
        _description=(
            f"Add a type annotation for '{var_name}'. "
            f"The type cannot be inferred at this site."
        ),
        _code_snippet=snippet,
        _confidence=0.70,
        _location=_extract_location(obs),
        _category=_ObstructionKind.MISSING_ANNOTATION,
        _affected_sites=frozenset(affected),
        _priority=5,
    )


def _fix_generic(obs: ObstructionData) -> RepairSuggestion:
    """Generic fallback repair suggestion."""
    affected: Set[SiteId] = set()
    for a_id, b_id in obs.conflicting_overlaps:
        affected.add(a_id)
        affected.add(b_id)

    snippet = (
        "# Review the conflicting type assignments:\n"
        "# Ensure types are consistent across the overlap region.\n"
        "# Possible fixes:\n"
        "#   1. Add a type guard (isinstance check)\n"
        "#   2. Widen the type annotation to a Union\n"
        "#   3. Add an explicit type assertion\n"
        "#   4. Refactor to avoid the type conflict"
    )

    return RepairSuggestion(
        _description=(
            f"Type conflict detected: {obs.explanation}. "
            f"Review the code to ensure types are consistent."
        ),
        _code_snippet=snippet,
        _confidence=0.40,
        _location=_extract_location(obs),
        _category=_ObstructionKind.UNKNOWN,
        _affected_sites=frozenset(affected),
        _priority=6,
    )


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _extract_bound_info(explanation: str) -> Dict[str, str]:
    """Extract bound information from an obstruction explanation string."""
    result: Dict[str, str] = {}
    lower_match = re.search(r"(?:lower|min|>=?)\s*(-?\d+(?:\.\d+)?)", explanation)
    if lower_match:
        result["lower"] = lower_match.group(1)
    upper_match = re.search(r"(?:upper|max|<=?)\s*(-?\d+(?:\.\d+)?)", explanation)
    if upper_match:
        result["upper"] = upper_match.group(1)
    range_match = re.search(
        r"\[(-?\d+(?:\.\d+)?)\s*,\s*(-?\d+(?:\.\d+)?)\]", explanation
    )
    if range_match:
        result.setdefault("lower", range_match.group(1))
        result.setdefault("upper", range_match.group(2))
    return result


def _compute_repair_confidence(
    obs: ObstructionData,
    kind: str,
) -> float:
    """Adjust confidence based on obstruction characteristics."""
    base_confidence: Dict[str, float] = {
        _ObstructionKind.MISSING_GUARD: 0.80,
        _ObstructionKind.TYPE_MISMATCH: 0.70,
        _ObstructionKind.BOUNDS_VIOLATION: 0.80,
        _ObstructionKind.NONE_SAFETY: 0.90,
        _ObstructionKind.SHAPE_MISMATCH: 0.65,
        _ObstructionKind.PROTOCOL_VIOLATION: 0.60,
        _ObstructionKind.MISSING_ANNOTATION: 0.70,
        _ObstructionKind.UNREACHABLE_ERROR: 0.50,
        _ObstructionKind.UNKNOWN: 0.40,
    }
    conf = base_confidence.get(kind, 0.50)
    n_conflicts = len(obs.conflicting_overlaps)
    if n_conflicts == 1:
        conf = min(1.0, conf + 0.05)
    elif n_conflicts > 3:
        conf = max(0.1, conf - 0.1)
    if obs.cohomology_class is not None and obs.cohomology_class.is_trivial:
        conf = min(1.0, conf + 0.1)
    return conf


# ---------------------------------------------------------------------------
# RepairGuidance
# ---------------------------------------------------------------------------

class RepairGuidance:
    """Analyze obstruction basis and suggest concrete code repairs.

    For each obstruction in the basis, RepairGuidance:
    1. Classifies the obstruction kind (guard, mismatch, bounds, etc.).
    2. Dispatches to the appropriate repair strategy.
    3. Adjusts confidence based on obstruction characteristics.
    4. Returns a prioritized list of RepairSuggestions.
    """

    def __init__(
        self,
        *,
        min_confidence: float = 0.0,
        max_suggestions_per_obstruction: int = 3,
    ) -> None:
        self._min_confidence = min_confidence
        self._max_per_obs = max_suggestions_per_obstruction
        self._dispatch: Dict[str, Any] = {
            _ObstructionKind.MISSING_GUARD: _fix_missing_guard,
            _ObstructionKind.TYPE_MISMATCH: _fix_type_mismatch,
            _ObstructionKind.BOUNDS_VIOLATION: _fix_bounds_violation,
            _ObstructionKind.NONE_SAFETY: _fix_none_safety,
            _ObstructionKind.SHAPE_MISMATCH: _fix_shape_mismatch,
            _ObstructionKind.PROTOCOL_VIOLATION: _fix_protocol_violation,
            _ObstructionKind.MISSING_ANNOTATION: _fix_missing_annotation,
            _ObstructionKind.UNKNOWN: _fix_generic,
            _ObstructionKind.UNREACHABLE_ERROR: _fix_generic,
        }

    def suggest_repairs(
        self,
        obstructions: List[ObstructionData],
    ) -> List[RepairSuggestion]:
        """Produce repair suggestions for all obstructions.

        Returns a list sorted by (priority, -confidence).
        """
        all_suggestions: List[RepairSuggestion] = []

        for obs in obstructions:
            if obs.is_trivial:
                continue

            suggestions = self._generate_suggestions(obs)

            filtered = [
                s for s in suggestions if s.confidence >= self._min_confidence
            ]
            filtered.sort(key=lambda s: (s.priority, -s.confidence))
            all_suggestions.extend(filtered[: self._max_per_obs])

        all_suggestions.sort(key=lambda s: (s.priority, -s.confidence))
        return all_suggestions

    def _generate_suggestions(
        self,
        obs: ObstructionData,
    ) -> List[RepairSuggestion]:
        """Generate one or more suggestions for a single obstruction."""
        kind = _classify_obstruction(obs)

        primary_fixer = self._dispatch.get(kind, _fix_generic)
        primary = primary_fixer(obs)

        suggestions: List[RepairSuggestion] = [primary]

        if kind == _ObstructionKind.NONE_SAFETY:
            guard_fix = _fix_missing_guard(obs)
            suggestions.append(guard_fix)
        elif kind == _ObstructionKind.TYPE_MISMATCH:
            guard_fix = _fix_missing_guard(obs)
            suggestions.append(guard_fix)
        elif kind == _ObstructionKind.BOUNDS_VIOLATION:
            annotation_fix = _fix_missing_annotation(obs)
            suggestions.append(annotation_fix)

        return suggestions

    def _fix_missing_guard(
        self,
        obs: ObstructionData,
    ) -> RepairSuggestion:
        """Instance method wrapper for missing guard fix."""
        return _fix_missing_guard(obs)

    def _fix_type_mismatch(
        self,
        obs: ObstructionData,
    ) -> RepairSuggestion:
        """Instance method wrapper for type mismatch fix."""
        return _fix_type_mismatch(obs)

    def _fix_bounds_violation(
        self,
        obs: ObstructionData,
    ) -> RepairSuggestion:
        """Instance method wrapper for bounds violation fix."""
        return _fix_bounds_violation(obs)

    def to_core_repairs(
        self,
        suggestions: List[RepairSuggestion],
    ) -> List[CoreRepairSuggestion]:
        """Convert RepairSuggestions to core RepairSuggestion objects."""
        core_repairs: List[CoreRepairSuggestion] = []
        for s in suggestions:
            sites_to_adjust: Dict[SiteId, Any] = {}
            for sid in s.affected_sites:
                sites_to_adjust[sid] = {
                    "category": s.category,
                    "snippet": s.code_snippet,
                }
            core_repairs.append(
                CoreRepairSuggestion(
                    sites_to_adjust=sites_to_adjust,
                    obstructions_resolved=1,
                    locality_score=s.confidence,
                    plausibility_score=s.confidence,
                )
            )
        return core_repairs

    def summarize(
        self,
        suggestions: List[RepairSuggestion],
    ) -> str:
        """Produce a human-readable summary of all repair suggestions."""
        if not suggestions:
            return "No repair suggestions generated."

        lines: List[str] = []
        lines.append(f"Repair Suggestions ({len(suggestions)} total):")
        lines.append("=" * 60)

        by_category: Dict[str, List[RepairSuggestion]] = {}
        for s in suggestions:
            by_category.setdefault(s.category, []).append(s)

        for category, cat_suggestions in sorted(by_category.items()):
            lines.append(f"\n  [{category}] ({len(cat_suggestions)} suggestions)")
            for i, s in enumerate(cat_suggestions, 1):
                loc_str = s.location.pretty() if s.location else "unknown"
                lines.append(
                    f"    {i}. [{s.confidence:.0%}] {s.description}"
                )
                lines.append(f"       Location: {loc_str}")
                snippet_lines = s.code_snippet.split("\n")
                for sl in snippet_lines[:3]:
                    lines.append(f"       | {sl}")
                if len(snippet_lines) > 3:
                    lines.append(f"       | ... ({len(snippet_lines) - 3} more lines)")

        return "\n".join(lines)
