"""Automatic repair synthesis from obstruction algebra.

Given a set of gluing obstructions (bugs), synthesize concrete Python
code fixes that close each obstruction.  The repair is the *dual* of
the obstruction: where the obstruction says "sections disagree at overlap",
the repair says "insert a guard that makes them agree".

Uses the module-valued ObstructionAlgebra to:
  1. Compute interaction_groups — obstructions that share basis elements
     can be fixed by a single compound guard.
  2. For each group, synthesize the minimal guard predicate.
  3. Generate concrete Python code (if-statement, assertion, or try-except).

Mathematically: the repair is a section of the *dual sheaf* — the sheaf
of valid completions of the partial global section.  Finding it is the
gluing repair problem: given local sections that disagree on overlaps,
find the minimal edit to make them glue.
"""

from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set, Tuple


class RepairKind(Enum):
    """Type of code repair."""
    GUARD_CHECK = "guard_check"          # if x is not None: ...
    ASSERTION = "assertion"              # assert x is not None
    DEFAULT_VALUE = "default_value"      # x = x if x is not None else default
    TRY_EXCEPT = "try_except"            # try: ... except: ...
    BOUND_CHECK = "bound_check"          # if 0 <= i < len(xs): ...
    TYPE_CHECK = "type_check"            # if isinstance(x, T): ...
    INITIALIZATION = "initialization"    # x = default before use


@dataclass
class RepairSuggestion:
    """A concrete code repair for a gluing obstruction."""
    kind: RepairKind
    target_line: int
    insert_before: bool = True  # Insert before (True) or replace (False)
    code: str = ""
    explanation: str = ""
    confidence: float = 0.8
    bug_types_fixed: List[str] = field(default_factory=list)
    obstruction_count: int = 1  # How many obstructions this fixes

    def format(self) -> str:
        loc = "before" if self.insert_before else "at"
        return (
            f"[{self.kind.value}] {loc} line {self.target_line}: "
            f"{self.explanation}\n"
            f"  Suggested code:\n"
            f"    {self.code}\n"
            f"  Fixes: {', '.join(self.bug_types_fixed)} "
            f"(confidence: {self.confidence:.0%})")


@dataclass
class RepairPlan:
    """A complete repair plan for a function."""
    function_name: str
    suggestions: List[RepairSuggestion] = field(default_factory=list)
    total_obstructions: int = 0
    obstructions_addressed: int = 0
    minimum_fixes: int = 0

    @property
    def coverage(self) -> float:
        if self.total_obstructions == 0:
            return 1.0
        return self.obstructions_addressed / self.total_obstructions

    def summary(self) -> str:
        lines = [
            f"Repair plan for {self.function_name}:",
            f"  {len(self.suggestions)} fixes address "
            f"{self.obstructions_addressed}/{self.total_obstructions} obstructions",
            f"  Minimum independent fixes needed: {self.minimum_fixes}",
        ]
        for i, s in enumerate(self.suggestions, 1):
            lines.append(f"\n  Fix {i}:")
            lines.append(f"    {s.format()}")
        return "\n".join(lines)


# ── Bug-type → repair-kind mapping ──────────────────────────────────────────

_BUG_REPAIR_MAP: Dict[str, Tuple[RepairKind, str]] = {
    "USE_BEFORE_CHECK": (RepairKind.GUARD_CHECK, "if {var} is not None:"),
    "NONE_RETURN_UNCHECKED": (RepairKind.GUARD_CHECK, "if {var} is not None:"),
    "OPTIONAL_ATTR_ACCESS": (RepairKind.GUARD_CHECK, "if {var} is not None:"),
    "DIVISION_BY_ZERO": (RepairKind.GUARD_CHECK, "if {var} != 0:"),
    "INDEX_OUT_OF_BOUNDS": (RepairKind.BOUND_CHECK, "if 0 <= {idx} < len({seq}):"),
    "EMPTY_SEQUENCE_ACCESS": (RepairKind.GUARD_CHECK, "if {var}:"),
    "KEY_ERROR": (RepairKind.GUARD_CHECK, "if {key} in {var}:"),
    "UNINITIALIZED_VARIABLE": (RepairKind.INITIALIZATION, "{var} = None"),
    "MISSING_RETURN": (RepairKind.DEFAULT_VALUE, "return None"),
    "TYPE_MISMATCH": (RepairKind.TYPE_CHECK, "if isinstance({var}, {type}):"),
    "RESOURCE_LEAK": (RepairKind.TRY_EXCEPT, "try: ... finally: {var}.close()"),
    "USE_AFTER_CLOSE": (RepairKind.GUARD_CHECK, "if not {var}.closed:"),
    "NEGATIVE_INDEX": (RepairKind.BOUND_CHECK, "if {var} >= 0:"),
    "MATH_DOMAIN_ERROR": (RepairKind.GUARD_CHECK, "if {var} > 0:"),
    "LOG_DOMAIN_ERROR": (RepairKind.GUARD_CHECK, "if {var} > 0:"),
    "SQRT_DOMAIN_ERROR": (RepairKind.GUARD_CHECK, "if {var} >= 0:"),
    "MOD_BY_ZERO": (RepairKind.GUARD_CHECK, "if {var} != 0:"),
    "DOUBLE_FREE": (RepairKind.GUARD_CHECK, "if {var} is not None:"),
    "ITERATOR_EXHAUSTION": (RepairKind.TRY_EXCEPT,
                            "try: val = next(it)\nexcept StopIteration: val = default"),
    # Alternative names used in deppy bug_detect
    "POSSIBLE_NONE_DEREF": (RepairKind.GUARD_CHECK, "if {var} is not None:"),
    "INDEX_OUT_OF_RANGE": (RepairKind.BOUND_CHECK, "if 0 <= {idx} < len({seq}):"),
    "POSSIBLE_DIVISION_BY_ZERO": (RepairKind.GUARD_CHECK, "if {var} != 0:"),
    "POSSIBLE_UNBOUND": (RepairKind.INITIALIZATION, "{var} = None"),
    "POSSIBLE_KEY_ERROR": (RepairKind.GUARD_CHECK, "if {key} in {var}:"),
    "POSSIBLE_TYPE_ERROR": (RepairKind.TYPE_CHECK, "if isinstance({var}, {type}):"),
}


def synthesize_repairs(
    report,  # SheafBugReport
    source: str = "",
) -> RepairPlan:
    """Synthesize repair suggestions from a bug report.

    Uses the ObstructionAlgebra to group interacting obstructions,
    then generates a minimal set of repairs.
    """
    from deppy.render.bug_detect import ObstructionAlgebra

    findings = report.findings
    if not findings:
        return RepairPlan(
            function_name=report.function_name,
            total_obstructions=0, obstructions_addressed=0, minimum_fixes=0)

    # Group by interaction — each group gets one compound repair
    groups = ObstructionAlgebra.interaction_groups(report.obstructions)
    min_fixes = ObstructionAlgebra.minimum_fix_count(report.obstructions)

    suggestions: List[RepairSuggestion] = []
    addressed = 0

    for group in groups:
        suggestion = _synthesize_group_repair(group, source)
        if suggestion is not None:
            suggestions.append(suggestion)
            addressed += len(group)

    # Handle ungrouped findings
    grouped_lines = set()
    for g in groups:
        for obs in g:
            grouped_lines.add(obs.line)

    for obs in findings:
        if obs.line not in grouped_lines:
            suggestion = _synthesize_single_repair(obs, source)
            if suggestion is not None:
                suggestions.append(suggestion)
                addressed += 1

    return RepairPlan(
        function_name=report.function_name,
        suggestions=suggestions,
        total_obstructions=len(findings),
        obstructions_addressed=addressed,
        minimum_fixes=min_fixes,
    )


def _synthesize_group_repair(
    group: list, source: str,
) -> Optional[RepairSuggestion]:
    """Synthesize a single repair for a group of interacting obstructions."""
    if not group:
        return None

    # Find the earliest line in the group — insert repair before it
    earliest = min(obs.line for obs in group)
    bug_types = list({obs.bug_type for obs in group})

    # If all are the same bug type, use that type's repair pattern
    if len(bug_types) == 1:
        return _synthesize_single_repair(group[0], source)

    # Compound repair: generate a multi-condition guard
    conditions = []
    for obs in group:
        cond = _bug_type_to_condition(obs)
        if cond:
            conditions.append(cond)

    if not conditions:
        return None

    combined = " and ".join(conditions)
    code = f"if {combined}:"

    return RepairSuggestion(
        kind=RepairKind.GUARD_CHECK,
        target_line=earliest,
        code=code,
        explanation=f"Compound guard for {len(group)} interacting obstructions",
        bug_types_fixed=bug_types,
        obstruction_count=len(group),
        confidence=0.7,
    )


def _synthesize_single_repair(
    obs, source: str,
) -> Optional[RepairSuggestion]:
    """Synthesize a repair for a single obstruction."""
    bug_type = obs.bug_type
    var = _extract_var_from_obstruction(obs)
    line = obs.line

    if bug_type in _BUG_REPAIR_MAP:
        kind, template = _BUG_REPAIR_MAP[bug_type]
        code = template.format(
            var=var or "x", idx=var or "i",
            seq="xs", key=var or "k", type="int")
        return RepairSuggestion(
            kind=kind,
            target_line=line,
            code=code,
            explanation=f"Guard against {bug_type} on '{var or '?'}'",
            bug_types_fixed=[bug_type],
            confidence=0.8 if var else 0.5,
        )

    # Fallback: generic guard from repair_guard predicate
    if obs.repair_guard is not None:
        code = f"if {_pred_to_python(obs.repair_guard)}:"
        return RepairSuggestion(
            kind=RepairKind.GUARD_CHECK,
            target_line=line,
            code=code,
            explanation=f"Guard from gap predicate for {bug_type}",
            bug_types_fixed=[bug_type],
            confidence=0.6,
        )

    # Last resort: generic assertion
    return RepairSuggestion(
        kind=RepairKind.ASSERTION,
        target_line=line,
        code=f"assert {var or 'condition'}, '{bug_type} guard'",
        explanation=f"Generic assertion for {bug_type}",
        bug_types_fixed=[bug_type],
        confidence=0.3,
    )


def _bug_type_to_condition(obs) -> Optional[str]:
    """Convert a bug obstruction to a Python guard condition."""
    bt = obs.bug_type
    var = _extract_var_from_obstruction(obs) or "x"

    cond_map = {
        "USE_BEFORE_CHECK": f"{var} is not None",
        "NONE_RETURN_UNCHECKED": f"{var} is not None",
        "OPTIONAL_ATTR_ACCESS": f"{var} is not None",
        "DIVISION_BY_ZERO": f"{var} != 0",
        "INDEX_OUT_OF_BOUNDS": f"0 <= idx < len({var})",
        "EMPTY_SEQUENCE_ACCESS": f"len({var}) > 0",
        "KEY_ERROR": f"key in {var}",
        "NEGATIVE_INDEX": f"{var} >= 0",
        "MATH_DOMAIN_ERROR": f"{var} > 0",
        "SQRT_DOMAIN_ERROR": f"{var} >= 0",
        "MOD_BY_ZERO": f"{var} != 0",
    }
    return cond_map.get(bt)


def _extract_var_from_obstruction(obs) -> Optional[str]:
    """Extract the primary variable from an obstruction."""
    import re
    desc = obs.requirement.description if obs.requirement else ""
    m = re.search(r"['\"`](\w+)['\"`]", desc)
    if m:
        return m.group(1)
    if obs.requirement and obs.requirement.ast_node:
        node = obs.requirement.ast_node
        if isinstance(node, ast.Name):
            return node.id
    return None


def _pred_to_python(pred) -> str:
    """Convert a predicate to a Python expression string."""
    try:
        return str(pred)
    except Exception:
        return "True"
