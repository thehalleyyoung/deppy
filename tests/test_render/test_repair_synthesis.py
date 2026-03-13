"""Tests for deppy.render.repair_synthesis — repair plan generation."""

from __future__ import annotations

import pytest

from deppy.render.repair_synthesis import (
    RepairKind,
    RepairPlan,
    RepairSuggestion,
    synthesize_repairs,
)


# ── RepairSuggestion ────────────────────────────────────────────────────────

class TestRepairSuggestion:
    def test_format(self):
        s = RepairSuggestion(
            kind=RepairKind.GUARD_CHECK,
            target_line=10,
            code="if x is not None:",
            explanation="Guard against None",
        )
        formatted = s.format()
        assert "10" in formatted
        assert "guard_check" in formatted

    def test_default_values(self):
        s = RepairSuggestion(kind=RepairKind.ASSERTION, target_line=1)
        assert s.insert_before is True
        assert s.confidence == 0.8
        assert s.obstruction_count == 1


# ── RepairPlan ───────────────────────────────────────────────────────────────

class TestRepairPlan:
    def test_empty_plan(self):
        plan = RepairPlan(function_name="f")
        # 0 obstructions → trivially covered (1.0)
        assert plan.coverage == 1.0
        summary = plan.summary().lower()
        assert "0" in summary and "fix" in summary

    def test_coverage_calculation(self):
        plan = RepairPlan(
            function_name="f",
            suggestions=[
                RepairSuggestion(kind=RepairKind.GUARD_CHECK, target_line=5),
                RepairSuggestion(kind=RepairKind.BOUND_CHECK, target_line=10),
            ],
            total_obstructions=4,
            obstructions_addressed=3,
        )
        assert plan.coverage == pytest.approx(0.75)

    def test_summary(self):
        plan = RepairPlan(
            function_name="f",
            suggestions=[RepairSuggestion(kind=RepairKind.GUARD_CHECK, target_line=5)],
            total_obstructions=2,
            obstructions_addressed=1,
            minimum_fixes=1,
        )
        summary = plan.summary()
        assert "f" in summary


# ── synthesize_repairs integration ───────────────────────────────────────────

class _MockRequirement:
    def __init__(self, desc="test", ast_node=None):
        self.description = desc
        self.ast_node = ast_node


class _MockObstruction:
    def __init__(self, line, bug_type, var="x", confidence=1.0,
                 resolved=False, repair_guard=None):
        self.line = line
        self.bug_type = bug_type
        self.requirement = _MockRequirement(var)
        self.confidence = confidence
        self.resolved_by_guard = resolved
        self.repair_guard = repair_guard


class _MockReport:
    def __init__(self, name, obstructions):
        self.function_name = name
        self.obstructions = obstructions

    @property
    def findings(self):
        return [o for o in self.obstructions if not o.resolved_by_guard]


class TestSynthesizeRepairs:
    def test_no_bugs(self):
        report = _MockReport("f", [])
        plan = synthesize_repairs(report)
        assert isinstance(plan, RepairPlan)
        assert len(plan.suggestions) == 0
        assert plan.total_obstructions == 0

    def test_null_deref_generates_guard(self):
        report = _MockReport("f", [
            _MockObstruction(10, "POSSIBLE_NONE_DEREF"),
        ])
        plan = synthesize_repairs(report)
        assert len(plan.suggestions) >= 1
        assert plan.obstructions_addressed >= 1
        # Should be a guard check
        kinds = {s.kind for s in plan.suggestions}
        assert RepairKind.GUARD_CHECK in kinds or RepairKind.TYPE_CHECK in kinds

    def test_division_by_zero_generates_check(self):
        report = _MockReport("f", [
            _MockObstruction(15, "DIVISION_BY_ZERO", var="d"),
        ])
        plan = synthesize_repairs(report)
        assert len(plan.suggestions) >= 1

    def test_index_error_generates_bound_check(self):
        report = _MockReport("f", [
            _MockObstruction(20, "INDEX_OUT_OF_RANGE", var="xs"),
        ])
        plan = synthesize_repairs(report)
        assert len(plan.suggestions) >= 1
        kinds = {s.kind for s in plan.suggestions}
        assert RepairKind.BOUND_CHECK in kinds or RepairKind.GUARD_CHECK in kinds

    def test_resolved_obstructions_skipped(self):
        report = _MockReport("f", [
            _MockObstruction(10, "POSSIBLE_NONE_DEREF", resolved=True),
        ])
        plan = synthesize_repairs(report)
        assert len(plan.suggestions) == 0

    def test_multiple_bugs_same_line(self):
        report = _MockReport("f", [
            _MockObstruction(10, "POSSIBLE_NONE_DEREF"),
            _MockObstruction(10, "DIVISION_BY_ZERO"),
        ])
        plan = synthesize_repairs(report)
        assert plan.total_obstructions >= 2
        assert len(plan.suggestions) >= 1

    def test_unknown_bug_type_gets_default_repair(self):
        report = _MockReport("f", [
            _MockObstruction(5, "SOME_NOVEL_BUG_TYPE"),
        ])
        plan = synthesize_repairs(report)
        # Should still produce something (fallback to assertion)
        assert len(plan.suggestions) >= 1

    def test_with_existing_repair_guard(self):
        """If obstruction already has a repair_guard, it should be used."""
        report = _MockReport("f", [
            _MockObstruction(10, "POSSIBLE_NONE_DEREF", repair_guard="guard_pred"),
        ])
        plan = synthesize_repairs(report)
        assert len(plan.suggestions) >= 1
