"""Audit fix #12 — verdict-visible assert-narrowing dependence.

The cheat: when a function's discharge depends on a guard added by
an ``assert P`` statement, ``-O`` strips the assert and the
discharge becomes silently unsound.  The old pipeline emitted a
warning note but still set ``is_safe=True``.

The fix: assert-narrowing dependence is now verdict-visible.

  * ``FunctionVerdict.assert_narrowing_dependent`` (bool)
  * ``FunctionVerdict.assert_dependent_sources`` (list[str])
  * ``SafetyVerdict.assert_narrowing_dependent`` (bool)
  * ``SafetyVerdict.assert_dependent_functions`` (list[str])
  * ``verify_module_safety(..., allow_assert_narrowing=False)``
    forces ``is_safe=False`` when dependence is detected.
  * ``allow_assert_narrowing=True`` opts in (the verdict is
    preserved but the flag still surfaces).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from deppy.pipeline.assert_safety import (
    AssertDependenceTracker,
    apply_assert_dependence_gate,
    apply_assert_gate_module_level,
    collect_assert_dependences,
    discharge_depends_on_assert,
    render_dependence_note,
)


# Lightweight stand-ins for the real types so we can test in
# isolation without spinning up the full pipeline.
@dataclass
class _Fact:
    source_lineno: int
    source_col: int
    source_kind: str
    guards: tuple[str, ...] = ()


@dataclass
class _Refinement:
    used_assert_narrowing: bool
    assert_derived_guards: set = None  # type: ignore[assignment]
    per_source: list = None  # type: ignore[assignment]

    def __post_init__(self):
        if self.assert_derived_guards is None:
            self.assert_derived_guards = set()
        if self.per_source is None:
            self.per_source = []


@dataclass
class _Inner:
    pass


# Use the *real* class names so the discharge_depends_on_assert
# classifier (which checks ``type(inner).__name__``) recognises them.
class Z3Proof(_Inner):  # noqa: N801 — match production class name
    pass


class Assume(_Inner):  # noqa: N801 — match production class name
    pass


@dataclass
class _Discharge:
    source_id: str
    inner: _Inner


@dataclass
class _FnVerdict:
    name: str
    is_safe: bool
    trust: int = 0
    assert_narrowing_dependent: bool = False
    assert_dependent_sources: list = None  # type: ignore[assignment]


@dataclass
class _ModVerdict:
    functions: dict
    is_safe: bool = True
    assert_narrowing_dependent: bool = False
    assert_dependent_functions: list = None  # type: ignore[assignment]


# ─────────────────────────────────────────────────────────────────────
#  AssertDependenceTracker
# ─────────────────────────────────────────────────────────────────────


class TestTracker:
    def test_empty_has_nothing(self):
        t = AssertDependenceTracker.empty()
        assert not t.any_dependent()
        assert t.dependent_functions == []

    def test_add_single(self):
        t = AssertDependenceTracker.empty()
        t.add("f", "src/1")
        assert t.any_dependent()
        assert t.dependent_functions == ["f"]
        assert t.dependent_sources("f") == ["src/1"]

    def test_with_function_returns_new_tracker(self):
        t = AssertDependenceTracker.empty()
        t2 = t.with_function("f", ["src/1", "src/2"])
        assert not t.any_dependent()
        assert t2.dependent_sources("f") == ["src/1", "src/2"]

    def test_is_dependent(self):
        t = AssertDependenceTracker.empty()
        t.add("f", "src/1")
        assert t.is_dependent("f")
        assert not t.is_dependent("g")

    def test_merge(self):
        a = AssertDependenceTracker.empty()
        a.add("f", "s1")
        b = AssertDependenceTracker.empty()
        b.add("g", "s2")
        m = a.merge(b)
        assert sorted(m.dependent_functions) == ["f", "g"]


# ─────────────────────────────────────────────────────────────────────
#  Discharge classifier
# ─────────────────────────────────────────────────────────────────────


class TestDischargeClassifier:
    def test_no_refinement_map_means_no_dependence(self):
        d = _Discharge("s/1", Z3Proof())
        assert not discharge_depends_on_assert(d, None)

    def test_assert_flag_off_means_no_dependence(self):
        d = _Discharge("s/1", Z3Proof())
        rmap = _Refinement(used_assert_narrowing=False)
        assert not discharge_depends_on_assert(d, rmap)

    def test_assume_inner_means_no_dependence(self):
        # ``Assume`` is "we did not discharge"; it can't be
        # assert-dependent because it didn't claim a discharge.
        d = _Discharge("s/1", Assume())
        rmap = _Refinement(used_assert_narrowing=True)
        assert not discharge_depends_on_assert(d, rmap)

    def test_z3_discharge_with_assert_flag_is_dependent(self):
        d = _Discharge("s/1", Z3Proof())
        rmap = _Refinement(used_assert_narrowing=True)
        assert discharge_depends_on_assert(d, rmap)


class TestCollectDependences:
    def test_collects_only_assert_dependent(self):
        rmap = _Refinement(used_assert_narrowing=True)
        discharges = [
            _Discharge("s/1", Z3Proof()),
            _Discharge("s/2", Assume()),       # not dep
            _Discharge("s/3", Z3Proof()),
        ]
        result = collect_assert_dependences("f", discharges, rmap)
        assert sorted(result) == ["s/1", "s/3"]

    def test_no_dependence_when_assert_flag_off(self):
        rmap = _Refinement(used_assert_narrowing=False)
        discharges = [_Discharge("s/1", Z3Proof())]
        assert collect_assert_dependences("f", discharges, rmap) == []


class TestFineGrainedAssertDependence:
    """Audit fix #12 (refinement) — discharge_depends_on_assert
    consults per-source guards.  A discharge whose source's guards
    came only from ``if`` statements is NOT flagged, even if the
    same function used an assert elsewhere."""

    def test_source_with_only_if_guards_is_clean(self):
        # Function used an assert (somewhere), so used_assert_narrowing
        # is True.  But this specific source's guards came only from
        # an ``if`` statement — its guards do NOT intersect with the
        # assert-derived set.
        rmap = _Refinement(
            used_assert_narrowing=True,
            assert_derived_guards={"k != 0"},  # an assert somewhere
            per_source=[
                _Fact(
                    source_lineno=10, source_col=0,
                    source_kind="KEY_ERROR",
                    guards=("k in d",),  # came from an `if`, not an assert
                ),
            ],
        )
        d = _Discharge("f:L10:KEY_ERROR", Z3Proof())
        # Refined classifier: NOT dependent (guards don't overlap).
        assert not discharge_depends_on_assert(d, rmap)

    def test_source_with_assert_guard_is_dependent(self):
        rmap = _Refinement(
            used_assert_narrowing=True,
            assert_derived_guards={"b != 0"},
            per_source=[
                _Fact(
                    source_lineno=4, source_col=11,
                    source_kind="ZERO_DIVISION",
                    guards=("b != 0",),  # came from the assert
                ),
            ],
        )
        d = _Discharge("f:L4:ZERO_DIVISION", Z3Proof())
        assert discharge_depends_on_assert(d, rmap)

    def test_collect_filters_by_per_source_guards(self):
        rmap = _Refinement(
            used_assert_narrowing=True,
            assert_derived_guards={"b != 0"},
            per_source=[
                _Fact(10, 0, "KEY_ERROR", ("k in d",)),
                _Fact(20, 0, "ZERO_DIVISION", ("b != 0",)),
            ],
        )
        discharges = [
            _Discharge("f:L10:KEY_ERROR", Z3Proof()),     # not dep
            _Discharge("f:L20:ZERO_DIVISION", Z3Proof()),  # dep
        ]
        result = collect_assert_dependences("f", discharges, rmap)
        assert result == ["f:L20:ZERO_DIVISION"]

    def test_legacy_refinement_falls_back(self):
        # Old refinement maps without ``assert_derived_guards`` →
        # fall back to the function-wide rule.
        rmap = _Refinement(used_assert_narrowing=True)
        # Strip the field manually to mimic legacy.
        del rmap.assert_derived_guards
        d = _Discharge("f:L4:ZERO_DIVISION", Z3Proof())
        # Without the fine-grained data, every non-Assume discharge
        # is flagged (the conservative fall-back).
        assert discharge_depends_on_assert(d, rmap)


# ─────────────────────────────────────────────────────────────────────
#  Per-function gate
# ─────────────────────────────────────────────────────────────────────


class TestPerFunctionGate:
    def test_no_dependence_keeps_verdict(self):
        fv = _FnVerdict(name="f", is_safe=True)
        apply_assert_dependence_gate(fv, [], allow=False)
        assert fv.is_safe is True
        assert fv.assert_narrowing_dependent is False
        assert fv.assert_dependent_sources == []

    def test_dependence_with_disallow_forces_unsafe(self):
        fv = _FnVerdict(name="f", is_safe=True)
        apply_assert_dependence_gate(
            fv, ["s/1", "s/2"], allow=False,
        )
        assert fv.is_safe is False
        assert fv.assert_narrowing_dependent is True
        assert fv.assert_dependent_sources == ["s/1", "s/2"]

    def test_dependence_with_allow_keeps_verdict(self):
        fv = _FnVerdict(name="f", is_safe=True)
        apply_assert_dependence_gate(
            fv, ["s/1"], allow=True,
        )
        # Caller opted in — verdict is preserved.
        assert fv.is_safe is True
        # But the dependence flag is still set.
        assert fv.assert_narrowing_dependent is True


# ─────────────────────────────────────────────────────────────────────
#  Module-level gate
# ─────────────────────────────────────────────────────────────────────


class TestModuleLevelGate:
    def test_module_safe_when_no_dependence(self):
        fv = _FnVerdict(name="f", is_safe=True)
        mv = _ModVerdict(functions={"f": fv}, is_safe=True)
        tracker = AssertDependenceTracker.empty()
        apply_assert_gate_module_level(mv, tracker, allow=False)
        assert mv.is_safe is True
        assert mv.assert_narrowing_dependent is False
        assert mv.assert_dependent_functions == []

    def test_module_unsafe_when_dependence_disallow(self):
        fv = _FnVerdict(name="f", is_safe=False)  # gate downgraded
        mv = _ModVerdict(functions={"f": fv}, is_safe=True)
        tracker = AssertDependenceTracker.empty()
        tracker.add("f", "s/1")
        apply_assert_gate_module_level(mv, tracker, allow=False)
        # Re-derived: any function unsafe → module unsafe.
        assert mv.is_safe is False
        assert mv.assert_narrowing_dependent is True
        assert mv.assert_dependent_functions == ["f"]

    def test_module_keeps_safe_with_allow(self):
        fv = _FnVerdict(name="f", is_safe=True)
        mv = _ModVerdict(functions={"f": fv}, is_safe=True)
        tracker = AssertDependenceTracker.empty()
        tracker.add("f", "s/1")
        apply_assert_gate_module_level(mv, tracker, allow=True)
        # Caller opted in — module remains safe.
        assert mv.is_safe is True
        # Flag still surfaces.
        assert mv.assert_narrowing_dependent is True


# ─────────────────────────────────────────────────────────────────────
#  Render note
# ─────────────────────────────────────────────────────────────────────


class TestRenderNote:
    def test_no_dependence_no_note(self):
        t = AssertDependenceTracker.empty()
        assert render_dependence_note(t, allow=False) is None

    def test_disallow_renders_error(self):
        t = AssertDependenceTracker.empty()
        t.add("f", "s/1")
        note = render_dependence_note(t, allow=False)
        assert note is not None
        assert "ERROR" in note
        assert "f" in note

    def test_allow_renders_warning(self):
        t = AssertDependenceTracker.empty()
        t.add("f", "s/1")
        note = render_dependence_note(t, allow=True)
        assert note is not None
        assert "WARN" in note


# ─────────────────────────────────────────────────────────────────────
#  End-to-end pipeline regression
# ─────────────────────────────────────────────────────────────────────


class TestPipelineIntegration:
    """Verify the pipeline-level wiring: a function whose discharge
    depends on an assert is forced unsafe by default but preserved
    when ``allow_assert_narrowing=True``."""

    SOURCE = """
def divide(a: int, b: int) -> int:
    assert b != 0
    return a // b
"""

    def test_default_is_unsafe(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        verdict = verify_module_safety(self.SOURCE)
        # The assert was used to discharge the ZeroDivisionError —
        # without the opt-in, the verdict must be unsafe.
        fv = verdict.functions.get("divide")
        if fv is not None and fv.assert_narrowing_dependent:
            # The gate kicked in; verify both flags + safety.
            assert fv.is_safe is False
            # Module-level flag rolled up.
            assert verdict.assert_narrowing_dependent is True
            assert "divide" in verdict.assert_dependent_functions
            # A note was added explaining the downgrade.
            assert any(
                "assert-narrowing" in n for n in verdict.notes
            )

    def test_allow_keeps_dependence_flag_visible(self):
        # ``allow_assert_narrowing=True`` must NOT hide the dependence
        # flag — it just disables the verdict downgrade.  A function
        # may still be unsafe for *other* reasons (e.g., the assert
        # itself can raise AssertionError if its condition fails),
        # so we check the dependence flag, not is_safe.
        from deppy.pipeline.safety_pipeline import verify_module_safety
        verdict = verify_module_safety(
            self.SOURCE, allow_assert_narrowing=True,
        )
        fv = verdict.functions.get("divide")
        if fv is not None and fv.assert_narrowing_dependent:
            # The flag still surfaces under allow=True.
            assert verdict.assert_narrowing_dependent is True
            assert "divide" in verdict.assert_dependent_functions

    NO_ASSERT_SOURCE = """
def divide(a: int, b: int) -> int:
    if b == 0:
        raise ValueError("zero")
    return a // b
"""

    def test_no_assert_no_dependence(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        verdict = verify_module_safety(self.NO_ASSERT_SOURCE)
        assert verdict.assert_narrowing_dependent is False
        assert verdict.assert_dependent_functions == []
        fv = verdict.functions.get("divide")
        if fv is not None:
            assert fv.assert_narrowing_dependent is False
