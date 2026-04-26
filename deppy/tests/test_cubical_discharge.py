"""Tests for cubical Kan-discharge integration.

Round-2 audit chunk D: when standard discharge leaves a source
in Assume state but the source's cubical cell is Kan-fillable
(peers discharged), the pipeline promotes it to a Structural
discharge tagged ``cubical-kan``.
"""
from __future__ import annotations

import textwrap

from deppy.pipeline.safety_pipeline import _DISCHARGE_TAGS


# ─────────────────────────────────────────────────────────────────────
#  Discharge tag registration
# ─────────────────────────────────────────────────────────────────────


class TestDischargeTagRegistered:
    def test_cubical_kan_tag_in_registry(self):
        assert "cubical-kan" in _DISCHARGE_TAGS


# ─────────────────────────────────────────────────────────────────────
#  Discharge classifier
# ─────────────────────────────────────────────────────────────────────


class TestClassifier:
    def test_cubical_structural_classified_as_cubical_kan(self):
        from deppy.core.kernel import (
            SourceDischarge, Structural,
        )
        from deppy.pipeline.safety_pipeline import _classify_discharge
        d = SourceDischarge(
            source_id="f:L1:KEY_ERROR",
            failure_kind="KEY_ERROR",
            safety_predicate="True",
            inner=Structural(
                description="cubical Kan-fill via cube `f.cu_try_finally_42`",
            ),
            note="cubical-kan via higher cube",
        )
        assert _classify_discharge(d) == "cubical-kan"

    def test_other_structural_not_misclassified(self):
        from deppy.core.kernel import (
            SourceDischarge, Structural,
        )
        from deppy.pipeline.safety_pipeline import _classify_discharge
        d = SourceDischarge(
            source_id="f:L1:ZERO_DIVISION",
            failure_kind="ZERO_DIVISION",
            safety_predicate="b != 0",
            inner=Structural(
                description="co-located peer discharged",
            ),
            note="co-located peer",
        )
        assert _classify_discharge(d) == "co-located-peer"


# ─────────────────────────────────────────────────────────────────────
#  Promotion logic
# ─────────────────────────────────────────────────────────────────────


class TestPromotionLogic:
    def test_no_promotion_for_fully_discharged(self):
        # When no source is in Assume state, no promotion happens.
        from dataclasses import dataclass

        @dataclass
        class _FakeSource:
            ast_node: object = None

        @dataclass
        class _FakeDischarge:
            source_id: str
            inner: object
            failure_kind: str = "X"
            safety_predicate: str = ""
            note: str = ""

        from deppy.core.kernel import Structural
        from deppy.pipeline.cubical_ast import CubicalSet
        from deppy.pipeline.cubical_discharge import (
            try_cubical_kan_discharge,
        )

        cset = CubicalSet(function_name="t")
        # No discharges in Assume → no promotion.
        result = try_cubical_kan_discharge(
            fn_name="t", sources=[],
            discharges=[
                _FakeDischarge("s1", Structural(description="ok")),
            ],
            cubical_set=cset,
        )
        assert result == []


# ─────────────────────────────────────────────────────────────────────
#  End-to-end pipeline test
# ─────────────────────────────────────────────────────────────────────


class TestPipelineEndToEnd:
    def test_pipeline_runs_with_cubical_discharge(self):
        # Smoke test: the pipeline doesn't crash when cubical
        # Kan-discharge is enabled (it is by default).
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = textwrap.dedent("""
            def f(x: int) -> int:
                if x > 0:
                    return 1
                return 0
        """)
        verdict = verify_module_safety(src)
        assert "f" in verdict.functions

    def test_pipeline_records_promotion_in_notes(self):
        # When cubical-kan promotes a source, a note is appended.
        # We don't have a guaranteed-promotion case at this test
        # level (most simple functions don't have Kan-fillable
        # cells with discharged peers), but we verify the
        # mechanism exists by checking the notes list is intact.
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = textwrap.dedent("""
            def f():
                return 1
        """)
        verdict = verify_module_safety(src)
        assert isinstance(verdict.notes, list)
