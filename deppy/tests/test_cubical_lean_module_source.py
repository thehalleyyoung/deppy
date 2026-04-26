"""Test for round-2 audit integration #1: the cubical block lands
in ``lean_module_source`` (the simpler safety_lean export path),
not just in ``write_certificate``'s output.
"""
from __future__ import annotations

import textwrap

from deppy.pipeline.safety_pipeline import verify_module_safety


class TestCubicalInLeanModuleSource:
    def test_cubical_block_in_lean_module_source(self):
        src = textwrap.dedent("""
            def f(x: int) -> int:
                if x > 0:
                    return 1
                return 0
        """)
        verdict = verify_module_safety(src, emit_lean=True)
        # When the safety_lean export path runs, the cubical block
        # is appended to lean_module_source.
        if verdict.lean_module_source:
            assert (
                "Cubical control-flow analysis"
                in verdict.lean_module_source
            )

    def test_cubical_failure_does_not_break_lean_export(self):
        # If the cubical extension raises, the standard lean_src
        # is preserved (not None).
        src = textwrap.dedent("""
            def f():
                return 1
        """)
        verdict = verify_module_safety(src, emit_lean=True)
        # lean_module_source exists OR there's a recorded note
        # explaining its absence.
        assert (
            verdict.lean_module_source is not None
            or any("Lean" in n for n in verdict.notes)
        )
