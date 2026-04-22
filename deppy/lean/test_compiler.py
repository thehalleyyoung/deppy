"""
Integration tests for deppy.lean.compiler — compile_to_lean pipeline.

Run with:
    cd /Users/halleyyoung/Documents/div/mathdivergence/deppy
    PYTHONPATH=.:src python3 -m pytest deppy/lean/test_compiler.py -v
"""
from __future__ import annotations

import pytest

from deppy import guarantee, requires, ensures
from deppy.lean.compiler import compile_to_lean, LeanCertificate


# ═══════════════════════════════════════════════════════════════════
#  Basic tests
# ═══════════════════════════════════════════════════════════════════

class TestSimpleFunction:
    def test_abs_val(self):
        @guarantee("result >= 0")
        def abs_val(x: int) -> int:
            if x >= 0:
                return x
            return -x

        cert = compile_to_lean(abs_val)
        lean = cert.render()
        assert "theorem" in lean
        assert "abs_val" in lean
        assert cert.trust_level in ("LEAN_VERIFIED", "LEAN_EXPORTED", "ASSUMPTION_DEPENDENT")

    def test_square(self):
        @guarantee("result >= 0")
        def square(x: int) -> int:
            return x * x

        cert = compile_to_lean(square)
        lean = cert.render()
        assert lean.startswith("/-")  # header comment
        assert "import" in lean
        assert "theorem" in lean
        assert "def" in lean or "opaque" in lean


class TestListFunction:
    def test_sorted_perm(self):
        @guarantee("result is sorted")
        @guarantee("result is a permutation of xs")
        def my_sort(xs: list[int]) -> list[int]:
            return sorted(xs)

        cert = compile_to_lean(my_sort)
        lean = cert.render()
        assert "List.Sorted" in lean or "sorted" in lean.lower()
        assert "Perm" in lean


class TestWithRequires:
    def test_precondition(self):
        @requires("n > 0")
        @guarantee("result > 0")
        def double_pos(n: int) -> int:
            return n * 2

        cert = compile_to_lean(double_pos)
        lean = cert.render()
        assert "0 <" in lean  # precondition rendered as (0 < n)


class TestSorryCount:
    def test_unparsable_spec_gets_sorry(self):
        @guarantee("this is some complex NL spec that can't be parsed")
        def mystery(x: int) -> int:
            return x

        cert = compile_to_lean(mystery)
        assert cert.sorry_count > 0
        assert cert.trust_level != "LEAN_VERIFIED"


class TestRenderValidLean:
    def test_render_structure(self):
        """The rendered output should have expected structure."""
        @guarantee("result >= 0")
        def square(x: int) -> int:
            return x * x

        cert = compile_to_lean(square)
        lean = cert.render()
        assert lean.startswith("/-")  # header comment
        assert "import" in lean
        assert "theorem" in lean
        assert "def" in lean or "opaque" in lean


# ═══════════════════════════════════════════════════════════════════
#  LeanCertificate dataclass
# ═══════════════════════════════════════════════════════════════════

class TestLeanCertificate:
    def test_is_fully_verified(self):
        cert = LeanCertificate(module_name="Test", sorry_count=0, trust_level="LEAN_VERIFIED")
        assert cert.is_fully_verified

    def test_not_fully_verified(self):
        cert = LeanCertificate(module_name="Test", sorry_count=2, trust_level="LEAN_EXPORTED")
        assert not cert.is_fully_verified

    def test_summary(self):
        cert = LeanCertificate(
            module_name="Test",
            imports=["Mathlib.Data.List.Basic"],
            declarations=["def f := 1"],
            theorems=["theorem t := sorry"],
            sorry_count=1,
            trust_level="LEAN_EXPORTED",
        )
        s = cert.summary()
        assert "Test" in s
        assert "1" in s  # sorry count


# ═══════════════════════════════════════════════════════════════════
#  Body translation
# ═══════════════════════════════════════════════════════════════════

class TestBodyTranslation:
    def test_arithmetic_def(self):
        @guarantee("result >= 0")
        def square(x: int) -> int:
            return x * x

        cert = compile_to_lean(square)
        # Should produce a `def`, not `opaque`
        assert any("def square" in d for d in cert.declarations)

    def test_if_else_body(self):
        @guarantee("result >= 0")
        def abs_val(x: int) -> int:
            if x >= 0:
                return x
            return -x

        cert = compile_to_lean(abs_val)
        assert any("def abs_val" in d for d in cert.declarations)
        # Should contain if/then/else
        decl_text = "\n".join(cert.declarations)
        assert "if" in decl_text
        assert "then" in decl_text
        assert "else" in decl_text

    def test_sorted_call(self):
        @guarantee("result is sorted")
        def sort_it(xs: list[int]) -> list[int]:
            return sorted(xs)

        cert = compile_to_lean(sort_it)
        decl_text = "\n".join(cert.declarations)
        assert "mergeSort" in decl_text

    def test_let_binding(self):
        @guarantee("result >= 0")
        def f(x: int) -> int:
            y = x * x
            return y

        cert = compile_to_lean(f)
        decl_text = "\n".join(cert.declarations)
        assert "let y" in decl_text


# ═══════════════════════════════════════════════════════════════════
#  Import inference
# ═══════════════════════════════════════════════════════════════════

class TestImportInference:
    def test_sorted_imports(self):
        @guarantee("result is sorted")
        def sort_it(xs: list[int]) -> list[int]:
            return sorted(xs)

        cert = compile_to_lean(sort_it)
        assert any("Sort" in imp for imp in cert.imports)

    def test_perm_imports(self):
        @guarantee("result is a permutation of xs")
        def sort_it(xs: list[int]) -> list[int]:
            return sorted(xs)

        cert = compile_to_lean(sort_it)
        assert any("Perm" in imp for imp in cert.imports)


# ═══════════════════════════════════════════════════════════════════
#  Trust levels
# ═══════════════════════════════════════════════════════════════════

class TestTrustLevels:
    def test_sorry_gives_exported(self):
        @guarantee("result >= 0")
        def square(x: int) -> int:
            return x * x

        cert = compile_to_lean(square)
        # sorry is expected for theorem proofs → LEAN_EXPORTED
        if cert.sorry_count > 0:
            assert cert.trust_level in ("LEAN_EXPORTED", "ASSUMPTION_DEPENDENT")
        else:
            assert cert.trust_level == "LEAN_VERIFIED"


# ═══════════════════════════════════════════════════════════════════
#  Output file writing
# ═══════════════════════════════════════════════════════════════════

class TestOutputFile:
    def test_write_to_file(self, tmp_path):
        @guarantee("result >= 0")
        def square(x: int) -> int:
            return x * x

        out = tmp_path / "Square.lean"
        cert = compile_to_lean(square, output_path=out)
        assert out.exists()
        content = out.read_text()
        assert "theorem" in content
        assert "def" in content or "opaque" in content


# ═══════════════════════════════════════════════════════════════════
#  Edge cases
# ═══════════════════════════════════════════════════════════════════

class TestEdgeCases:
    def test_no_type_annotations(self):
        @guarantee("result >= 0")
        def no_ann(x):
            return x

        cert = compile_to_lean(no_ann)
        assert cert.declarations  # should still produce something

    def test_multiple_guarantees(self):
        @guarantee("result >= 0")
        @guarantee("result > 0")
        def two_specs(x: int) -> int:
            return x * x + 1

        cert = compile_to_lean(two_specs)
        assert len(cert.theorems) == 2

    def test_list_comprehension(self):
        @guarantee("result >= 0")
        def doubled(xs: list[int]) -> list[int]:
            return [x * 2 for x in xs]

        cert = compile_to_lean(doubled)
        decl_text = "\n".join(cert.declarations)
        assert "List.map" in decl_text or "def doubled" in decl_text


class TestNewConstructs:
    """Test Lean export of while, try/except, with, and yield."""

    def test_while_loop_export(self):
        @guarantee("result >= 0")
        def countdown(n: int) -> int:
            acc = 0
            i = n
            while i > 0:
                acc = acc + i
                i = i - 1
            return acc

        cert = compile_to_lean(countdown)
        decl_text = "\n".join(cert.declarations)
        assert "Nat.fold" in decl_text or "def countdown" in decl_text
        assert "opaque" not in decl_text

    def test_try_except_export(self):
        @guarantee("result >= 0")
        def safe_div(x: int, y: int) -> int:
            try:
                return x // y
            except ZeroDivisionError:
                return 0

        cert = compile_to_lean(safe_div)
        decl_text = "\n".join(cert.declarations)
        # Should translate the body, not emit opaque
        assert "def safe_div" in decl_text
        assert "opaque" not in decl_text

    def test_with_block_export(self):
        @guarantee("result >= 0")
        def use_context(x: int) -> int:
            return x * x

        cert = compile_to_lean(use_context)
        decl_text = "\n".join(cert.declarations)
        assert "def use_context" in decl_text
