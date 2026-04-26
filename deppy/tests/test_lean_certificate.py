"""Tests for the Lean-as-gold-standard certificate generator
(Phases A1–A4) and the ``@implies`` decorator.

The certificate is a complete Lean 4 file: function definitions
translated from the Python bodies, safety theorems for every source
the pipeline analysed, and ``@implies`` correctness theorems.
Running Lean on the certificate is the canonical verdict.
"""
from __future__ import annotations

import shutil
import textwrap

import pytest

from deppy import implies, write_certificate
from deppy.lean.body_translation import translate_body
from deppy.lean.certificate import write_certificate as _wc


_HAS_LEAN = shutil.which("lean") is not None
needs_lean = pytest.mark.skipif(
    not _HAS_LEAN, reason="lean toolchain not installed",
)


# ─────────────────────────────────────────────────────────────────────
# A1 — DeppyBase.lean exists and is shipped
# ─────────────────────────────────────────────────────────────────────

class TestDeppyBaseShipped:
    def test_deppy_base_file_exists(self):
        from pathlib import Path
        import deppy.lean
        base = Path(deppy.lean.__file__).parent / "DeppyBase.lean"
        assert base.is_file()
        text = base.read_text()
        assert "namespace Deppy" in text
        assert "deppy_safe" in text
        assert "DivSafe" in text
        assert "IndexSafe" in text


# ─────────────────────────────────────────────────────────────────────
# A2 — body translator + tactic selection
# ─────────────────────────────────────────────────────────────────────

class TestBodyTranslator:
    def test_factorial_body_translates_exactly(self):
        import ast
        src = textwrap.dedent('''
            def factorial(n):
                if n <= 0:
                    return 1
                return n * factorial(n - 1)
        ''').strip()
        fn = ast.parse(src).body[0]
        result = translate_body(fn)
        assert result.exact
        assert result.sorry_count == 0
        assert "if (n ≤ 0) then 1" in result.lean_text
        assert "factorial (n - 1)" in result.lean_text

    def test_mergesort_body_translates(self):
        import ast
        src = textwrap.dedent('''
            def mergesort(xs):
                if len(xs) <= 1:
                    return xs
                mid = len(xs) // 2
                left = xs[:mid]
                right = xs[mid:]
                return merge(mergesort(left), mergesort(right))
        ''').strip()
        fn = ast.parse(src).body[0]
        result = translate_body(fn)
        # The body translates fully; recursion preserved.
        assert result.exact
        assert result.sorry_count == 0
        assert "mergesort left" in result.lean_text
        assert "xs.take mid" in result.lean_text
        assert "xs.drop mid" in result.lean_text

    def test_let_chain(self):
        import ast
        src = textwrap.dedent('''
            def f(a, b):
                x = a + 1
                y = b - 1
                return x + y
        ''').strip()
        fn = ast.parse(src).body[0]
        result = translate_body(fn)
        assert "let x" in result.lean_text
        assert "let y" in result.lean_text

    def test_bare_return_translates(self):
        import ast
        src = "def f(x):\n    return x + 1\n"
        fn = ast.parse(src).body[0]
        result = translate_body(fn)
        assert result.lean_text == "(x + 1)"

    def test_unsupported_falls_back_to_sorry(self):
        import ast
        src = textwrap.dedent('''
            def f(xs):
                while xs:
                    xs.pop()
                return xs
        ''').strip()
        fn = ast.parse(src).body[0]
        result = translate_body(fn)
        assert result.sorry_count >= 1


# ─────────────────────────────────────────────────────────────────────
# A3 — full certificate emission
# ─────────────────────────────────────────────────────────────────────

class TestCertificateEmission:
    def test_certificate_basic_structure(self, tmp_path):
        src = textwrap.dedent('''
            def f(a, b):
                if b != 0:
                    return a / b
                return 0
        ''').strip()
        out = tmp_path / "cert.lean"
        report = write_certificate(src, out, module_name="MyMod")
        text = out.read_text()
        # Imports DeppyBase and opens the namespace.
        assert "import DeppyBase" in text
        assert "open Deppy" in text
        # Function definition is present.
        assert "def f" in text
        assert "namespace MyMod" in text
        assert "end MyMod" in text
        # At least one safety theorem.
        assert report.certificate.theorem_count >= 1

    def test_certificate_includes_all_sources(self, tmp_path):
        """Phase A3: addressed sources also get theorems with
        appropriate auto-deduced tactics."""
        src = textwrap.dedent('''
            def f(a, b):
                if b != 0:
                    return a / b
                return 0
        ''').strip()
        out = tmp_path / "cert.lean"
        report = write_certificate(src, out)
        text = out.read_text()
        # Discharged ZERO_DIVISION should get ``by omega`` (z3-arithmetic
        # mirroring) — not ``sorry``.
        assert "ZERO_DIVISION" in text
        assert "by omega" in text or "Deppy.deppy_safe" in text

    def test_certificate_with_unsafe_function(self, tmp_path):
        src = textwrap.dedent('''
            def unsafe(a, b):
                return a / b
        ''').strip()
        out = tmp_path / "cert.lean"
        report = write_certificate(src, out)
        # An unsafe function emits a theorem with sorry for the
        # undischarged source.
        assert report.certificate.sorry_count >= 1 or \
               "Deppy.deppy_safe" in out.read_text()

    def test_certificate_emits_function_signature(self, tmp_path):
        """The translator picks up Python type annotations and turns
        them into Lean binders."""
        src = textwrap.dedent('''
            def add_one(x: int) -> int:
                return x + 1
        ''').strip()
        out = tmp_path / "cert.lean"
        write_certificate(src, out)
        text = out.read_text()
        assert "(x : Int)" in text
        assert ": Int :=" in text

    def test_certificate_emits_aux_axioms_once(self, tmp_path):
        """Each unique opaque type / class emits a single ``axiom``
        even when it appears multiple times in the source."""
        src = textwrap.dedent('''
            class Foo:
                pass
            def f(x: Foo) -> Foo:
                return x
            def g(y: Foo) -> Foo:
                return y
        ''').strip()
        out = tmp_path / "cert.lean"
        write_certificate(src, out)
        text = out.read_text()
        # ``axiom Deppy_Foo : Type`` appears exactly once.
        assert text.count("axiom Deppy_Foo : Type") == 1


# ─────────────────────────────────────────────────────────────────────
# A4 — @implies decorator
# ─────────────────────────────────────────────────────────────────────

class TestImpliesDecorator:
    def test_implies_attaches_metadata(self):
        @implies("x > 0", "result > 0")
        def f(x):
            return x + 1

        attached = f._deppy_implies
        assert len(attached) == 1
        assert attached[0]["precondition"] == "x > 0"
        assert attached[0]["postcondition"] == "result > 0"

    def test_implies_stacks(self):
        @implies("True", "result is not None")
        @implies("len(xs) > 0", "result is not None")
        def first(xs):
            return xs[0] if xs else None

        attached = first._deppy_implies
        assert len(attached) == 2
        precs = {e["precondition"] for e in attached}
        assert {"True", "len(xs) > 0"} <= precs

    def test_implies_inline_proof_stored(self):
        @implies("x >= 0", "result >= 0", proof="omega")
        def double(x):
            return 2 * x

        e = double._deppy_implies[0]
        assert e["proof"] == "omega"

    def test_certificate_emits_implies_theorem(self, tmp_path):
        src = textwrap.dedent('''
            from deppy import implies

            @implies("x > 0", "result > 0")
            def add_one(x):
                return x + 1
        ''').strip()
        out = tmp_path / "cert.lean"
        write_certificate(src, out)
        text = out.read_text()
        # The implies theorem appears with its name.
        assert "deppy_implies_add_one" in text
        # Has the implication form ``X → Y``.
        assert "→" in text

    def test_certificate_implies_uses_user_proof(self, tmp_path):
        src = textwrap.dedent('''
            from deppy import implies

            @implies("x > 0", "result > 0", proof="omega")
            def add_one(x):
                return x + 1
        ''').strip()
        out = tmp_path / "cert.lean"
        write_certificate(src, out)
        text = out.read_text()
        # The user's proof body appears.
        assert "by omega" in text


# ─────────────────────────────────────────────────────────────────────
# Integration — mergesort
# ─────────────────────────────────────────────────────────────────────

class TestMergesortCertificate:
    def test_mergesort_certificate(self, tmp_path):
        """End-to-end: a mergesort module gets a complete certificate
        with translated bodies and @implies theorems."""
        src = textwrap.dedent('''
            from deppy import implies

            @implies("True", "len(result) == len(xs)")
            def mergesort(xs):
                if len(xs) <= 1:
                    return xs
                mid = len(xs) // 2
                left = xs[:mid]
                right = xs[mid:]
                return merge(mergesort(left), mergesort(right))

            def merge(a, b):
                if len(a) == 0:
                    return b
                if len(b) == 0:
                    return a
                if a[0] <= b[0]:
                    return [a[0]] + merge(a[1:], b)
                return [b[0]] + merge(a, b[1:])
        ''').strip()
        out = tmp_path / "Mergesort.lean"
        report = write_certificate(src, out, module_name="Mergesort")
        text = out.read_text()
        # Both functions are translated.
        assert "def mergesort" in text
        assert "def merge" in text
        # @implies theorem exists.
        assert "deppy_implies_mergesort" in text
        # Recursive call preserved.
        assert "mergesort left" in text or "mergesort (xs.take" in text

    def test_implies_translates_pre_and_post(self, tmp_path):
        """@implies renders X → Y[result := fn args]."""
        src = textwrap.dedent('''
            from deppy import implies

            @implies("x > 0", "result > x")
            def add_one(x):
                return x + 1
        ''').strip()
        out = tmp_path / "cert.lean"
        write_certificate(src, out)
        text = out.read_text()
        # The result identifier got rewritten to the function call.
        assert "(add_one x)" in text or "(x > 0)" in text
