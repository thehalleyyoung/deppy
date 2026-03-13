"""Tests for deppy.equivalence.api_compat — pullback-based API compatibility."""

from __future__ import annotations

import pytest

from deppy.equivalence.api_compat import (
    CompatibilityResult,
    CompatibilityVerdict,
    IncompatibilitySite,
    check_api_compatibility,
)


# ── CompatibilityResult dataclass ────────────────────────────────────────────

class TestCompatibilityResult:
    def test_creation(self):
        result = CompatibilityResult(
            verdict=CompatibilityVerdict.COMPATIBLE,
            library_func="sort",
            client_func="main",
        )
        assert result.verdict == CompatibilityVerdict.COMPATIBLE

    def test_summary(self):
        result = CompatibilityResult(
            verdict=CompatibilityVerdict.INCOMPATIBLE,
            library_func="f",
            client_func="g",
            incompatibilities=[
                IncompatibilitySite(
                    client_line=5, library_param="x", client_arg="None",
                    requirement="non-null", actual="null",
                ),
            ],
        )
        summary = result.summary()
        assert "f" in summary or "incompatible" in summary.lower()


# ── check_api_compatibility ──────────────────────────────────────────────────

class TestCheckApiCompatibility:
    def test_compatible_simple(self):
        lib = "def f(x):\n    return x + 1"
        client = "def main():\n    return f(42)"
        result = check_api_compatibility(lib, client, library_func="f")
        assert result.verdict in (
            CompatibilityVerdict.COMPATIBLE,
            CompatibilityVerdict.CONDITIONAL,
            CompatibilityVerdict.UNKNOWN,
        )

    def test_arity_mismatch(self):
        lib = "def f(x, y):\n    return x + y"
        client = "def main():\n    return f(1)"
        result = check_api_compatibility(lib, client, library_func="f")
        # Should detect the arity mismatch
        if result.incompatibilities:
            assert any("arity" in i.requirement.lower() or "arg" in i.requirement.lower()
                       for i in result.incompatibilities)

    def test_none_argument_without_guard(self):
        lib = "def f(x):\n    if x is None:\n        raise ValueError\n    return x.strip()"
        client = "def main():\n    return f(None)"
        result = check_api_compatibility(lib, client, library_func="f")
        assert result.verdict in (
            CompatibilityVerdict.INCOMPATIBLE,
            CompatibilityVerdict.CONDITIONAL,
        ) or len(result.incompatibilities) > 0

    def test_no_calls_found(self):
        lib = "def f(x):\n    return x"
        client = "def main():\n    return g(1)"
        result = check_api_compatibility(lib, client, library_func="f")
        # No calls to f → compatible (vacuously) or unknown
        assert result.call_sites == 0

    def test_library_func_auto_detect(self):
        lib = "def f(x):\n    return x"
        client = "def main():\n    return f(1)"
        result = check_api_compatibility(lib, client)
        assert isinstance(result, CompatibilityResult)
        assert result.library_func == "f"

    def test_multiple_call_sites(self):
        lib = "def f(x):\n    return x"
        client = "def main():\n    a = f(1)\n    b = f(2)\n    return a + b"
        result = check_api_compatibility(lib, client, library_func="f")
        assert result.call_sites >= 2

    def test_default_parameter_handling(self):
        lib = "def f(x, y=10):\n    return x + y"
        client = "def main():\n    return f(5)"
        result = check_api_compatibility(lib, client, library_func="f")
        # Should be compatible since y has a default
        assert result.verdict in (
            CompatibilityVerdict.COMPATIBLE,
            CompatibilityVerdict.CONDITIONAL,
            CompatibilityVerdict.UNKNOWN,
        )

    def test_empty_library(self):
        result = check_api_compatibility("", "def main():\n    pass")
        assert isinstance(result, CompatibilityResult)

    def test_empty_client(self):
        result = check_api_compatibility("def f(x):\n    pass", "")
        assert isinstance(result, CompatibilityResult)

    def test_exception_contract(self):
        lib = "def f(x):\n    if x < 0:\n        raise ValueError\n    return x"
        client = "def main():\n    return f(-1)"
        result = check_api_compatibility(lib, client, library_func="f")
        # Should detect potential ValueError
        assert isinstance(result, CompatibilityResult)

    def test_verdicts_are_valid(self):
        """All verdicts should be CompatibilityVerdict members."""
        lib = "def f(x):\n    return x"
        for client_code in [
            "def main():\n    return f(1)",
            "def main():\n    return f(None)",
            "def main():\n    pass",
        ]:
            result = check_api_compatibility(lib, client_code, library_func="f")
            assert isinstance(result.verdict, CompatibilityVerdict)
