"""Tests for deppy.contracts.hyperdoctrine — Lawvere hyperdoctrine."""

from __future__ import annotations

import pytest

from deppy.contracts.hyperdoctrine import (
    ContractFiber,
    FunctionSignature,
    Hyperdoctrine,
    PropagationResult,
)


# ── FunctionSignature ────────────────────────────────────────────────────────

class TestFunctionSignature:
    def test_creation(self):
        sig = FunctionSignature(name="f", params=["x", "y"])
        assert sig.name == "f"
        assert sig.return_name == "result"

    def test_default_params(self):
        sig = FunctionSignature(name="f")
        assert sig.params == []


# ── ContractFiber ────────────────────────────────────────────────────────────

class TestContractFiber:
    def test_substitute(self):
        fiber = ContractFiber(
            function=FunctionSignature(name="f", params=["x"]),
            requires=["x > 0"],
            ensures=["result >= 0"],
        )
        sub = fiber.substitute({"x": "data"})
        assert "data > 0" in sub.requires
        assert "result >= 0" in sub.ensures

    def test_substitute_multiple(self):
        fiber = ContractFiber(
            function=FunctionSignature(name="f", params=["x", "y"]),
            requires=["x > 0", "y != 0"],
            ensures=["result == x + y"],
        )
        sub = fiber.substitute({"x": "a", "y": "b"})
        assert "a > 0" in sub.requires
        assert "b != 0" in sub.requires

    def test_weaken(self):
        fiber = ContractFiber(
            function=FunctionSignature(name="f", params=["x"]),
            requires=["x > 0"],
            ensures=["result >= 0"],
        )
        weak = fiber.weaken()
        # weaken drops constraints involving non-param variables
        # For this fiber, x IS a param, so it should be kept
        assert isinstance(weak, ContractFiber)

    def test_strengthen(self):
        fiber = ContractFiber(
            function=FunctionSignature(name="f", params=["x"]),
            requires=["x > 0"],
            ensures=[],
        )
        strong = fiber.strengthen(["x < 100"])
        assert "x > 0" in strong.requires
        assert "x < 100" in strong.requires


# ── Hyperdoctrine ────────────────────────────────────────────────────────────

class TestHyperdoctrine:
    def test_register_function(self):
        hd = Hyperdoctrine()
        hd.register_function("f", params=["x"], requires=["x > 0"], ensures=["result >= 0"])
        assert "f" in hd._fibers

    def test_propagate_simple(self):
        hd = Hyperdoctrine()
        hd.register_function("f", params=["x"], requires=["x > 0"], ensures=["result >= 0"])
        result = hd.propagate_through_call("g", "f", arg_mapping={"x": "data"})
        assert isinstance(result, PropagationResult)
        assert "data > 0" in result.inherited_requires
        assert "result >= 0" in result.inherited_ensures

    def test_propagate_beck_chevalley(self):
        hd = Hyperdoctrine()
        hd.register_function("f", params=["x"], requires=["x > 0"], ensures=["result >= 0"])
        result = hd.propagate_through_call("g", "f", arg_mapping={"x": "data"})
        assert result.beck_chevalley_satisfied

    def test_propagate_unknown_callee(self):
        hd = Hyperdoctrine()
        result = hd.propagate_through_call("g", "unknown_func", arg_mapping={"x": "data"})
        assert len(result.inherited_requires) == 0
        assert len(result.inherited_ensures) == 0

    def test_propagate_no_mapping(self):
        hd = Hyperdoctrine()
        hd.register_function("f", params=["x"], requires=["x > 0"], ensures=["result >= 0"])
        result = hd.propagate_through_call("g", "f")
        # Without mapping, formal params stay unchanged
        assert "x > 0" in result.inherited_requires

    def test_register_from_ast_simple(self):
        hd = Hyperdoctrine()
        source = "def f(x: int) -> str:\n    return str(x)"
        hd.register_from_ast(source)
        assert "f" in hd._fibers

    def test_register_from_ast_none_check(self):
        hd = Hyperdoctrine()
        source = "def f(x):\n    if x is None:\n        raise ValueError\n    return x"
        hd.register_from_ast(source)
        fiber = hd._fibers.get("f")
        assert fiber is not None

    def test_register_from_ast_multiple_functions(self):
        hd = Hyperdoctrine()
        source = "def f(x):\n    return x\ndef g(y):\n    return y"
        hd.register_from_ast(source)
        assert "f" in hd._fibers
        assert "g" in hd._fibers

    def test_propagate_all(self):
        hd = Hyperdoctrine()
        source = "def f(x):\n    return x + 1\ndef g():\n    return f(5)"
        hd.register_from_ast(source)
        results = hd.propagate_all()
        assert isinstance(results, dict)

    def test_multiple_params_propagation(self):
        hd = Hyperdoctrine()
        hd.register_function(
            "f",
            params=["x", "y"],
            requires=["x > 0", "y != 0"],
            ensures=["result == x / y"],
        )
        result = hd.propagate_through_call(
            "g", "f", arg_mapping={"x": "a", "y": "b"})
        assert "a > 0" in result.inherited_requires
        assert "b != 0" in result.inherited_requires

    def test_propagation_result_summary(self):
        result = PropagationResult(
            caller="g",
            callee="f",
            inherited_requires=["x > 0"],
            inherited_ensures=["result >= 0"],
        )
        summary = result.summary()
        assert "g" in summary or "f" in summary


class TestSubstitutionEdgeCases:
    """Test that variable substitution handles edge cases properly."""

    def test_no_substring_replacement(self):
        """'x' should not be replaced inside 'extra'."""
        hd = Hyperdoctrine()
        hd.register_function("f", params=["x"], requires=["extra > 0"])
        result = hd.propagate_through_call("g", "f", arg_mapping={"x": "data"})
        # 'extra' should NOT become 'edatatra'
        for req in result.inherited_requires:
            assert "edatatra" not in req

    def test_result_in_ensures(self):
        hd = Hyperdoctrine()
        hd.register_function("f", params=[], ensures=["result > 0"])
        result = hd.propagate_through_call("g", "f")
        assert "result > 0" in result.inherited_ensures
