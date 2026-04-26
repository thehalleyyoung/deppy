"""Tests for round-3 audit fixes (B11/B12/B13 + F9 + D7).

Each block guards one fix from the audit:

* F9   — _call_predicate uses inspect.signature, not TypeError-msg matching.
* B11  — protocol_spec really records protocol methods; trust_boundary
         supports both decorator and callable forms; safe_patch runs
         a real equivalence check.
* B12  — ConditionalDuckPath / FiberedLookup verify cleanly through
         the kernel and reject invalid inputs.
* B13  — EquivMethod is a str-subclass enum; CLI accepts --sidecar.
* D7   — duck_path supports the 3-arg ``(Protocol, val1, val2)`` form;
         Fibration.from_metaclass enumerates subclasses + rejects non-types.
"""
from __future__ import annotations

import pytest


# ─────────────────────────────────────────────────────────────────────
# F9 — _call_predicate signature handling
# ─────────────────────────────────────────────────────────────────────

def test_call_predicate_handles_zero_arg_predicate():
    from deppy.async_verify import _call_predicate
    assert _call_predicate(lambda: True, (1, 2), {"x": 3}) is True


def test_call_predicate_handles_one_arg_predicate():
    from deppy.async_verify import _call_predicate
    assert _call_predicate(lambda x: x > 0, (5, 9), {}) is True
    assert _call_predicate(lambda x: x > 0, (-1, 9), {}) is False


def test_call_predicate_propagates_internal_typeerror():
    """If the predicate body itself raises TypeError, propagate it."""
    from deppy.async_verify import _call_predicate, ContractViolation

    def bad(x):
        raise TypeError("internal explosion")

    with pytest.raises((TypeError, ContractViolation)):
        _call_predicate(bad, (1,), {})


def test_call_predicate_rejects_non_bool_return():
    from deppy.async_verify import _call_predicate, ContractViolation
    with pytest.raises(ContractViolation):
        _call_predicate(lambda x: "yes", (1,), {})


# ─────────────────────────────────────────────────────────────────────
# B11 — protocol_spec / trust_boundary / safe_patch
# ─────────────────────────────────────────────────────────────────────

def test_protocol_spec_records_methods():
    from typing import Protocol
    from deppy import protocol_spec

    @protocol_spec
    class Renderable(Protocol):
        def render(self) -> str: ...
        def height(self) -> int: ...

    assert Renderable._deppy_protocol_spec is True
    assert set(Renderable._deppy_protocol_methods) == {"render", "height"}


def test_protocol_spec_with_description():
    from typing import Protocol
    from deppy import protocol_spec

    @protocol_spec("things that render to a string")
    class Renderable(Protocol):
        def render(self) -> str: ...

    assert Renderable._deppy_protocol_spec is True
    assert Renderable._deppy_protocol_description == \
        "things that render to a string"


def test_trust_boundary_decorator_form():
    from deppy import trust_boundary

    @trust_boundary
    def legacy(x):
        return x * 2

    assert legacy._deppy_trust_boundary is True
    assert legacy(5) == 10


def test_trust_boundary_callable_form_validates_return_type():
    from deppy import trust_boundary

    def legacy_compute(data, factor):
        return [item * factor for item in data]

    result = trust_boundary(
        legacy_compute,
        args=([1, 2, 3], 2),
        expected_return=list,
        expected_properties=["len(result) == len(data)"],
    )
    assert result == [2, 4, 6]


def test_trust_boundary_callable_form_rejects_wrong_type():
    from deppy import trust_boundary

    def returns_int():
        return 42

    with pytest.raises(TypeError):
        trust_boundary(
            returns_int,
            args=(),
            expected_return=list,
        )


def test_trust_boundary_callable_form_rejects_failed_property():
    from deppy import trust_boundary

    def returns_short():
        return [1]

    with pytest.raises(ValueError):
        trust_boundary(
            returns_short,
            args=(),
            expected_return=list,
            expected_properties=["len(result) >= 5"],
        )


def test_safe_patch_installs_when_signatures_match():
    from deppy.patching import safe_patch

    class L1:
        def log(self, message: str) -> None:
            pass

    @safe_patch(L1, "log")
    def log_patched(self, message: str) -> None:
        pass

    # The wrapper is installed on L1.
    assert L1.log is log_patched
    assert log_patched._deppy_safe_patch is True
    assert log_patched._deppy_patch_method == "log"


def test_safe_patch_rejects_arity_mismatch():
    from deppy.patching import safe_patch, SafePatchRejected

    class L2:
        def log(self, message: str) -> None:
            pass

    with pytest.raises(SafePatchRejected):
        @safe_patch(L2, "log")
        def log_broken(self, message: str, extra: str) -> None:
            pass


def test_safe_patch_rejects_unknown_method():
    from deppy.patching import safe_patch, SafePatchRejected

    class L3:
        def log(self, m: str) -> None:
            pass

    with pytest.raises(SafePatchRejected):
        @safe_patch(L3, "noSuchMethod")
        def replacement(self, m: str) -> None:
            pass


def test_safe_patch_install_false_skips_class_mutation():
    from deppy.patching import safe_patch

    class L4:
        def log(self, message: str) -> None:
            pass

    original = L4.log

    @safe_patch(L4, "log", install=False)
    def log_alt(self, message: str) -> None:
        pass

    assert L4.log is original  # not installed
    assert log_alt._deppy_safe_patch is True


# ─────────────────────────────────────────────────────────────────────
# B12 — ConditionalDuckPath / FiberedLookup
# ─────────────────────────────────────────────────────────────────────

def test_conditional_duck_path_construct_validates_condition():
    from deppy import ConditionalDuckPath, DuckPath

    base = DuckPath.auto_construct(int, int)
    with pytest.raises(ValueError):
        ConditionalDuckPath.construct(condition="", evidence=base)
    with pytest.raises(ValueError):
        ConditionalDuckPath.construct(condition="   ", evidence=base)


def test_conditional_duck_path_construct_rejects_non_proof_evidence():
    from deppy import ConditionalDuckPath
    with pytest.raises(TypeError):
        ConditionalDuckPath.construct(
            condition="x > 0", evidence="not a proof",  # type: ignore[arg-type]
        )


def test_fibered_lookup_repr_includes_attribute_and_method():
    from deppy import FiberedLookup, DuckPath
    base = DuckPath.auto_construct(int, int)
    fl = FiberedLookup(
        fiber_over="_target", base_path=base,
        transport_through="__getattr__",
    )
    s = repr(fl)
    assert "_target" in s
    assert "__getattr__" in s


def test_kernel_verifies_conditional_duck_path():
    """The kernel accepts a ConditionalDuckPath whose evidence is a
    valid DuckPath, clamping the result to STRUCTURAL_CHAIN trust."""
    from deppy import ProofKernel, ConditionalDuckPath, DuckPath, TrustLevel
    from deppy.core.kernel import Refl, Var
    from deppy.core.types import PyClassType
    from deppy.core.kernel import Judgment, JudgmentKind, Context

    base = DuckPath.auto_construct(int, int)
    cdp = ConditionalDuckPath.construct(
        condition="isinstance(self._target, Iterable)",
        evidence=base,
    )

    kernel = ProofKernel()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=Context(),
        type_=PyClassType(name="Renderable"),
    )
    r = kernel.verify(Context(), goal, cdp)
    assert r.success
    assert r.trust_level.value <= TrustLevel.STRUCTURAL_CHAIN.value


def test_kernel_rejects_fibered_lookup_with_invalid_attribute():
    from deppy import ProofKernel, FiberedLookup, DuckPath
    from deppy.core.kernel import Judgment, JudgmentKind, Context
    from deppy.core.types import PyClassType

    base = DuckPath.auto_construct(int, int)
    fl = FiberedLookup(
        fiber_over="not an identifier!",
        base_path=base,
        transport_through="__getattr__",
    )
    kernel = ProofKernel()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=Context(),
        type_=PyClassType(name="Renderable"),
    )
    r = kernel.verify(Context(), goal, fl)
    assert not r.success
    assert "fiber attribute" in r.message.lower()


# ─────────────────────────────────────────────────────────────────────
# B13 — EquivMethod + sidecar CLI
# ─────────────────────────────────────────────────────────────────────

def test_equiv_method_str_subclass_compatibility():
    from deppy import EquivMethod
    assert EquivMethod.Z3 == "z3"
    assert EquivMethod.TESTING == "testing"
    assert EquivMethod.SPEC == "spec"
    assert EquivMethod.SPEC_Z3 == "spec+z3"
    assert EquivMethod.INCONCLUSIVE == "inconclusive"


def test_equiv_method_values_and_validation():
    from deppy import EquivMethod
    assert "z3" in EquivMethod.values()
    assert "spec+z3" in EquivMethod.values()
    assert EquivMethod.is_valid("z3")
    assert not EquivMethod.is_valid("foo")


def test_cli_check_accepts_sidecar_flag(tmp_path):
    """Smoke test: the --sidecar flag is plumbed through and
    rejects a missing path with exit 3."""
    import subprocess
    import sys

    src = tmp_path / "m.py"
    src.write_text("def f(x: int) -> int:\n    return x\n")
    missing_sidecar = tmp_path / "no.deppy"
    proc = subprocess.run(
        [sys.executable, "-m", "deppy", "check",
         str(src), "--sidecar", str(missing_sidecar)],
        capture_output=True, text=True, timeout=30,
    )
    assert proc.returncode == 3
    assert "sidecar" in (proc.stderr + proc.stdout).lower()


# ─────────────────────────────────────────────────────────────────────
# D7 — duck_path 3-arg form + Fibration.from_metaclass
# ─────────────────────────────────────────────────────────────────────

def test_duck_path_three_arg_form():
    from typing import Iterable
    from deppy import duck_path

    p = duck_path(Iterable[int], [1, 2, 3], (1, 2, 3))
    assert p.type_a is list
    assert p.type_b is tuple
    proven = {name for name, _ in p.method_proofs}
    assert "__iter__" in proven  # Iterable's defining method


def test_duck_path_two_arg_form_unchanged():
    """The legacy two-arg form must keep working."""
    from deppy import duck_path
    p = duck_path(int, int)
    assert p.type_a is int
    assert p.type_b is int


def test_duck_path_explicit_witnesses_form_unchanged():
    from deppy import duck_path
    from deppy.core.kernel import Refl, Var
    p = duck_path(int, int, ("foo", Refl(term=Var("foo"))))
    methods = {name for name, _ in p.method_proofs}
    assert "foo" in methods


def test_fibration_from_metaclass_rejects_non_type():
    from deppy.hott import Fibration
    with pytest.raises(TypeError):
        Fibration.from_metaclass("not a class")  # type: ignore[arg-type]


def test_fibration_from_metaclass_enumerates_subclasses():
    from deppy.hott import Fibration

    class Base:
        pass

    class Mid(Base):
        pass

    class Leaf(Mid):
        pass

    fib = Fibration.from_metaclass(Base)
    assert hasattr(fib, "subclasses")
    assert Mid in fib.subclasses
    assert Leaf in fib.subclasses
