from __future__ import annotations

import pytest

from deppy.proof_decorators import ProofDecoratorConfigurationError, VerificationError, compile_invariant, prove
from deppy.solver.solver_interface import SolverResult, SolverStatus


def test_compile_string_invariant():
    compiled = compile_invariant("result >= x", phase="post")
    assert compiled.phase == "post"
    assert compiled.free_variables == ("result", "x")


def test_annotation_written_and_runtime_success():
    @prove(requires=("x >= 0",), ensures=("result >= x",))
    def inc(x):
        return x + 1

    assert "__proof__" in inc.__annotations__
    pending = inc.__annotations__["__proof__"]
    assert pending["status"] in {"pending", "refuted"}

    assert inc(2) == 3
    artifact = inc.__annotations__["__proof__"]
    assert artifact["status"] == "verified"
    assert all(check["status"] == "verified" for check in artifact["checks"])
    assert artifact["checks"][0]["proof_certificate"]["certificate_hash"]


def test_runtime_failure_embeds_artifact_without_raising_in_non_strict_mode():
    @prove(ensures=("result > x",))
    def bad(x):
        return x

    assert bad(3) == 3
    artifact = bad.__annotations__["__proof__"]
    assert artifact["status"] == "refuted"
    assert artifact["checks"][0]["status"] == "refuted"


def test_strict_mode_raises_verification_error():
    @prove(ensures=("result > x",), strict=True)
    def bad(x):
        return x

    with pytest.raises(VerificationError):
        bad(1)


def test_timeout_behavior(monkeypatch):
    def fake_quick_check(*args, **kwargs):
        return SolverResult(status=SolverStatus.TIMEOUT, explanation="late")

    monkeypatch.setattr("deppy.proof_decorators.decorator.quick_check", fake_quick_check)

    @prove(ensures=("result >= x",))
    def ident(x):
        return x

    ident(5)
    artifact = ident.__annotations__["__proof__"]
    assert artifact["status"] == "timeout"
    assert artifact["checks"][0]["status"] == "timeout"


def test_cache_reuse_by_source_hash():
    def base(x):
        return x + 1

    first = prove(ensures=("result >= x",))(base)
    first_pending = dict(first.__annotations__["__proof__"])
    second = prove(ensures=("result >= x",))(base)

    assert first_pending["from_cache"] is False
    assert second.__annotations__["__proof__"]["from_cache"] is True


def test_unsupported_invariant_syntax_raises():
    with pytest.raises(ProofDecoratorConfigurationError):
        compile_invariant("sum(xs) > 0")
