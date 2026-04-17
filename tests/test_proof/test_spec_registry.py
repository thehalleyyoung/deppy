"""Tests for the spec registry and trust-as-proven-spec enforcement."""
from __future__ import annotations

import pytest
from cctt.proof_theory.spec_registry import (
    ProofStatus, ProvenSpec, SpecRef, SpecRegistry,
    CallObligation, ObligationResult,
    extract_call_obligations, check_obligation, check_all_obligations,
    compute_proof_order,
)
from cctt.proof_theory.spec_inference import C4Spec, SpecSource


class TestProofStatus:
    def test_trusted_statuses(self):
        assert ProofStatus.Z3_PROVED.is_trusted
        assert ProofStatus.STRUCTURALLY_PROVED.is_trusted
        assert ProofStatus.ASSUMED.is_trusted

    def test_untrusted_statuses(self):
        assert not ProofStatus.UNPROVED.is_trusted
        assert not ProofStatus.CANDIDATE.is_trusted
        assert not ProofStatus.FAILED.is_trusted


class TestProvenSpec:
    def test_candidate_only(self):
        ps = ProvenSpec(
            qualname="math.sqrt",
            candidate_spec=C4Spec(ensures=["result >= 0"]),
        )
        assert ps.usable_spec is None
        assert ps.usable_ensures == []

    def test_proved_spec(self):
        ps = ProvenSpec(
            qualname="math.sqrt",
            candidate_spec=C4Spec(ensures=["result >= 0", "result * result == x"]),
            proved_spec=C4Spec(ensures=["result >= 0"]),
            proof_status=ProofStatus.Z3_PROVED,
        )
        assert ps.usable_spec is not None
        assert ps.usable_ensures == ["result >= 0"]
        # Candidate has more, but we can only use proved
        assert len(ps.candidate_spec.ensures) == 2
        assert len(ps.usable_ensures) == 1

    def test_failed_spec(self):
        ps = ProvenSpec(
            qualname="bad_func",
            candidate_spec=C4Spec(ensures=["result > 0"]),
            proved_spec=C4Spec(ensures=["result > 0"]),
            proof_status=ProofStatus.FAILED,
        )
        # Failed status → not usable even though proved_spec exists
        assert ps.usable_spec is None


class TestSpecRef:
    def test_covers_exact_match(self):
        ref = SpecRef(
            qualname="math.sqrt",
            ensures=("result >= 0", "isinstance(result, float)"),
            status=ProofStatus.Z3_PROVED,
        )
        assert ref.covers("result >= 0")
        assert ref.covers("isinstance(result, float)")

    def test_covers_substring(self):
        ref = SpecRef(
            qualname="math.sqrt",
            ensures=("result >= 0 and result * result == x",),
            status=ProofStatus.Z3_PROVED,
        )
        assert ref.covers("result >= 0")

    def test_does_not_cover(self):
        ref = SpecRef(
            qualname="math.sqrt",
            ensures=("isinstance(result, float)",),
            status=ProofStatus.Z3_PROVED,
        )
        assert not ref.covers("result >= 0")

    def test_serialization(self):
        ref = SpecRef(
            qualname="math.sqrt",
            ensures=("result >= 0",),
            requires=("x >= 0",),
            status=ProofStatus.Z3_PROVED,
            source="registry",
        )
        j = ref.to_json()
        ref2 = SpecRef.from_json(j)
        assert ref2.qualname == "math.sqrt"
        assert ref2.ensures == ("result >= 0",)
        assert ref2.status == ProofStatus.Z3_PROVED

    def test_is_trusted(self):
        assert SpecRef("f", status=ProofStatus.Z3_PROVED).is_trusted
        assert not SpecRef("f", status=ProofStatus.UNPROVED).is_trusted


class TestSpecRegistry:
    def test_register_candidate(self):
        reg = SpecRegistry()
        reg.register_candidate("math.sqrt", C4Spec(ensures=["result >= 0"]))
        ps = reg.get_spec("math.sqrt")
        assert ps is not None
        assert ps.proof_status == ProofStatus.UNPROVED
        assert ps.usable_ensures == []

    def test_register_proved(self):
        reg = SpecRegistry()
        reg.register_proved("math.sqrt", C4Spec(
            requires=["x >= 0"],
            ensures=["result >= 0"],
        ))
        ps = reg.get_spec("math.sqrt")
        assert ps is not None
        assert ps.proof_status == ProofStatus.Z3_PROVED
        assert ps.usable_ensures == ["result >= 0"]

    def test_get_ref(self):
        reg = SpecRegistry()
        reg.register_proved("math.sqrt", C4Spec(ensures=["result >= 0"]))
        ref = reg.get_ref("math.sqrt")
        assert ref is not None
        assert ref.qualname == "math.sqrt"
        assert "result >= 0" in ref.ensures

    def test_has_proven(self):
        reg = SpecRegistry()
        reg.register_candidate("math.sqrt", C4Spec())
        assert not reg.has_proven("math.sqrt")
        reg.register_proved("math.sqrt", C4Spec(ensures=["result >= 0"]))
        assert reg.has_proven("math.sqrt")

    def test_proved_names(self):
        reg = SpecRegistry()
        reg.register_proved("a", C4Spec())
        reg.register_candidate("b", C4Spec())
        reg.register_proved("c", C4Spec())
        assert reg.proved_names == {"a", "c"}
        assert reg.unproved_names == {"b"}

    def test_stats(self):
        reg = SpecRegistry()
        reg.register_proved("a", C4Spec())
        reg.register_proved("b", C4Spec())
        reg.register_candidate("c", C4Spec())
        stats = reg.stats()
        assert stats["z3_proved"] == 2
        assert stats["unproved"] == 1

    def test_resolve_trust_refs_with_proven(self):
        reg = SpecRegistry()
        reg.register_proved("math.sqrt", C4Spec(ensures=["result >= 0"]))
        refs = reg.resolve_trust_refs(["math.sqrt", "assumed:unknown"])
        assert len(refs) == 2
        assert refs[0].qualname == "math.sqrt"
        assert refs[0].is_trusted
        assert "result >= 0" in refs[0].ensures
        assert refs[1].qualname == "assumed:unknown"

    def test_resolve_trust_refs_unresolved(self):
        reg = SpecRegistry()
        refs = reg.resolve_trust_refs(["unknown.func"])
        assert len(refs) == 1
        assert refs[0].status == ProofStatus.UNPROVED
        assert refs[0].source == "unresolved"

    def test_resolve_circular(self):
        reg = SpecRegistry()
        refs = reg.resolve_trust_refs(["CIRCULAR:sympy.core.add"])
        assert refs[0].status == ProofStatus.FAILED

    def test_resolve_kernel_refs(self):
        reg = SpecRegistry()
        refs = reg.resolve_trust_refs(["lean.C4.Reduction", "z3.Solver.check"])
        assert all(r.status == ProofStatus.Z3_PROVED for r in refs)
        assert all(r.source == "kernel" for r in refs)


class TestCallObligations:
    def test_extract_direct_call(self):
        reg = SpecRegistry()
        reg.register_proved("helper", C4Spec(ensures=["result >= 0"]))

        src = "def f(x):\n    y = helper(x)\n    return y + 1"
        obls = extract_call_obligations(src, "f", reg, "mod.f")
        assert len(obls) == 1
        assert obls[0].callee == "helper"
        assert obls[0].caller == "mod.f"

    def test_no_obligations_for_unregistered(self):
        reg = SpecRegistry()
        src = "def f(x):\n    return unknown(x)"
        obls = extract_call_obligations(src, "f", reg)
        assert len(obls) == 0

    def test_check_obligation_satisfied(self):
        reg = SpecRegistry()
        reg.register_proved("helper", C4Spec(ensures=["result >= 0"]))
        obl = CallObligation(
            caller="f", callee="helper",
            assumed=["result >= 0"],
        )
        result = check_obligation(obl, reg)
        assert result.satisfied

    def test_check_obligation_unsatisfied(self):
        reg = SpecRegistry()
        reg.register_proved("helper", C4Spec(
            ensures=["isinstance(result, int)"],
        ))
        obl = CallObligation(
            caller="f", callee="helper",
            assumed=["result > 0"],  # Assumes more than proved!
        )
        result = check_obligation(obl, reg)
        assert not result.satisfied
        assert "result > 0" in result.unsatisfied

    def test_check_obligation_no_spec(self):
        reg = SpecRegistry()
        obl = CallObligation(caller="f", callee="unknown")
        result = check_obligation(obl, reg)
        assert not result.satisfied
        assert "No spec" in result.reason

    def test_check_all_obligations(self):
        reg = SpecRegistry()
        reg.register_proved("helper", C4Spec(ensures=["result >= 0"]))
        obls = [
            CallObligation(caller="f", callee="helper", assumed=["result >= 0"]),
            CallObligation(caller="f", callee="helper", assumed=["result > 100"]),
        ]
        results, all_ok = check_all_obligations(obls, reg)
        assert not all_ok
        assert results[0].satisfied
        assert not results[1].satisfied


class TestProofOrder:
    def test_linear_chain(self):
        graph = {"a": {"b"}, "b": {"c"}, "c": set()}
        order = compute_proof_order(graph)
        # c first (leaf), then b, then a
        flat = [n for scc in order for n in scc]
        assert flat.index("c") < flat.index("b")
        assert flat.index("b") < flat.index("a")

    def test_cycle_detection(self):
        graph = {"a": {"b"}, "b": {"a"}}
        order = compute_proof_order(graph)
        # a and b should be in the same SCC
        for scc in order:
            if "a" in scc:
                assert "b" in scc

    def test_diamond(self):
        graph = {"a": {"b", "c"}, "b": {"d"}, "c": {"d"}, "d": set()}
        order = compute_proof_order(graph)
        flat = [n for scc in order for n in scc]
        assert flat.index("d") < flat.index("b")
        assert flat.index("d") < flat.index("c")
        assert flat.index("b") < flat.index("a")
        assert flat.index("c") < flat.index("a")

    def test_empty_graph(self):
        order = compute_proof_order({})
        assert order == []

    def test_isolated_nodes(self):
        graph = {"a": set(), "b": set(), "c": set()}
        order = compute_proof_order(graph)
        assert len(order) == 3  # 3 singleton SCCs


class TestRegistryWithOrchestrator:
    """Test that the registry integrates with the orchestrator."""

    def test_make_annotation_with_registry(self):
        from cctt.proof_theory.library_proof_orchestrator import (
            _make_annotation, Definition, DefKind,
            RefinedType, PathSpec, FiberSpec, CubicalPathSpec,
            ProofStrategy,
        )

        reg = SpecRegistry()
        reg.register_proved("math.sqrt", C4Spec(ensures=["result >= 0"]))

        defn = Definition(
            name="f", qualname="mod.f", kind=DefKind.FUNCTION,
            lineno=1, end_lineno=3,
            source="def f(x): return math.sqrt(x)",
            docstring="",
            params=["x"],
            return_annotation=None,
            decorators=[],
            class_name=None,
            module_path="mod",
        )

        ann = _make_annotation(
            defn, PathSpec(lhs="f(x)", rhs="sqrt(x)", over=RefinedType()),
            RefinedType(), RefinedType(),
            "f computes sqrt", [], ProofStrategy.REFL, {},
            [], ["math.sqrt"], True, [], "test_lib",
            registry=reg,
        )

        assert ann.trust_refs is not None
        assert len(ann.trust_refs) == 1
        assert ann.trust_refs[0]["qualname"] == "math.sqrt"
        assert "result >= 0" in ann.trust_refs[0]["ensures"]

    def test_make_annotation_without_registry(self):
        from cctt.proof_theory.library_proof_orchestrator import (
            _make_annotation, Definition, DefKind,
            RefinedType, PathSpec, FiberSpec, CubicalPathSpec,
            ProofStrategy,
        )

        defn = Definition(
            name="f", qualname="mod.f", kind=DefKind.FUNCTION,
            lineno=1, end_lineno=3,
            source="def f(x): return x",
            docstring="",
            params=["x"],
            return_annotation=None,
            decorators=[],
            class_name=None,
            module_path="mod",
        )

        ann = _make_annotation(
            defn, PathSpec(lhs="f(x)", rhs="x", over=RefinedType()),
            RefinedType(), RefinedType(),
            "identity", [], ProofStrategy.REFL, {},
            [], ["assumed:stub"], True, [], "test_lib",
        )

        # Without registry, trust_refs should be None (backward compat)
        assert ann.trust_refs is None
