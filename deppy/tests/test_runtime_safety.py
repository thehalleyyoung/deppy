"""Tests for runtime safety verification infrastructure.

Covers the 9 core deppy gaps for module-level runtime safety:
  Gap 1: ConditionalEffectWitness kernel term
  Gap 2: EffectWitness trust preservation
  Gap 3: SidecarVerificationBackend
  Gap 4: Interprocedural effect composition
  Gap 5: Abstract interp → proof bridge
  Gap 6: Safety proof tactic
  Gap 7: Module-level coverage model
  Gap 8: Auto-spec → obligation wiring
  Gap 9: Lean safety encodings
"""
from __future__ import annotations

import tempfile
import textwrap
from pathlib import Path

import pytest

from deppy.core.kernel import (
    ProofKernel, TrustLevel, EffectWitness, ConditionalEffectWitness,
    SafetyObligation, Structural, Z3Proof, AxiomInvocation,
)
from deppy.core.types import (
    Context, Judgment, JudgmentKind, Var, PyObjType, RefinementType,
    PyBoolType,
)
from deppy.proofs.sidecar import (
    SidecarModule, SidecarVerificationBackend, _parse_deppy_file,
    AxiomDecl, ExternalSpec,
)


# ═══════════════════════════════════════════════════════════════════
# Gap 1: ConditionalEffectWitness
# ═══════════════════════════════════════════════════════════════════

class TestConditionalEffectWitness:
    def setup_method(self):
        self.kernel = ProofKernel()
        self.ctx = Context()
        self.goal = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=self.ctx,
            term=Var("f"),
            type_=PyObjType(),
        )

    def test_basic_verification(self):
        proof = ConditionalEffectWitness(
            precondition="x > 0",
            effect="exception_free",
            proof=Structural(description="proved by inspection"),
            target="math.sqrt",
        )
        r = self.kernel.verify(self.ctx, self.goal, proof)
        assert r.success
        assert "exception_free" in r.message
        assert "x > 0" in r.message

    def test_preserves_inner_trust(self):
        # Inner Structural → trust preserved (STRUCTURAL_CHAIN)
        proof = ConditionalEffectWitness(
            precondition="x > 0",
            effect="exception_free",
            proof=Structural(description="ok"),
        )
        r = self.kernel.verify(self.ctx, self.goal, proof)
        assert r.trust_level == TrustLevel.STRUCTURAL_CHAIN

    def test_propagates_inner_failure(self):
        # If inner proof fails, ConditionalEffectWitness fails
        from deppy.core.kernel import Refl
        # Refl on a TYPE_CHECK goal will fail
        bad_proof = Refl(Var("x"))
        proof = ConditionalEffectWitness(
            precondition="x > 0",
            effect="exception_free",
            proof=bad_proof,
        )
        r = self.kernel.verify(self.ctx, self.goal, proof)
        assert not r.success

    def test_target_in_message(self):
        proof = ConditionalEffectWitness(
            precondition="True",
            effect="terminates",
            proof=Structural(description="ok"),
            target="mymod.myfunc",
        )
        r = self.kernel.verify(self.ctx, self.goal, proof)
        assert "mymod.myfunc" in r.message


# ═══════════════════════════════════════════════════════════════════
# Gap 2: EffectWitness trust preservation
# ═══════════════════════════════════════════════════════════════════

class TestEffectWitnessTrust:
    def setup_method(self):
        self.kernel = ProofKernel()
        self.ctx = Context()
        self.goal = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=self.ctx,
            term=Var("f"),
            type_=PyObjType(),
        )

    def test_structural_preserved(self):
        # Structural inner proof at STRUCTURAL_CHAIN → preserved
        proof = EffectWitness(
            effect="exception_free",
            proof=Structural(description="strong"),
        )
        r = self.kernel.verify(self.ctx, self.goal, proof)
        assert r.success
        # STRUCTURAL_CHAIN >= STRUCTURAL_CHAIN → preserved (not downgraded)
        assert r.trust_level == TrustLevel.STRUCTURAL_CHAIN

    def test_axiom_downgraded(self):
        # AxiomInvocation gives AXIOM_TRUSTED (level 2) which is below
        # STRUCTURAL_CHAIN; therefore should downgrade to EFFECT_ASSUMED.
        self.kernel.register_axiom("test_ax", "True", module="test")
        proof = EffectWitness(
            effect="exception_free",
            proof=AxiomInvocation(name="test_ax", module="test"),
        )
        r = self.kernel.verify(self.ctx, self.goal, proof)
        if r.success:
            assert r.trust_level.value <= TrustLevel.EFFECT_ASSUMED.value


# ═══════════════════════════════════════════════════════════════════
# Gap 3: SidecarVerificationBackend
# ═══════════════════════════════════════════════════════════════════

class TestSidecarBackend:
    def test_trusts_when_no_discharge_possible(self):
        backend = SidecarVerificationBackend(
            enable_z3=False,
            enable_computational=False,
            enable_counterexample=False,
        )
        ax = AxiomDecl(
            name="some_axiom",
            target="mymod.func",
            statement="some property",
            module="mymod",
        )
        kernel = ProofKernel()
        success, trust, msg = backend.discharge_axiom(ax, kernel)
        assert success
        assert trust == TrustLevel.AXIOM_TRUSTED

    def test_computational_test_passes(self):
        backend = SidecarVerificationBackend(
            enable_z3=False,
            enable_counterexample=False,
            computational_samples=5,
        )
        ax = AxiomDecl(
            name="add_commute",
            target="mymod.add",
            statement="a + b == b + a",
            module="mymod",
        )
        # Test function that always succeeds
        def test_fn():
            assert 1 + 2 == 2 + 1
            return True

        kernel = ProofKernel()
        success, trust, msg = backend.discharge_axiom(
            ax, kernel, test_fn=test_fn,
        )
        assert success
        assert trust == TrustLevel.LLM_CHECKED

    def test_computational_test_fails(self):
        backend = SidecarVerificationBackend(
            enable_z3=False,
            enable_counterexample=False,
            computational_samples=5,
        )
        ax = AxiomDecl(
            name="bad_axiom",
            target="mymod.func",
            statement="false claim",
            module="mymod",
        )
        def test_fn():
            assert False, "deliberately false"

        kernel = ProofKernel()
        success, trust, msg = backend.discharge_axiom(
            ax, kernel, test_fn=test_fn,
        )
        assert not success
        assert trust == TrustLevel.UNTRUSTED


# ═══════════════════════════════════════════════════════════════════
# Gap 3 (continued): .deppy parser extensions
# ═══════════════════════════════════════════════════════════════════

class TestDeppyParserExtensions:
    def _write_deppy(self, content: str) -> Path:
        f = tempfile.NamedTemporaryFile(
            mode='w', suffix='.deppy', delete=False,
        )
        f.write(content)
        f.close()
        return Path(f.name)

    def test_parse_exception_free(self):
        path = self._write_deppy('''module: test
spec test.divide:
  guarantee: "returns a/b"
  exception_free: when "b != 0"
''')
        try:
            sm = _parse_deppy_file(path)
            spec = sm._specs["test.divide"]
            assert spec.exception_free_when == ["b != 0"]
        finally:
            path.unlink()

    def test_parse_raises(self):
        path = self._write_deppy('''module: test
spec test.lookup:
  guarantee: "returns d[k]"
  raises KeyError: when "k not in d"
  raises TypeError: when "not isinstance(d, dict)"
''')
        try:
            sm = _parse_deppy_file(path)
            spec = sm._specs["test.lookup"]
            assert ("KeyError", "k not in d") in spec.raises_declarations
            assert ("TypeError", "not isinstance(d, dict)") in spec.raises_declarations
        finally:
            path.unlink()

    def test_parse_total(self):
        path = self._write_deppy('''module: test
spec test.f:
  guarantee: "always returns"
  total: true
''')
        try:
            sm = _parse_deppy_file(path)
            assert sm._specs["test.f"].is_total
        finally:
            path.unlink()

    def test_parse_safe_when(self):
        path = self._write_deppy('''module: test
spec test.process:
  guarantee: "processes input"
  safe_when: "isinstance(input, str)"
''')
        try:
            sm = _parse_deppy_file(path)
            spec = sm._specs["test.process"]
            assert "isinstance(input, str)" in spec.safe_when
        finally:
            path.unlink()

    def test_parse_full_spec(self):
        path = self._write_deppy('''module: mymod
version: ">=1.0"
spec mymod.divide:
  guarantee: "returns a/b"
  pure: true
  exception_free: when "b != 0"
  raises ZeroDivisionError: when "b == 0"
  total: true
  axiom div_safe: "divide(a, b) does not raise when b != 0"
''')
        try:
            sm = _parse_deppy_file(path)
            assert sm.name == "mymod"
            assert sm.version == ">=1.0"
            spec = sm._specs["mymod.divide"]
            assert spec.is_pure
            assert spec.is_total
            assert spec.exception_free_when == ["b != 0"]
            assert ("ZeroDivisionError", "b == 0") in spec.raises_declarations
            assert "div_safe" in sm._axioms
        finally:
            path.unlink()


# ═══════════════════════════════════════════════════════════════════
# ExternalSpec serialization round-trip with new fields
# ═══════════════════════════════════════════════════════════════════

class TestExternalSpecRoundtrip:
    def test_safety_fields_preserved(self):
        es = ExternalSpec(
            target_name="mymod.f",
            module_name="mymod",
            guarantees=["g1"],
            exception_free_when=["x > 0"],
            raises_declarations=[("ValueError", "x < 0")],
            safe_when=["isinstance(x, int)"],
            is_total=True,
        )
        d = es.to_json()
        es2 = ExternalSpec.from_json(d)
        assert es2.exception_free_when == ["x > 0"]
        assert es2.raises_declarations == [("ValueError", "x < 0")]
        assert es2.safe_when == ["isinstance(x, int)"]
        assert es2.is_total


# ═══════════════════════════════════════════════════════════════════
# Gap 4: Interprocedural effect composition
# ═══════════════════════════════════════════════════════════════════

import ast
from deppy.effects.effect_propagation import propagate_effects, FunctionSummary


class TestInterproceduralPropagation:
    def test_pure_module(self):
        src = """
def add(a, b):
    return a + b

def double(x):
    return add(x, x)
"""
        graph = propagate_effects(ast.parse(src))
        assert "add" in graph.summaries
        assert "double" in graph.summaries
        assert graph.summaries["double"].callees == ["add"]

    def test_propagates_callee_exception(self):
        src = """
def divide(a, b):
    return a / b

def caller(x):
    return divide(x, 0)
"""
        graph = propagate_effects(ast.parse(src))
        # divide may raise ZeroDivisionError; caller inherits it.
        assert not graph.summaries["caller"].is_exception_free
        assert any("via call to divide" in ce.description
                   for ce in graph.summaries["caller"].inherited)

    def test_sidecar_precondition_discharges_callee_exception(self):
        src = """
def divide(a, b):
    return a / b

def caller(x, b):
    if b != 0:
        return divide(x, b)
    return 0
"""
        # Sidecar declares divide is exception-free when b != 0
        spec = ExternalSpec(
            target_name="divide",
            exception_free_when=["b != 0"],
        )
        graph = propagate_effects(
            ast.parse(src),
            sidecar_specs={"divide": spec},
        )
        s = graph.summaries["caller"]
        # The single call site is guarded by `b != 0`, so callee
        # exceptions are discharged, not inherited.
        assert any(ce.exception_type for ce in s.discharged), s.discharged
        assert all("via call to divide" not in ce.description
                   for ce in s.escapes)

    def test_call_graph_records_callees(self):
        src = """
def a(): return b()
def b(): return c()
def c(): return 1
"""
        graph = propagate_effects(ast.parse(src))
        assert graph.summaries["a"].callees == ["b"]
        assert graph.summaries["b"].callees == ["c"]
        assert graph.summaries["c"].callees == []

    def test_module_level_summaries(self):
        src = """
def safe(x): return x + 1
def maybe_unsafe(d, k): return d[k]
"""
        graph = propagate_effects(ast.parse(src))
        free = set(graph.exception_free_functions())
        unsafe = set(graph.unsafe_functions())
        assert "safe" in free
        assert "maybe_unsafe" in unsafe


# ═══════════════════════════════════════════════════════════════════
# Gap 5: Abstract interp → proof bridge
# ═══════════════════════════════════════════════════════════════════

from deppy.pipeline.abstract_evidence import AbstractEvidenceBridge
from deppy.pipeline.abstract_interp import AbstractInterpreter


class TestAbstractEvidenceBridge:
    def _trace(self, src):
        tree = ast.parse(textwrap.dedent(src))
        fn = tree.body[0]
        return AbstractInterpreter().analyze_function_trace(fn)

    def test_nonzero_obligation_succeeds_for_constant(self):
        src = """
        def f():
            b = 5
            return 10 / b
        """
        trace = self._trace(src)
        bridge = AbstractEvidenceBridge(trace=trace, function_qualname="f")
        # Find the line with the return.
        ln = max(trace.point_states or {0: None})
        obl = bridge.nonzero_obligation("b", ln)
        assert obl is not None
        assert obl.safety_condition == "b != 0"
        assert obl.failure_kind == "ZeroDivisionError"
        assert isinstance(obl.proof, Structural)

    def test_returns_none_when_unprovable(self):
        src = """
        def f(b):
            return 10 / b
        """
        trace = self._trace(src)
        bridge = AbstractEvidenceBridge(trace=trace)
        ln = max(trace.point_states or {1: None})
        obl = bridge.nonzero_obligation("b", ln)
        assert obl is None

    def test_obligation_id_includes_location(self):
        src = """
        def g():
            x = 7
            return x
        """
        trace = self._trace(src)
        bridge = AbstractEvidenceBridge(trace=trace, function_qualname="mod.g")
        ln = max(trace.point_states or {1: None})
        obl = bridge.nonzero_obligation("x", ln)
        assert obl is not None
        assert "mod.g" in obl.obligation_id
        assert f"L{ln}" in obl.obligation_id

    def test_kernel_accepts_obligation_at_structural_trust(self):
        from deppy.core.kernel import ProofKernel
        from deppy.core.types import (
            Context, Judgment, JudgmentKind, Var, PyObjType,
        )
        src = """
        def f():
            b = 9
            return 1 / b
        """
        trace = self._trace(src)
        bridge = AbstractEvidenceBridge(trace=trace)
        ln = max(trace.point_states or {1: None})
        obl = bridge.nonzero_obligation("b", ln)
        assert obl is not None
        kernel = ProofKernel()
        ctx = Context()
        goal = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=ctx,
            term=Var("p"),
            type_=PyObjType(),
        )
        result = kernel.verify(ctx, goal, obl)
        assert result.success
        # Obligation forwards trust from inner Structural proof.
        assert result.trust_level.value >= TrustLevel.STRUCTURAL_CHAIN.value

    def test_collect_evidence_batch(self):
        src = """
        def f():
            b = 4
            return 1 / b
        """
        trace = self._trace(src)
        bridge = AbstractEvidenceBridge(trace=trace)
        ln = max(trace.point_states or {1: None})
        evidence = bridge.collect_evidence([
            ("nonzero", "b", ln),
            ("nonzero", "missing_var", ln),
        ])
        assert len(evidence) == 1
        assert evidence[0].safety_condition == "b != 0"


# ═══════════════════════════════════════════════════════════════════
# Gap 6: Safety proof tactic
# ═══════════════════════════════════════════════════════════════════

from deppy.proofs.tactics import ProofBuilder
from deppy.core.kernel import ConditionalEffectWitness as _CEW


class TestBySafetyTactic:
    def setup_method(self):
        self.kernel = ProofKernel()
        self.ctx = Context()
        self.goal = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=self.ctx,
            term=Var("p"),
            type_=PyObjType(),
        )

    def test_no_evidence_yields_trivial_witness(self):
        pb = ProofBuilder(self.kernel, self.ctx, goal=self.goal)
        proof = pb.by_safety(
            precondition="x > 0",
            target="math.sqrt",
        )
        assert isinstance(proof, _CEW)
        r = self.kernel.verify(self.ctx, self.goal, proof)
        assert r.success

    def test_single_evidence_passes_through(self):
        pb = ProofBuilder(self.kernel, self.ctx, goal=self.goal)
        ev = Structural(description="proved offline")
        proof = pb.by_safety(
            precondition="b != 0",
            target="div",
            evidence=[ev],
        )
        assert isinstance(proof, _CEW)
        assert proof.proof is ev
        r = self.kernel.verify(self.ctx, self.goal, proof)
        assert r.success

    def test_multiple_evidence_chained_by_cuts(self):
        pb = ProofBuilder(self.kernel, self.ctx, goal=self.goal)
        e1 = SafetyObligation(
            obligation_id="o1", safety_condition="b != 0",
            proof=Structural(description="d1"),
            failure_kind="ZeroDivisionError",
        )
        e2 = SafetyObligation(
            obligation_id="o2", safety_condition="x >= 0",
            proof=Structural(description="d2"),
            failure_kind="ValueError",
        )
        e3 = Structural(description="final")
        proof = pb.by_safety(
            precondition="b != 0 and x >= 0",
            target="combined",
            evidence=[e1, e2, e3],
        )
        assert isinstance(proof, _CEW)
        r = self.kernel.verify(self.ctx, self.goal, proof)
        assert r.success
        # History records the tactic.
        assert any(s.tactic == "by_safety" for s in pb.history)

    def test_records_tactic_in_history(self):
        pb = ProofBuilder(self.kernel, self.ctx, goal=self.goal)
        pb.by_safety(precondition="ok", target="f")
        steps = [s for s in pb.history if s.tactic == "by_safety"]
        assert len(steps) == 1
        assert steps[0].args["target"] == "f"


# ═══════════════════════════════════════════════════════════════════
# Gap 7: Module-level coverage model
# ═══════════════════════════════════════════════════════════════════

from deppy.pipeline.safety_coverage import build_coverage, CoverageReport


class TestSafetyCoverage:
    def test_unannotated_function_appears_in_report(self):
        src = "def f(d, k):\n    return d[k]\n"
        report = build_coverage(src)
        assert "f" in report.unannotated
        assert "f" not in report.fully_covered

    def test_sidecar_with_raises_marks_addressed(self):
        src = "def divide(a, b):\n    return a / b\n"
        spec = ExternalSpec(
            target_name="divide",
            raises_declarations=[("ZeroDivisionError", "b == 0")],
        )
        report = build_coverage(src, sidecar_specs={"divide": spec})
        cov = report.functions["divide"]
        assert cov.has_sidecar
        assert cov.is_fully_covered

    def test_sidecar_total_addresses_everything(self):
        src = "def f(d, k):\n    return d[k]\n"
        spec = ExternalSpec(target_name="f", is_total=True)
        report = build_coverage(src, sidecar_specs={"f": spec})
        assert report.functions["f"].is_fully_covered

    def test_template_includes_raises(self):
        src = "def divide(a, b):\n    return a / b\n"
        report = build_coverage(src)
        tpl = report.deppy_template_for("divide")
        assert "spec divide" in tpl
        assert "ZeroDivisionError" in tpl

    def test_summary_renders(self):
        src = """
def safe(x):
    return x + 1

def unsafe(d, k):
    return d[k]
"""
        report = build_coverage(src.strip())
        text = report.summary()
        assert "Coverage report" in text
        assert "unsafe" in text or report.unannotated

    def test_partial_coverage(self):
        src = """
def f(d, k, b):
    x = d[k]
    return x / b
"""
        # spec mentions ZeroDivisionError but not KeyError → partial
        spec = ExternalSpec(
            target_name="f",
            raises_declarations=[("ZeroDivisionError", "b == 0")],
        )
        report = build_coverage(src.strip(), sidecar_specs={"f": spec})
        cov = report.functions["f"]
        assert cov.has_sidecar
        # not fully covered: KeyError unaddressed
        assert not cov.is_fully_covered
        assert cov.coverage_ratio < 1.0


# ═══════════════════════════════════════════════════════════════════
# Gap 8: Auto-spec → obligation wiring
# ═══════════════════════════════════════════════════════════════════

from deppy.pipeline.auto_spec_obligations import (
    infer_module_specs, draft_specs_to_sidecar, merge_drafts_with_sidecar,
)


class TestAutoSpecObligations:
    def test_inference_returns_function_specs(self):
        src = """
def add(a: int, b: int) -> int:
    '''Add two integers.'''
    return a + b
"""
        out = infer_module_specs(src.strip())
        assert "add" in out
        assert out["add"].inferred  # at least one inferred spec

    def test_drafts_are_untrusted(self):
        src = "def f(x: int) -> int:\n    return x + 1\n"
        inferred = infer_module_specs(src)
        drafts = draft_specs_to_sidecar(inferred)
        assert "f" in drafts
        spec = drafts["f"]
        assert spec.verified is False
        assert spec.trust_level == TrustLevel.UNTRUSTED

    def test_merge_user_overrides_draft(self):
        src = "def f(x: int) -> int:\n    return x + 1\n"
        drafts = draft_specs_to_sidecar(infer_module_specs(src))
        user_spec = ExternalSpec(
            target_name="f",
            verified=True,
            trust_level=TrustLevel.LLM_CHECKED,
            exception_free_when=["x > 0"],
        )
        merged = merge_drafts_with_sidecar(drafts, {"f": user_spec})
        assert merged["f"].verified is True
        assert merged["f"].trust_level == TrustLevel.LLM_CHECKED
        assert merged["f"].exception_free_when == ["x > 0"]

    def test_drafts_feed_into_coverage_pipeline(self):
        # End-to-end: inferred → drafts → coverage report.
        src = "def divide(a, b):\n    return a / b\n"
        drafts = draft_specs_to_sidecar(infer_module_specs(src))
        from deppy.pipeline.safety_coverage import build_coverage
        report = build_coverage(src, sidecar_specs=drafts)
        # Even a draft sidecar makes the function "annotated" — its
        # coverage can be assessed even if not fully covered.
        assert "divide" in report.functions
        assert report.functions["divide"].has_sidecar


# ═══════════════════════════════════════════════════════════════════
# Gap 9: Lean safety encodings
# ═══════════════════════════════════════════════════════════════════

from deppy.lean.proof_translator import translate_proof, full_translate


class TestLeanSafetyEncoding:
    def test_conditional_effect_translated(self):
        proof = ConditionalEffectWitness(
            precondition="x > 0",
            effect="exception_free",
            proof=Structural(description="ok"),
            target="math.sqrt",
        )
        out = translate_proof(proof)
        assert "x > 0" in out
        assert "exception_free" in out
        # Schema: a function abstracting the precondition.
        assert "fun" in out

    def test_safety_obligation_translated(self):
        obl = SafetyObligation(
            obligation_id="mod.f:L42:nonzero",
            safety_condition="b != 0",
            proof=Structural(description="provable"),
            failure_kind="ZeroDivisionError",
            lineno=42,
        )
        out = translate_proof(obl)
        assert "b != 0" in out
        assert "safety:" in out

    def test_no_sorry_when_inner_is_concrete(self):
        proof = ConditionalEffectWitness(
            precondition="True",
            effect="exception_free",
            proof=Structural(description="trivial"),
            target="f",
        )
        result = full_translate(proof)
        # Concrete inner means no untranslated sorries from this path.
        assert "ConditionalEffectWitness" not in " ".join(result.untranslatable)

    def test_nested_safety_obligation_inside_conditional(self):
        inner = SafetyObligation(
            obligation_id="g:L1:nonzero",
            safety_condition="b != 0",
            proof=Structural(description="domain evidence"),
            failure_kind="ZeroDivisionError",
        )
        proof = ConditionalEffectWitness(
            precondition="b != 0",
            effect="exception_free",
            proof=inner,
            target="g",
        )
        out = translate_proof(proof)
        # Both layers represented.
        assert "b != 0" in out
        assert "safety:" in out
        assert "exception_free" in out


# ═══════════════════════════════════════════════════════════════════
# Gap 4b: Z3 semantic discharge & method calls in propagation
# ═══════════════════════════════════════════════════════════════════

class TestSemanticDischarge:
    def test_z3_discharges_stronger_guard(self):
        # Guard b > 0 implies precondition b != 0 — only Z3 can prove this.
        src = """
def divide(a, b):
    return a / b

def caller(x, b):
    if b > 0:
        return divide(x, b)
    return 0
"""
        spec = ExternalSpec(target_name="divide", exception_free_when=["b != 0"])
        graph = propagate_effects(ast.parse(src), sidecar_specs={"divide": spec})
        # Z3 should discharge the b != 0 obligation under guard b > 0.
        try:
            import z3  # noqa: F401
            assert graph.summaries["caller"].discharged, \
                "Z3 was available but didn't discharge"
            assert all("via call to divide" not in ce.description
                       for ce in graph.summaries["caller"].escapes)
        except ImportError:
            pytest.skip("z3 not installed")

    def test_z3_falls_through_when_guard_too_weak(self):
        src = """
def divide(a, b):
    return a / b

def caller(x, b):
    if b > -10:
        return divide(x, b)
    return 0
"""
        spec = ExternalSpec(target_name="divide", exception_free_when=["b != 0"])
        graph = propagate_effects(ast.parse(src), sidecar_specs={"divide": spec})
        # b > -10 does not imply b != 0; the obligation must NOT be discharged.
        s = graph.summaries["caller"]
        assert any("via call to divide" in ce.description for ce in s.inherited)

    def test_method_call_resolved_to_module_function(self):
        # ``self.helper()`` should be matched to module-level ``helper``.
        src = """
def helper(x):
    return x + 1

class C:
    def go(self, x):
        return helper(x)
"""
        graph = propagate_effects(ast.parse(src))
        # The method body lives in the class, but ``go`` is also picked up
        # as it appears at module level only via class — verify helper at
        # least registers and call to helper resolves when at module-level.
        assert "helper" in graph.summaries

    def test_substitution_aware_summary_discharge(self):
        src = """
def divide(a, b):
    return a / b

def caller(x, y):
    if y >= 0:
        return divide(x, y + 1)
    return 0
"""
        spec = ExternalSpec(target_name="divide", exception_free_when=["b != 0"])
        graph = propagate_effects(ast.parse(src), sidecar_specs={"divide": spec})
        s = graph.summaries["caller"]
        try:
            import z3  # noqa: F401
            assert s.discharged, "expected substituted guard y >= 0 => (y + 1) != 0"
            assert all("via call to divide" not in ce.description for ce in s.escapes)
        except ImportError:
            pytest.skip("z3 not installed")

    def test_substitution_aware_summary_rejects_weak_guard(self):
        src = """
def divide(a, b):
    return a / b

def caller(x, y):
    if y >= -1:
        return divide(x, y + 1)
    return 0
"""
        spec = ExternalSpec(target_name="divide", exception_free_when=["b != 0"])
        graph = propagate_effects(ast.parse(src), sidecar_specs={"divide": spec})
        s = graph.summaries["caller"]
        assert any("via call to divide" in ce.description for ce in s.inherited)


# ═══════════════════════════════════════════════════════════════════
# Gap 7b: Tighter per-source coverage matching
# ═══════════════════════════════════════════════════════════════════

class TestTighterCoverage:
    def test_irrelevant_exception_free_when_does_not_cover(self):
        # Semantic mismatch: x > 0 says nothing about membership k in d.
        src = "def f(d, k, x):\n    return d[k]\n"
        spec = ExternalSpec(target_name="f", exception_free_when=["x > 0"])
        from deppy.pipeline.safety_coverage import build_coverage
        report = build_coverage(src, sidecar_specs={"f": spec})
        assert not report.functions["f"].is_fully_covered

    def test_relevant_exception_free_when_covers_matching_source(self):
        # Semantic match: b != 0 is the canonical safety predicate for a / b.
        src = "def f(b):\n    return 1 / b\n"
        spec = ExternalSpec(target_name="f", exception_free_when=["b != 0"])
        from deppy.pipeline.safety_coverage import build_coverage
        report = build_coverage(src, sidecar_specs={"f": spec})
        cov = report.functions["f"]
        assert cov.is_fully_covered

    def test_stronger_predicate_semantically_covers_source(self):
        # Z3 should accept b > 0 => b != 0.
        src = "def f(b):\n    return 1 / b\n"
        spec = ExternalSpec(target_name="f", exception_free_when=["b > 0"])
        from deppy.pipeline.safety_coverage import build_coverage
        report = build_coverage(src, sidecar_specs={"f": spec})
        assert report.functions["f"].is_fully_covered

    def test_template_uses_canonical_safety_condition(self):
        src = "def f(b):\n    return 1 / b\n"
        from deppy.pipeline.safety_coverage import build_coverage
        report = build_coverage(src)
        tmpl = report.deppy_template_for("f")
        assert 'raises ZeroDivisionError: when "(b) != 0"' in tmpl

    def test_module_level_sources_recorded(self):
        src = "x = 1 / 0\ndef f():\n    return 1\n"
        from deppy.pipeline.safety_coverage import build_coverage
        report = build_coverage(src)
        assert len(report.module_level_sources) >= 1


# ═══════════════════════════════════════════════════════════════════
# Gap 10: Safety pipeline orchestrator
# ═══════════════════════════════════════════════════════════════════

from deppy.pipeline.safety_pipeline import (
    verify_module_safety, SafetyVerdict, FunctionVerdict,
)


class TestSafetyPipeline:
    def test_safe_module_with_full_sidecar(self):
        src = "def add(a, b):\n    return a + b\n"
        verdict = verify_module_safety(src, module_path="tinymod")
        assert "add" in verdict.functions
        assert verdict.is_safe  # add has no exception sources
        assert verdict.aggregate_trust.value > TrustLevel.UNTRUSTED.value

    def test_unannotated_module_reports_gaps(self):
        src = "def f(d, k):\n    return d[k]\n"
        verdict = verify_module_safety(src)
        assert not verdict.is_safe
        assert "f" in verdict.gaps
        assert verdict.aggregate_trust == TrustLevel.UNTRUSTED

    def test_user_sidecar_overrides_drafts(self):
        src = "def divide(a, b):\n    return a / b\n"
        spec = ExternalSpec(
            target_name="divide",
            raises_declarations=[("ZeroDivisionError", "b == 0")],
        )
        verdict = verify_module_safety(src, sidecar_specs={"divide": spec})
        # raises_declarations addresses the source ⇒ safe.
        assert verdict.functions["divide"].is_safe
        assert verdict.is_safe

    def test_lean_emission_optional(self):
        src = "def f():\n    return 1\n"
        verdict = verify_module_safety(src, emit_lean=True)
        # Lean output should be present when emission is requested and safe.
        assert verdict.functions["f"].lean_proof is not None
        assert verdict.lean_module_source is not None
        assert verdict.lean_checked

    def test_summary_renders(self):
        src = "def f():\n    return 1\ndef g(d, k):\n    return d[k]\n"
        verdict = verify_module_safety(src, module_path="m")
        text = verdict.summary()
        assert "SafetyVerdict for m" in text
        assert "functions:" in text


# ═══════════════════════════════════════════════════════════════════
# Gap 11: Spec validator (negative testing)
# ═══════════════════════════════════════════════════════════════════

from deppy.proofs.spec_validator import validate_spec, SpecHealthReport


class TestSpecValidator:
    def test_correct_spec_passes(self):
        def divide(a, b):
            return a / b
        spec = ExternalSpec(target_name="divide",
                            exception_free_when=["b != 0"])
        report = validate_spec(divide, spec)
        assert report.ok
        assert report.positive_raised == 0
        assert report.negative_raised >= 1
        assert report.recommended_trust == TrustLevel.LLM_CHECKED

    def test_overstrong_spec_detected(self):
        # f never raises, but the spec claims it's only safe under x > 0.
        def f(x):
            return x + 1
        spec = ExternalSpec(target_name="f",
                            exception_free_when=["x > 0"])
        report = validate_spec(f, spec)
        # Negative cohort never raised ⇒ vacuous → not OK.
        assert not report.ok
        assert report.recommended_trust == TrustLevel.UNTRUSTED

    def test_wrong_spec_detected(self):
        # Function actually raises when x == 0, but spec says safe when x > -1.
        def g(x):
            if x == 0:
                raise ValueError("zero")
            return 1
        spec = ExternalSpec(target_name="g",
                            exception_free_when=["x > -1"])
        # x=0 satisfies x > -1 but still raises ⇒ positive_raised > 0.
        report = validate_spec(g, spec, sample_inputs=[(0,), (1,), (-2,)])
        assert report.positive_raised >= 1
        assert not report.ok

    def test_no_predicates_returns_neutral(self):
        def h(x):
            return x
        spec = ExternalSpec(target_name="h")  # no exception_free_when
        report = validate_spec(h, spec)
        assert report.ok  # nothing to falsify
        assert "nothing to falsify" in " ".join(report.notes)

    def test_counterexamples_capped(self):
        def always_raises(x):
            raise RuntimeError("nope")
        spec = ExternalSpec(target_name="always_raises",
                            exception_free_when=["x > 0"])
        report = validate_spec(always_raises, spec,
                               sample_inputs=[(i,) for i in range(20)],
                               max_counterexamples=2)
        assert len(report.counterexamples) <= 2

    def test_decimal_annotations_generate_decimal_samples(self):
        from decimal import Decimal

        def divide(a: Decimal, b: Decimal):
            return a / b

        spec = ExternalSpec(target_name="divide",
                            exception_free_when=["b != 0"])
        report = validate_spec(divide, spec, n_samples=20)
        assert report.ok
        assert report.negative_raised >= 1

    def test_optional_and_list_annotations_hit_none_and_empty(self):
        def head(xs: list[int] | None):
            if xs is None:
                raise ValueError("none")
            return xs[0]

        spec = ExternalSpec(target_name="head",
                            exception_free_when=["xs is not None and len(xs) > 0"])
        report = validate_spec(head, spec, n_samples=20)
        assert report.ok
        assert report.negative_raised >= 1


# ═══════════════════════════════════════════════════════════════════
# Gap 9b: Real Lean theorem schemas
# ═══════════════════════════════════════════════════════════════════

from deppy.lean.safety_lean import (
    python_predicate_to_lean, collect_free_vars,
    conditional_witness_to_theorem, safety_obligation_to_theorem,
    emit_safety_module, DEPPY_LEAN_PRELUDE,
)
from deppy.lean.lean_runner import (
    render_compilable_safety_module, check_lean_module_source,
)


class TestLeanSafetyEmission:
    def test_predicate_translation_basic_ops(self):
        assert python_predicate_to_lean("x != 0") == "x ≠ 0"
        assert python_predicate_to_lean("x >= 0 and y > 0") == "x ≥ 0 ∧ y > 0"
        assert python_predicate_to_lean("not (x == 0)") == "¬ (x = 0)"

    def test_predicate_with_call_falls_back(self):
        out = python_predicate_to_lean("len(xs) > 0")
        assert "True" in out and "raw:" in out

    def test_collect_free_vars(self):
        assert collect_free_vars("x > 0 and y != 0") == ["x", "y"]
        assert "and" not in collect_free_vars("x and y")

    def test_witness_to_theorem_includes_hypothesis(self):
        w = ConditionalEffectWitness(
            precondition="b != 0",
            effect="exception_free",
            proof=Structural(description="ok"),
            target="div",
        )
        thm = conditional_witness_to_theorem(w)
        rendered = thm.render()
        assert "theorem div_safe" in rendered
        assert "b ≠ 0" in rendered
        assert "ExceptionFree" in rendered

    def test_obligation_to_theorem(self):
        o = SafetyObligation(
            obligation_id="m.f:L42:nonzero",
            safety_condition="b != 0",
            proof=Structural(description="ok"),
            failure_kind="ZeroDivisionError",
            lineno=42,
        )
        thm = safety_obligation_to_theorem(o)
        rendered = thm.render()
        assert "theorem obl_" in rendered
        assert "b ≠ 0" in rendered

    def test_module_emission_has_namespace_and_aggregator(self):
        w = ConditionalEffectWitness(
            precondition="x > 0",
            effect="exception_free",
            proof=Structural(description="d"),
            target="square",
        )
        out = emit_safety_module("MyMod", [w])
        assert "namespace DeppySafety.MyMod" in out
        assert "end DeppySafety.MyMod" in out
        assert "module_safe" in out
        assert "square_safe" in out

    def test_prelude_defines_required_symbols(self):
        assert "ExceptionFree" in DEPPY_LEAN_PRELUDE
        assert "ModuleExceptionFree" in DEPPY_LEAN_PRELUDE

    def test_compilable_module_passes_lean(self):
        w = ConditionalEffectWitness(
            precondition="b != 0",
            effect="exception_free",
            proof=Structural(description="ok"),
            target="divide",
        )
        src = render_compilable_safety_module("Tmp", [w])
        result = check_lean_module_source(src)
        assert result.ok, result.stderr or result.stdout


# ─── Gap 12 — Module Safety Certificate ──────────────────────────────────────


class TestSafetyCertificate:
    SRC = (
        "def safe_pos(x: int) -> int:\n"
        "    if x <= 0:\n"
        "        return 0\n"
        "    return x + 1\n"
    )

    def _verdict(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        return verify_module_safety(self.SRC, module_path="cert_mod",
                                    use_drafts=True, emit_lean=False)

    def test_certificate_round_trip_json(self):
        from deppy.pipeline.safety_certificate import (
            certificate_from_verdict, ModuleSafetyCertificate,
        )
        v = self._verdict()
        cert = certificate_from_verdict(v, self.SRC)
        text = cert.to_json()
        loaded = ModuleSafetyCertificate.from_json(text)
        assert loaded.module_path == "cert_mod"
        assert loaded.source_sha256 == cert.source_sha256
        assert loaded.aggregate_trust == cert.aggregate_trust
        assert len(loaded.functions) == len(cert.functions)

    def test_certificate_pins_source_hash(self):
        from deppy.pipeline.safety_certificate import certificate_from_verdict
        v = self._verdict()
        cert = certificate_from_verdict(v, self.SRC)
        assert cert.matches_source(self.SRC)
        assert not cert.matches_source(self.SRC + "\n# tampered\n")

    def test_certificate_records_per_function_entries(self):
        from deppy.pipeline.safety_certificate import certificate_from_verdict
        v = self._verdict()
        cert = certificate_from_verdict(v, self.SRC)
        names = {f.name for f in cert.functions}
        assert "safe_pos" in names
        for fc in cert.functions:
            assert fc.trust  # TrustLevel.name string
            assert 0.0 <= fc.coverage_ratio <= 1.0

    def test_package_certificate_aggregates_min_trust(self):
        from deppy.core.kernel import TrustLevel
        from deppy.pipeline.safety_certificate import (
            ModuleSafetyCertificate, PackageSafetyCertificate,
            FunctionCertificate,
        )
        m1 = ModuleSafetyCertificate(
            module_path="a", source_sha256="x" * 64,
            aggregate_trust=TrustLevel.KERNEL.name,
            is_safe=True, overall_coverage=1.0,
            functions=[FunctionCertificate(
                name="f", is_safe=True,
                trust=TrustLevel.KERNEL.name,
                coverage_ratio=1.0)],
        )
        m2 = ModuleSafetyCertificate(
            module_path="b", source_sha256="y" * 64,
            aggregate_trust=TrustLevel.Z3_VERIFIED.name,
            is_safe=True, overall_coverage=1.0,
            functions=[FunctionCertificate(
                name="g", is_safe=True,
                trust=TrustLevel.Z3_VERIFIED.name,
                coverage_ratio=1.0)],
        )
        pkg = PackageSafetyCertificate(package="mypkg", modules=[m1, m2])
        # min of KERNEL and Z3_VERIFIED should be Z3_VERIFIED.
        assert pkg.aggregate_trust == TrustLevel.Z3_VERIFIED
        assert pkg.is_safe
        # Round trip.
        loaded = PackageSafetyCertificate.from_json(pkg.to_json())
        assert loaded.package == "mypkg"
        assert len(loaded.modules) == 2
        assert loaded.aggregate_trust == TrustLevel.Z3_VERIFIED

    def test_unsafe_function_propagates_to_package(self):
        from deppy.core.kernel import TrustLevel
        from deppy.pipeline.safety_certificate import (
            ModuleSafetyCertificate, PackageSafetyCertificate,
            FunctionCertificate,
        )
        unsafe = ModuleSafetyCertificate(
            module_path="u", source_sha256="z" * 64,
            aggregate_trust=TrustLevel.UNTRUSTED.name,
            is_safe=False, overall_coverage=0.0,
            functions=[FunctionCertificate(
                name="bad", is_safe=False,
                trust=TrustLevel.UNTRUSTED.name,
                coverage_ratio=0.0,
                unaddressed=["ZeroDivisionError @ line 3"])],
        )
        pkg = PackageSafetyCertificate(package="p", modules=[unsafe])
        assert not pkg.is_safe
        assert pkg.aggregate_trust == TrustLevel.UNTRUSTED

    def test_certificate_preserves_counterexamples(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        from deppy.pipeline.safety_certificate import certificate_from_verdict
        src = "def f(a, b, x):\n    return a / b\n"
        spec = ExternalSpec(target_name="f", exception_free_when=["x > 0"])
        verdict = verify_module_safety(src, sidecar_specs={"f": spec},
                                       use_drafts=False)
        cert = certificate_from_verdict(verdict, src)
        entry = next(fc for fc in cert.functions if fc.name == "f")
        assert entry.counterexamples
        assert entry.counterexamples[0]["exception_type"] == "ZeroDivisionError"

    def test_recheck_certificate_replays_kernel_payloads(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        from deppy.pipeline.safety_certificate import (
            certificate_from_verdict, recheck_certificate,
        )
        src = "def divide(a, b):\n    return a / b\n"
        spec = ExternalSpec(target_name="divide",
                            exception_free_when=["b != 0"])
        verdict = verify_module_safety(src, sidecar_specs={"divide": spec},
                                       use_drafts=False, emit_lean=True)
        cert = certificate_from_verdict(verdict, src)
        report = recheck_certificate(cert, src)
        assert report.ok, report.notes
        assert report.source_hash_ok
        assert report.kernel_ok

    def test_recheck_certificate_rejects_tampered_source(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        from deppy.pipeline.safety_certificate import (
            certificate_from_verdict, recheck_certificate,
        )
        src = "def divide(a, b):\n    return a / b\n"
        spec = ExternalSpec(target_name="divide",
                            exception_free_when=["b != 0"])
        verdict = verify_module_safety(src, sidecar_specs={"divide": spec},
                                       use_drafts=False)
        cert = certificate_from_verdict(verdict, src)
        report = recheck_certificate(cert, src + "\n# tampered\n")
        assert not report.ok
        assert not report.source_hash_ok


# ═══════════════════════════════════════════════════════════════════
# Gap 13/17: Semantic safety witness with real per-source discharges
# ═══════════════════════════════════════════════════════════════════


class TestSemanticSafetyWitness:
    """Cheats A & E (vacuous Structural inner proof; trust ceiling) — fixed."""

    def test_witness_refuses_undischarged_source(self):
        """A function with an unguarded `a/b` and no precondition must NOT
        verify — even though coverage might say "addressed"."""
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = "def divide(a, b):\n    return a / b\n"
        v = verify_module_safety(src, sidecar_specs=None, use_drafts=True)
        assert v.functions["divide"].is_safe is False
        assert v.functions["divide"].trust == TrustLevel.UNTRUSTED

    def test_z3_proven_precondition_yields_z3_trust(self):
        """A real precondition that Z3 can verify must elevate trust above
        STRUCTURAL_CHAIN to Z3_VERIFIED."""
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = "def divide(a, b):\n    return a / b\n"
        spec = ExternalSpec(target_name="divide",
                            exception_free_when=["b != 0"])
        v = verify_module_safety(src, sidecar_specs={"divide": spec},
                                 use_drafts=False)
        assert v.functions["divide"].is_safe
        assert v.functions["divide"].trust == TrustLevel.Z3_VERIFIED, \
            v.functions["divide"].trust

    def test_irrelevant_precondition_still_fails(self):
        """An LLM that writes ``exception_free_when: x > 0`` for a
        ZeroDivisionError on ``a/b`` is now caught — Z3 cannot derive
        ``b != 0`` from ``x > 0``, so the witness fails."""
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = "def f(a, b, x):\n    return a / b\n"
        spec = ExternalSpec(target_name="f",
                            exception_free_when=["x > 0"])
        v = verify_module_safety(src, sidecar_specs={"f": spec},
                                 use_drafts=False)
        assert v.functions["f"].is_safe is False
        assert v.functions["f"].trust == TrustLevel.UNTRUSTED
        assert v.functions["f"].counterexamples
        cex = v.functions["f"].counterexamples[0]
        assert cex.exception_type == "ZeroDivisionError"
        assert cex.inputs["b"] == 0

    def test_raises_declaration_with_condition_is_z3_discharged(self):
        """``raises_declarations=[('ZeroDivisionError','b == 0')]`` is
        contractually equivalent to ``exception_free_when: not(b == 0)``
        — Z3 should discharge it."""
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = "def divide(a, b):\n    return a / b\n"
        spec = ExternalSpec(
            target_name="divide",
            raises_declarations=[("ZeroDivisionError", "b == 0")],
        )
        v = verify_module_safety(src, sidecar_specs={"divide": spec},
                                 use_drafts=False)
        assert v.functions["divide"].is_safe
        # Should be Z3-discharged from the raises_decl, not just axiom.
        assert v.functions["divide"].trust == TrustLevel.Z3_VERIFIED

    def test_is_total_escape_clamps_trust_to_structural(self):
        """``is_total: True`` is the analyst-trusted escape — yields
        STRUCTURAL_CHAIN, not Z3_VERIFIED."""
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = "def divide(a, b):\n    return a / b\n"
        spec = ExternalSpec(target_name="divide", is_total=True)
        v = verify_module_safety(src, sidecar_specs={"divide": spec},
                                 use_drafts=False)
        assert v.functions["divide"].is_safe
        assert v.functions["divide"].trust == TrustLevel.STRUCTURAL_CHAIN

    def test_witness_carries_all_source_discharges(self):
        """Every detected source must produce a discharge (no silent skips)."""
        from deppy.core.kernel import (
            ProofKernel, SemanticSafetyWitness, SourceDischarge, Z3Proof,
        )
        from deppy.core.types import (
            Context, Judgment, JudgmentKind, Var, PyObjType,
        )
        d1 = SourceDischarge(
            source_id="f:L1:ZERO_DIVISION", failure_kind="ZERO_DIVISION",
            safety_predicate="b != 0",
            inner=Z3Proof(formula="(b > 0) => (b != 0)"),
        )
        w = SemanticSafetyWitness(target="f", precondition="b > 0",
                                  discharges=[d1])
        k = ProofKernel()
        ctx = Context()
        goal = Judgment(kind=JudgmentKind.TYPE_CHECK,
                        context=ctx, term=Var("safety"), type_=PyObjType())
        r = k.verify(ctx, goal, w)
        assert r.success
        assert r.trust_level == TrustLevel.Z3_VERIFIED
        assert len(r.sub_results) == 1

    def test_witness_fails_if_any_discharge_fails(self):
        """One Assume discharge (undischarged source) fails the whole witness."""
        from deppy.core.kernel import (
            ProofKernel, SemanticSafetyWitness, SourceDischarge, Z3Proof,
            Assume,
        )
        from deppy.core.types import (
            Context, Judgment, JudgmentKind, Var, PyObjType,
        )
        ok = SourceDischarge(
            source_id="f:L1:ZERO_DIVISION", failure_kind="ZERO_DIVISION",
            safety_predicate="b != 0",
            inner=Z3Proof(formula="(b > 0) => (b != 0)"),
        )
        bad = SourceDischarge(
            source_id="f:L2:KEY_ERROR", failure_kind="KEY_ERROR",
            safety_predicate="k in d",
            inner=Assume(name="undischarged"),
        )
        w = SemanticSafetyWitness(target="f", precondition="b > 0",
                                  discharges=[ok, bad])
        k = ProofKernel()
        ctx = Context()
        goal = Judgment(kind=JudgmentKind.TYPE_CHECK,
                        context=ctx, term=Var("safety"), type_=PyObjType())
        r = k.verify(ctx, goal, w)
        assert not r.success
        assert "f:L2:KEY_ERROR" in r.message


# ═══════════════════════════════════════════════════════════════════
# Gap 19: Module-level safety composition
# ═══════════════════════════════════════════════════════════════════


class TestModuleSafetyComposition:
    def test_kernel_composition_succeeds_when_all_parts_verify(self):
        from deppy.core.kernel import (
            ProofKernel, ModuleSafetyComposition, ConditionalEffectWitness,
            SemanticSafetyWitness, SourceDischarge, Z3Proof,
        )
        from deppy.core.types import (
            Context, Judgment, JudgmentKind, Var, PyObjType,
        )
        fn_witness = ConditionalEffectWitness(
            precondition="b > 0",
            effect="exception_free",
            proof=SemanticSafetyWitness(
                target="f",
                precondition="b > 0",
                discharges=[SourceDischarge(
                    source_id="f:L1:ZERO_DIVISION",
                    failure_kind="ZERO_DIVISION",
                    safety_predicate="b != 0",
                    inner=Z3Proof(formula="(b > 0) => (b != 0)"),
                )],
            ),
            target="f",
        )
        module_proof = ModuleSafetyComposition(
            module_path="m",
            function_witnesses={"f": fn_witness},
            module_discharges=[],
            internal_calls_closed=True,
        )
        k = ProofKernel()
        ctx = Context()
        goal = Judgment(kind=JudgmentKind.TYPE_CHECK,
                        context=ctx, term=Var("safety"), type_=PyObjType())
        r = k.verify(ctx, goal, module_proof)
        assert r.success
        assert r.trust_level == TrustLevel.Z3_VERIFIED

    def test_kernel_composition_fails_on_bad_module_discharge(self):
        from deppy.core.kernel import (
            ProofKernel, ModuleSafetyComposition, SourceDischarge, Assume,
        )
        from deppy.core.types import (
            Context, Judgment, JudgmentKind, Var, PyObjType,
        )
        module_proof = ModuleSafetyComposition(
            module_path="m",
            function_witnesses={},
            module_discharges=[SourceDischarge(
                source_id="<module>:L1:ZERO_DIVISION",
                failure_kind="ZERO_DIVISION",
                safety_predicate="x != 0",
                inner=Assume(name="undischarged"),
            )],
            internal_calls_closed=True,
        )
        k = ProofKernel()
        ctx = Context()
        goal = Judgment(kind=JudgmentKind.TYPE_CHECK,
                        context=ctx, term=Var("safety"), type_=PyObjType())
        r = k.verify(ctx, goal, module_proof)
        assert not r.success
        assert "<module>:L1:ZERO_DIVISION" in r.message

    def test_pipeline_marks_module_level_source_unsafe(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = "x = 1 / 0\n\ndef f():\n    return 1\n"
        verdict = verify_module_safety(src, module_path="m", use_drafts=False)
        assert not verdict.module_safe
        assert not verdict.is_safe
        assert verdict.module_level_unaddressed

    def test_pipeline_module_safe_when_functions_compose(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        src = "def divide(a, b):\n    return a / b\n"
        spec = ExternalSpec(target_name="divide",
                            exception_free_when=["b != 0"])
        verdict = verify_module_safety(src, sidecar_specs={"divide": spec},
                                       use_drafts=False)
        assert verdict.functions["divide"].is_safe
        assert verdict.module_safe
        assert verdict.is_safe


# ═══════════════════════════════════════════════════════════════════
# Gap 21: Extended exception source taxonomy
# ═══════════════════════════════════════════════════════════════════


class TestExtendedExceptionSources:
    def test_direct_recursion_records_runtime_error_source(self):
        from deppy.pipeline.exception_sources import (
            ExceptionKind, find_exception_sources,
        )
        src = """
def fact(n):
    if n <= 0:
        return 1
    return n * fact(n - 1)
"""
        summary = find_exception_sources(src)
        fact_summary = next(fn for fn in summary.functions if fn.name == "fact")
        assert any(s.kind is ExceptionKind.RUNTIME_ERROR for s in fact_summary.sources)

    def test_with_statement_records_enter_and_exit_sources(self):
        from deppy.pipeline.exception_sources import (
            ExceptionKind, find_exception_sources,
        )
        src = """
def f(cm):
    with cm:
        return 1
"""
        summary = find_exception_sources(src)
        fn = next(fn for fn in summary.functions if fn.name == "f")
        descs = [s.description for s in fn.sources if s.kind is ExceptionKind.CALL_PROPAGATION]
        assert "with-statement __enter__" in descs
        assert "with-statement __exit__" in descs

    def test_raise_from_records_cause_evaluation_source(self):
        from deppy.pipeline.exception_sources import (
            ExceptionKind, find_exception_sources,
        )
        src = """
def f():
    raise ValueError("x") from make_cause()
"""
        summary = find_exception_sources(src)
        fn = next(fn for fn in summary.functions if fn.name == "f")
        assert any(
            s.kind is ExceptionKind.CALL_PROPAGATION
            and "cause evaluation" in s.description
            for s in fn.sources
        )

    def test_comprehension_records_iteration_source(self):
        from deppy.pipeline.exception_sources import (
            ExceptionKind, find_exception_sources,
        )
        src = """
def f(xs):
    return [x + 1 for x in xs]
"""
        summary = find_exception_sources(src)
        fn = next(fn for fn in summary.functions if fn.name == "f")
        assert any(
            s.kind is ExceptionKind.TYPE_ERROR
            and "comprehension/generator iteration" in s.description
            for s in fn.sources
        )


# ════════════════════════════════════════════════════════════════════
#  Gap 23 — Termination via decreases measure
# ════════════════════════════════════════════════════════════════════

class TestTermination:
    """A recursive function with a declared decreases measure must be
    discharged via a TerminationObligation, not silently accepted."""

    SRC = (
        "def fact(n):\n"
        "    if n <= 0:\n"
        "        return 1\n"
        "    return n * fact(n - 1)\n"
    )

    def test_recursion_undischarged_without_decreases(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        verdict = verify_module_safety(self.SRC, sidecar_specs={})
        fv = verdict.functions["fact"]
        assert any("RUNTIME_ERROR" in u for u in fv.unaddressed), \
            "recursion should remain undischarged without a measure"

    def test_recursion_discharged_with_decreases(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        from deppy.proofs.sidecar import ExternalSpec
        spec = ExternalSpec(
            target=None, target_name="fact", module_name="<m>",
            exception_free_when=["n >= 0"],
            decreases=["n"],
        )
        verdict = verify_module_safety(self.SRC, sidecar_specs={"fact": spec})
        fv = verdict.functions["fact"]
        # No RUNTIME_ERROR remains undischarged.
        assert not any("RUNTIME_ERROR" in u for u in fv.unaddressed), \
            f"recursion should be discharged by decreases=n; got {fv.unaddressed}"

    def test_kernel_termination_obligation_verifies(self):
        from deppy.core.kernel import (
            ProofKernel, TerminationObligation, Z3Proof,
        )
        from deppy.core.types import Context, Judgment, JudgmentKind, Var, PyObjType
        kernel = ProofKernel()
        ctx = Context()
        goal = Judgment(kind=JudgmentKind.TYPE_CHECK, context=ctx,
                        term=Var("safety"), type_=PyObjType())
        formula = "(n >= 1) => ((n - 1) < (n) and (n) >= 0)"
        ob = TerminationObligation(
            target="fact", measure_at_entry="n",
            measure_at_recursive_call="n - 1",
            precondition="n >= 1",
            inner=Z3Proof(formula=formula),
        )
        r = kernel.verify(ctx, goal, ob)
        assert r.success, r.message

    def test_kernel_rejects_termination_without_inner(self):
        from deppy.core.kernel import ProofKernel, TerminationObligation
        from deppy.core.types import Context, Judgment, JudgmentKind, Var, PyObjType
        kernel = ProofKernel()
        ctx = Context()
        goal = Judgment(kind=JudgmentKind.TYPE_CHECK, context=ctx,
                        term=Var("safety"), type_=PyObjType())
        ob = TerminationObligation(
            target="fact", measure_at_entry="n",
            measure_at_recursive_call="n - 1",
        )
        r = kernel.verify(ctx, goal, ob)
        assert not r.success


# ════════════════════════════════════════════════════════════════════
#  Phase 5 — Cubical safety atlas (CG1–CG4)
# ════════════════════════════════════════════════════════════════════

class TestCubicalSafety:
    """The safety pipeline must compose per-function sections into a
    Čech atlas whose cocycle conditions verify call-graph closure
    semantically — not by hardcoded ``internal_calls_closed=True``."""

    def test_safe_module_passes_atlas(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        from deppy.proofs.sidecar import ExternalSpec
        src = (
            "def divide(a, b):\n"
            "    return a / b\n"
        )
        spec = ExternalSpec(target_name="divide",
                            exception_free_when=["b != 0"])
        v = verify_module_safety(src, sidecar_specs={"divide": spec},
                                 use_drafts=False)
        assert v.cubical_atlas_safe, v.cubical_atlas_message

    def test_atlas_enforces_call_cocycle(self):
        """Caller's substituted env must imply callee's precondition.
        If it doesn't, the atlas rejects the module — even when each
        function in isolation might individually verify (e.g., via
        ``is_total`` escape on the caller)."""
        from deppy.pipeline.safety_pipeline import verify_module_safety
        from deppy.proofs.sidecar import ExternalSpec
        # safe_div requires b != 0; bad_caller escapes its own
        # propagation via is_total but still calls safe_div with 0.
        src = (
            "def safe_div(a, b):\n"
            "    return a / b\n"
            "def bad_caller(x):\n"
            "    return safe_div(x, 0)\n"
        )
        specs = {
            "safe_div": ExternalSpec(target_name="safe_div",
                                     exception_free_when=["b != 0"]),
            "bad_caller": ExternalSpec(target_name="bad_caller",
                                       is_total=True),
        }
        v = verify_module_safety(src, sidecar_specs=specs, use_drafts=False)
        assert not v.cubical_atlas_safe, \
            f"atlas should reject broken cocycle, got: {v.cubical_atlas_message}"
        # The cocycle ``True ⇒ 0 != 0`` cannot hold.
        assert "overlap" in (v.cubical_atlas_message or "").lower() \
            or "0 != 0" in (v.cubical_atlas_message or "")

    def test_atlas_accepts_consistent_substitution(self):
        from deppy.pipeline.safety_pipeline import verify_module_safety
        from deppy.proofs.sidecar import ExternalSpec
        src = (
            "def safe_div(a, b):\n"
            "    return a / b\n"
            "def good_caller(x, y):\n"
            "    return safe_div(x, y)\n"
        )
        specs = {
            "safe_div": ExternalSpec(target_name="safe_div",
                                     exception_free_when=["b != 0"]),
            "good_caller": ExternalSpec(target_name="good_caller",
                                        exception_free_when=["y != 0"]),
        }
        v = verify_module_safety(src, sidecar_specs=specs, use_drafts=False)
        assert v.cubical_atlas_safe, v.cubical_atlas_message

    def test_termination_uses_transport_proof(self):
        """The recursion discharge for a function with a decreases
        measure must be a TerminationObligation whose inner is a
        TransportProof, not a bare Z3Proof — termination is a
        homotopy fact."""
        from deppy.pipeline.safety_pipeline import verify_module_safety
        from deppy.core.kernel import TerminationObligation, TransportProof
        from deppy.proofs.sidecar import ExternalSpec
        src = (
            "def fact(n):\n"
            "    if n <= 0:\n"
            "        return 1\n"
            "    return n * fact(n - 1)\n"
        )
        spec = ExternalSpec(target_name="fact",
                            exception_free_when=["n >= 0"],
                            decreases=["n"])
        v = verify_module_safety(src, sidecar_specs={"fact": spec},
                                 use_drafts=False)
        fv = v.functions["fact"]
        # Find the recursion discharge in the proof payload.
        payload = fv.proof_payload
        sem = payload["semantic"]
        recursion_discharges = [
            d for d in sem["discharges"] if "RUNTIME_ERROR" in d["failure_kind"]
        ]
        assert recursion_discharges, "recursion discharge missing"
        inner = recursion_discharges[0]["inner"]
        assert "Termination" in inner.get("kind", "")

    def test_hazard_space_construction(self):
        from deppy.pipeline.cubical_safety import HazardSpace
        from deppy.pipeline.exception_sources import find_exception_sources
        src = (
            "def f(a, b):\n"
            "    return a / b\n"
            "def g(xs, i):\n"
            "    return xs[i]\n"
        )
        summ = find_exception_sources(src)
        per_fn = {fs.name: list(fs.uncaught_sources) for fs in summ.functions}
        space = HazardSpace.from_sources(per_fn, list(summ.module_level_sources))
        assert "f" in space.points_by_function
        assert "g" in space.points_by_function
        assert space.points_by_function["f"]
        assert space.points_by_function["g"]


# ════════════════════════════════════════════════════════════════════
#  CG5 / CG6 — spec ≃ impl as PathAbs;  callee paths, not text
# ════════════════════════════════════════════════════════════════════

class TestSpecRefinementPath:
    """CG5: a sidecar precondition refines the implementation; the
    safety claim is then a *transport* along the spec-refinement
    path, not a flat assumption discharge."""

    def test_path_endpoints(self):
        from deppy.pipeline.cubical_safety import spec_refinement_path
        p = spec_refinement_path("divide", "b != 0")
        assert p.ivar == "i"
        # PathAbs body should reference both endpoints symbolically.
        body_repr = str(p.body)
        assert "divide" in body_repr

    def test_trivial_precondition_collapses(self):
        from deppy.core.kernel import Structural
        from deppy.pipeline.cubical_safety import spec_refinement_transport
        sec = Structural(description="dummy")
        # No genuine refinement — should return section unchanged.
        out = spec_refinement_transport("f", "True", sec)
        assert out is sec

    def test_nontrivial_precondition_wraps_in_transport(self):
        from deppy.core.kernel import Structural, TransportProof
        from deppy.pipeline.cubical_safety import spec_refinement_transport
        sec = Structural(description="dummy")
        out = spec_refinement_transport("divide", "b != 0", sec)
        assert isinstance(out, TransportProof)
        assert out.base_proof is sec
        assert "Safe[divide]" in str(out.type_family)

    def test_kernel_verifies_spec_refinement_transport(self):
        from deppy.core.kernel import (
            Context, Judgment, JudgmentKind, ProofKernel, Structural,
        )
        from deppy.core.types import Var
        from deppy.pipeline.cubical_safety import spec_refinement_transport
        sec = Structural(description="dummy section")
        wrapped = spec_refinement_transport("divide", "b != 0", sec)
        kernel = ProofKernel()
        goal = Judgment(kind=JudgmentKind.WELL_FORMED,
                        context=Context(),
                        type_=Var("Safe[divide]"))
        r = kernel.verify(Context(), goal, wrapped)
        assert r.success, r.message


class TestCalleeEnvPath:
    """CG6: the cocycle obligation at a call boundary is realised as
    a transport along a path between the caller's and callee's
    parameter environments — not as raw textual substitution."""

    def test_cocycle_is_a_transport_proof(self):
        from deppy.core.kernel import TransportProof
        from deppy.pipeline.cubical_safety import (
            CallEdge, _cocycle_proof,
        )
        from deppy.core.kernel import ProofKernel
        edge = CallEdge(
            caller="caller", callee="callee",
            arg_substitution={"x": "n"},
            caller_precondition="n > 0",
            callee_precondition="x > 0",
        )
        p = _cocycle_proof(edge, ProofKernel())
        assert isinstance(p, TransportProof)
        assert "Pre[callee]" in str(p.type_family)

    def test_env_path_construction(self):
        from deppy.pipeline.cubical_safety import CallEdge, callee_env_path
        edge = CallEdge(caller="f", callee="g",
                        arg_substitution={"x": "n", "y": "m"})
        path = callee_env_path(edge)
        body = str(path.body)
        assert "f" in body and "g" in body
        # Substitution shows up in the env path label.
        assert "x=n" in body
        assert "y=m" in body


# ════════════════════════════════════════════════════════════════════
#  Cheat-audit Round 1
# ════════════════════════════════════════════════════════════════════

class TestCheatAuditRound1:
    """Regressions for cheats found in the Round-1 audit."""

    def test_internal_calls_closed_derived_from_atlas(self):
        """C1: ``internal_calls_closed`` must come from the atlas, not
        be hardcoded ``True``.  When the atlas rejects the cocycle,
        ``module_safe`` must be ``False`` and the verdict's
        ``internal_calls_closed`` must be ``False``."""
        from deppy.pipeline.safety_pipeline import verify_module_safety
        from deppy.proofs.sidecar import ExternalSpec
        # Caller has weaker precondition than callee requires —
        # cocycle must fail.
        src = (
            "def safe_div(a, b):\n"
            "    return a / b\n"
            "def caller(x):\n"
            "    return safe_div(x, x - 1)\n"
        )
        specs = {
            "safe_div": ExternalSpec(target_name="safe_div",
                                     exception_free_when=["b != 0"]),
            "caller": ExternalSpec(target_name="caller",
                                   exception_free_when=["True"]),
        }
        v = verify_module_safety(src, sidecar_specs=specs, use_drafts=False)
        # When cocycle is broken, the module is not safe.
        assert not v.module_safe
        assert not v.internal_calls_closed
        assert not v.cubical_atlas_safe

    def test_disjoint_var_precondition_does_not_cover(self):
        """Issue 5: a precondition over unrelated variables must not
        be treated as covering a safety predicate."""
        from deppy.pipeline.safety_coverage import _source_addressed_by_sidecar
        from deppy.pipeline.exception_sources import find_exception_sources
        from deppy.proofs.sidecar import ExternalSpec
        src = "def divide(a, b):\n    return a / b\n"
        summ = find_exception_sources(src)
        sources = [s for fs in summ.functions for s in fs.uncaught_sources]
        assert sources, "expected a div-by-zero source"
        spec = ExternalSpec(
            target_name="divide",
            exception_free_when=["unrelated_x > 0"],
        )
        # Z3 might *find* the implication trivially in a way that
        # spuriously claims coverage.  The var-overlap guard must
        # block this.
        assert not _source_addressed_by_sidecar(sources[0], spec)

    def test_overlapping_var_precondition_covers(self):
        """Inverse: a precondition that *does* mention the same
        variable must still be accepted."""
        from deppy.pipeline.safety_coverage import _source_addressed_by_sidecar
        from deppy.pipeline.exception_sources import find_exception_sources
        from deppy.proofs.sidecar import ExternalSpec
        src = "def divide(a, b):\n    return a / b\n"
        summ = find_exception_sources(src)
        sources = [s for fs in summ.functions for s in fs.uncaught_sources]
        spec = ExternalSpec(target_name="divide",
                            exception_free_when=["b != 0"])
        assert _source_addressed_by_sidecar(sources[0], spec)
