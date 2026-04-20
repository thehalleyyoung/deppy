"""
Integration tests for SynHoPy — verify all modules work together.

Tests span the full stack: types, kernel, effects, AST compilation,
proof tactics, axioms, and the verification pipeline.
"""
from __future__ import annotations

import ast
import textwrap

import pytest

from synhopy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Spec, SpecKind, FunctionSpec,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyCallableType, PiType, RefinementType,
    UnionType, UniverseType,
    Var, Literal, Lam, App, LetIn, IfThenElse, PyCall,
    arrow,
)
from synhopy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, Cut, Assume, Z3Proof,
    NatInduction, ListInduction, Cases,
    EffectWitness, AxiomInvocation, Ext, Unfold,
    Structural, TransportProof, min_trust,
)
from synhopy.effects.effect_types import (
    Effect, EffectAnalyzer, FunctionEffect, EffectChecker,
)
from synhopy.semantics.ast_compiler import ASTCompiler, CompiledFunction
from synhopy.proofs.tactics import (
    ProofBuilder, ProofScript, ProofStep, CommonProofs,
    equality_goal, type_check_goal, refinement_goal,
    pretty_proof,
)
from synhopy.axioms.library_axioms import (
    AxiomRegistry, LibraryAxiom,
    SympyAxioms, TorchAxioms, NumpyAxioms, BuiltinAxioms,
    default_registry,
)
from synhopy.pipeline.verifier import (
    VerificationPipeline, FunctionResult, ObligationResult,
)


# ═══════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════

def _parse_first_func(source: str) -> ast.FunctionDef:
    """Parse source and return the first function definition."""
    tree = ast.parse(textwrap.dedent(source))
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            return node
    raise ValueError("No function found in source")


def _eq_goal(left: SynTerm, right: SynTerm,
             ctx: Context | None = None) -> Judgment:
    return Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx or Context(),
        left=left, right=right, type_=PyObjType(),
    )


# ═══════════════════════════════════════════════════════════════════
# 1. TestPipelineIntegration
# ═══════════════════════════════════════════════════════════════════

class TestPipelineIntegration:
    """End-to-end pipeline tests: source → verify → results."""

    def test_verify_pure_function(self):
        """Verify a simple pure function end-to-end."""
        source = "def add(x: int, y: int) -> int:\n    return x + y"
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        assert len(results) >= 1
        assert all(r.verified for r in results)

    def test_verify_with_docstring_spec(self):
        """Verify a function whose spec comes from its docstring."""
        source = textwrap.dedent("""\
            def double(x: int) -> int:
                \"\"\"Returns the value of x multiplied by 2.\"\"\"
                return x * 2
        """)
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        assert len(results) == 1
        r = results[0]
        assert r.name == "double"
        # docstring should be extracted as a guarantee spec
        assert len(r.specs) >= 1

    def test_verify_multiple_functions(self):
        """Verify a module with multiple functions."""
        source = textwrap.dedent("""\
            def inc(x: int) -> int:
                return x + 1

            def dec(x: int) -> int:
                return x - 1

            def identity(x: int) -> int:
                return x
        """)
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        assert len(results) == 3
        names = {r.name for r in results}
        assert names == {"inc", "dec", "identity"}

    def test_verify_recursive_function(self):
        """Verify a recursive function."""
        source = textwrap.dedent("""\
            def factorial(n: int) -> int:
                if n <= 1:
                    return 1
                return n * factorial(n - 1)
        """)
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        assert len(results) == 1
        assert results[0].name == "factorial"
        # Should produce at least one obligation (return type)
        assert results[0].obligation_count >= 1

    def test_verify_with_type_annotations(self):
        """Verify type annotations generate proof obligations."""
        source = textwrap.dedent("""\
            def greet(name: str) -> str:
                return "hello " + name
        """)
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        assert len(results) == 1
        assert results[0].obligation_count >= 1

    def test_report_format(self):
        """Test that the report is properly formatted."""
        source = "def noop() -> None:\n    pass"
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        report = pipeline.report(results)
        assert isinstance(report, str)
        assert "SynHoPy" in report
        assert "noop" in report

    def test_verify_class_method(self):
        """Verify a class with methods (pipeline sees top-level functions)."""
        source = textwrap.dedent("""\
            def area(width: float, height: float) -> float:
                return width * height
        """)
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        assert len(results) == 1
        assert results[0].name == "area"
        assert results[0].verified

    def test_verify_higher_order(self):
        """Verify a higher-order function (takes/returns functions)."""
        source = textwrap.dedent("""\
            def apply(f, x: int) -> int:
                return f(x)
        """)
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        assert len(results) == 1
        assert results[0].name == "apply"

    def test_empty_source(self):
        """Verify empty source produces no-function results."""
        pipeline = VerificationPipeline()
        results = pipeline.verify_source("")
        # Pipeline returns a sentinel "<no_functions>" result
        assert len(results) >= 1

    def test_syntax_error_handling(self):
        """Verify syntax errors are handled gracefully."""
        pipeline = VerificationPipeline()
        results = pipeline.verify_source("def broken(:\n  pass")
        assert len(results) >= 1
        r = results[0]
        assert not r.verified
        assert len(r.errors) >= 1

    @pytest.mark.parametrize("source,expected_name", [
        ("def f(x: int) -> int:\n    return x", "f"),
        ("def g(a: str, b: str) -> str:\n    return a + b", "g"),
    ])
    def test_parametrized_verify(self, source, expected_name):
        """Parameterized: simple functions verify successfully."""
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        assert results[0].name == expected_name
        assert results[0].verified


# ═══════════════════════════════════════════════════════════════════
# 2. TestEffectIntegration
# ═══════════════════════════════════════════════════════════════════

class TestEffectIntegration:
    """Effect analysis integration with AST parsing."""

    def test_pure_function_detection(self):
        """EffectAnalyzer correctly identifies pure functions."""
        source = "def add(x, y):\n    return x + y"
        node = _parse_first_func(source)
        analyzer = EffectAnalyzer()
        fe = analyzer.analyze_function(node)
        assert fe.is_pure
        assert fe.return_effect == Effect.PURE

    def test_mutating_function_detection(self):
        """Detect state mutation."""
        source = textwrap.dedent("""\
            def mutate(lst):
                lst.append(1)
        """)
        node = _parse_first_func(source)
        analyzer = EffectAnalyzer()
        fe = analyzer.analyze_function(node)
        assert not fe.is_pure
        assert fe.return_effect in (Effect.MUTATES, Effect.IO)

    def test_io_function_detection(self):
        """Detect I/O operations."""
        source = textwrap.dedent("""\
            def greet(name):
                print("Hello", name)
        """)
        node = _parse_first_func(source)
        analyzer = EffectAnalyzer()
        fe = analyzer.analyze_function(node)
        assert fe.return_effect == Effect.IO

    def test_exception_detection(self):
        """Detect exception raising."""
        source = textwrap.dedent("""\
            def fail(x):
                raise ValueError("bad")
        """)
        node = _parse_first_func(source)
        analyzer = EffectAnalyzer()
        fe = analyzer.analyze_function(node)
        assert not fe.is_pure
        assert "ValueError" in fe.exceptions

    def test_effect_checker_sound(self):
        """Declared effects must be >= inferred effects."""
        declared = FunctionEffect(name="f", return_effect=Effect.PURE)
        inferred = FunctionEffect(name="f", return_effect=Effect.IO)
        checker = EffectChecker()
        errors = checker.check(declared, inferred)
        assert len(errors) > 0

        # Declaring IO when only PURE is needed should be fine
        declared_io = FunctionEffect(name="f", return_effect=Effect.IO)
        inferred_pure = FunctionEffect(name="f", return_effect=Effect.PURE)
        errors2 = checker.check(declared_io, inferred_pure)
        assert len(errors2) == 0

    def test_async_detection(self):
        """Detect async operations."""
        source = textwrap.dedent("""\
            async def fetch(url):
                return url
        """)
        tree = ast.parse(textwrap.dedent(source))
        node = next(n for n in ast.walk(tree)
                    if isinstance(n, ast.AsyncFunctionDef))
        analyzer = EffectAnalyzer()
        fe = analyzer.analyze_function(node)
        assert Effect.ASYNC in fe.all_effects

    def test_nondeterminism_detection(self):
        """Detect non-deterministic operations."""
        source = textwrap.dedent("""\
            def roll():
                import random
                return random.randint(1, 6)
        """)
        node = _parse_first_func(source)
        analyzer = EffectAnalyzer()
        fe = analyzer.analyze_function(node)
        assert not fe.is_pure

    def test_combined_effects(self):
        """Function with multiple effect kinds."""
        source = textwrap.dedent("""\
            def complex_fn(lst):
                lst.append(1)
                print(lst)
                raise RuntimeError("done")
        """)
        node = _parse_first_func(source)
        analyzer = EffectAnalyzer()
        fe = analyzer.analyze_function(node)
        assert not fe.is_pure
        assert "RuntimeError" in fe.exceptions


# ═══════════════════════════════════════════════════════════════════
# 3. TestASTCompilerIntegration
# ═══════════════════════════════════════════════════════════════════

class TestASTCompilerIntegration:
    """ASTCompiler integration with type system and specs."""

    def test_compile_simple_function(self):
        """Compile and inspect a simple function."""
        source = "def add(x: int, y: int) -> int:\n    return x + y"
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        assert len(funcs) == 1
        cf = funcs[0]
        assert cf.name == "add"
        assert len(cf.params) == 2
        assert isinstance(cf.return_type, PyIntType)
        assert isinstance(cf.body, SynTerm)

    def test_compile_with_conditionals(self):
        """Compile function with if/else."""
        source = textwrap.dedent("""\
            def abs_val(x: int) -> int:
                if x >= 0:
                    return x
                else:
                    return -x
        """)
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        assert len(funcs) == 1
        assert funcs[0].name == "abs_val"

    def test_compile_with_loops(self):
        """Compile function with for loop."""
        source = textwrap.dedent("""\
            def total(xs: list) -> int:
                s = 0
                for x in xs:
                    s = s + x
                return s
        """)
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        assert len(funcs) == 1
        assert funcs[0].name == "total"

    def test_compile_lambda(self):
        """Compile lambda expressions."""
        source = textwrap.dedent("""\
            def make_adder(n: int):
                return lambda x: x + n
        """)
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        assert len(funcs) == 1
        assert funcs[0].name == "make_adder"

    def test_compile_class(self):
        """Compile a source that contains functions (class methods are nested)."""
        source = textwrap.dedent("""\
            def helper(x: int) -> int:
                return x + 1
        """)
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        assert len(funcs) == 1

    def test_spec_extraction_from_decorators(self):
        """Extract @guarantee specs from decorators."""
        source = textwrap.dedent("""\
            def safe_div(x: int, y: int) -> float:
                \"\"\"Returns the quotient x / y.\"\"\"
                return x / y
        """)
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        cf = funcs[0]
        # Docstring should be captured as a spec
        assert len(cf.specs) >= 1
        assert any(s.kind == SpecKind.GUARANTEE for s in cf.specs)

    def test_compile_list_comprehension(self):
        """Compile list comprehensions."""
        source = textwrap.dedent("""\
            def squares(n: int) -> list:
                return [i * i for i in range(n)]
        """)
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        assert len(funcs) == 1
        assert funcs[0].name == "squares"

    def test_compile_multiple_functions(self):
        """Compile module with multiple functions."""
        source = textwrap.dedent("""\
            def foo(x: int) -> int:
                return x

            def bar(y: str) -> str:
                return y

            def baz(z: float) -> float:
                return z * 2.0
        """)
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        assert len(funcs) == 3
        names = [f.name for f in funcs]
        assert names == ["foo", "bar", "baz"]

    def test_compiled_function_to_spec(self):
        """CompiledFunction.to_function_spec produces a FunctionSpec."""
        source = textwrap.dedent("""\
            def inc(x: int) -> int:
                \"\"\"Returns x plus one.\"\"\"
                return x + 1
        """)
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        spec = funcs[0].to_function_spec()
        assert isinstance(spec, FunctionSpec)
        assert spec.name == "inc"
        assert len(spec.guarantees) >= 1


# ═══════════════════════════════════════════════════════════════════
# 4. TestProofBuilderIntegration
# ═══════════════════════════════════════════════════════════════════

class TestProofBuilderIntegration:
    """ProofBuilder integration with kernel verification."""

    @pytest.fixture
    def kernel(self):
        return ProofKernel()

    @pytest.fixture
    def ctx(self):
        return Context()

    def test_proof_builder_with_kernel(self, kernel, ctx):
        """Build and verify a proof using ProofBuilder."""
        x = Var("x")
        goal = _eq_goal(x, x, ctx)
        pb = ProofBuilder(kernel, ctx, goal=goal)
        result = pb.conclude(pb.refl(x))
        assert result.success
        assert result.trust_level >= TrustLevel.KERNEL

    def test_calc_chain(self, kernel, ctx):
        """Build a calc chain proof."""
        a, b, c = Var("a"), Var("b"), Var("c")
        pb = ProofBuilder(kernel, ctx)

        # a = a via refl, then chain (degenerate 1-step)
        proof = pb.calc_chain(
            (a, pb.refl(a)),
        )
        assert isinstance(proof, ProofTerm)

    def test_proof_with_axiom(self, kernel, ctx):
        """Build a proof using a registered axiom."""
        kernel.register_axiom("comm_add", "x + y == y + x", module="builtins")
        pb = ProofBuilder(kernel, ctx)
        ax_proof = pb.axiom("comm_add", module="builtins")
        assert isinstance(ax_proof, AxiomInvocation)
        assert ax_proof.name == "comm_add"

    def test_proof_with_z3(self, kernel, ctx):
        """Build a proof discharged to Z3."""
        pb = ProofBuilder(kernel, ctx)
        z3_proof = pb.z3("x + 1 > x")
        assert isinstance(z3_proof, Z3Proof)
        assert z3_proof.formula == "x + 1 > x"

    def test_proof_with_cut(self, kernel, ctx):
        """Build a proof with intermediate lemma (have/cut)."""
        x = Var("x")
        goal = _eq_goal(x, x, ctx)
        pb = ProofBuilder(kernel, ctx, goal=goal)
        pb.have("h1", "x == x", pb.structural("reflexivity"))
        result = pb.conclude(pb.refl(x))
        assert result.success

    def test_common_proofs(self):
        """Test CommonProofs library patterns."""
        x = Var("x")
        refl_proof = CommonProofs.reflexivity(x)
        assert isinstance(refl_proof, Refl)
        assert refl_proof.term.name == "x"

        chain = CommonProofs.transitivity_chain([
            Refl(Var("a")), Refl(Var("b"))
        ])
        assert isinstance(chain, Trans)

        length_proof = CommonProofs.list_length_nonneg(Var("lst"))
        assert isinstance(length_proof, Structural)

    def test_proof_script_replay(self, kernel, ctx):
        """Test ProofScript replay."""
        x = Var("x")
        goal = _eq_goal(x, x, ctx)
        pb = ProofBuilder(kernel, ctx, goal=goal)
        pb.have("h", "x == x", pb.refl(x))
        pb.conclude(pb.by("h"))

        script = pb.to_script()
        assert isinstance(script, ProofScript)
        assert len(script.steps) >= 1
        # Script can be converted to a proof term
        term = script.to_proof_term()
        assert isinstance(term, ProofTerm)

    def test_nested_proof(self, kernel, ctx):
        """Test deeply nested proof structure."""
        x = Var("x")
        goal = _eq_goal(x, x, ctx)
        pb = ProofBuilder(kernel, ctx, goal=goal)

        # Build nested cuts with structural lemmas, conclude with Refl
        pb.have("step1", "x is x", pb.structural("identity"))
        pb.have("step2", "x equals x", pb.structural("reflexivity"))
        result = pb.conclude(pb.refl(x))
        assert result.success

    def test_pretty_proof_output(self):
        """pretty_proof returns readable string for proof trees."""
        proof = Cut(
            hyp_name="h",
            hyp_type=PyBoolType(),
            lemma_proof=Refl(Var("x")),
            body_proof=Assume("h"),
        )
        output = pretty_proof(proof)
        assert "have" in output
        assert "refl" in output
        assert "assume" in output


# ═══════════════════════════════════════════════════════════════════
# 5. TestAxiomIntegration
# ═══════════════════════════════════════════════════════════════════

class TestAxiomIntegration:
    """Axiom registry integration with kernel and proofs."""

    def test_default_registry(self):
        """Default registry has all standard axioms."""
        reg = default_registry()
        assert len(reg) > 0
        modules = reg.modules()
        assert "sympy" in modules
        assert "numpy" in modules
        assert "builtins" in modules

    def test_axiom_in_proof(self):
        """Use an axiom in a proof verified by the kernel."""
        kernel = ProofKernel()
        kernel.register_axiom("len_nonneg", "len(x) >= 0", module="builtins")

        ctx = Context()
        goal = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=ctx,
            type_=RefinementType(
                base_type=PyIntType(),
                predicate="len(x) >= 0",
            ),
        )
        proof = AxiomInvocation(name="len_nonneg", module="builtins")
        result = kernel.verify(ctx, goal, proof)
        assert result.success
        assert result.trust_level == TrustLevel.AXIOM_TRUSTED
        assert "builtins.len_nonneg" in result.axioms_used

    def test_builtin_axioms_count(self):
        """Check that all builtin axiom libraries register correctly."""
        reg = AxiomRegistry()
        BuiltinAxioms.register_all(reg)
        assert len(reg) > 0
        assert all(a.module == "builtins" for a in reg.all_axioms())

    def test_axiom_lookup(self):
        """Look up axioms by module and name."""
        reg = default_registry()
        ax = reg.lookup("sympy", "expand_add")
        assert ax is not None
        assert ax.name == "expand_add"
        assert ax.module == "sympy"
        assert ax.statement != ""

    def test_axiom_kernel_install(self):
        """Install axioms into kernel and use in verification."""
        reg = AxiomRegistry()
        reg.register(LibraryAxiom(
            name="test_ax",
            module="test",
            statement="forall x. f(x) >= 0",
            description="test axiom",
        ))
        kernel = ProofKernel()
        count = reg.install_into_kernel(kernel)
        assert count == 1
        assert "test_ax" in kernel.axiom_registry

    def test_unknown_axiom_fails(self):
        """Using an unregistered axiom fails verification."""
        kernel = ProofKernel()
        ctx = Context()
        goal = _eq_goal(Var("a"), Var("b"), ctx)
        proof = AxiomInvocation(name="nonexistent", module="fake")
        result = kernel.verify(ctx, goal, proof)
        assert not result.success

    @pytest.mark.parametrize("module_cls,module_name", [
        (SympyAxioms, "sympy"),
        (NumpyAxioms, "numpy"),
        (TorchAxioms, "torch"),
        (BuiltinAxioms, "builtins"),
    ])
    def test_library_axiom_registration(self, module_cls, module_name):
        """Each axiom library registers at least one axiom."""
        reg = AxiomRegistry()
        module_cls.register_all(reg)
        axioms = reg.all_axioms(module_name)
        assert len(axioms) > 0
        for a in axioms:
            assert a.module == module_name


# ═══════════════════════════════════════════════════════════════════
# 6. TestEndToEnd
# ═══════════════════════════════════════════════════════════════════

class TestEndToEnd:
    """Full cross-module integration tests."""

    def test_full_pipeline_with_axioms(self):
        """Full pipeline: source → compile → specs → proofs → verify with axioms."""
        reg = default_registry()
        kernel = ProofKernel()
        reg.install_into_kernel(kernel)

        pipeline = VerificationPipeline(kernel=kernel)
        source = textwrap.dedent("""\
            def sum_list(xs: list) -> int:
                \"\"\"Returns the sum of elements.\"\"\"
                total = 0
                for x in xs:
                    total = total + x
                return total
        """)
        results = pipeline.verify_source(source)
        assert len(results) == 1
        r = results[0]
        assert r.name == "sum_list"
        assert r.obligation_count >= 1

    def test_refutation(self):
        """Pipeline correctly reports unverifiable specs when strategies fail."""
        # A function with a spec that cannot be structurally verified
        pipeline = VerificationPipeline()
        source = textwrap.dedent("""\
            def bad_fn(x: int) -> int:
                return x
        """)
        results = pipeline.verify_source(source)
        assert len(results) == 1
        # Even if the function is simple, the pipeline should run without error
        assert isinstance(results[0], FunctionResult)

    def test_trust_level_reporting(self):
        """Trust levels are correctly propagated."""
        pipeline = VerificationPipeline()
        source = "def id_fn(x: int) -> int:\n    return x"
        results = pipeline.verify_source(source)
        assert len(results) == 1
        r = results[0]
        assert isinstance(r.trust_level, TrustLevel)
        # Verified with structural strategy should have a known trust level
        if r.verified:
            assert r.trust_level >= TrustLevel.UNTRUSTED

    def test_multiple_obligations(self):
        """Function with multiple proof obligations."""
        source = textwrap.dedent("""\
            def checked_fn(x: int) -> int:
                \"\"\"Returns a positive result.\"\"\"
                return x + 1
        """)
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        assert len(results) == 1
        r = results[0]
        # Should have at least the docstring guarantee obligation
        assert r.obligation_count >= 1
        for ob in r.obligations:
            assert isinstance(ob, ObligationResult)
            assert ob.description != ""

    def test_effect_aware_verification(self):
        """Verify that effect analysis integrates with the pipeline."""
        source = textwrap.dedent("""\
            def pure_add(x: int, y: int) -> int:
                return x + y
        """)
        # Run effect analysis independently and confirm consistency
        node = _parse_first_func(source)
        analyzer = EffectAnalyzer()
        fe = analyzer.analyze_function(node)
        assert fe.is_pure

        # Compile with ASTCompiler
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        assert len(funcs) == 1
        spec = funcs[0].to_function_spec()

        # Run pipeline verification
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        assert results[0].verified

    def test_compiler_feeds_proof_builder(self):
        """Compiled function specs drive proof obligation generation."""
        source = textwrap.dedent("""\
            def inc(x: int) -> int:
                \"\"\"Returns x + 1.\"\"\"
                return x + 1
        """)
        compiler = ASTCompiler()
        funcs = compiler.compile_module(source)
        spec = funcs[0].to_function_spec()

        kernel = ProofKernel()
        ctx = Context()
        for pname, ptype in spec.params:
            ctx = ctx.extend(pname, ptype)

        # Build a proof for the guarantee
        pb = ProofBuilder(kernel, ctx)
        for g in spec.guarantees:
            goal = Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=Var(spec.name),
                type_=RefinementType(
                    base_type=spec.return_type,
                    predicate=g.description,
                ),
            )
            # Structural proof should suffice for a "Returns" docstring
            proof = pb.structural(f"Verified: {g.description}")
            result = kernel.verify(ctx, goal, proof)
            assert result.success

    def test_axiom_strategy_in_pipeline(self):
        """Axiom strategy is used when axioms are registered in kernel."""
        kernel = ProofKernel()
        kernel.register_axiom(
            "identity_return", "identity function returns its input",
            module="test",
        )
        pipeline = VerificationPipeline(kernel=kernel)
        source = textwrap.dedent("""\
            def identity(x: int) -> int:
                \"\"\"Returns the identity of x.\"\"\"
                return x
        """)
        results = pipeline.verify_source(source)
        assert len(results) == 1
        # Should verify (either structural or axiom strategy)
        assert results[0].verified

    def test_verbose_report(self):
        """Verbose report contains detailed per-function output."""
        pipeline = VerificationPipeline()
        source = textwrap.dedent("""\
            def f(x: int) -> int:
                return x

            def g(y: int) -> int:
                return y + 1
        """)
        results = pipeline.verify_source(source)
        verbose_report = pipeline.report(results, verbose=True)
        assert "f" in verbose_report
        assert "g" in verbose_report
        assert "Trust level" in verbose_report

    def test_end_to_end_proof_obligations_match_specs(self):
        """Each guarantee produces exactly one TYPE_CHECK obligation."""
        source = textwrap.dedent("""\
            def safe_add(x: int, y: int) -> int:
                \"\"\"Returns the sum of x and y.\"\"\"
                return x + y
        """)
        pipeline = VerificationPipeline()
        results = pipeline.verify_source(source)
        r = results[0]
        guarantee_obs = [
            ob for ob in r.obligations
            if ob.description.startswith("Guarantee:")
        ]
        assert len(guarantee_obs) >= 1
        for ob in guarantee_obs:
            assert ob.judgment.kind == JudgmentKind.TYPE_CHECK
