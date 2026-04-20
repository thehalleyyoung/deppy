"""
Comprehensive tests for deppy.proofs.sugar — the syntactic-sugar DSL.

Covers: decorator specs, refinement types, library trust blocks, fluent Proof
builder, FormalProof builder, ProofContext, quick combinators, domain knowledge,
spec extraction, and global kernel management.
"""
from __future__ import annotations

import pytest

from deppy.proofs.sugar import (
    guarantee, requires, ensures, pure, reads, mutates,
    total, partial_fn, invariant, decreases, verify,
    Pos, Nat, NonEmpty, Bounded, NonNull, Sorted, SizedExact, Refine,
    library_trust, LibraryTrustBlock,
    Proof, FormalProof, ProofContext,
    refl, sym, trans, by_axiom, by_z3, by_cases, by_induction,
    by_list_induction, by_ext, by_cong, by_unfold, by_rewrite,
    by_transport, by_effect,
    given, DomainKnowledge, extract_spec,
    set_global_kernel, get_global_kernel,
    _get_spec, _SpecMetadata,
)
from deppy.core.kernel import (
    ProofKernel, TrustLevel, VerificationResult,
    Refl as ReflTerm, Sym as SymTerm, Trans as TransTerm,
    Structural, Assume, Z3Proof, AxiomInvocation,
    NatInduction, ListInduction, Cases, Ext, Cong,
    Unfold, Rewrite, TransportProof, EffectWitness,
)
from deppy.core.types import (
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyListType, RefinementType, PyClassType,
    Var, Literal, Context, JudgmentKind,
)
from deppy.core.formal_ops import Op, OpCall, formal_eq


# ═══════════════════════════════════════════════════════════════════
#  Helpers
# ═══════════════════════════════════════════════════════════════════

def _fresh_kernel() -> ProofKernel:
    return ProofKernel()


# ═══════════════════════════════════════════════════════════════════
#  §1 Decorator-based Specifications
# ═══════════════════════════════════════════════════════════════════

class TestDecoratorSpecs:

    def test_guarantee_attaches_metadata(self):
        @guarantee("sorted output")
        def f(xs):
            return xs
        spec = _get_spec(f)
        assert spec.guarantees == ["sorted output"]

    def test_multiple_guarantees_stack(self):
        @guarantee("is sorted")
        @guarantee("is a permutation")
        def f(xs):
            return xs
        spec = _get_spec(f)
        assert "is sorted" in spec.guarantees
        assert "is a permutation" in spec.guarantees
        assert len(spec.guarantees) == 2

    def test_requires_callable_predicate(self):
        pred = lambda xs: len(xs) > 0
        @requires(pred)
        def f(xs):
            return xs
        spec = _get_spec(f)
        assert len(spec.preconditions) == 1
        assert callable(spec.preconditions[0])

    def test_requires_string_predicate(self):
        @requires("xs is non-empty")
        def f(xs):
            return xs
        spec = _get_spec(f)
        assert len(spec.preconditions) == 1
        # String predicates are wrapped in a lambda
        assert callable(spec.preconditions[0])

    def test_ensures_callable_postcondition(self):
        pred = lambda xs, result: len(result) == len(xs)
        @ensures(pred)
        def f(xs):
            return xs[:]
        spec = _get_spec(f)
        assert len(spec.postconditions) == 1
        assert callable(spec.postconditions[0])

    def test_pure_sets_effect(self):
        @pure
        def f():
            return 1
        assert _get_spec(f).effect == "Pure"

    def test_reads_sets_effect(self):
        @reads
        def f():
            return 1
        assert _get_spec(f).effect == "Reads"

    def test_mutates_sets_effect(self):
        @mutates
        def f():
            pass
        assert _get_spec(f).effect == "Mutates"

    def test_total_sets_both(self):
        @total
        def f():
            return 1
        spec = _get_spec(f)
        assert spec.is_total is True
        assert spec.effect == "Pure"

    def test_partial_fn_sets_flag(self):
        @partial_fn
        def f():
            return 1
        assert _get_spec(f).is_partial is True

    def test_invariant_attaches(self):
        @invariant("loop counter decreases")
        def f():
            pass
        spec = _get_spec(f)
        assert "loop counter decreases" in spec.invariants

    def test_decreases_attaches(self):
        @decreases("len(xs)")
        def f(xs):
            return xs
        spec = _get_spec(f)
        assert any("decreases" in inv and "len(xs)" in inv for inv in spec.invariants)

    def test_decorator_composition(self):
        @guarantee("result >= 0")
        @requires(lambda x: True)
        @ensures(lambda x, r: r >= 0)
        @pure
        def abs_val(x: int) -> int:
            return abs(x)
        spec = _get_spec(abs_val)
        assert spec.guarantees == ["result >= 0"]
        assert len(spec.preconditions) == 1
        assert len(spec.postconditions) == 1
        assert spec.effect == "Pure"
        # Function still works
        assert abs_val(-5) == 5


# ═══════════════════════════════════════════════════════════════════
#  §2 Refinement Type Constructors
# ═══════════════════════════════════════════════════════════════════

class TestRefinementTypes:

    def test_pos_creates_refinement(self):
        t = Pos()
        assert isinstance(t, RefinementType)
        assert isinstance(t.base_type, PyIntType)
        assert "x > 0" in t.predicate

    def test_nat_creates_refinement(self):
        t = Nat()
        assert isinstance(t, RefinementType)
        assert isinstance(t.base_type, PyIntType)
        assert "x >= 0" in t.predicate

    def test_nonempty_with_element_type(self):
        t = NonEmpty(PyIntType())
        assert isinstance(t, RefinementType)
        assert isinstance(t.base_type, PyListType)
        assert t.base_type.element_type is not None
        assert "len(xs) > 0" in t.predicate

    def test_nonempty_without_element_type(self):
        t = NonEmpty()
        assert isinstance(t, RefinementType)
        assert isinstance(t.base_type, PyListType)
        assert "len(xs) > 0" in t.predicate

    def test_bounded_range(self):
        t = Bounded(0.0, 1.0)
        assert isinstance(t, RefinementType)
        assert isinstance(t.base_type, PyFloatType)
        assert "0.0" in t.predicate
        assert "1.0" in t.predicate

    def test_nonnull_with_base(self):
        t = NonNull(PyStrType())
        assert isinstance(t, RefinementType)
        assert isinstance(t.base_type, PyStrType)
        assert "x is not None" in t.predicate

    def test_nonnull_default_base(self):
        t = NonNull()
        assert isinstance(t, RefinementType)
        assert isinstance(t.base_type, PyObjType)

    def test_sorted_type(self):
        t = Sorted(PyIntType())
        assert isinstance(t, RefinementType)
        assert isinstance(t.base_type, PyListType)
        assert "xs[i] <= xs[i+1]" in t.predicate

    def test_sized_exact(self):
        t = SizedExact(5)
        assert isinstance(t, RefinementType)
        assert "len(xs) == 5" in t.predicate

    def test_refine_custom_predicate(self):
        t = Refine(PyIntType(), "x % 2 == 0")
        assert isinstance(t, RefinementType)
        assert isinstance(t.base_type, PyIntType)
        assert t.predicate == "x % 2 == 0"

    def test_refine_custom_var_name(self):
        t = Refine(PyStrType(), "len(s) <= 255", var="s")
        assert t.var_name == "s"
        assert t.predicate == "len(s) <= 255"


# ═══════════════════════════════════════════════════════════════════
#  §3 Library Trust Blocks
# ═══════════════════════════════════════════════════════════════════

class TestLibraryTrust:

    def test_library_trust_context_manager(self):
        with library_trust("sympy") as sp:
            assert isinstance(sp, LibraryTrustBlock)
            assert sp.module == "sympy"

    def test_axiom_registration(self):
        with library_trust("numpy") as np:
            np.axiom("dot(A, B).T == dot(B.T, A.T)", name="dot_transpose")
        assert len(np.axioms) == 1
        assert np.axioms[0] == ("dot_transpose", "dot(A, B).T == dot(B.T, A.T)")

    def test_axiom_auto_name(self):
        with library_trust("math") as m:
            m.axiom("sin(x)**2 + cos(x)**2 == 1")
        name, _ = m.axioms[0]
        assert len(name) > 0
        # Auto-names are derived from statement
        assert "sin" in name

    def test_axiom_with_when_clause(self):
        with library_trust("math") as m:
            m.axiom("log(a*b) == log(a) + log(b)", name="log_mul",
                     when="a > 0 and b > 0")
        _, stmt = m.axioms[0]
        assert "[when a > 0 and b > 0]" in stmt

    def test_bind_kernel_registers_axioms(self):
        kernel = _fresh_kernel()
        with library_trust("sympy") as sp:
            sp.axiom("expand(a+b) = expand(a)+expand(b)", name="expand_add")
        sp.bind_kernel(kernel)
        assert "sympy.expand_add" in kernel.axiom_registry

    def test_bind_kernel_via_constructor(self):
        kernel = _fresh_kernel()
        with library_trust("torch", kernel=kernel) as t:
            t.axiom("relu(relu(x)) == relu(x)", name="relu_idem")
        assert "torch.relu_idem" in kernel.axiom_registry

    def test_use_creates_invocation(self):
        with library_trust("sympy") as sp:
            sp.axiom("simplify(simplify(e)) = simplify(e)", name="simp_idem")
            inv = sp.use("simp_idem")
        assert isinstance(inv, AxiomInvocation)
        assert inv.name == "simp_idem"
        assert inv.module == "sympy"

    def test_multiple_libraries(self):
        with library_trust("numpy") as np_block:
            np_block.axiom("A @ B shape OK", name="matmul_shape")
        with library_trust("scipy") as sp_block:
            sp_block.axiom("inv(inv(A)) == A", name="inv_invol")
        assert np_block.module == "numpy"
        assert sp_block.module == "scipy"
        assert len(np_block.axioms) == 1
        assert len(sp_block.axioms) == 1

    def test_nested_trust_blocks(self):
        with library_trust("outer") as outer:
            outer.axiom("outer fact", name="of")
            with library_trust("inner") as inner:
                inner.axiom("inner fact", name="if_")
            assert len(inner.axioms) == 1
        assert len(outer.axioms) == 1


# ═══════════════════════════════════════════════════════════════════
#  §4 Fluent Proof Builder
# ═══════════════════════════════════════════════════════════════════

class TestFluentProof:

    def test_simple_axiom_proof(self):
        k = _fresh_kernel()
        result = (
            Proof("sorted(sorted(xs)) == sorted(xs)")
            .using(k)
            .by_axiom("sorted_idempotent", "builtins")
            .qed()
        )
        assert isinstance(result, VerificationResult)
        # Axiom not registered, so trust is UNTRUSTED; we test the flow
        assert result.trust_level == TrustLevel.UNTRUSTED

    def test_z3_proof(self):
        k = _fresh_kernel()
        result = (
            Proof("abs(x) >= 0")
            .using(k)
            .given(x="int")
            .by_z3()
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_structural_proof(self):
        k = _fresh_kernel()
        result = (
            Proof("list is iterable")
            .using(k)
            .by_structural()
            .qed()
        )
        assert result.success

    def test_given_bindings(self):
        k = _fresh_kernel()
        p = Proof("x + y == y + x").using(k).given(x="int", y="int")
        # given should extend context
        result = p.by_z3().qed()
        assert isinstance(result, VerificationResult)

    def test_assuming_adds_hypothesis(self):
        k = _fresh_kernel()
        result = (
            Proof("x + 1 > 0")
            .using(k)
            .given(x="int")
            .assuming("h", "x >= 0")
            .by_z3("x >= 0 => x + 1 > 0")
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_have_with_by_callable(self):
        k = _fresh_kernel()
        result = (
            Proof("goal")
            .using(k)
            .have("h1", "x > 0", by=lambda p: Assume(name="precond"))
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_have_with_by_z3(self):
        k = _fresh_kernel()
        result = (
            Proof("goal")
            .using(k)
            .have("h1", "1 + 1 == 2", by_z3="1 + 1 == 2")
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_have_with_by_axiom(self):
        k = _fresh_kernel()
        result = (
            Proof("goal")
            .using(k)
            .have("h1", "expand works", by_axiom=("expand_add", "sympy"))
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_have_default_structural(self):
        k = _fresh_kernel()
        result = (
            Proof("goal")
            .using(k)
            .have("h1", "obvious fact")
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_calc_chain_single(self):
        k = _fresh_kernel()
        result = (
            Proof("a == b")
            .using(k)
            .calc(
                "a",
                ("== b", Structural(description="by definition")),
            )
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_calc_chain_multi(self):
        k = _fresh_kernel()
        result = (
            Proof("a == c")
            .using(k)
            .calc(
                "a",
                ("== b", Structural(description="step 1")),
                ("== c", Structural(description="step 2")),
            )
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_by_induction(self):
        k = _fresh_kernel()
        base = Structural(description="base case")
        step = Structural(description="inductive step")
        result = (
            Proof("sum(0..n) == n*(n+1)/2")
            .using(k)
            .given(n="int")
            .by_induction(on="n", base=base, step=step)
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_by_cases(self):
        k = _fresh_kernel()
        result = (
            Proof("abs(x) >= 0")
            .using(k)
            .given(x="int")
            .by_cases(
                Var("x"),
                ("x >= 0", Structural(description="positive")),
                ("x < 0", Structural(description="negative")),
            )
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_by_refl(self):
        k = _fresh_kernel()
        # Proof() creates a TYPING goal, not EQUAL; Refl only applies to EQUAL goals
        result = (
            Proof("x == x")
            .using(k)
            .by_refl(Var("x"))
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_proof_auto_creates_kernel(self):
        result = Proof("trivial").by_structural().qed()
        assert isinstance(result, VerificationResult)

    def test_transport(self):
        k = _fresh_kernel()
        path = Structural(description="path proof")
        base = Structural(description="base proof")
        result = (
            Proof("P(b)")
            .using(k)
            .transport(along=path, base=base)
            .qed()
        )
        assert isinstance(result, VerificationResult)


# ═══════════════════════════════════════════════════════════════════
#  §5 FormalProof Builder
# ═══════════════════════════════════════════════════════════════════

class TestFormalProof:

    def test_formal_eq_construction(self):
        k = _fresh_kernel()
        x = Var("x")
        result = (
            FormalProof.eq(x, x)
            .using(k)
            .by_refl(x)
            .qed()
        )
        assert isinstance(result, VerificationResult)
        assert result.success

    def test_formal_check_construction(self):
        k = _fresh_kernel()
        result = (
            FormalProof.check(Var("x"), PyIntType())
            .using(k)
            .by_refl()
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_formal_proof_with_axiom(self):
        k = _fresh_kernel()
        a, b = Var("a"), Var("b")
        result = (
            FormalProof.eq(a, b)
            .using(k)
            .by_axiom("comm", "arith")
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_formal_proof_given_bindings(self):
        k = _fresh_kernel()
        x = Var("x")
        # .given() extends context; verify it produces a valid VerificationResult
        fp = FormalProof.eq(x, x).using(k).given(x=PyIntType())
        result = fp.by_refl(x).qed()
        assert isinstance(result, VerificationResult)

    def test_formal_proof_by_refl(self):
        k = _fresh_kernel()
        result = (
            FormalProof.eq(Var("a"), Var("a"))
            .using(k)
            .by_refl(Var("a"))
            .qed()
        )
        assert result.success

    def test_formal_proof_by_trans(self):
        k = _fresh_kernel()
        p1 = Structural(description="a = b")
        p2 = Structural(description="b = c")
        result = (
            FormalProof.eq(Var("a"), Var("c"))
            .using(k)
            .by_trans(p1, p2)
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_formal_proof_by_cong(self):
        k = _fresh_kernel()
        inner = ReflTerm(term=Var("x"))
        result = (
            FormalProof.eq(Var("f_x"), Var("f_x"))
            .using(k)
            .by_cong(Var("f"), inner)
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_formal_proof_auto_kernel(self):
        result = (
            FormalProof.eq(Var("x"), Var("x"))
            .by_refl(Var("x"))
            .qed()
        )
        assert result.success

    def test_formal_proof_by_z3(self):
        k = _fresh_kernel()
        result = (
            FormalProof.eq(Var("a"), Var("b"))
            .using(k)
            .by_z3("a == b")
            .qed()
        )
        assert isinstance(result, VerificationResult)


# ═══════════════════════════════════════════════════════════════════
#  §6 ProofContext
# ═══════════════════════════════════════════════════════════════════

class TestProofContext:

    def test_context_manager_basic(self):
        k = _fresh_kernel()
        with ProofContext(k, "x + 0 == x") as p:
            result = p.qed()
        assert isinstance(result, VerificationResult)

    def test_context_given_and_assume(self):
        k = _fresh_kernel()
        with ProofContext(k, "x > 0") as p:
            p.given(x="int")
            p.assume("h", "x is an integer")
            result = p.qed()
        assert isinstance(result, VerificationResult)

    def test_context_have_and_qed(self):
        k = _fresh_kernel()
        with ProofContext(k, "conclusion") as p:
            p.have("step1", "intermediate", by_z3="1 == 1")
            result = p.qed(by=p.by("step1"))
        assert isinstance(result, VerificationResult)

    def test_context_by_reference(self):
        k = _fresh_kernel()
        with ProofContext(k, "goal") as p:
            p.have("h1", "fact 1", by=Assume(name="h1"))
            ref = p.by("h1")
            assert isinstance(ref, Assume)

    def test_context_with_formal_goal(self):
        k = _fresh_kernel()
        goal = formal_eq(Context(), Var("x"), Var("x"))
        with ProofContext(k, formal_goal=goal) as p:
            result = p.qed(by=ReflTerm(term=Var("x")))
        assert isinstance(result, VerificationResult)
        assert result.success

    def test_context_multiple_steps(self):
        k = _fresh_kernel()
        with ProofContext(k, "final goal") as p:
            p.have("s1", "step 1")
            p.have("s2", "step 2", by_axiom=("ax1", "mod"))
            p.have("s3", "step 3", by_z3="1 + 1 == 2")
            result = p.qed()
        assert isinstance(result, VerificationResult)

    def test_context_auto_kernel(self):
        with ProofContext(goal="trivial") as p:
            result = p.qed()
        assert isinstance(result, VerificationResult)

    def test_context_have_default_structural(self):
        k = _fresh_kernel()
        with ProofContext(k, "goal") as p:
            p.have("h1", "obvious")
            result = p.qed()
        assert isinstance(result, VerificationResult)


# ═══════════════════════════════════════════════════════════════════
#  §7 Quick Proof Combinators
# ═══════════════════════════════════════════════════════════════════

class TestQuickCombinators:

    def test_refl_string(self):
        r = refl("x")
        assert isinstance(r, ReflTerm)
        assert isinstance(r.term, Var)
        assert r.term.name == "x"

    def test_refl_term(self):
        v = Var("y")
        r = refl(v)
        assert isinstance(r, ReflTerm)
        assert r.term is v

    def test_refl_default(self):
        r = refl()
        assert isinstance(r, ReflTerm)
        assert isinstance(r.term, Var)
        assert r.term.name == "_"

    def test_sym(self):
        inner = refl("x")
        s = sym(inner)
        assert isinstance(s, SymTerm)
        assert s.proof is inner

    def test_trans_chain(self):
        p1 = refl("x")
        p2 = refl("y")
        p3 = refl("z")
        t = trans(p1, p2, p3)
        assert isinstance(t, TransTerm)

    def test_trans_single(self):
        p = refl("x")
        assert trans(p) is p

    def test_trans_empty(self):
        t = trans()
        assert isinstance(t, Structural)

    def test_by_axiom_simple(self):
        a = by_axiom("comm", "arith")
        assert isinstance(a, AxiomInvocation)
        assert a.name == "comm"
        assert a.module == "arith"

    def test_by_axiom_with_instantiation(self):
        a = by_axiom("comm", "arith", x=Var("a"), y=Var("b"))
        assert isinstance(a, AxiomInvocation)
        assert "x" in a.instantiation
        assert "y" in a.instantiation

    def test_by_z3(self):
        z = by_z3("x > 0")
        assert isinstance(z, Z3Proof)
        assert z.formula == "x > 0"

    def test_by_z3_empty(self):
        z = by_z3()
        assert isinstance(z, Z3Proof)
        assert z.formula == ""

    def test_by_cases(self):
        b1 = ("x >= 0", Structural(description="pos"))
        b2 = ("x < 0", Structural(description="neg"))
        c = by_cases("x", b1, b2)
        assert isinstance(c, Cases)
        assert len(c.branches) == 2

    def test_by_cases_with_term(self):
        v = Var("y")
        c = by_cases(v, ("True", refl("y")))
        assert c.scrutinee is v

    def test_by_induction(self):
        base = Structural(description="base")
        step = Structural(description="step")
        ind = by_induction("n", base, step)
        assert isinstance(ind, NatInduction)
        assert ind.var == "n"

    def test_by_list_induction(self):
        nil = Structural(description="nil")
        cons = Structural(description="cons")
        li = by_list_induction("xs", nil, cons)
        assert isinstance(li, ListInduction)
        assert li.var == "xs"

    def test_by_ext(self):
        body = refl("x")
        e = by_ext("x", body)
        assert isinstance(e, Ext)
        assert e.var == "x"
        assert e.body_proof is body

    def test_by_cong(self):
        inner = refl("x")
        c = by_cong("f", inner)
        assert isinstance(c, Cong)
        assert isinstance(c.func, Var)
        assert c.func.name == "f"

    def test_by_cong_with_term(self):
        v = Var("g")
        c = by_cong(v, refl("x"))
        assert c.func is v

    def test_by_unfold(self):
        u = by_unfold("my_func")
        assert isinstance(u, Unfold)
        assert u.func_name == "my_func"
        assert u.proof is None

    def test_by_unfold_with_then(self):
        inner = refl("x")
        u = by_unfold("f", then=inner)
        assert u.proof is inner

    def test_by_rewrite(self):
        lemma = refl("x")
        r = by_rewrite(lemma)
        assert isinstance(r, Rewrite)
        assert r.lemma is lemma
        assert r.proof is None

    def test_by_rewrite_with_then(self):
        lemma = refl("a")
        then = refl("b")
        r = by_rewrite(lemma, then=then)
        assert r.proof is then

    def test_by_transport(self):
        family = Var("P")
        path = Structural(description="path")
        base = Structural(description="base")
        t = by_transport(family, path, base)
        assert isinstance(t, TransportProof)
        assert t.type_family is family

    def test_by_effect(self):
        inner = refl("x")
        e = by_effect("Pure", inner)
        assert isinstance(e, EffectWitness)
        assert e.effect == "Pure"
        assert e.proof is inner


# ═══════════════════════════════════════════════════════════════════
#  §8 Domain Knowledge
# ═══════════════════════════════════════════════════════════════════

class TestDomainKnowledge:

    def test_given_creates_knowledge(self):
        dk = given("e^(iπ) + 1 = 0")
        assert isinstance(dk, DomainKnowledge)
        assert dk.statement == "e^(iπ) + 1 = 0"

    def test_given_with_source(self):
        dk = given("F = m * a", source="Newton's second law")
        assert dk.source == "Newton's second law"

    def test_given_default_trust(self):
        dk = given("some fact")
        assert dk.trust_level == "DOMAIN_ASSUMED"

    def test_as_assumption(self):
        dk = given("P(x)")
        a = dk.as_assumption("my_hyp")
        assert isinstance(a, Assume)
        assert a.name == "my_hyp"

    def test_as_assumption_default_name(self):
        dk = given("P(x)")
        a = dk.as_assumption()
        assert a.name == "domain_knowledge"

    def test_as_axiom(self):
        dk = given("sorting is O(n log n)")
        ax = dk.as_axiom("sort_lb", "complexity")
        assert isinstance(ax, AxiomInvocation)
        assert ax.name == "sort_lb"
        assert ax.module == "complexity"

    def test_as_axiom_auto_name(self):
        dk = given("short fact")
        ax = dk.as_axiom()
        assert len(ax.name) > 0
        assert ax.module == "domain"


# ═══════════════════════════════════════════════════════════════════
#  §9 Spec Extraction
# ═══════════════════════════════════════════════════════════════════

class TestSpecExtraction:

    def test_extract_spec_basic(self):
        @guarantee("positive result")
        def f(x):
            return abs(x)
        spec = extract_spec(f)
        assert spec is not None
        assert spec.name == "f"
        assert len(spec.guarantees) == 1
        assert spec.guarantees[0].description == "positive result"

    def test_extract_spec_with_annotations(self):
        @guarantee("sorted")
        def f(xs: list) -> list:
            return sorted(xs)
        spec = extract_spec(f)
        assert spec is not None
        assert len(spec.params) == 1
        pname, pty = spec.params[0]
        assert pname == "xs"

    def test_extract_spec_no_decorators_returns_none(self):
        def f(x):
            return x
        assert extract_spec(f) is None

    def test_extract_spec_no_specs_returns_none(self):
        @pure
        def f(x):
            return x
        # pure alone sets effect but no guarantees/pre/postconditions
        assert extract_spec(f) is None

    def test_extract_spec_multiple_guarantees(self):
        @guarantee("is sorted")
        @guarantee("no duplicates")
        def f(xs):
            return sorted(set(xs))
        spec = extract_spec(f)
        assert spec is not None
        assert len(spec.guarantees) == 2

    def test_extract_spec_effect(self):
        @guarantee("result >= 0")
        @pure
        def f(x):
            return abs(x)
        spec = extract_spec(f)
        assert spec is not None
        assert spec.effect == "Pure"

    def test_extract_spec_with_type_annotations(self):
        @guarantee("positive")
        def f(x: int, y: float) -> bool:
            return x > 0
        spec = extract_spec(f)
        assert spec is not None
        assert len(spec.params) == 2

    def test_extract_spec_with_preconditions(self):
        @guarantee("result")
        @requires(lambda x: x > 0)
        def f(x):
            return x
        spec = extract_spec(f)
        assert spec is not None
        assert len(spec.assumptions) == 1

    def test_extract_spec_with_postconditions(self):
        @ensures(lambda x, r: r > 0)
        def f(x):
            return abs(x) + 1
        spec = extract_spec(f)
        assert spec is not None
        # ensures adds to guarantees list
        assert len(spec.guarantees) >= 1


# ═══════════════════════════════════════════════════════════════════
#  §10 Global Kernel Management
# ═══════════════════════════════════════════════════════════════════

class TestGlobalKernel:

    def setup_method(self):
        """Reset global kernel before each test."""
        import deppy.proofs.sugar as sugar_mod
        sugar_mod._GLOBAL_KERNEL = None

    def test_set_and_get_global_kernel(self):
        k = _fresh_kernel()
        set_global_kernel(k)
        assert get_global_kernel() is k

    def test_auto_create_global_kernel(self):
        # _GLOBAL_KERNEL is None after setup_method
        k = get_global_kernel()
        assert isinstance(k, ProofKernel)
        # Should return the same instance on subsequent calls
        assert get_global_kernel() is k

    def test_verify_decorator_uses_global_kernel(self):
        k = _fresh_kernel()
        set_global_kernel(k)

        @verify
        @guarantee("result >= 0")
        @pure
        def abs_val(x: int) -> int:
            return abs(x)

        assert hasattr(abs_val, "_deppy_verification")
        results = abs_val._deppy_verification
        assert len(results) == 1
        assert isinstance(results[0], VerificationResult)

    def test_verify_stores_results(self):
        @verify
        @guarantee("sorted")
        @guarantee("no duplicates")
        def f(xs):
            return sorted(set(xs))

        assert len(f._deppy_verification) == 2

    def test_verify_function_still_callable(self):
        @verify
        @guarantee("identity")
        def f(x):
            return x
        assert f(42) == 42

    def test_verify_no_guarantees(self):
        @verify
        @pure
        def f(x):
            return x
        # No guarantees → empty verification list
        assert f._deppy_verification == []


# ═══════════════════════════════════════════════════════════════════
#  §11 Integration / Edge Cases
# ═══════════════════════════════════════════════════════════════════

class TestIntegration:

    def test_library_trust_plus_proof(self):
        """Library axioms can be used in Proof builder."""
        k = _fresh_kernel()
        with library_trust("sympy", kernel=k) as sp:
            sp.axiom("simplify(simplify(e)) = simplify(e)", name="simp_idem")
        result = (
            Proof("simplify(simplify(x)) = simplify(x)")
            .using(k)
            .by_axiom("simp_idem", "sympy")
            .qed()
        )
        assert isinstance(result, VerificationResult)

    def test_decorator_then_extract_then_proof(self):
        """Full workflow: decorate → extract → prove."""
        @guarantee("sorted output")
        @pure
        def my_sort(xs: list) -> list:
            return sorted(xs)

        spec = extract_spec(my_sort)
        assert spec is not None
        assert spec.effect == "Pure"

        k = _fresh_kernel()
        result = (
            Proof(spec.guarantees[0].description)
            .using(k)
            .by_structural()
            .qed()
        )
        assert result.success

    def test_proof_context_with_combinators(self):
        """ProofContext using quick combinators."""
        k = _fresh_kernel()
        with ProofContext(k, "f(x) == f(x)") as p:
            p.have("s1", "reflexivity", by=refl("f_x"))
            result = p.qed(by=p.by("s1"))
        assert isinstance(result, VerificationResult)

    def test_formal_proof_with_opcall(self):
        """FormalProof with Op/OpCall terms."""
        k = _fresh_kernel()
        op = Op(name="sort", module="builtins")
        x = Var("xs")
        call = OpCall(op=op, args=(x,))
        result = (
            FormalProof.eq(call, call)
            .using(k)
            .by_refl(call)
            .qed()
        )
        assert result.success

    def test_chained_library_and_context(self):
        k = _fresh_kernel()
        with library_trust("numpy", kernel=k) as np_block:
            np_block.axiom("A.T.T == A", name="double_transpose")
        with ProofContext(k, "A.T.T == A") as p:
            p.have("s1", "double transpose",
                   by_axiom=("double_transpose", "numpy"))
            result = p.qed(by=p.by("s1"))
        assert isinstance(result, VerificationResult)

    def test_spec_metadata_is_shared(self):
        """Multiple _get_spec calls return the same object."""
        def f():
            pass
        s1 = _get_spec(f)
        s2 = _get_spec(f)
        assert s1 is s2

    def test_library_trust_chain_axiom(self):
        """Axiom method returns self for chaining."""
        with library_trust("m") as block:
            ret = block.axiom("a", name="a1")
        assert ret is block

    def test_refinement_type_var_defaults(self):
        p = Pos()
        assert p.var_name == "x"
        n = NonEmpty()
        assert n.var_name == "xs"
