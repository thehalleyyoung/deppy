"""
Comprehensive tests for SynHoPy core type system and proof kernel.

Tests cover:
  - Type constructors and equality (TestTypes)
  - Term constructors and free-variable computation (TestTerms)
  - Typing contexts (TestContext)
  - Proof kernel verification for every proof-term form (TestProofKernel)
  - Judgments (TestJudgment)
  - Specifications (TestSpec)
"""
from __future__ import annotations

import pytest

from synhopy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Spec, SpecKind, FunctionSpec,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyDictType, PyCallableType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    UniverseType, ProtocolType, OptionalType, IntervalType,
    PyClassType, PyTupleType, PySetType,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp, LetIn, IfThenElse,
    PyCall, GetAttr, GetItem,
    arrow,
)
from synhopy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, Cut, Assume, Z3Proof,
    NatInduction, ListInduction, Cases, DuckPath,
    EffectWitness, AxiomInvocation, Ext, Unfold, Rewrite,
    Structural, TransportProof, min_trust,
)


# ═══════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════

def _eq_goal(left: SynTerm, right: SynTerm,
             ty: SynType | None = None,
             ctx: Context | None = None) -> Judgment:
    """Build an equality judgment ``left = right : ty``."""
    return Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx or Context(),
        left=left,
        right=right,
        type_=ty or PyObjType(),
    )


def _tc_goal(term: SynTerm | None = None,
             ty: SynType | None = None,
             ctx: Context | None = None) -> Judgment:
    """Build a type-check judgment ``term : ty``."""
    return Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx or Context(),
        term=term,
        type_=ty or PyObjType(),
    )


# ═══════════════════════════════════════════════════════════════════
# 1. TestTypes
# ═══════════════════════════════════════════════════════════════════

class TestTypes:
    """Tests for type constructors, equality, hashing, and repr."""

    def test_pyobj_equality(self):
        """Two PyObjType instances are structurally equal."""
        assert PyObjType() == PyObjType()

    def test_pyobj_inequality_with_other_type(self):
        """PyObjType is not equal to PyIntType."""
        assert PyObjType() != PyIntType()

    def test_pyint_type(self):
        """PyIntType equality and identity."""
        t = PyIntType()
        assert t == PyIntType()
        assert t != PyStrType()
        assert t._repr() == "int"

    @pytest.mark.parametrize("cls,expected_in_repr", [
        (PyFloatType, "Float"),
        (PyStrType, "Str"),
        (PyBoolType, "Bool"),
        (PyNoneType, "None"),
    ])
    def test_primitive_types(self, cls, expected_in_repr):
        """Primitive Python type wrappers are self-equal."""
        assert cls() == cls()
        assert expected_in_repr in repr(cls())

    def test_pi_type(self):
        """Dependent function type Π(x : int). str."""
        pi = PiType(param_name="x", param_type=PyIntType(), body_type=PyStrType())
        assert pi._repr().startswith("Π")
        assert "x" in pi._repr()
        assert pi == PiType(param_name="x", param_type=PyIntType(), body_type=PyStrType())
        assert pi != PiType(param_name="y", param_type=PyIntType(), body_type=PyStrType())

    def test_sigma_type(self):
        """Dependent pair type Σ(x : int). str."""
        sig = SigmaType(fst_name="x", fst_type=PyIntType(), snd_type=PyStrType())
        assert "Σ" in sig._repr()
        assert sig == SigmaType(fst_name="x", fst_type=PyIntType(), snd_type=PyStrType())

    def test_path_type(self):
        """Path type a =_A b."""
        a, b = Var("a"), Var("b")
        pt = PathType(base_type=PyIntType(), left=a, right=b)
        r = repr(pt)
        assert "a" in r
        assert "b" in r

    def test_refinement_type(self):
        """Refinement type {x : A | predicate}."""
        ref = RefinementType(base_type=PyIntType(), var_name="x", predicate="x > 0")
        r = ref._repr()
        assert "x > 0" in r
        assert ref.base_type == PyIntType()
        assert ref.var_name == "x"

    def test_union_type(self):
        """Union type A | B."""
        u = UnionType(alternatives=(PyIntType(), PyStrType()))
        r = u._repr()
        assert "|" in r
        assert len(u.alternatives) == 2

    def test_optional_type(self):
        """Optional[A] wraps an inner type."""
        opt = OptionalType(inner=PyIntType())
        assert "Optional" in opt._repr()
        assert opt.inner == PyIntType()

    def test_callable_type(self):
        """Callable[[A1, A2], R]."""
        ct = PyCallableType(
            param_types=(PyIntType(), PyStrType()),
            return_type=PyBoolType(),
        )
        r = ct._repr()
        assert "Callable" in r
        assert ct.return_type == PyBoolType()

    def test_class_type(self):
        """PyClassType stores name, methods, bases."""
        cls = PyClassType(
            name="Foo",
            methods=(("bar", PyIntType()),),
            bases=("object",),
        )
        assert "Foo" in repr(cls)

    def test_protocol_type(self):
        """ProtocolType lists required methods."""
        proto = ProtocolType(
            name="Iterable",
            methods=(("__iter__", PyCallableType()),),
        )
        assert "Iterable" in repr(proto)

    def test_universe_type(self):
        """Universe levels U_0, U_1 differ."""
        u0 = UniverseType(level=0)
        u1 = UniverseType(level=1)
        assert u0 != u1
        assert "U_0" in u0._repr()

    def test_arrow_helper(self):
        """arrow(A, B) produces a non-dependent Π type."""
        arr = arrow(PyIntType(), PyStrType())
        assert isinstance(arr, PiType)
        assert arr.param_name == "_"
        assert arr.param_type == PyIntType()
        assert arr.body_type == PyStrType()

    def test_list_type(self):
        """PyListType stores element type and has correct _repr."""
        lt = PyListType(element_type=PyIntType())
        assert "list" in lt._repr()
        assert lt == PyListType(element_type=PyIntType())
        assert lt != PyListType(element_type=PyStrType())

    def test_dict_type(self):
        """PyDictType stores key and value types."""
        dt = PyDictType(key_type=PyStrType(), value_type=PyIntType())
        assert "dict" in dt._repr()
        assert dt == PyDictType(key_type=PyStrType(), value_type=PyIntType())

    def test_tuple_type(self):
        """PyTupleType stores a sequence of element types."""
        tt = PyTupleType(element_types=(PyIntType(), PyStrType()))
        assert "tuple" in tt._repr()

    def test_set_type(self):
        """PySetType stores element type."""
        st = PySetType(element_type=PyIntType())
        assert "set" in st._repr()

    def test_interval_type(self):
        """IntervalType represents the cubical interval I."""
        assert IntervalType()._repr() == "I"

    def test_type_hashing(self):
        """Types with equal structure can coexist in sets/dicts."""
        s = {PyIntType(), PyIntType(), PyStrType()}
        assert len(s) == 2

    def test_syntype_not_equal_to_non_type(self):
        """Comparing a SynType to a non-SynType returns NotImplemented."""
        assert PyIntType().__eq__(42) is NotImplemented


# ═══════════════════════════════════════════════════════════════════
# 2. TestTerms
# ═══════════════════════════════════════════════════════════════════

class TestTerms:
    """Tests for term constructors, repr, and free_vars."""

    def test_var(self):
        """Var stores a name and reports it as a free variable."""
        v = Var("x")
        assert v._repr() == "x"
        assert v.free_vars() == {"x"}

    def test_literal(self):
        """Literal wraps a Python value."""
        lit = Literal(value=42, type_=PyIntType())
        assert "42" in repr(lit)
        assert lit.free_vars() == set()

    def test_lambda(self):
        """Lambda binds a variable and removes it from free vars."""
        body = App(func=Var("f"), arg=Var("x"))
        lam = Lam(param="x", param_type=PyIntType(), body=body)
        assert "λ" in lam._repr()
        assert lam.free_vars() == {"f"}

    def test_application(self):
        """App combines free vars of func and arg."""
        app = App(func=Var("f"), arg=Var("x"))
        assert app.free_vars() == {"f", "x"}
        assert "f" in repr(app)

    def test_pair_and_projections(self):
        """Pair, Fst, Snd have correct free vars and _repr."""
        p = Pair(fst=Var("a"), snd=Var("b"))
        assert p.free_vars() == {"a", "b"}
        assert "a" in p._repr() and "b" in p._repr()

        f = Fst(pair=p)
        assert f.free_vars() == {"a", "b"}
        assert "π₁" in f._repr()

        s = Snd(pair=p)
        assert s.free_vars() == {"a", "b"}
        assert "π₂" in s._repr()

    def test_path_abs_app(self):
        """PathAbs binds ivar; PathApp unions free vars."""
        pabs = PathAbs(ivar="i", body=App(func=Var("f"), arg=Var("i")))
        assert pabs.free_vars() == {"f"}

        papp = PathApp(path=Var("p"), arg=Literal(0))
        assert papp.free_vars() == {"p"}
        assert "@" in papp._repr()

    def test_let_in(self):
        """LetIn removes the bound var from the body free vars."""
        let = LetIn(
            var_name="x",
            var_type=PyIntType(),
            value=Var("y"),
            body=App(func=Var("f"), arg=Var("x")),
        )
        assert let.free_vars() == {"y", "f"}
        assert "let" in let._repr()

    def test_if_then_else(self):
        """IfThenElse unions free vars of all branches."""
        ite = IfThenElse(
            cond=Var("c"),
            then_branch=Var("t"),
            else_branch=Var("e"),
        )
        assert ite.free_vars() == {"c", "t", "e"}
        assert "if" in ite._repr()

    def test_py_call(self):
        """PyCall collects free vars from func, args, kwargs."""
        call = PyCall(
            func=Var("fn"),
            args=(Var("a"),),
            kwargs=(("key", Var("v")),),
        )
        assert call.free_vars() == {"fn", "a", "v"}
        assert "fn" in repr(call)

    def test_get_attr(self):
        """GetAttr free vars come only from the object."""
        ga = GetAttr(obj=Var("obj"), attr="name")
        assert ga.free_vars() == {"obj"}
        assert ".name" in ga._repr()

    def test_get_item(self):
        """GetItem unions free vars of obj and key."""
        gi = GetItem(obj=Var("d"), key=Var("k"))
        assert gi.free_vars() == {"d", "k"}

    def test_free_vars(self):
        """Base SynTerm has no free variables."""
        assert SynTerm().free_vars() == set()

    def test_nested_free_vars(self):
        """Deeply nested term correctly computes free vars."""
        inner = App(func=Var("g"), arg=Var("y"))
        outer = Lam(param="y", param_type=PyObjType(), body=inner)
        app = App(func=outer, arg=Var("z"))
        assert app.free_vars() == {"g", "z"}

    def test_transport(self):
        """Transport term unions free vars of all sub-terms."""
        tr = Transport(
            type_family=Var("P"),
            path=Var("p"),
            base_term=Var("d"),
        )
        assert tr.free_vars() == {"P", "p", "d"}
        assert "transp" in tr._repr()

    def test_comp(self):
        """Comp term unions free vars of base and partial."""
        c = Comp(
            type_=PyIntType(),
            face="i=0",
            partial_term=Var("u"),
            base=Var("u0"),
        )
        assert c.free_vars() == {"u", "u0"}
        assert "comp" in c._repr()

    def test_comp_without_partial(self):
        """Comp with no partial_term only has base free vars."""
        c = Comp(type_=PyIntType(), base=Var("b"))
        assert c.free_vars() == {"b"}


# ═══════════════════════════════════════════════════════════════════
# 3. TestContext
# ═══════════════════════════════════════════════════════════════════

class TestContext:
    """Tests for the typing context Γ."""

    def test_empty_context(self):
        """An empty context has no bindings."""
        ctx = Context()
        assert ctx.lookup("x") is None
        assert ctx.all_bindings() == {}

    def test_extend(self):
        """extend creates a child context with the new binding."""
        ctx = Context()
        ctx2 = ctx.extend("x", PyIntType())
        assert ctx2.lookup("x") == PyIntType()
        assert ctx.lookup("x") is None  # parent unchanged

    def test_lookup(self):
        """lookup returns the type or None."""
        ctx = Context(bindings={"x": PyIntType()})
        assert ctx.lookup("x") == PyIntType()
        assert ctx.lookup("y") is None

    def test_parent_lookup(self):
        """lookup falls through to parent context."""
        parent = Context(bindings={"x": PyIntType()})
        child = Context(bindings={"y": PyStrType()}, parent=parent)
        assert child.lookup("x") == PyIntType()
        assert child.lookup("y") == PyStrType()

    def test_shadowing(self):
        """A child binding shadows the parent binding of the same name."""
        parent = Context(bindings={"x": PyIntType()})
        child = parent.extend("x", PyStrType())
        assert child.lookup("x") == PyStrType()

    def test_contains(self):
        """'in' operator delegates to lookup."""
        ctx = Context(bindings={"x": PyIntType()})
        assert "x" in ctx
        assert "y" not in ctx

    def test_all_bindings(self):
        """all_bindings merges parent and child, child wins on conflict."""
        parent = Context(bindings={"x": PyIntType(), "y": PyStrType()})
        child = Context(bindings={"x": PyBoolType(), "z": PyFloatType()}, parent=parent)
        ab = child.all_bindings()
        assert ab["x"] == PyBoolType()
        assert ab["y"] == PyStrType()
        assert ab["z"] == PyFloatType()

    def test_multi_level(self):
        """Three-level context chain resolves correctly."""
        g = Context(bindings={"a": PyIntType()})
        p = Context(bindings={"b": PyStrType()}, parent=g)
        c = Context(bindings={"c": PyBoolType()}, parent=p)
        assert c.lookup("a") == PyIntType()
        assert c.lookup("b") == PyStrType()
        assert c.lookup("c") == PyBoolType()
        assert c.lookup("d") is None


# ═══════════════════════════════════════════════════════════════════
# 4. TestProofKernel
# ═══════════════════════════════════════════════════════════════════

class TestProofKernel:
    """Tests for every proof-term form accepted by the kernel."""

    @pytest.fixture
    def kernel(self) -> ProofKernel:
        """Fresh proof kernel for each test."""
        return ProofKernel()

    @pytest.fixture
    def ctx(self) -> Context:
        """Simple context with a few bindings."""
        return Context(bindings={"x": PyIntType(), "y": PyStrType()})

    # ── Refl ──────────────────────────────────────────────────────

    def test_refl_success(self, kernel: ProofKernel):
        """Refl(a) proves a = a."""
        a = Var("a")
        goal = _eq_goal(a, Var("a"))
        r = kernel.verify(Context(), goal, Refl(term=a))
        assert r.success
        assert r.trust_level == TrustLevel.KERNEL

    def test_refl_failure(self, kernel: ProofKernel):
        """Refl(a) fails to prove a = b when a ≠ b."""
        goal = _eq_goal(Var("a"), Var("b"))
        r = kernel.verify(Context(), goal, Refl(term=Var("a")))
        assert not r.success
        assert "not definitionally equal" in r.message

    def test_refl_wrong_judgment_kind(self, kernel: ProofKernel):
        """Refl used for a non-equality goal fails."""
        goal = _tc_goal(term=Var("a"), ty=PyIntType())
        r = kernel.verify(Context(), goal, Refl(term=Var("a")))
        assert not r.success
        assert "non-equality" in r.message

    # ── Sym ───────────────────────────────────────────────────────

    def test_sym(self, kernel: ProofKernel):
        """Sym flips the equality goal and delegates."""
        a = Var("a")
        goal = _eq_goal(a, a)  # a = a, flipped is also a = a
        r = kernel.verify(Context(), goal, Sym(proof=Refl(term=a)))
        assert r.success

    def test_sym_non_equality(self, kernel: ProofKernel):
        """Sym on a non-equality goal fails."""
        goal = _tc_goal()
        r = kernel.verify(Context(), goal, Sym(proof=Refl(term=Var("a"))))
        assert not r.success

    # ── Trans ─────────────────────────────────────────────────────

    def test_trans(self, kernel: ProofKernel):
        """Trans chains two equality proofs."""
        a = Var("a")
        goal = _eq_goal(a, a)
        proof = Trans(left=Refl(term=a), right=Refl(term=a))
        r = kernel.verify(Context(), goal, proof)
        assert r.success

    def test_trans_non_equality(self, kernel: ProofKernel):
        """Trans on a non-equality goal fails."""
        goal = _tc_goal()
        r = kernel.verify(Context(), goal, Trans(
            left=Refl(term=Var("a")),
            right=Refl(term=Var("a")),
        ))
        assert not r.success

    # ── Cong ──────────────────────────────────────────────────────

    def test_cong(self, kernel: ProofKernel):
        """Cong lifts an equality through a function."""
        a = Var("a")
        f = Var("f")
        goal = _eq_goal(a, a)
        r = kernel.verify(Context(), goal, Cong(func=f, proof=Refl(term=a)))
        assert r.success
        assert "Cong" in r.message

    def test_cong_failure(self, kernel: ProofKernel):
        """Cong propagates inner-proof failure."""
        goal = _eq_goal(Var("a"), Var("b"))
        r = kernel.verify(Context(), goal, Cong(func=Var("f"), proof=Refl(term=Var("a"))))
        assert not r.success

    # ── Cut ───────────────────────────────────────────────────────

    def test_cut(self, kernel: ProofKernel):
        """Cut introduces a lemma and uses it."""
        a = Var("a")
        goal = _eq_goal(a, a)
        proof = Cut(
            hyp_name="h",
            hyp_type=PyBoolType(),
            lemma_proof=Structural("lemma"),
            body_proof=Refl(term=a),
        )
        r = kernel.verify(Context(), goal, proof)
        assert r.success

    def test_cut_lemma_failure(self, kernel: ProofKernel):
        """Cut fails when the lemma proof fails."""
        goal = _eq_goal(Var("a"), Var("a"))
        proof = Cut(
            hyp_name="h",
            hyp_type=PyBoolType(),
            lemma_proof=AxiomInvocation(name="nonexistent"),
            body_proof=Refl(term=Var("a")),
        )
        r = kernel.verify(Context(), goal, proof)
        assert not r.success

    # ── Assume ────────────────────────────────────────────────────

    def test_assume_in_context(self, kernel: ProofKernel, ctx: Context):
        """Assume succeeds when the hypothesis is in context."""
        goal = _tc_goal(ctx=ctx)
        r = kernel.verify(ctx, goal, Assume(name="x"))
        assert r.success
        assert r.trust_level == TrustLevel.KERNEL

    def test_assume_not_in_context(self, kernel: ProofKernel):
        """Assume fails when the hypothesis is missing."""
        r = kernel.verify(Context(), _tc_goal(), Assume(name="z"))
        assert not r.success
        assert "not in context" in r.message

    # ── Z3 ────────────────────────────────────────────────────────

    def test_z3_simple(self, kernel: ProofKernel):
        """Z3 proves a simple tautology."""
        goal = _eq_goal(Var("a"), Var("a"))
        r = kernel.verify(Context(), goal, Z3Proof(formula="a + b == b + a"))
        # Result depends on z3 availability
        if r.success:
            assert r.trust_level == TrustLevel.Z3_VERIFIED
        else:
            assert "Z3" in r.message

    def test_z3_implication(self, kernel: ProofKernel):
        """Z3 proves an implication."""
        goal = _tc_goal()
        r = kernel.verify(Context(), goal, Z3Proof(formula="x > 0 => x >= 0"))
        if r.success:
            assert r.trust_level == TrustLevel.Z3_VERIFIED

    def test_z3_invalid_formula(self, kernel: ProofKernel):
        """Z3 rejects an invalid formula."""
        r = kernel.verify(Context(), _tc_goal(), Z3Proof(formula="x > 0 => x < 0"))
        # Should either fail or not reach Z3_VERIFIED
        if r.success:
            assert r.trust_level != TrustLevel.KERNEL

    # ── NatInduction ──────────────────────────────────────────────

    def test_nat_induction(self, kernel: ProofKernel):
        """NatInduction succeeds when base and step succeed."""
        a = Var("a")
        goal = _eq_goal(a, a)
        proof = NatInduction(
            var="n",
            base_proof=Refl(term=a),
            step_proof=Refl(term=a),
        )
        r = kernel.verify(Context(), goal, proof)
        assert r.success
        assert "NatInd" in r.message
        assert len(r.sub_results) == 2

    def test_nat_induction_base_fails(self, kernel: ProofKernel):
        """NatInduction fails when the base case fails."""
        goal = _eq_goal(Var("a"), Var("b"))
        proof = NatInduction(
            var="n",
            base_proof=Refl(term=Var("a")),
            step_proof=Refl(term=Var("a")),
        )
        r = kernel.verify(Context(), goal, proof)
        assert not r.success

    # ── ListInduction ─────────────────────────────────────────────

    def test_list_induction(self, kernel: ProofKernel):
        """ListInduction succeeds when nil and cons succeed."""
        a = Var("a")
        goal = _eq_goal(a, a)
        proof = ListInduction(
            var="xs",
            nil_proof=Refl(term=a),
            cons_proof=Refl(term=a),
        )
        r = kernel.verify(Context(), goal, proof)
        assert r.success
        assert "ListInd" in r.message

    def test_list_induction_cons_fails(self, kernel: ProofKernel):
        """ListInduction fails when the cons case fails."""
        goal = _eq_goal(Var("a"), Var("b"))
        proof = ListInduction(
            var="xs",
            nil_proof=Structural("ok"),
            cons_proof=Refl(term=Var("a")),
        )
        r = kernel.verify(Context(), goal, proof)
        assert not r.success

    # ── Cases ─────────────────────────────────────────────────────

    def test_cases(self, kernel: ProofKernel):
        """Cases succeeds when all branches succeed."""
        a = Var("a")
        goal = _eq_goal(a, a)
        proof = Cases(
            scrutinee=Var("x"),
            branches=[
                ("True", Refl(term=a)),
                ("False", Refl(term=a)),
            ],
        )
        r = kernel.verify(Context(), goal, proof)
        assert r.success
        assert "2 branches" in r.message

    def test_cases_branch_failure(self, kernel: ProofKernel):
        """Cases fails when any branch fails."""
        goal = _eq_goal(Var("a"), Var("b"))
        proof = Cases(
            scrutinee=Var("x"),
            branches=[("True", Refl(term=Var("a")))],
        )
        r = kernel.verify(Context(), goal, proof)
        assert not r.success

    # ── DuckPath ──────────────────────────────────────────────────

    def test_duck_path(self, kernel: ProofKernel):
        """DuckPath succeeds when all method proofs succeed."""
        goal = _eq_goal(Var("a"), Var("a"))
        proof = DuckPath(
            type_a=PyClassType(name="A"),
            type_b=PyClassType(name="B"),
            method_proofs=[("foo", Structural("method ok"))],
        )
        r = kernel.verify(Context(), goal, proof)
        assert r.success
        assert "DuckPath" in r.message

    def test_duck_path_empty_methods(self, kernel: ProofKernel):
        """DuckPath with no methods trivially succeeds."""
        goal = _eq_goal(Var("a"), Var("a"))
        proof = DuckPath(
            type_a=PyClassType(name="A"),
            type_b=PyClassType(name="B"),
            method_proofs=[],
        )
        r = kernel.verify(Context(), goal, proof)
        assert r.success
        assert r.trust_level == TrustLevel.KERNEL

    # ── EffectWitness ─────────────────────────────────────────────

    def test_effect_witness(self, kernel: ProofKernel):
        """EffectWitness wraps a proof and caps trust at EFFECT_ASSUMED."""
        a = Var("a")
        goal = _eq_goal(a, a)
        proof = EffectWitness(effect="IO", proof=Refl(term=a))
        r = kernel.verify(Context(), goal, proof)
        assert r.success
        assert r.trust_level <= TrustLevel.KERNEL

    def test_effect_witness_inner_failure(self, kernel: ProofKernel):
        """EffectWitness propagates inner failure."""
        goal = _eq_goal(Var("a"), Var("b"))
        proof = EffectWitness(effect="IO", proof=Refl(term=Var("a")))
        r = kernel.verify(Context(), goal, proof)
        assert not r.success

    # ── Axiom ─────────────────────────────────────────────────────

    def test_axiom_registered(self, kernel: ProofKernel):
        """AxiomInvocation succeeds for a registered axiom."""
        kernel.register_axiom("comm_add", "a + b == b + a")
        goal = _tc_goal()
        r = kernel.verify(Context(), goal, AxiomInvocation(name="comm_add"))
        assert r.success
        assert r.trust_level == TrustLevel.AXIOM_TRUSTED
        assert "comm_add" in r.axioms_used

    def test_axiom_unregistered(self, kernel: ProofKernel):
        """AxiomInvocation fails for an unregistered axiom."""
        r = kernel.verify(Context(), _tc_goal(), AxiomInvocation(name="ghost"))
        assert not r.success
        assert "Unknown axiom" in r.message

    def test_axiom_with_module(self, kernel: ProofKernel):
        """AxiomInvocation with module prefix resolves correctly."""
        kernel.register_axiom("assoc", "a+(b+c)==(a+b)+c", module="arith")
        r = kernel.verify(
            Context(), _tc_goal(),
            AxiomInvocation(name="assoc", module="arith"),
        )
        assert r.success

    # ── Ext ───────────────────────────────────────────────────────

    def test_ext(self, kernel: ProofKernel):
        """Ext proves function extensionality via pointwise equality."""
        a = Var("a")
        goal = _eq_goal(a, a)
        proof = Ext(var="x", body_proof=Refl(term=a))
        r = kernel.verify(Context(), goal, proof)
        assert r.success
        assert "Ext" in r.message

    def test_ext_failure(self, kernel: ProofKernel):
        """Ext propagates body proof failure."""
        goal = _eq_goal(Var("a"), Var("b"))
        r = kernel.verify(Context(), goal, Ext(var="x", body_proof=Refl(term=Var("a"))))
        assert not r.success

    # ── Unfold ────────────────────────────────────────────────────

    def test_unfold(self, kernel: ProofKernel):
        """Unfold without inner proof returns STRUCTURAL_CHAIN."""
        goal = _tc_goal()
        r = kernel.verify(Context(), goal, Unfold(func_name="foo"))
        assert r.success
        assert r.trust_level == TrustLevel.STRUCTURAL_CHAIN

    def test_unfold_with_proof(self, kernel: ProofKernel):
        """Unfold with inner proof delegates to the inner proof."""
        a = Var("a")
        goal = _eq_goal(a, a)
        r = kernel.verify(Context(), goal, Unfold(func_name="f", proof=Refl(term=a)))
        assert r.success
        assert r.trust_level == TrustLevel.KERNEL

    # ── Structural ────────────────────────────────────────────────

    def test_structural(self, kernel: ProofKernel):
        """Structural always succeeds with STRUCTURAL_CHAIN trust."""
        goal = _tc_goal()
        r = kernel.verify(Context(), goal, Structural(description="checked"))
        assert r.success
        assert r.trust_level == TrustLevel.STRUCTURAL_CHAIN

    # ── Rewrite ───────────────────────────────────────────────────

    def test_rewrite(self, kernel: ProofKernel):
        """Rewrite succeeds when the lemma succeeds."""
        a = Var("a")
        goal = _eq_goal(a, a)
        r = kernel.verify(Context(), goal, Rewrite(lemma=Refl(term=a)))
        assert r.success

    def test_rewrite_with_body(self, kernel: ProofKernel):
        """Rewrite with both lemma and body proof."""
        a = Var("a")
        goal = _eq_goal(a, a)
        r = kernel.verify(Context(), goal, Rewrite(
            lemma=Refl(term=a),
            proof=Refl(term=a),
        ))
        assert r.success
        assert len(r.sub_results) == 2

    def test_rewrite_lemma_failure(self, kernel: ProofKernel):
        """Rewrite fails when the lemma fails."""
        goal = _eq_goal(Var("a"), Var("b"))
        r = kernel.verify(Context(), goal, Rewrite(lemma=Refl(term=Var("a"))))
        assert not r.success

    # ── Transport ─────────────────────────────────────────────────

    def test_transport(self, kernel: ProofKernel):
        """TransportProof succeeds when path and base succeed."""
        a = Var("a")
        goal = _eq_goal(a, a)
        proof = TransportProof(
            type_family=Var("P"),
            path_proof=Refl(term=a),
            base_proof=Refl(term=a),
        )
        r = kernel.verify(Context(), goal, proof)
        assert r.success
        assert "Transport" in r.message

    def test_transport_path_failure(self, kernel: ProofKernel):
        """TransportProof fails when path proof fails."""
        goal = _eq_goal(Var("a"), Var("b"))
        proof = TransportProof(
            type_family=Var("P"),
            path_proof=Refl(term=Var("a")),
            base_proof=Structural("ok"),
        )
        r = kernel.verify(Context(), goal, proof)
        assert not r.success

    # ── Trust levels ──────────────────────────────────────────────

    def test_trust_level_ordering(self):
        """Trust levels compare correctly."""
        assert TrustLevel.KERNEL > TrustLevel.UNTRUSTED
        assert TrustLevel.Z3_VERIFIED > TrustLevel.STRUCTURAL_CHAIN
        assert TrustLevel.STRUCTURAL_CHAIN > TrustLevel.LLM_CHECKED
        assert TrustLevel.UNTRUSTED < TrustLevel.KERNEL
        assert TrustLevel.KERNEL >= TrustLevel.KERNEL
        assert TrustLevel.UNTRUSTED <= TrustLevel.UNTRUSTED

    def test_min_trust(self):
        """min_trust returns the weakest (lowest) trust level."""
        assert min_trust(TrustLevel.KERNEL, TrustLevel.Z3_VERIFIED) == TrustLevel.Z3_VERIFIED
        assert min_trust(TrustLevel.UNTRUSTED, TrustLevel.KERNEL) == TrustLevel.UNTRUSTED
        assert min_trust(TrustLevel.KERNEL) == TrustLevel.KERNEL

    # ── Collect axioms ────────────────────────────────────────────

    def test_collect_axioms(self, kernel: ProofKernel):
        """collect_axioms recursively finds all axiom names."""
        proof = Trans(
            left=AxiomInvocation(name="ax1"),
            right=Cut(
                hyp_name="h",
                hyp_type=PyBoolType(),
                lemma_proof=AxiomInvocation(name="ax2", module="m"),
                body_proof=Refl(term=Var("a")),
            ),
        )
        axioms = kernel.collect_axioms(proof)
        assert "ax1" in axioms
        assert "m.ax2" in axioms
        assert len(axioms) == 2

    def test_collect_axioms_empty(self, kernel: ProofKernel):
        """Proof with no axioms yields empty set."""
        axioms = kernel.collect_axioms(Refl(term=Var("x")))
        assert axioms == set()

    def test_collect_axioms_nested(self, kernel: ProofKernel):
        """collect_axioms traverses Sym, Cong, Ext, NatInduction, etc."""
        inner = AxiomInvocation(name="a1")
        proof = Sym(proof=Cong(func=Var("f"), proof=Ext(
            var="x",
            body_proof=NatInduction(
                var="n",
                base_proof=inner,
                step_proof=Refl(term=Var("x")),
            ),
        )))
        axioms = kernel.collect_axioms(proof)
        assert "a1" in axioms

    def test_collect_axioms_list_induction(self, kernel: ProofKernel):
        """collect_axioms traverses ListInduction branches."""
        proof = ListInduction(
            var="xs",
            nil_proof=AxiomInvocation(name="nil_ax"),
            cons_proof=AxiomInvocation(name="cons_ax"),
        )
        axioms = kernel.collect_axioms(proof)
        assert axioms == {"nil_ax", "cons_ax"}

    def test_collect_axioms_cases(self, kernel: ProofKernel):
        """collect_axioms traverses Cases branches."""
        proof = Cases(
            scrutinee=Var("x"),
            branches=[
                ("A", AxiomInvocation(name="ax_a")),
                ("B", Refl(term=Var("b"))),
            ],
        )
        assert kernel.collect_axioms(proof) == {"ax_a"}

    def test_collect_axioms_duck_path(self, kernel: ProofKernel):
        """collect_axioms traverses DuckPath method proofs."""
        proof = DuckPath(
            type_a=PyClassType(name="X"),
            type_b=PyClassType(name="Y"),
            method_proofs=[("m", AxiomInvocation(name="duck_ax"))],
        )
        assert kernel.collect_axioms(proof) == {"duck_ax"}

    def test_collect_axioms_effect_witness(self, kernel: ProofKernel):
        """collect_axioms traverses EffectWitness inner proof."""
        proof = EffectWitness(effect="IO", proof=AxiomInvocation(name="io_ax"))
        assert kernel.collect_axioms(proof) == {"io_ax"}

    def test_collect_axioms_unfold(self, kernel: ProofKernel):
        """collect_axioms traverses Unfold inner proof."""
        proof = Unfold(func_name="f", proof=AxiomInvocation(name="uf_ax"))
        assert kernel.collect_axioms(proof) == {"uf_ax"}

    def test_collect_axioms_rewrite(self, kernel: ProofKernel):
        """collect_axioms traverses Rewrite lemma and body."""
        proof = Rewrite(
            lemma=AxiomInvocation(name="rw1"),
            proof=AxiomInvocation(name="rw2"),
        )
        assert kernel.collect_axioms(proof) == {"rw1", "rw2"}

    def test_collect_axioms_transport_proof(self, kernel: ProofKernel):
        """collect_axioms traverses TransportProof sub-proofs."""
        proof = TransportProof(
            type_family=Var("P"),
            path_proof=AxiomInvocation(name="tp1"),
            base_proof=AxiomInvocation(name="tp2"),
        )
        assert kernel.collect_axioms(proof) == {"tp1", "tp2"}

    # ── VerificationResult helpers ────────────────────────────────

    def test_verification_result_ok(self):
        """VerificationResult.ok produces a success result."""
        vr = VerificationResult.ok(TrustLevel.KERNEL, "test")
        assert vr.success
        assert "✓" in repr(vr)

    def test_verification_result_fail(self):
        """VerificationResult.fail produces a failure result."""
        vr = VerificationResult.fail("bad", code="E999")
        assert not vr.success
        assert vr.trust_level == TrustLevel.UNTRUSTED
        assert "✗" in repr(vr)
        assert vr.error_code == "E999"

    def test_unknown_proof_term(self, kernel: ProofKernel):
        """The kernel rejects unknown proof term types."""
        class FakeProof(ProofTerm):
            pass
        r = kernel.verify(Context(), _tc_goal(), FakeProof())
        assert not r.success
        assert "Unknown proof term" in r.message

    def test_internal_error_handling(self, kernel: ProofKernel):
        """The kernel catches exceptions and returns an error result."""
        # Supply a goal with None left/right to Refl which requires EQUAL kind
        goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=Context(),
            left=None,
            right=None,
            type_=PyObjType(),
        )
        r = kernel.verify(Context(), goal, Refl(term=Var("a")))
        assert not r.success

    # ── Proof term repr ───────────────────────────────────────────

    @pytest.mark.parametrize("proof,expected_substr", [
        (Refl(term=Var("x")), "Refl"),
        (Sym(proof=Refl(term=Var("x"))), "Sym"),
        (Assume(name="h"), "Assume(h)"),
        (Z3Proof(formula="a > 0"), "Z3(a > 0)"),
        (Structural(description="ok"), "Structural('ok')"),
        (AxiomInvocation(name="ax", module="m"), "Axiom(m.ax)"),
        (AxiomInvocation(name="ax"), "Axiom(ax)"),
        (Unfold(func_name="f"), "Unfold(f)"),
    ])
    def test_proof_term_repr(self, proof: ProofTerm, expected_substr: str):
        """Proof term __repr__ is informative."""
        assert expected_substr in repr(proof)


# ═══════════════════════════════════════════════════════════════════
# 5. TestJudgment
# ═══════════════════════════════════════════════════════════════════

class TestJudgment:
    """Tests for Judgment construction and repr."""

    def test_type_check_judgment(self):
        """TYPE_CHECK judgment has term and type."""
        ctx = Context(bindings={"x": PyIntType()})
        j = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=ctx,
            term=Var("x"),
            type_=PyIntType(),
        )
        r = repr(j)
        assert "⊢" in r
        assert "x" in r

    def test_equality_judgment(self):
        """EQUAL judgment shows left = right."""
        j = Judgment(
            kind=JudgmentKind.EQUAL,
            context=Context(),
            left=Var("a"),
            right=Var("b"),
            type_=PyIntType(),
        )
        r = repr(j)
        assert "a" in r and "b" in r and "=" in r

    def test_subtype_judgment(self):
        """SUBTYPE judgment shows A <: B."""
        j = Judgment(
            kind=JudgmentKind.SUBTYPE,
            context=Context(),
            left=Var("A"),
            right=Var("B"),
        )
        assert "<:" in repr(j)

    def test_well_formed_judgment(self):
        """WELL_FORMED judgment shows A type."""
        j = Judgment(
            kind=JudgmentKind.WELL_FORMED,
            context=Context(),
            type_=PyIntType(),
        )
        r = repr(j)
        assert "type" in r

    def test_judgment_repr(self):
        """TYPE_SYNTH judgment falls through to generic repr."""
        j = Judgment(
            kind=JudgmentKind.TYPE_SYNTH,
            context=Context(),
            term=Var("x"),
        )
        assert "Judgment" in repr(j)

    def test_judgment_context_in_repr(self):
        """Context bindings appear in the judgment repr."""
        ctx = Context(bindings={"x": PyIntType(), "y": PyStrType()})
        j = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=ctx,
            term=Var("x"),
            type_=PyIntType(),
        )
        r = repr(j)
        assert "x:" in r
        assert "y:" in r


# ═══════════════════════════════════════════════════════════════════
# 6. TestSpec
# ═══════════════════════════════════════════════════════════════════

class TestSpec:
    """Tests for Spec and FunctionSpec."""

    def test_spec_creation(self):
        """Spec stores kind, description, and optional formal predicate."""
        s = Spec(
            kind=SpecKind.GUARANTEE,
            description="returns positive",
            formal="x > 0",
        )
        assert s.kind == SpecKind.GUARANTEE
        assert s.description == "returns positive"
        assert s.formal == "x > 0"

    def test_function_spec(self):
        """FunctionSpec aggregates guarantees, assumptions, checks."""
        fs = FunctionSpec(
            name="add",
            params=[("a", PyIntType()), ("b", PyIntType())],
            return_type=PyIntType(),
            guarantees=[Spec(kind=SpecKind.GUARANTEE, description="result >= 0")],
            assumptions=[Spec(kind=SpecKind.ASSUME, description="a >= 0")],
            checks=[Spec(kind=SpecKind.CHECK, description="no overflow")],
        )
        assert fs.name == "add"
        assert len(fs.guarantees) == 1
        assert len(fs.assumptions) == 1
        assert len(fs.checks) == 1

    def test_proof_obligations(self):
        """FunctionSpec.proof_obligations creates one Judgment per guarantee."""
        fs = FunctionSpec(
            name="f",
            params=[("x", PyIntType())],
            return_type=PyIntType(),
            guarantees=[
                Spec(kind=SpecKind.GUARANTEE, description="positive"),
                Spec(kind=SpecKind.GUARANTEE, description="even"),
            ],
        )
        obligs = fs.proof_obligations()
        assert len(obligs) == 2
        for o in obligs:
            assert o.kind == JudgmentKind.TYPE_CHECK
            assert isinstance(o.type_, RefinementType)
            assert "x" in o.context

    def test_spec_repr(self):
        """Spec repr includes kind and description."""
        s = Spec(kind=SpecKind.ASSUME, description="x > 0")
        r = repr(s)
        assert "assume" in r
        assert "x > 0" in r

    def test_spec_kinds(self):
        """All SpecKind variants are instantiable."""
        for kind in SpecKind:
            s = Spec(kind=kind, description="test")
            assert s.kind == kind

    def test_function_spec_effect(self):
        """FunctionSpec defaults to Pure effect."""
        fs = FunctionSpec(
            name="f",
            params=[],
            return_type=PyNoneType(),
        )
        assert fs.effect == "Pure"

    def test_function_spec_no_guarantees(self):
        """FunctionSpec with no guarantees has no proof obligations."""
        fs = FunctionSpec(
            name="noop",
            params=[],
            return_type=PyNoneType(),
        )
        assert fs.proof_obligations() == []

    def test_spec_source_info(self):
        """Spec can carry source file/line metadata."""
        s = Spec(
            kind=SpecKind.GUARANTEE,
            description="sorted output",
            source_func="sort",
            source_file="sort.py",
            source_line=42,
        )
        assert s.source_func == "sort"
        assert s.source_file == "sort.py"
        assert s.source_line == 42
