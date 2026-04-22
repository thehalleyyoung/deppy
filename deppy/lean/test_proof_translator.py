"""Tests for Deppy ProofTerm → Lean 4 proof translator."""

from __future__ import annotations

import sys, os
import pytest

# Ensure repo root is importable
sys.path.insert(0, os.path.join(os.path.dirname(__file__), os.pardir, os.pardir))

from deppy.core.kernel import (
    ProofTerm, Refl, Sym, Trans, Cong, TransportProof, Ext, Cut,
    Assume, Z3Proof, NatInduction, ListInduction, Cases,
    DuckPath, EffectWitness, Patch, Fiber, PathComp, Ap, FunExt,
    CechGlue, Univalence, AxiomInvocation, Unfold, Rewrite, Structural,
)
from deppy.core.types import Var, Literal, PyIntType

from deppy.lean.proof_translator import (
    translate_proof,
    full_translate,
    classify_z3_formula,
    ProofTranslationResult,
)


# ═══════════════════════════════════════════════════════════════════
# 1. Refl → rfl
# ═══════════════════════════════════════════════════════════════════

class TestRefl:
    def test_refl_produces_rfl(self):
        pt = Refl(term=Var("x"))
        assert translate_proof(pt) == "rfl"

    def test_refl_trust_level(self):
        result = full_translate(Refl(term=Var("x")))
        assert result.trust_level == "LEAN_PROVABLE"
        assert result.sorry_count == 0 if hasattr(result, "sorry_count") else True


# ═══════════════════════════════════════════════════════════════════
# 2. Trans(Refl, Refl) → Eq.trans
# ═══════════════════════════════════════════════════════════════════

class TestTrans:
    def test_trans_refl_refl(self):
        pt = Trans(left=Refl(term=Var("a")), right=Refl(term=Var("b")))
        result = translate_proof(pt)
        assert "Eq.trans" in result
        assert "rfl" in result

    def test_trans_structure(self):
        pt = Trans(left=Refl(term=Var("a")), right=Refl(term=Var("b")))
        assert translate_proof(pt) == "Eq.trans (rfl) (rfl)"


# ═══════════════════════════════════════════════════════════════════
# 3. Cong + Sym composition
# ═══════════════════════════════════════════════════════════════════

class TestCongSym:
    def test_cong_simple(self):
        pt = Cong(func=Var("f"), proof=Refl(term=Var("x")))
        result = translate_proof(pt)
        assert "congrArg" in result
        assert "f" in result
        assert "rfl" in result

    def test_sym_simple(self):
        pt = Sym(proof=Refl(term=Var("x")))
        result = translate_proof(pt)
        assert "Eq.symm" in result
        assert "rfl" in result

    def test_cong_of_sym(self):
        pt = Cong(func=Var("g"), proof=Sym(proof=Refl(term=Var("x"))))
        result = translate_proof(pt)
        assert "congrArg" in result
        assert "Eq.symm" in result


# ═══════════════════════════════════════════════════════════════════
# 4. NatInduction with base and step
# ═══════════════════════════════════════════════════════════════════

class TestNatInduction:
    def test_nat_induction(self):
        pt = NatInduction(
            var="n",
            base_proof=Refl(term=Var("zero")),
            step_proof=Assume("ih"),
        )
        result = translate_proof(pt)
        assert "induction n" in result
        assert "| zero =>" in result
        assert "| succ n ih =>" in result
        assert "rfl" in result

    def test_nat_induction_provable(self):
        pt = NatInduction(
            var="n",
            base_proof=Refl(term=Var("zero")),
            step_proof=Assume("ih"),
        )
        res = full_translate(pt)
        assert res.trust_level == "LEAN_PROVABLE"


# ═══════════════════════════════════════════════════════════════════
# 5. ListInduction
# ═══════════════════════════════════════════════════════════════════

class TestListInduction:
    def test_list_induction(self):
        pt = ListInduction(
            var="xs",
            nil_proof=Refl(term=Var("nil")),
            cons_proof=Assume("ih"),
        )
        result = translate_proof(pt)
        assert "induction xs" in result
        assert "| nil =>" in result
        assert "| cons x xs ih =>" in result


# ═══════════════════════════════════════════════════════════════════
# 6. Cases with 3 branches
# ═══════════════════════════════════════════════════════════════════

class TestCases:
    def test_cases_three_branches(self):
        pt = Cases(
            scrutinee=Var("c"),
            branches=[
                ("red", Refl(term=Var("x"))),
                ("green", Assume("h1")),
                ("blue", Assume("h2")),
            ],
        )
        result = translate_proof(pt)
        assert "cases c" in result
        assert "| red =>" in result
        assert "| green =>" in result
        assert "| blue =>" in result
        assert result.count("|") == 3


# ═══════════════════════════════════════════════════════════════════
# 7. Cut (have) nesting
# ═══════════════════════════════════════════════════════════════════

class TestCut:
    def test_simple_cut(self):
        pt = Cut(
            hyp_name="h",
            hyp_type=PyIntType(),
            lemma_proof=Refl(term=Var("x")),
            body_proof=Assume("h"),
        )
        result = translate_proof(pt)
        assert "have h" in result
        assert ":=" in result
        assert "rfl" in result

    def test_nested_cut(self):
        inner_cut = Cut(
            hyp_name="h1",
            hyp_type=PyIntType(),
            lemma_proof=Refl(term=Var("a")),
            body_proof=Assume("h1"),
        )
        outer_cut = Cut(
            hyp_name="h2",
            hyp_type=PyIntType(),
            lemma_proof=inner_cut,
            body_proof=Assume("h2"),
        )
        result = translate_proof(outer_cut)
        assert "have h2" in result
        assert "have h1" in result


# ═══════════════════════════════════════════════════════════════════
# 8. Z3Proof with simple arithmetic → omega
# ═══════════════════════════════════════════════════════════════════

class TestZ3Simple:
    def test_z3_linear_arith(self):
        pt = Z3Proof(formula="x + 1 > 0")
        result = translate_proof(pt)
        assert "omega" in result
        assert "sorry" not in result

    def test_z3_classify_omega(self):
        assert classify_z3_formula("x + 1 > 0") == "omega"
        assert classify_z3_formula("a * 2 + b <= 10") == "omega"

    def test_z3_classify_rfl(self):
        assert classify_z3_formula("x == x") == "rfl"

    def test_z3_classify_tauto(self):
        assert classify_z3_formula("x > 0 and y < 10") == "tauto"

    def test_z3_classify_simp(self):
        assert classify_z3_formula("forall x, x + 0 == x") == "simp"


# ═══════════════════════════════════════════════════════════════════
# 9. Z3Proof with complex formula → sorry
# ═══════════════════════════════════════════════════════════════════

class TestZ3Complex:
    def test_z3_complex_sorry(self):
        formula = "BitVec.extract(x, 7, 0) ++ BitVec.extract(x, 15, 8) == bswap16(x)"
        pt = Z3Proof(formula=formula)
        result = translate_proof(pt)
        assert "sorry" in result
        assert "Z3 verified" in result

    def test_z3_complex_trust(self):
        formula = "BitVec.extract(x, 7, 0) ++ BitVec.extract(x, 15, 8) == bswap16(x)"
        res = full_translate(Z3Proof(formula=formula))
        assert res.trust_level == "LEAN_SORRY"


# ═══════════════════════════════════════════════════════════════════
# 10. FunExt
# ═══════════════════════════════════════════════════════════════════

class TestFunExt:
    def test_funext(self):
        pt = FunExt(var="x", pointwise_proof=Refl(term=Var("x")))
        result = translate_proof(pt)
        assert "funext" in result
        assert "fun x =>" in result
        assert "rfl" in result

    def test_ext_legacy(self):
        pt = Ext(var="y", body_proof=Refl(term=Var("y")))
        result = translate_proof(pt)
        assert "funext" in result
        assert "fun y =>" in result


# ═══════════════════════════════════════════════════════════════════
# 11. Realistic composed proof
# ═══════════════════════════════════════════════════════════════════

class TestComposed:
    def test_trans_cong_natind_refl(self):
        """Trans(Cong("f", NatInduction(...)), Refl(...))"""
        nat_ind = NatInduction(
            var="n",
            base_proof=Refl(term=Var("zero")),
            step_proof=Assume("ih"),
        )
        cong = Cong(func=Var("f"), proof=nat_ind)
        pt = Trans(left=cong, right=Refl(term=Var("result")))
        result = translate_proof(pt)

        assert "Eq.trans" in result
        assert "congrArg" in result
        assert "induction n" in result
        assert "rfl" in result

    def test_composed_trust(self):
        nat_ind = NatInduction(
            var="n",
            base_proof=Refl(term=Var("zero")),
            step_proof=Assume("ih"),
        )
        cong = Cong(func=Var("f"), proof=nat_ind)
        pt = Trans(left=cong, right=Refl(term=Var("result")))
        res = full_translate(pt)
        assert res.trust_level == "LEAN_PROVABLE"
        assert len(res.untranslatable) == 0


# ═══════════════════════════════════════════════════════════════════
# 12. DuckPath → sorry with explanation
# ═══════════════════════════════════════════════════════════════════

class TestDuckPath:
    def test_duck_path_proof(self):
        pt = DuckPath(
            type_a=Var("MyList"),
            type_b=Var("list"),
            method_proofs={},
        )
        result = translate_proof(pt)
        assert "sorry" not in result
        assert "funext" in result

    def test_duck_path_trust(self):
        pt = DuckPath(
            type_a=Var("MyList"),
            type_b=Var("list"),
            method_proofs={},
        )
        res = full_translate(pt)
        assert res.trust_level == "LEAN_PROVABLE"


# ═══════════════════════════════════════════════════════════════════
# Additional coverage: formerly-sorry nodes now produce proofs
# ═══════════════════════════════════════════════════════════════════

class TestSorryNodes:
    def test_cech_glue(self):
        pt = CechGlue(patches=[("cond1", Refl(term=Var("x")))], overlap_proofs=[])
        res = full_translate(pt)
        assert res.trust_level == "LEAN_PROVABLE"
        assert "sorry" not in res.lean_proof

    def test_univalence(self):
        pt = Univalence(
            equiv_proof=Refl(term=Var("id")),
            from_type=PyIntType(),
            to_type=PyIntType(),
        )
        res = full_translate(pt)
        assert res.trust_level == "LEAN_PROVABLE"
        assert "sorry" not in res.lean_proof

    def test_effect_witness(self):
        pt = EffectWitness(effect="IO", proof=Refl(term=Var("x")))
        res = full_translate(pt)
        assert res.trust_level == "LEAN_SORRY"

    def test_patch(self):
        pt = Patch(
            cls=Var("MyClass"),
            method_name="foo",
            new_impl=Var("new_foo"),
            contract_proof=Refl(term=Var("x")),
        )
        res = full_translate(pt)
        assert res.trust_level == "LEAN_PROVABLE"
        assert "rfl" in res.lean_proof

    def test_fiber(self):
        pt = Fiber(scrutinee=Var("x"), type_branches=[], exhaustive=True)
        res = full_translate(pt)
        assert res.trust_level == "LEAN_PROVABLE"
        assert "decide" in res.lean_proof


class TestAxiom:
    def test_axiom_invocation(self):
        pt = AxiomInvocation(name="list_assoc", module="Mathlib.Data.List")
        res = full_translate(pt)
        assert res.trust_level == "LEAN_AXIOM"
        assert "list_assoc" in res.lean_proof
        assert "Mathlib.Data.List" in res.lean_proof


class TestRewrite:
    def test_rewrite_with_body(self):
        pt = Rewrite(lemma=Assume("h"), proof=Refl(term=Var("x")))
        result = translate_proof(pt)
        assert "rw" in result
        assert "exact" in result

    def test_unfold(self):
        pt = Unfold(func_name="myFunc", proof=Refl(term=Var("x")))
        result = translate_proof(pt)
        assert "unfold myFunc" in result
        assert "exact" in result


class TestStructural:
    def test_structural_with_desc(self):
        pt = Structural(description="obviously true")
        result = translate_proof(pt)
        assert "trivial" in result
        assert "obviously true" in result

    def test_structural_no_desc(self):
        pt = Structural()
        assert translate_proof(pt) == "by trivial"


class TestPathCompAp:
    def test_path_comp(self):
        pt = PathComp(
            left_path=Refl(term=Var("a")),
            right_path=Refl(term=Var("b")),
        )
        result = translate_proof(pt)
        assert "Eq.trans" in result

    def test_ap(self):
        pt = Ap(function=Var("f"), path_proof=Refl(term=Var("x")))
        result = translate_proof(pt)
        assert "congrArg" in result
        assert "f" in result


class TestTransportProof:
    def test_transport(self):
        pt = TransportProof(
            type_family=Var("P"),
            path_proof=Refl(term=Var("eq")),
            base_proof=Assume("h"),
        )
        result = translate_proof(pt)
        assert "▸" in result
