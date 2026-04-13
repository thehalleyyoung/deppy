"""Mathlib: String — auto-generated from Mathlib4.

Contains 74 rewrite rules derived from Mathlib theorems.
Plus 38 untranslatable theorems stored for reference.
"""
from __future__ import annotations

from typing import Any, Dict, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)
from cctt.path_search import FiberCtx


# ════════════════════════════════════════════════════════════
# Axiom metadata
# ════════════════════════════════════════════════════════════

AXIOM_NAME = "mathlib_ml_string"
AXIOM_CATEGORY = "mathlib"
REQUIRES: List[str] = []
COMPOSES_WITH: List[str] = []


# ════════════════════════════════════════════════════════════
# Pattern matching helpers
# ════════════════════════════════════════════════════════════

def _match_op(term: OTerm, name: str, arity: int = -1) -> Optional[Tuple[OTerm, ...]]:
    """Match an OOp with given name and optional arity."""
    if not isinstance(term, OOp):
        return None
    if term.name != name:
        return None
    if arity >= 0 and len(term.args) != arity:
        return None
    return term.args


def _is_lit(term: OTerm, value: Any = None) -> bool:
    """Check if term is a literal, optionally with a specific value."""
    if not isinstance(term, OLit):
        return False
    if value is not None:
        return term.value == value
    return True


def _is_empty_seq(term: OTerm) -> bool:
    """Check if term is an empty sequence."""
    return isinstance(term, OSeq) and len(term.elements) == 0


# ════════════════════════════════════════════════════════════
# Rewrite rules (74 total)
# ════════════════════════════════════════════════════════════

def _r0000_cast_eq_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.cast_eq_mod
    # (k : R) = (k % p : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "k", 2)
    if args is not None:
        try:
            rhs = OOp("k", (OVar("_unknown"), OVar("p"), args[0], OVar("_unknown"),))
            results.append((rhs, "Mathlib: CharP_cast_eq_mod"))
        except Exception:
            pass
    return results


def _r0001_natCast_eq_ite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharTwo.natCast_eq_ite
    # (n : R) = if Even n then 0 else 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OOp("if", (OVar("Even"), OVar("n"), OVar("then"), OLit(0), OVar("else"), OLit(1),))
            results.append((rhs, "Mathlib: CharTwo_natCast_eq_ite"))
        except Exception:
            pass
    return results


def _r0002_dual_rTensor_conj_homEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharacterModule.dual_rTensor_conj_homEquiv
    # homEquiv.symm.toLinearMap ∘ₗ dual (f.rTensor B) ∘ₗ homEquiv.toLinearMap = f.lcomp R _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homEquiv_symm_toLinearMap", 5)
    if args is not None:
        try:
            rhs = OOp("f_lcomp", (OVar("R"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: CharacterModule_dual_rTensor_conj_homEquiv"))
        except Exception:
            pass
    return results


def _r0003_eq_neg_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharZero.eq_neg_self_iff
    # a = -a ↔ a = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("minus_a"), OVar("a"))), OLit(0)))
            results.append((rhs, "Mathlib: CharZero_eq_neg_self_iff"))
    except Exception:
        pass
    return results


def _r0004_equivAlgHom_symm_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.equivAlgHom_symm_coe
    # ⇑(equivAlgHom.symm f) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("equivAlgHom_symm_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_equivAlgHom_symm_coe"))
    except Exception:
        pass
    return results


def _r0005_asString_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.asString_nil
    # ofList [] = ""
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OLit("")
            results.append((rhs, "Mathlib: String_asString_nil"))
        except Exception:
            pass
    return results


def _r0006_length_eq_list_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.length_eq_list_length
    # (String.ofList l).length = l.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("String_ofList_l_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_length")
            results.append((rhs, "Mathlib: String_length_eq_list_length"))
    except Exception:
        pass
    return results


def _r0007_leftpad_prefix(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.leftpad_prefix
    # ∀ s, IsPrefix (replicate (n - length s) c) (leftpad n c s)   | s =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "is_prefix", 4)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: String_leftpad_prefix"))
        except Exception:
            pass
    return results


def _r0008_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.ext
    # φ = ψ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("psi")
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_ext"))
    except Exception:
        pass
    return results


def _r0009_natCast_eq_natCast_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.natCast_eq_natCast_mod
    # (a : R) = a % p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("p"),))
            results.append((rhs, "Mathlib: CharP_natCast_eq_natCast_mod"))
        except Exception:
            pass
    return results


def _r0010_natCast_eq_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.natCast_eq_natCast
    # (a : R) = b ↔ a ≡ b [MOD p]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("b"), OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("MOD", (OVar("p"),)),)),))))
            results.append((rhs, "Mathlib: CharP_natCast_eq_natCast"))
        except Exception:
            pass
    return results


def _r0011_ringChar_of_prime_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.ringChar_of_prime_eq_zero
    # ringChar R = p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ringChar", 1)
    if args is not None:
        try:
            rhs = OVar("p")
            results.append((rhs, "Mathlib: CharP_ringChar_of_prime_eq_zero"))
        except Exception:
            pass
    return results


def _r0012_charP_iff_prime_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.charP_iff_prime_eq_zero
    # CharP R p ↔ (p : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CharP_charP_iff_prime_eq_zero"))
        except Exception:
            pass
    return results


def _r0013_cast_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.cast_eq_zero
    # (p : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CharP_cast_eq_zero"))
        except Exception:
            pass
    return results


def _r0014_cast_eq_iff_mod_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.cast_eq_iff_mod_eq
    # (a : R) = (b : R) ↔ a % p = b % p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("b", (args[0], args[1],)), OOp("a", (OVar("_unknown"), OVar("p"),)))), OOp("b", (OVar("_unknown"), OVar("p"),))))
            results.append((rhs, "Mathlib: CharP_cast_eq_iff_mod_eq"))
        except Exception:
            pass
    return results


def _r0015_ofNat_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.ofNat_eq_zero
    # (ofNat(p) : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNat_p", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CharP_ofNat_eq_zero"))
        except Exception:
            pass
    return results


def _r0016_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.eq
    # p = q
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q")
            results.append((rhs, "Mathlib: CharP_eq"))
    except Exception:
        pass
    return results


def _r0017_ringChar_zero_iff_CharZero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.ringChar_zero_iff_CharZero
    # ringChar R = 0 ↔ CharZero R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ringChar", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OOp("CharZero", (args[0],))))
            results.append((rhs, "Mathlib: CharP_ringChar_zero_iff_CharZero"))
        except Exception:
            pass
    return results


def _r0018_intCast_mul_natCast_gcdA_eq_gcd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.intCast_mul_natCast_gcdA_eq_gcd
    # (n * n.gcdA p : R) = n.gcd p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("n_gcd", (OVar("p"),))
            results.append((rhs, "Mathlib: CharP_intCast_mul_natCast_gcdA_eq_gcd"))
        except Exception:
            pass
    return results


def _r0019_natCast_gcdA_mul_intCast_eq_gcd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.natCast_gcdA_mul_intCast_eq_gcd
    # (n.gcdA p * n : R) = n.gcd p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("n_gcd", (OVar("p"),))
            results.append((rhs, "Mathlib: CharP_natCast_gcdA_mul_intCast_eq_gcd"))
        except Exception:
            pass
    return results


def _r0020_ker_intAlgebraMap_eq_span(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.ker_intAlgebraMap_eq_span
    # RingHom.ker (algebraMap ℤ R) = Ideal.span {(p : ℤ)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "RingHom_ker", 1)
    if args is not None:
        try:
            rhs = OOp("Ideal_span", (OVar("p_colon"),))
            results.append((rhs, "Mathlib: CharP_ker_intAlgebraMap_eq_span"))
        except Exception:
            pass
    return results


def _r0021_quotient_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.quotient_iff
    # CharP (R ⧸ I) n ↔ ∀ x : ℕ, ↑x ∈ I → (x : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CharP_quotient_iff"))
        except Exception:
            pass
    return results


def _r0022_two_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharTwo.two_eq_zero
    # (2 : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_2", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CharTwo_two_eq_zero"))
        except Exception:
            pass
    return results


def _r0023_natCast_cases(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharTwo.natCast_cases
    # (n : R) = 0 ∨ (n : R) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(0), OOp("n", (args[0], args[1],)))), OLit(1)))
            results.append((rhs, "Mathlib: CharTwo_natCast_cases"))
        except Exception:
            pass
    return results


def _r0024_natCast_eq_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharTwo.natCast_eq_mod
    # (n : R) = (n % 2 : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OLit(2), args[0], OVar("_unknown"),))
            results.append((rhs, "Mathlib: CharTwo_natCast_eq_mod"))
        except Exception:
            pass
    return results


def _r0025_ofNat_eq_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharTwo.ofNat_eq_mod
    # (ofNat(n) : R) = (ofNat(n) % 2 : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNat_n", 2)
    if args is not None:
        try:
            rhs = OOp("ofNat_n", (OVar("_unknown"), OLit(2), args[0], OVar("_unknown"),))
            results.append((rhs, "Mathlib: CharTwo_ofNat_eq_mod"))
        except Exception:
            pass
    return results


def _r0026_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharacterModule.ext
    # c = c'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("c_prime")
            results.append((rhs, "Mathlib: CharacterModule_ext"))
    except Exception:
        pass
    return results


def _r0027_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharacterModule.smul_apply
    # (r • c) a = c (r • a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r_c", 1)
    if args is not None:
        try:
            rhs = OOp("c", (OOp("r", (OVar("_unknown"), args[0],)),))
            results.append((rhs, "Mathlib: CharacterModule_smul_apply"))
        except Exception:
            pass
    return results


def _r0028_dual_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharacterModule.dual_comp
    # dual (g.comp f) = (dual f).comp (dual g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dual", 1)
    if args is not None:
        try:
            rhs = OOp("dual_f_comp", (OOp("dual", (OVar("g"),)),))
            results.append((rhs, "Mathlib: CharacterModule_dual_comp"))
        except Exception:
            pass
    return results


def _r0029_neg_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharZero.neg_eq_self_iff
    # -a = a ↔ a = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("a"), OVar("a"))), OLit(0)))
            results.append((rhs, "Mathlib: CharZero_neg_eq_self_iff"))
    except Exception:
        pass
    return results


def _r0030_exists_apply_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.exists_apply_eq_zero
    # ∃ f : characterSpace ℂ A, f a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 7)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_exists_apply_eq_zero"))
        except Exception:
            pass
    return results


def _r0031_mem_spectrum_iff_exists(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.mem_spectrum_iff_exists
    # z ∈ spectrum ℂ a ↔ ∃ f : characterSpace ℂ A, f a = z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("z")
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_mem_spectrum_iff_exists"))
        except Exception:
            pass
    return results


def _r0032_compContinuousMap_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.compContinuousMap_id
    # compContinuousMap (StarAlgHom.id 𝕜 A) = ContinuousMap.id (characterSpace 𝕜 A)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "compContinuousMap", 1)
    if args is not None:
        try:
            rhs = OOp("ContinuousMap_id", (OOp("characterSpace", (OVar("_unknown"), OVar("A"),)),))
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_compContinuousMap_id"))
        except Exception:
            pass
    return results


def _r0033_compContinuousMap_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.compContinuousMap_comp
    # compContinuousMap (ψ₂.comp ψ₁) = (compContinuousMap ψ₁).comp (compContinuousMap ψ₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "compContinuousMap", 1)
    if args is not None:
        try:
            rhs = OOp("compContinuousMap_psi_1_comp", (OOp("compContinuousMap", (OVar("psi_2"),)),))
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_compContinuousMap_comp"))
        except Exception:
            pass
    return results


def _r0034_homeoEval_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.homeoEval_naturality
    # (homeoEval Y 𝕜 : C(_, _)).comp f =       (f.compStarAlgHom' 𝕜 𝕜 |> compContinuousMap).comp (homeoEval X 𝕜 : C(_, _))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homeoEval_Y_colon_C_comp", 1)
    if args is not None:
        try:
            rhs = OOp("f_compStarAlgHom_prime_pipe_gt_compContinuousMap_comp", (OOp("homeoEval", (OVar("X"), OVar("_unknown"), OVar("colon"), OVar("C"),)),))
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_homeoEval_naturality"))
        except Exception:
            pass
    return results


def _r0035_equivAlgHom_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.equivAlgHom_coe
    # ⇑(equivAlgHom f) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("equivAlgHom_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_equivAlgHom_coe"))
    except Exception:
        pass
    return results


def _r0036_ltb_cons_addChar(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.ltb_cons_addChar
    # ltb ⟨ofList (c :: cs₁), i₁ + c⟩ ⟨ofList (c :: cs₂), i₂ + c⟩ =       ltb ⟨ofList cs₁, i₁⟩ ⟨ofList cs₂, i₂⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ltb", 2)
    if args is not None:
        try:
            rhs = OOp("ltb", (OVar("ofList_cs_1_i_1"), OVar("ofList_cs_2_i_2"),))
            results.append((rhs, "Mathlib: String_ltb_cons_addChar"))
        except Exception:
            pass
    return results


def _r0037_lt_iff_toList_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.lt_iff_toList_lt
    # ∀ {s₁ s₂ : String}, s₁ < s₂ ↔ s₁.toList < s₂.toList   | s₁, s₂ => show ltb ⟨s₁, 0⟩ ⟨s₂, 0⟩ ↔ s₁.toList < s₂.toList
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("iff", (OOp("gt", (OVar("show"), OVar("ltb"), OVar("s_1_0"), OVar("s_2_0"),)), OVar("s_1_toList"))), OVar("s_2_toList")))
            results.append((rhs, "Mathlib: String_lt_iff_toList_lt"))
        except Exception:
            pass
    return results


def _r0038_asString_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.asString_toList
    # ofList s.toList = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: String_asString_toList"))
        except Exception:
            pass
    return results


def _r0039_toList_nonempty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.toList_nonempty
    # ∀ {s : String}, s ≠ "" → s.toList = String.Legacy.front s :: (String.Legacy.drop s 1).toList   | s, h =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("String_Legacy_front", (OVar("s"), OVar("colon_colon"), OVar("String_Legacy_drop_s_1_toList"), OVar("pipe"), OVar("s"), OVar("h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: String_toList_nonempty"))
    except Exception:
        pass
    return results


def _r0040_head_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.head_empty
    # "".toList.head! = default
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toList_head_bang")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("default")
            results.append((rhs, "Mathlib: String_head_empty"))
    except Exception:
        pass
    return results


def _r0041_ofList_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.ofList_eq
    # ofList l = s ↔ l = s.toList
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("s"), args[0])), OVar("s_toList")))
            results.append((rhs, "Mathlib: String_ofList_eq"))
        except Exception:
            pass
    return results


def _r0042_congr_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.congr_append
    # a ++ b = String.ofList (a.toList ++ b.toList)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OOp("String_ofList", (OOp("concat", (OVar("a_toList"), OVar("b_toList"))),))
            results.append((rhs, "Mathlib: String_congr_append"))
        except Exception:
            pass
    return results


def _r0043_length_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.length_replicate
    # (replicate n c).length = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("replicate_n_c_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: String_length_replicate"))
    except Exception:
        pass
    return results


def _r0044_length_leftpad(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.length_leftpad
    # ∀ (s : String), (leftpad n c s).length = max n s.length   | s =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("leftpad_n_c_s_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("max", (OVar("n"), OVar("s_length"), OVar("pipe"), OVar("s"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: String_length_leftpad"))
    except Exception:
        pass
    return results


def _r0045_leftpad_suffix(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.leftpad_suffix
    # ∀ s, IsSuffix s (leftpad n c s)   | s =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "is_suffix", 4)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: String_leftpad_suffix"))
        except Exception:
            pass
    return results


def _r0046_sq_add_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.sq_add_sq
    # ∃ a b : ℕ, ((a : R) ^ 2 + (b : R) ^ 2) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 5)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: CharP_sq_add_sq"))
        except Exception:
            pass
    return results


def _r0047_stalkMap_locallyRingedSpaceMapAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ChartedSpace.stalkMap_locallyRingedSpaceMapAux
    # (locallyRingedSpaceMapAux f hf).stalkMap x ≫       smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =       smoothSheafCommRing
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "locallyRingedSpaceMapAux_f_hf_stalkMap", 8)
    if args is not None:
        try:
            rhs = OOp("smoothSheafCommRing_evalHom", (OVar("IN"), args[6], OVar("N"), args[6], OOp("f", (args[7],)),))
            results.append((rhs, "Mathlib: ChartedSpace_stalkMap_locallyRingedSpaceMapAux"))
        except Exception:
            pass
    return results


def _r0048_stalkMap_locallyRingedSpaceMap_evalHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom
    # (locallyRingedSpaceMap f hf).stalkMap x ≫       smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =       smoothSheafCommRing.ev
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "locallyRingedSpaceMap_f_hf_stalkMap", 8)
    if args is not None:
        try:
            rhs = OOp("smoothSheafCommRing_evalHom", (OVar("IN"), args[6], OVar("N"), args[6], OOp("f", (args[7],)),))
            results.append((rhs, "Mathlib: ChartedSpace_stalkMap_locallyRingedSpaceMap_evalHom"))
        except Exception:
            pass
    return results


def _r0049_locallyRingedSpace_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ChartedSpace.locallyRingedSpace_id
    # locallyRingedSpaceMap (IM := IM) (IN := IM) (M := M) id contMDiff_id = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "locallyRingedSpaceMap", 5)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: ChartedSpace_locallyRingedSpace_id"))
        except Exception:
            pass
    return results


def _r0050_locallyRingedSpace_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ChartedSpace.locallyRingedSpace_comp
    # locallyRingedSpaceMap (g ∘ f) (hg.comp hf) =       locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "locallyRingedSpaceMap", 2)
    if args is not None:
        try:
            rhs = OOp("locallyRingedSpaceMap", (OVar("f"), OVar("hf"), OVar("_unknown"), OVar("locallyRingedSpaceMap"), OVar("g"), OVar("hg"),))
            results.append((rhs, "Mathlib: ChartedSpace_locallyRingedSpace_comp"))
        except Exception:
            pass
    return results


def _r0051_orderOf_eq_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.orderOf_eq_two_iff
    # orderOf x = 2 ↔ x = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "orderOf", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(2), args[0])), OVar("minus_1")))
            results.append((rhs, "Mathlib: CharP_orderOf_eq_two_iff"))
        except Exception:
            pass
    return results


def _r0052_card_pow_char_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Char.card_pow_char_pow
    # (χ (-1) * Fintype.card R) ^ (p ^ n / 2) = χ ((p : R) ^ n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("chi", (OOp("**", (OOp("p", (OVar("colon"), OVar("R"),)), OVar("n"))),))
            results.append((rhs, "Mathlib: Char_card_pow_char_pow"))
        except Exception:
            pass
    return results


def _r0053_card_pow_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Char.card_pow_card
    # (χ (-1) * Fintype.card F) ^ (Fintype.card F' / 2) = χ (Fintype.card F')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("chi", (OOp("Fintype_card", (OVar("F_prime"),)),))
            results.append((rhs, "Mathlib: Char_card_pow_card"))
        except Exception:
            pass
    return results


def _r0054_isNat_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Tactic.ReduceModChar.CharP.isNat_pow
    # ∀ {f : α → ℕ → α} {a : α} {a' b b' c n n' : ℕ},     CharP α n → f = HPow.hPow → IsNat a a' → IsNat b b' → IsNat n n' →  
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsNat", 17)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("by_rw_h_Nat_cast_id_Nat_pow_eq_from_Nat_cast_pow_CharP_natCast_eq_natCast_mod_a_n_rfl_attribute"), OSeq((OOp("local", (OVar("instance"),)),)), OVar("Mathlib_Meta_monadLiftOptionMetaM"), OVar("in_def"), OVar("normBareNumeral"), OVar("a_colon_Q_Type_u"), OOp("n", (OVar("n_prime"), OVar("colon"), OVar("Q"),)), OOp("pn", (OVar("colon"), OVar("Q_IsNat_n_n_prime"),)), OOp("e", (OVar("colon"), OVar("Q_a"),)), OOp("_unknown", (OVar("colon"), OVar("Q_Ring_a"),)), OOp("instCharP", (OVar("colon"), OVar("Q_CharP_a_n"),)), OVar("colon"), OVar("MetaM"), OOp("Result", (OVar("e"),)),))
            results.append((rhs, "Mathlib: Tactic_ReduceModChar_CharP_isNat_pow"))
        except Exception:
            pass
    return results


def _r0055_intCast_eq_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Tactic.CharP.intCast_eq_mod
    # (k : R) = (k % p : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "k", 2)
    if args is not None:
        try:
            rhs = OOp("k", (OVar("_unknown"), OVar("p"), args[0], OVar("_unknown"),))
            results.append((rhs, "Mathlib: Tactic_CharP_intCast_eq_mod"))
        except Exception:
            pass
    return results


def _r0056_neg_eq_sub_one_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Tactic.CharP.neg_eq_sub_one_mul
    # -b = a' * b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("a_prime"), OVar("b")))
            results.append((rhs, "Mathlib: Tactic_CharP_neg_eq_sub_one_mul"))
    except Exception:
        pass
    return results


def _r0057_neg_mul_eq_sub_one_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Tactic.CharP.neg_mul_eq_sub_one_mul
    # -(a * b) = na' * b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_a_star_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("na_prime"), OVar("b")))
            results.append((rhs, "Mathlib: Tactic_CharP_neg_mul_eq_sub_one_mul"))
    except Exception:
        pass
    return results


def _r0058_coe_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.coe_coe
    # ⇑(φ : WeakDual 𝕜 A) = (φ : A → 𝕜)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_colon_WeakDual_A")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("implies", (OOp("phi", (OVar("colon"), OVar("A"),)), OVar("_unknown")))
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_coe_coe"))
    except Exception:
        pass
    return results


def _r0059_coe_toCLM(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.coe_toCLM
    # ⇑(toCLM φ) = φ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toCLM_phi")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("phi")
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_coe_toCLM"))
    except Exception:
        pass
    return results


def _r0060_coe_toNonUnitalAlgHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.coe_toNonUnitalAlgHom
    # ⇑(toNonUnitalAlgHom φ) = φ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toNonUnitalAlgHom_phi")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("phi")
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_coe_toNonUnitalAlgHom"))
    except Exception:
        pass
    return results


def _r0061_union_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.union_zero
    # characterSpace 𝕜 A ∪ {0} = {φ : WeakDual 𝕜 A | ∀ x y : A, φ (x * y) = φ x * φ y}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OVar("phi_colon_WeakDual_A_pipe_forall_x_y_colon_A_phi_x_star_y_eq_phi_x_star_phi_y")
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_union_zero"))
        except Exception:
            pass
    return results


def _r0062_continuousMapEval_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WeakDual.CharacterSpace.continuousMapEval_apply_apply
    # continuousMapEval X 𝕜 x f = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "continuousMapEval", 4)
    if args is not None:
        try:
            rhs = OOp("f", (args[2],))
            results.append((rhs, "Mathlib: WeakDual_CharacterSpace_continuousMapEval_apply_apply"))
        except Exception:
            pass
    return results


def _r0063_isOpen_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ChartedSpace.isOpen_iff
    # IsOpen s ↔ ∀ x : M, IsOpen <| chartAt H x '' ((chartAt H x).source ∩ s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsOpen", 1)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("x"), OVar("colon"), OVar("M"), OVar("IsOpen"), OVar("lt_pipe"), OVar("chartAt"), OVar("H"), OVar("x"), OVar("prime_prime"), OOp("inter", (OVar("chartAt_H_x_source"), args[0])),))
            results.append((rhs, "Mathlib: ChartedSpace_isOpen_iff"))
        except Exception:
            pass
    return results


def _r0064_charZero_iff_forall_prime_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharZero.charZero_iff_forall_prime_ne_zero
    # CharZero R ↔ ∀ p : ℕ, p.Prime → (p : R) ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "CharZero", 1)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("implies", (OOp("forall", (OVar("p"), OVar("colon"), OVar("_unknown"), OVar("p_Prime"),)), OOp("p", (OVar("colon"), args[0],)))), OLit(0)))
            results.append((rhs, "Mathlib: CharZero_charZero_iff_forall_prime_ne_zero"))
        except Exception:
            pass
    return results


def _r0065_isUnit_natCast_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.isUnit_natCast_iff
    # IsUnit (n : R) ↔ ¬p ∣ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsUnit", 1)
    if args is not None:
        try:
            rhs = OOp("not_p", (OVar("_unknown"), OVar("n"),))
            results.append((rhs, "Mathlib: CharP_isUnit_natCast_iff"))
        except Exception:
            pass
    return results


def _r0066_isUnit_ofNat_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.isUnit_ofNat_iff
    # IsUnit (ofNat(n) : R) ↔ ¬p ∣ ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsUnit", 1)
    if args is not None:
        try:
            rhs = OOp("not_p", (OVar("_unknown"), OVar("ofNat_n"),))
            results.append((rhs, "Mathlib: CharP_isUnit_ofNat_iff"))
        except Exception:
            pass
    return results


def _r0067_isUnit_intCast_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.isUnit_intCast_iff
    # IsUnit (z : R) ↔ ¬↑p ∣ z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsUnit", 1)
    if args is not None:
        try:
            rhs = OOp("not_p", (OVar("_unknown"), OVar("z"),))
            results.append((rhs, "Mathlib: CharP_isUnit_intCast_iff"))
        except Exception:
            pass
    return results


def _r0068_quotient_iff_le_ker_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.quotient_iff_le_ker_natCast
    # CharP (R ⧸ I) n ↔ I.comap (Nat.castRingHom R) ≤ RingHom.ker (Nat.castRingHom R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "CharP", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("I_comap", (OOp("Nat_castRingHom", (OVar("R"),)),)), OOp("RingHom_ker", (OOp("Nat_castRingHom", (OVar("R"),)),))))
            results.append((rhs, "Mathlib: CharP_quotient_iff_le_ker_natCast"))
        except Exception:
            pass
    return results


def _r0069_charP_center_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CharP.charP_center_iff
    # CharP (Subring.center R) p ↔ CharP R p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "CharP", 2)
    if args is not None:
        try:
            rhs = OOp("CharP", (OVar("R"), args[1],))
            results.append((rhs, "Mathlib: CharP_charP_center_iff"))
        except Exception:
            pass
    return results


def _r0070_le_iff_toList_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: String.le_iff_toList_le
    # s₁ ≤ s₂ ↔ s₁.toList ≤ s₂.toList
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("s_1_toList"), OVar("s_2_toList")))
            results.append((rhs, "Mathlib: String_le_iff_toList_le"))
        except Exception:
            pass
    return results


def _r0071_liftPropAt_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ChartedSpace.liftPropAt_iff
    # LiftPropAt P f x ↔       ContinuousAt f x ∧ P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) univ (chartAt H x x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LiftPropAt", 3)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("ContinuousAt", (args[1], args[2],)), OOp("P", (OOp("comp", (OOp("chartAt", (OVar("H_prime"), OOp("f", (args[2],)),)), OOp("comp", (args[1], OVar("chartAt_H_x_symm"))))), OVar("univ"), OOp("chartAt", (OVar("H"), args[2], args[2],)),))))
            results.append((rhs, "Mathlib: ChartedSpace_liftPropAt_iff"))
        except Exception:
            pass
    return results


def _r0072_liftProp_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ChartedSpace.liftProp_iff
    # LiftProp P f ↔       Continuous f ∧ ∀ x, P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) univ (chartAt H x x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LiftProp", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("Continuous", (args[1],)), OOp("forall", (OVar("x"), args[0], OOp("comp", (OOp("chartAt", (OVar("H_prime"), OOp("f", (OVar("x"),)),)), OOp("comp", (args[1], OVar("chartAt_H_x_symm"))))), OVar("univ"), OOp("chartAt", (OVar("H"), OVar("x"), OVar("x"),)),))))
            results.append((rhs, "Mathlib: ChartedSpace_liftProp_iff"))
        except Exception:
            pass
    return results


def _r0073_liftPropWithinAt_subtypeVal_comp_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    # LiftPropWithinAt P (Subtype.val ∘ f) s x ↔ LiftPropWithinAt P f s x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LiftPropWithinAt", 4)
    if args is not None:
        try:
            rhs = OOp("LiftPropWithinAt", (args[0], OVar("f"), args[2], args[3],))
            results.append((rhs, "Mathlib: ChartedSpace_liftPropWithinAt_subtypeVal_comp_iff"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_string rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "**", "+", "-", "//", "<", "<=", "CharP", "CharZero", "Fintype_card", "IM", "IN", "IsNat", "IsOpen", "IsUnit", "LiftProp", "LiftPropAt", "LiftPropWithinAt", "M", "R", "RingHom_ker", "StarAlgHom_id", "Subring_center", "_2", "a", "algebraMap", "b", "characterSpace", "chi", "comp", "compContinuousMap", "concat", "continuousMapEval", "dual", "exists", "f", "f_rTensor", "g_comp", "hg_comp", "homEquiv_symm_toLinearMap", "homeoEval_Y_colon_C_comp", "iff", "in", "is_prefix", "is_suffix", "k", "leftpad", "len", "locallyRingedSpaceMap", "locallyRingedSpaceMapAux_f_hf_stalkMap",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_string axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_string rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_cast_eq_mod(term, ctx))
    results.extend(_r0001_natCast_eq_ite(term, ctx))
    results.extend(_r0002_dual_rTensor_conj_homEquiv(term, ctx))
    results.extend(_r0003_eq_neg_self_iff(term, ctx))
    results.extend(_r0004_equivAlgHom_symm_coe(term, ctx))
    results.extend(_r0005_asString_nil(term, ctx))
    results.extend(_r0006_length_eq_list_length(term, ctx))
    results.extend(_r0007_leftpad_prefix(term, ctx))
    results.extend(_r0008_ext(term, ctx))
    results.extend(_r0009_natCast_eq_natCast_mod(term, ctx))
    results.extend(_r0010_natCast_eq_natCast(term, ctx))
    results.extend(_r0011_ringChar_of_prime_eq_zero(term, ctx))
    results.extend(_r0012_charP_iff_prime_eq_zero(term, ctx))
    results.extend(_r0013_cast_eq_zero(term, ctx))
    results.extend(_r0014_cast_eq_iff_mod_eq(term, ctx))
    results.extend(_r0015_ofNat_eq_zero(term, ctx))
    results.extend(_r0016_eq(term, ctx))
    results.extend(_r0017_ringChar_zero_iff_CharZero(term, ctx))
    results.extend(_r0018_intCast_mul_natCast_gcdA_eq_gcd(term, ctx))
    results.extend(_r0019_natCast_gcdA_mul_intCast_eq_gcd(term, ctx))
    results.extend(_r0020_ker_intAlgebraMap_eq_span(term, ctx))
    results.extend(_r0021_quotient_iff(term, ctx))
    results.extend(_r0022_two_eq_zero(term, ctx))
    results.extend(_r0023_natCast_cases(term, ctx))
    results.extend(_r0024_natCast_eq_mod(term, ctx))
    results.extend(_r0025_ofNat_eq_mod(term, ctx))
    results.extend(_r0026_ext(term, ctx))
    results.extend(_r0027_smul_apply(term, ctx))
    results.extend(_r0028_dual_comp(term, ctx))
    results.extend(_r0029_neg_eq_self_iff(term, ctx))
    results.extend(_r0030_exists_apply_eq_zero(term, ctx))
    results.extend(_r0031_mem_spectrum_iff_exists(term, ctx))
    results.extend(_r0032_compContinuousMap_id(term, ctx))
    results.extend(_r0033_compContinuousMap_comp(term, ctx))
    results.extend(_r0034_homeoEval_naturality(term, ctx))
    results.extend(_r0035_equivAlgHom_coe(term, ctx))
    results.extend(_r0036_ltb_cons_addChar(term, ctx))
    results.extend(_r0037_lt_iff_toList_lt(term, ctx))
    results.extend(_r0038_asString_toList(term, ctx))
    results.extend(_r0039_toList_nonempty(term, ctx))
    results.extend(_r0040_head_empty(term, ctx))
    results.extend(_r0041_ofList_eq(term, ctx))
    results.extend(_r0042_congr_append(term, ctx))
    results.extend(_r0043_length_replicate(term, ctx))
    results.extend(_r0044_length_leftpad(term, ctx))
    results.extend(_r0045_leftpad_suffix(term, ctx))
    results.extend(_r0046_sq_add_sq(term, ctx))
    results.extend(_r0047_stalkMap_locallyRingedSpaceMapAux(term, ctx))
    results.extend(_r0048_stalkMap_locallyRingedSpaceMap_evalHom(term, ctx))
    results.extend(_r0049_locallyRingedSpace_id(term, ctx))
    results.extend(_r0050_locallyRingedSpace_comp(term, ctx))
    results.extend(_r0051_orderOf_eq_two_iff(term, ctx))
    results.extend(_r0052_card_pow_char_pow(term, ctx))
    results.extend(_r0053_card_pow_card(term, ctx))
    results.extend(_r0054_isNat_pow(term, ctx))
    results.extend(_r0055_intCast_eq_mod(term, ctx))
    results.extend(_r0056_neg_eq_sub_one_mul(term, ctx))
    results.extend(_r0057_neg_mul_eq_sub_one_mul(term, ctx))
    results.extend(_r0058_coe_coe(term, ctx))
    results.extend(_r0059_coe_toCLM(term, ctx))
    results.extend(_r0060_coe_toNonUnitalAlgHom(term, ctx))
    results.extend(_r0061_union_zero(term, ctx))
    results.extend(_r0062_continuousMapEval_apply_apply(term, ctx))
    results.extend(_r0063_isOpen_iff(term, ctx))
    results.extend(_r0064_charZero_iff_forall_prime_ne_zero(term, ctx))
    results.extend(_r0065_isUnit_natCast_iff(term, ctx))
    results.extend(_r0066_isUnit_ofNat_iff(term, ctx))
    results.extend(_r0067_isUnit_intCast_iff(term, ctx))
    results.extend(_r0068_quotient_iff_le_ker_natCast(term, ctx))
    results.extend(_r0069_charP_center_iff(term, ctx))
    results.extend(_r0070_le_iff_toList_le(term, ctx))
    results.extend(_r0071_liftPropAt_iff(term, ctx))
    results.extend(_r0072_liftProp_iff(term, ctx))
    results.extend(_r0073_liftPropWithinAt_subtypeVal_comp_iff(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_string rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("CharP_dvd_of_ringHom", "q_p", "Not an equality or iff proposition"),
    ("CharP_of_ringHom_of_ne_zero", "CharP_A_p", "Not an equality or iff proposition"),
    ("CharP_natCast_eq_natCast", "_unknown", "Empty proposition"),
    ("CharP_natCast_injOn_Iio", "Set_Iio_p_InjOn_colon_to_R", "Not an equality or iff proposition"),
    ("CharP_cast_ne_zero_of_ne_of_prime", "q_colon_R_ne_0", "Not an equality or iff proposition"),
    ("CharP_ofNat_eq_zero", "_unknown", "Empty proposition"),
    ("CharP_congr", "CharP_R_q", "Not an equality or iff proposition"),
    ("CharP_neg_one_ne_one", "minus_1_colon_R_ne_1_colon_R", "Not an equality or iff proposition"),
    ("CharOne_subsingleton", "Subsingleton_R", "Not an equality or iff proposition"),
    ("CharP_char_ne_zero_of_finite", "p_ne_0", "Not an equality or iff proposition"),
    ("CharP_ringChar_ne_zero_of_finite", "ringChar_R_ne_0", "Not an equality or iff proposition"),
    ("CharP_quotient", "CharP_R_Ideal_span_p_colon_R_colon_Set_R_colon_Ideal_R_p", "Not an equality or iff proposition"),
    ("CharP_quotient", "_unknown", "Empty proposition"),
    ("CharTwo_of_one_ne_zero_of_two_eq_zero", "CharP_R_2", "Not an equality or iff proposition"),
    ("CharTwo_range_natCast", "Set_range_colon_to_R_eq_0_1", "Not an equality or iff proposition"),
    ("CharZero_of_addMonoidHom", "CharZero_N", "Not an equality or iff proposition"),
    ("CharacterModule_dual_zero", "dual_0_colon_A_to_R_B_eq_0", "Not an equality or iff proposition"),
    ("CharacterModule_dual_injective_of_surjective", "Function_Injective_dual_f", "Not an equality or iff proposition"),
    ("CharacterModule_dual_surjective_of_injective", "Function_Surjective_dual_f", "Not an equality or iff proposition"),
    ("CharZero_of_module", "CharZero_R", "Not an equality or iff proposition"),
    ("CharZero_of_isAddTorsionFree", "CharZero_R", "Not an equality or iff proposition"),
    ("WeakDual_CharacterSpace_norm_le_norm_one", "toStrongDual_phi_colon_WeakDual_A_le_1_colon_A", "Not an equality or iff proposition"),
    ("String_ltb_cons_addChar", "_unknown", "Empty proposition"),
    ("ChartedSpace_secondCountable_of_countable_cover", "SecondCountableTopology_M", "Not an equality or iff proposition"),
    ("ChartedSpace_secondCountable_of_sigmaCompact", "SecondCountableTopology_M", "Not an equality or iff proposition"),
    ("ChartedSpace_locallyCompactSpace", "LocallyCompactSpace_M", "Not an equality or iff proposition"),
    ("ChartedSpace_locallyConnectedSpace", "LocallyConnectedSpace_M", "Not an equality or iff proposition"),
    ("ChartedSpace_locPathConnectedSpace", "LocPathConnectedSpace_M", "Not an equality or iff proposition"),
    ("ChartedSpace_t1Space", "T1Space_M", "Not an equality or iff proposition"),
    ("ChartedSpace_discreteTopology", "DiscreteTopology_M", "Not an equality or iff proposition"),
    ("ChartedSpace_sum_chartAt_inl", "haveI_colon_Nonempty_H", "Not an equality or iff proposition"),
    ("ChartedSpace_sum_chartAt_inr", "haveI_colon_Nonempty_H", "Not an equality or iff proposition"),
    ("ChartedSpace_mem_atlas_sum", "exists_f_colon_OpenPartialHomeomorph_M_H_f_in_atlas_H_M_and_e_eq_f_lift_openEmbedd", "Not an equality or iff proposition"),
    ("ChartedSpaceCore_open_source", "_unknown", "Empty proposition"),
    ("ChartedSpaceCore_open_target", "IsOpen_e_target", "Not an equality or iff proposition"),
    ("CharP_addOrderOf_one", "CharP_R_addOrderOf_1_colon_R", "Not an equality or iff proposition"),
    ("Tactic_ReduceModChar_CharP_isInt_of_mod", "IsInt_e_r", "Not an equality or iff proposition"),
    ("WeakDual_CharacterSpace_union_zero_isClosed", "IsClosed_characterSpace_A_union_0", "Not an equality or iff proposition"),
]
