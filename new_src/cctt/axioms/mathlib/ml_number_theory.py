"""Mathlib: Number Theory — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 233 untranslatable theorems stored for reference.
(Truncated from more rules to keep file manageable)
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

AXIOM_NAME = "mathlib_ml_number_theory"
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
# Rewrite rules (400 total)
# ════════════════════════════════════════════════════════════

def _r0000_prod_ofPNatList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.prod_ofPNatList
    # (ofPNatList l h).prod = l.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofPNatList_l_h_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_prod")
            results.append((rhs, "Mathlib: PrimeMultiset_prod_ofPNatList"))
    except Exception:
        pass
    return results


def _r0001_prod_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.prod_add
    # (u + v).prod = u.prod * v.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("u_plus_v_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("u_prod"), OVar("v_prod")))
            results.append((rhs, "Mathlib: PrimeMultiset_prod_add"))
    except Exception:
        pass
    return results


def _r0002_val_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.val_natCast
    # (a : ZMod n).val = a % n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_ZMod_n_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a", (OVar("_unknown"), OVar("n"),))
            results.append((rhs, "Mathlib: ZMod_val_natCast"))
    except Exception:
        pass
    return results


def _r0003_natCast_pow_eq_zero_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.natCast_pow_eq_zero_of_le
    # (p ^ m : ZMod (p ^ n)) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ZMod_natCast_pow_eq_zero_of_le"))
        except Exception:
            pass
    return results


def _r0004_castHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.castHom_comp
    # (castHom hm (ZMod n)).comp (castHom hd (ZMod m)) = castHom (dvd_trans hm hd) (ZMod n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castHom_hm_ZMod_n_comp", 1)
    if args is not None:
        try:
            rhs = OOp("castHom", (OOp("dvd_trans", (OVar("hm"), OVar("hd"),)), OOp("ZMod", (OVar("n"),)),))
            results.append((rhs, "Mathlib: ZMod_castHom_comp"))
        except Exception:
            pass
    return results


def _r0005_lift_castAddHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.lift_castAddHom
    # lift n f (Int.castAddHom (ZMod n) x) = f.1 x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 3)
    if args is not None:
        try:
            rhs = OOp("f_1", (OVar("x"),))
            results.append((rhs, "Mathlib: ZMod_lift_castAddHom"))
        except Exception:
            pass
    return results


def _r0006_lift_comp_castAddHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.lift_comp_castAddHom
    # (ZMod.lift n f).comp (Int.castAddHom (ZMod n)) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ZMod_lift_n_f_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ZMod_lift_comp_castAddHom"))
        except Exception:
            pass
    return results


def _r0007_lift_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.lift_injective
    # Injective (lift n f) ↔ ∀ m, f.1 m = 0 → (m : ZMod n) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ZMod_lift_injective"))
        except Exception:
            pass
    return results


def _r0008_valMinAbs_def_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_def_pos
    # ∀ {n : ℕ} [NeZero n] (x : ZMod n),     valMinAbs x = if x.val ≤ n / 2 then (x.val : ℤ) else x.val - n   | 0, _, x =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "valMinAbs", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("if", (OVar("x_val"),)), OOp("-", (OOp("//", (OVar("n"), OOp("_2", (OVar("then"), OOp("x_val", (OVar("colon"), OVar("_unknown"),)), OVar("else"), OVar("x_val"),)))), OOp("n", (OVar("pipe"), OVar("_0"), OVar("_unknown"), args[0], OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: ZMod_valMinAbs_def_pos"))
        except Exception:
            pass
    return results


def _r0009_natCast_natAbs_valMinAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.natCast_natAbs_valMinAbs
    # (a.valMinAbs.natAbs : ZMod n) = if a.val ≤ (n : ℕ) / 2 then a else -a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_valMinAbs_natAbs", 3)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("if", (OVar("a_val"),)), OOp("//", (OOp("n", (args[0], OVar("_unknown"),)), OOp("_2", (OVar("then"), OVar("a"), OVar("else"), OVar("minus_a"),))))))
            results.append((rhs, "Mathlib: ZMod_natCast_natAbs_valMinAbs"))
        except Exception:
            pass
    return results


def _r0010_pow_card_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.pow_card_pow
    # x ^ p ^ n = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ZMod_pow_card_pow"))
        except Exception:
            pass
    return results


def _r0011_completedLFunction_const_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.completedLFunction_const_mul
    # completedLFunction (fun j ↦ a * Φ j) s = a * completedLFunction Φ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completedLFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), OOp("completedLFunction", (OVar("_unknown"), args[1],))))
            results.append((rhs, "Mathlib: ZMod_completedLFunction_const_mul"))
        except Exception:
            pass
    return results


def _r0012_continuousAddCharEquiv_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.continuousAddCharEquiv_symm_apply
    # (continuousAddCharEquiv p R).symm ⟨r, hr⟩ =     (addChar_of_value_at_one r hr : AddChar ℤ_[p] R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "continuousAddCharEquiv_p_R_symm", 1)
    if args is not None:
        try:
            rhs = OOp("addChar_of_value_at_one", (OVar("r"), OVar("hr"), OVar("colon"), OVar("AddChar"), OVar("p"), OVar("R"),))
            results.append((rhs, "Mathlib: PadicInt_continuousAddCharEquiv_symm_apply"))
        except Exception:
            pass
    return results


def _r0013_continuousAddCharEquiv_of_norm_mul_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.continuousAddCharEquiv_of_norm_mul_symm_apply
    # (continuousAddCharEquiv_of_norm_mul p R).symm ⟨r, hr⟩ = (addChar_of_value_at_one r     (tendsto_pow_atTop_nhds_zero_iff_
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "continuousAddCharEquiv_of_norm_mul_p_R_symm", 1)
    if args is not None:
        try:
            rhs = OOp("addChar_of_value_at_one", (OVar("r"), OOp("tendsto_pow_atTop_nhds_zero_iff_norm_lt_one_mpr", (OVar("hr"),)), OVar("colon"), OVar("AddChar"), OVar("p"), OVar("R"),))
            results.append((rhs, "Mathlib: PadicInt_continuousAddCharEquiv_of_norm_mul_symm_apply"))
        except Exception:
            pass
    return results


def _r0014_norm_extends(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicAlgCl.norm_extends
    # ‖(x : PadicAlgCl p)‖ = ‖x‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_colon_PadicAlgCl_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x")
            results.append((rhs, "Mathlib: PadicAlgCl_norm_extends"))
    except Exception:
        pass
    return results


def _r0015_valuation_p(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicAlgCl.valuation_p
    # Valued.v (p : PadicAlgCl p) = 1 / (p : ℝ≥0)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Valued_v", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OLit(1), OOp("p", (OVar("colon"), OVar("ge_0"),))))
            results.append((rhs, "Mathlib: PadicAlgCl_valuation_p"))
        except Exception:
            pass
    return results


def _r0016_coe_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicComplex.coe_natCast
    # ((n : PadicAlgCl p) : ℂ_[p]) = (n : ℂ_[p])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_colon_PadicAlgCl_p", 2)
    if args is not None:
        try:
            rhs = OOp("n", (args[0], args[1],))
            results.append((rhs, "Mathlib: PadicComplex_coe_natCast"))
        except Exception:
            pass
    return results


def _r0017_coe_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_add
    # ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z1_plus_z2_colon_p", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("z1"), OVar("z2")))
            results.append((rhs, "Mathlib: PadicInt_coe_add"))
        except Exception:
            pass
    return results


def _r0018_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_mul
    # ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z1_star_z2_colon_p", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("z1"), OVar("z2")))
            results.append((rhs, "Mathlib: PadicInt_coe_mul"))
        except Exception:
            pass
    return results


def _r0019_coe_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_neg
    # ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_z1_colon_p", 2)
    if args is not None:
        try:
            rhs = OVar("minus_z1")
            results.append((rhs, "Mathlib: PadicInt_coe_neg"))
        except Exception:
            pass
    return results


def _r0020_coe_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_sub
    # ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z1_minus_z2_colon_p", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("z1"), OVar("z2")))
            results.append((rhs, "Mathlib: PadicInt_coe_sub"))
        except Exception:
            pass
    return results


def _r0021_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_one
    # ((1 : ℤ_[p]) : ℚ_[p]) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_p", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PadicInt_coe_one"))
        except Exception:
            pass
    return results


def _r0022_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_zero
    # ((0 : ℤ_[p]) : ℚ_[p]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_p", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PadicInt_coe_zero"))
        except Exception:
            pass
    return results


def _r0023_coe_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_eq_zero
    # (x : ℚ_[p]) = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("x"))), OLit(0)))
            results.append((rhs, "Mathlib: PadicInt_coe_eq_zero"))
        except Exception:
            pass
    return results


def _r0024_coe_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_natCast
    # ((n : ℤ_[p]) : ℚ_[p]) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_colon_p", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: PadicInt_coe_natCast"))
        except Exception:
            pass
    return results


def _r0025_coe_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_intCast
    # ((z : ℤ_[p]) : ℚ_[p]) = z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z_colon_p", 2)
    if args is not None:
        try:
            rhs = OVar("z")
            results.append((rhs, "Mathlib: PadicInt_coe_intCast"))
        except Exception:
            pass
    return results


def _r0026_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_pow
    # (↑(x ^ n) : ℚ_[p]) = (↑x : ℚ_[p]) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_pow_n", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("x", (args[0], args[1],)), OVar("n")))
            results.append((rhs, "Mathlib: PadicInt_coe_pow"))
        except Exception:
            pass
    return results


def _r0027_mk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.mk_coe
    # (⟨k, k.2⟩ : ℤ_[p]) = k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "k_k_2", 2)
    if args is not None:
        try:
            rhs = OVar("k")
            results.append((rhs, "Mathlib: PadicInt_mk_coe"))
        except Exception:
            pass
    return results


def _r0028_norm_intCast_eq_padic_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_intCast_eq_padic_norm
    # ‖(z : ℤ_[p])‖ = ‖(z : ℚ_[p])‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z_colon_p")
            results.append((rhs, "Mathlib: PadicInt_norm_intCast_eq_padic_norm"))
    except Exception:
        pass
    return results


def _r0029_norm_p(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_p
    # ‖(p : ℤ_[p])‖ = (p : ℝ)⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_colon_inv")
            results.append((rhs, "Mathlib: PadicInt_norm_p"))
    except Exception:
        pass
    return results


def _r0030_norm_p_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_p_pow
    # ‖(p : ℤ_[p]) ^ n‖ = (p : ℝ) ^ (-n : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("p", (OVar("colon"), OVar("_unknown"),)), OOp("minus_n", (OVar("colon"), OVar("_unknown"),))))
            results.append((rhs, "Mathlib: PadicInt_norm_p_pow"))
        except Exception:
            pass
    return results


def _r0031_valuation_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.valuation_zero
    # valuation (0 : ℤ_[p]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "valuation", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PadicInt_valuation_zero"))
        except Exception:
            pass
    return results


def _r0032_valuation_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.valuation_one
    # valuation (1 : ℤ_[p]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "valuation", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PadicInt_valuation_one"))
        except Exception:
            pass
    return results


def _r0033_valuation_p(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.valuation_p
    # valuation (p : ℤ_[p]) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "valuation", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PadicInt_valuation_p"))
        except Exception:
            pass
    return results


def _r0034_norm_eq_zpow_neg_valuation(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_eq_zpow_neg_valuation
    # ‖x‖ = p ^ (-x.valuation : ℤ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("p"), OOp("minus_x_valuation", (OVar("colon"), OVar("_unknown"),))))
            results.append((rhs, "Mathlib: PadicInt_norm_eq_zpow_neg_valuation"))
    except Exception:
        pass
    return results


def _r0035_mkUnits_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.mkUnits_eq
    # ((mkUnits h : ℤ_[p]) : ℚ_[p]) = u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mkUnits_h_colon_p", 2)
    if args is not None:
        try:
            rhs = OVar("u")
            results.append((rhs, "Mathlib: PadicInt_mkUnits_eq"))
        except Exception:
            pass
    return results


def _r0036_unitCoeff_spec(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.unitCoeff_spec
    # x = (unitCoeff hx : ℤ_[p]) * (p : ℤ_[p]) ^ x.valuation
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OOp("unitCoeff", (OVar("hx"), OVar("colon"), OVar("p"),)), OOp("**", (OOp("p", (OVar("colon"), OVar("p"),)), OVar("x_valuation")))))
            results.append((rhs, "Mathlib: PadicInt_unitCoeff_spec"))
    except Exception:
        pass
    return results


def _r0037_norm_p_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_p_pow
    # ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-n : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("p", (OVar("colon"), OVar("_unknown"),)), OOp("minus_n", (OVar("colon"), OVar("_unknown"),))))
            results.append((rhs, "Mathlib: Padic_norm_p_pow"))
        except Exception:
            pass
    return results


def _r0038_im_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_zero
    # (0 : ℤ√d).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_d_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Zsqrtd_im_zero"))
    except Exception:
        pass
    return results


def _r0039_im_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_one
    # (1 : ℤ√d).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_d_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Zsqrtd_im_one"))
    except Exception:
        pass
    return results


def _r0040_im_sqrtd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_sqrtd
    # (sqrtd : ℤ√d).im = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sqrtd_colon_d_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Zsqrtd_im_sqrtd"))
    except Exception:
        pass
    return results


def _r0041_re_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_add
    # (z + w).re = z.re + w.re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_plus_w_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("z_re"), OVar("w_re")))
            results.append((rhs, "Mathlib: Zsqrtd_re_add"))
    except Exception:
        pass
    return results


def _r0042_im_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_add
    # (z + w).im = z.im + w.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_plus_w_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("z_im"), OVar("w_im")))
            results.append((rhs, "Mathlib: Zsqrtd_im_add"))
    except Exception:
        pass
    return results


def _r0043_im_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_neg
    # (-z).im = -z.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_z_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_z_im")
            results.append((rhs, "Mathlib: Zsqrtd_im_neg"))
    except Exception:
        pass
    return results


def _r0044_im_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_mul
    # (z * w).im = z.re * w.im + z.im * w.re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_star_w_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OOp("*", (OVar("z_re"), OVar("w_im"))), OOp("*", (OVar("z_im"), OVar("w_re")))))
            results.append((rhs, "Mathlib: Zsqrtd_im_mul"))
    except Exception:
        pass
    return results


def _r0045_im_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_sub
    # (z - w).im = z.im - w.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_minus_w_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("z_im"), OVar("w_im")))
            results.append((rhs, "Mathlib: Zsqrtd_im_sub"))
    except Exception:
        pass
    return results


def _r0046_re_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_star
    # (star z).re = z.re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("star_z_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z_re")
            results.append((rhs, "Mathlib: Zsqrtd_re_star"))
    except Exception:
        pass
    return results


def _r0047_im_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_star
    # (star z).im = -z.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("star_z_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_z_im")
            results.append((rhs, "Mathlib: Zsqrtd_im_star"))
    except Exception:
        pass
    return results


def _r0048_re_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_ofNat
    # (ofNat(n) : ℤ√d).re = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon_d_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Zsqrtd_re_ofNat"))
    except Exception:
        pass
    return results


def _r0049_im_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_natCast
    # (n : ℤ√d).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_d_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Zsqrtd_im_natCast"))
    except Exception:
        pass
    return results


def _r0050_im_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_ofNat
    # (ofNat(n) : ℤ√d).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon_d_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Zsqrtd_im_ofNat"))
    except Exception:
        pass
    return results


def _r0051_natCast_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.natCast_val
    # (n : ℤ√d) = ⟨n, 0⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OVar("n_0")
            results.append((rhs, "Mathlib: Zsqrtd_natCast_val"))
        except Exception:
            pass
    return results


def _r0052_im_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_intCast
    # (n : ℤ√d).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_d_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Zsqrtd_im_intCast"))
    except Exception:
        pass
    return results


def _r0053_intCast_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.intCast_val
    # (n : ℤ√d) = ⟨n, 0⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OVar("n_0")
            results.append((rhs, "Mathlib: Zsqrtd_intCast_val"))
        except Exception:
            pass
    return results


def _r0054_nsmul_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.nsmul_val
    # (n : ℤ√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("n_star_x_n_star_y")
            results.append((rhs, "Mathlib: Zsqrtd_nsmul_val"))
        except Exception:
            pass
    return results


def _r0055_smul_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.smul_val
    # (n : ℤ√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("n_star_x_n_star_y")
            results.append((rhs, "Mathlib: Zsqrtd_smul_val"))
        except Exception:
            pass
    return results


def _r0056_re_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_smul
    # (↑a * b).re = a * b.re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_star_b_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("a"), OVar("b_re")))
            results.append((rhs, "Mathlib: Zsqrtd_re_smul"))
    except Exception:
        pass
    return results


def _r0057_dmuld(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.dmuld
    # sqrtd (d := d) * sqrtd (d := d) = d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("d")
            results.append((rhs, "Mathlib: Zsqrtd_dmuld"))
        except Exception:
            pass
    return results


def _r0058_smuld_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.smuld_val
    # sqrtd * (n : ℤ√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("d_star_n_star_y_n_star_x")
            results.append((rhs, "Mathlib: Zsqrtd_smuld_val"))
        except Exception:
            pass
    return results


def _r0059_decompose(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.decompose
    # (⟨x, y⟩ : ℤ√d) = x + sqrtd (d := d) * y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_y", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("x"), OOp("*", (OOp("sqrtd", (OOp("d", (OVar("colon_eq"), args[1],)),)), OVar("y")))))
            results.append((rhs, "Mathlib: Zsqrtd_decompose"))
        except Exception:
            pass
    return results


def _r0060_zeroLocus_span(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.zeroLocus_span
    # zeroLocus (Ideal.span s : Set R) = zeroLocus s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zeroLocus", 1)
    if args is not None:
        try:
            rhs = OOp("zeroLocus", (OVar("s"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_zeroLocus_span"))
        except Exception:
            pass
    return results


def _r0061_map_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.BasicConstructibleSetData.map_comp
    # C.map (φ.comp ψ) = (C.map ψ).map φ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "C_map", 1)
    if args is not None:
        try:
            rhs = OOp("C_map_psi_map", (OVar("phi"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_BasicConstructibleSetData_map_comp"))
        except Exception:
            pass
    return results


def _r0062_map_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.ConstructibleSetData.map_comp
    # s.map (f.comp g) = (s.map g).map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_map", 1)
    if args is not None:
        try:
            rhs = OOp("s_map_g_map", (OVar("f"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_ConstructibleSetData_map_comp"))
        except Exception:
            pass
    return results


def _r0063_toAddCircle_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.toAddCircle_eq_zero
    # toAddCircle j = 0 ↔ j = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAddCircle", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: ZMod_toAddCircle_eq_zero"))
        except Exception:
            pass
    return results


def _r0064_valMinAbs_nonneg_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_nonneg_iff
    # 0 ≤ x.valMinAbs ↔ x.val ≤ n / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("x_val"), OOp("//", (OVar("n"), OLit(2)))))
            results.append((rhs, "Mathlib: ZMod_valMinAbs_nonneg_iff"))
        except Exception:
            pass
    return results


def _r0065_coe_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_ne_zero
    # (x : ℚ_[p]) ≠ 0 ↔ x ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("x"), OLit(0)))
            results.append((rhs, "Mathlib: PadicInt_coe_ne_zero"))
        except Exception:
            pass
    return results


def _r0066_subset_zeroLocus_iff_le_vanishingIdeal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal
    # t ⊆ zeroLocus I ↔ I ≤ vanishingIdeal t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("I"), OOp("vanishingIdeal", (args[0],))))
            results.append((rhs, "Mathlib: PrimeSpectrum_subset_zeroLocus_iff_le_vanishingIdeal"))
        except Exception:
            pass
    return results


def _r0067_asIdeal_lt_asIdeal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.asIdeal_lt_asIdeal
    # x.asIdeal < y.asIdeal ↔ x < y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: PrimeSpectrum_asIdeal_lt_asIdeal"))
        except Exception:
            pass
    return results


def _r0068_mul_inv_cancel_aux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.mul_inv_cancel_aux
    # a * a⁻¹ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_mul_inv_cancel_aux"))
        except Exception:
            pass
    return results


def _r0069_map_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.map_smul
    # f (c • x) = c • f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OVar("f"), OVar("x"),))
            results.append((rhs, "Mathlib: ZMod_map_smul"))
        except Exception:
            pass
    return results


def _r0070_auxDFT_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.auxDFT_neg
    # auxDFT (fun j ↦ Φ (-j)) = fun k ↦ auxDFT Φ (-k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "auxDFT", 1)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("k"), OVar("_unknown"), OVar("auxDFT"), OVar("_unknown"), OVar("minus_k"),))
            results.append((rhs, "Mathlib: ZMod_auxDFT_neg"))
        except Exception:
            pass
    return results


def _r0071_auxDFT_auxDFT(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.auxDFT_auxDFT
    # auxDFT (auxDFT Φ) = fun j ↦ (N : ℂ) • Φ (-j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "auxDFT", 1)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("j"), OVar("_unknown"), OOp("N", (OVar("colon"), OVar("_unknown"),)), OVar("_unknown"), OVar("_unknown"), OVar("minus_j"),))
            results.append((rhs, "Mathlib: ZMod_auxDFT_auxDFT"))
        except Exception:
            pass
    return results


def _r0072_auxDFT_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.auxDFT_smul
    # auxDFT (c • Φ) = c • auxDFT Φ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "auxDFT", 1)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OVar("auxDFT"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: ZMod_auxDFT_smul"))
        except Exception:
            pass
    return results


def _r0073_toCircle_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.toCircle_intCast
    # toCircle (j : ZMod N) = exp (2 * π * I * j / N)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCircle", 1)
    if args is not None:
        try:
            rhs = OOp("exp", (OOp("*", (OLit(2), OOp("*", (OVar("pi"), OOp("*", (OVar("I"), OOp("//", (OVar("j"), OVar("N"))))))))),))
            results.append((rhs, "Mathlib: ZMod_toCircle_intCast"))
        except Exception:
            pass
    return results


def _r0074_toCircle_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.toCircle_natCast
    # toCircle (j : ZMod N) = exp (2 * π * I * j / N)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCircle", 1)
    if args is not None:
        try:
            rhs = OOp("exp", (OOp("*", (OLit(2), OOp("*", (OVar("pi"), OOp("*", (OVar("I"), OOp("//", (OVar("j"), OVar("N"))))))))),))
            results.append((rhs, "Mathlib: ZMod_toCircle_natCast"))
        except Exception:
            pass
    return results


def _r0075_toCircle_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.toCircle_apply
    # toCircle j = exp (2 * π * I * j.val / N)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCircle", 1)
    if args is not None:
        try:
            rhs = OOp("exp", (OOp("*", (OLit(2), OOp("*", (OVar("pi"), OOp("*", (OVar("I"), OOp("//", (OVar("j_val"), OVar("N"))))))))),))
            results.append((rhs, "Mathlib: ZMod_toCircle_apply"))
        except Exception:
            pass
    return results


def _r0076_toCircle_eq_circleExp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.toCircle_eq_circleExp
    # toCircle j = Circle.exp (2 * π * (j.val / N))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCircle", 1)
    if args is not None:
        try:
            rhs = OOp("Circle_exp", (OOp("*", (OLit(2), OOp("*", (OVar("pi"), OOp("//", (OVar("j_val"), OVar("N"))))))),))
            results.append((rhs, "Mathlib: ZMod_toCircle_eq_circleExp"))
        except Exception:
            pass
    return results


def _r0077_stdAddChar_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.stdAddChar_coe
    # stdAddChar (j : ZMod N) = exp (2 * π * I * j / N)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stdAddChar", 1)
    if args is not None:
        try:
            rhs = OOp("exp", (OOp("*", (OLit(2), OOp("*", (OVar("pi"), OOp("*", (OVar("I"), OOp("//", (OVar("j"), OVar("N"))))))))),))
            results.append((rhs, "Mathlib: ZMod_stdAddChar_coe"))
        except Exception:
            pass
    return results


def _r0078_stdAddChar_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.stdAddChar_apply
    # stdAddChar j = ↑(toCircle j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stdAddChar", 1)
    if args is not None:
        try:
            rhs = OVar("toCircle_j")
            results.append((rhs, "Mathlib: ZMod_stdAddChar_apply"))
        except Exception:
            pass
    return results


def _r0079_rootsOfUnityAddChar_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.rootsOfUnityAddChar_val
    # (rootsOfUnityAddChar n x).val = toCircle x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("rootsOfUnityAddChar_n_x_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("toCircle", (OVar("x"),))
            results.append((rhs, "Mathlib: ZMod_rootsOfUnityAddChar_val"))
    except Exception:
        pass
    return results


def _r0080_erdos_ginzburg_ziv_prime(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.erdos_ginzburg_ziv_prime
    # ∃ t ⊆ s, #t = p ∧ ∑ i ∈ t, a i = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OVar("p"), OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("t", (OVar("a"), OVar("i"),)))))), OLit(0)))
            results.append((rhs, "Mathlib: ZMod_erdos_ginzburg_ziv_prime"))
        except Exception:
            pass
    return results


def _r0081_erdos_ginzburg_ziv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.erdos_ginzburg_ziv
    # ∃ t ⊆ s, #t = n ∧ ∑ i ∈ t, a i = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OVar("n"), OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("t", (OVar("a"), OVar("i"),)))))), OLit(0)))
            results.append((rhs, "Mathlib: ZMod_erdos_ginzburg_ziv"))
        except Exception:
            pass
    return results


def _r0082_erdos_ginzburg_ziv_multiset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.erdos_ginzburg_ziv_multiset
    # ∃ t ≤ s, Multiset.card t = n ∧ t.sum = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OVar("n"), OVar("t_sum"))), OLit(0)))
            results.append((rhs, "Mathlib: ZMod_erdos_ginzburg_ziv_multiset"))
        except Exception:
            pass
    return results


def _r0083_even_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prime.even_iff
    # Even p ↔ p = 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(2)
            results.append((rhs, "Mathlib: Prime_even_iff"))
        except Exception:
            pass
    return results


def _r0084_mod_two_eq_one_iff_ne_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prime.mod_two_eq_one_iff_ne_two
    # p % 2 = 1 ↔ p ≠ 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OLit(1), OVar("p"))), OLit(2)))
            results.append((rhs, "Mathlib: Prime_mod_two_eq_one_iff_ne_two"))
        except Exception:
            pass
    return results


def _r0085_eq_one_of_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prime.eq_one_of_pow
    # n = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Prime_eq_one_of_pow"))
    except Exception:
        pass
    return results


def _r0086_pow_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prime.pow_eq_iff
    # a ^ k = p ↔ a = p ∧ k = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("p"), args[0])), OOp("==", (OOp("and", (OVar("p"), args[1])), OLit(1)))))
            results.append((rhs, "Mathlib: Prime_pow_eq_iff"))
        except Exception:
            pass
    return results


def _r0087_mul_eq_prime_sq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prime.mul_eq_prime_sq_iff
    # x * y = p ^ 2 ↔ x = p ∧ y = p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("**", (OVar("p"), OLit(2))), args[0])), OOp("==", (OOp("and", (OVar("p"), args[1])), OVar("p")))))
            results.append((rhs, "Mathlib: Prime_mul_eq_prime_sq_iff"))
        except Exception:
            pass
    return results


def _r0088_coe_nat_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Primes.coe_nat_inj
    # (p : ℕ) = (q : ℕ) ↔ p = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("q", (args[0], args[1],)), OVar("p"))), OVar("q")))
            results.append((rhs, "Mathlib: Primes_coe_nat_inj"))
        except Exception:
            pass
    return results


def _r0089_card_ofPrime(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.card_ofPrime
    # Multiset.card (ofPrime p) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PrimeMultiset_card_ofPrime"))
        except Exception:
            pass
    return results


def _r0090_coeNat_ofPrime(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.coeNat_ofPrime
    # (ofPrime p : Multiset ℕ) = {(p : ℕ)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofPrime", 4)
    if args is not None:
        try:
            rhs = OVar("p_colon")
            results.append((rhs, "Mathlib: PrimeMultiset_coeNat_ofPrime"))
        except Exception:
            pass
    return results


def _r0091_coePNat_ofPrime(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.coePNat_ofPrime
    # (ofPrime p : Multiset ℕ+) = {(p : ℕ+)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofPrime", 4)
    if args is not None:
        try:
            rhs = OVar("p_colon_plus")
            results.append((rhs, "Mathlib: PrimeMultiset_coePNat_ofPrime"))
        except Exception:
            pass
    return results


def _r0092_coePNat_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.coePNat_nat
    # ((v : Multiset ℕ+) : Multiset ℕ) = (v : Multiset ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_colon_Multiset_plus", 3)
    if args is not None:
        try:
            rhs = OOp("v", (args[0], args[1], args[2],))
            results.append((rhs, "Mathlib: PrimeMultiset_coePNat_nat"))
        except Exception:
            pass
    return results


def _r0093_coe_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.coe_prod
    # (v.prod : ℕ) = (v : Multiset ℕ).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_prod", 2)
    if args is not None:
        try:
            rhs = OVar("v_colon_Multiset_prod")
            results.append((rhs, "Mathlib: PrimeMultiset_coe_prod"))
        except Exception:
            pass
    return results


def _r0094_prod_ofPrime(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.prod_ofPrime
    # (ofPrime p).prod = (p : ℕ+)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofPrime_p_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p", (OVar("colon"), OVar("plus"),))
            results.append((rhs, "Mathlib: PrimeMultiset_prod_ofPrime"))
    except Exception:
        pass
    return results


def _r0095_to_ofNatMultiset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.to_ofNatMultiset
    # (ofNatMultiset v h : Multiset ℕ) = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNatMultiset", 5)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: PrimeMultiset_to_ofNatMultiset"))
        except Exception:
            pass
    return results


def _r0096_prod_ofNatMultiset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.prod_ofNatMultiset
    # ((ofNatMultiset v h).prod : ℕ) = (v.prod : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNatMultiset_v_h_prod", 2)
    if args is not None:
        try:
            rhs = OOp("v_prod", (args[0], args[1],))
            results.append((rhs, "Mathlib: PrimeMultiset_prod_ofNatMultiset"))
        except Exception:
            pass
    return results


def _r0097_to_ofPNatMultiset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.to_ofPNatMultiset
    # (ofPNatMultiset v h : Multiset ℕ+) = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofPNatMultiset", 5)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: PrimeMultiset_to_ofPNatMultiset"))
        except Exception:
            pass
    return results


def _r0098_prod_ofPNatMultiset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.prod_ofPNatMultiset
    # ((ofPNatMultiset v h).prod : ℕ+) = v.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofPNatMultiset_v_h_prod", 2)
    if args is not None:
        try:
            rhs = OVar("v_prod")
            results.append((rhs, "Mathlib: PrimeMultiset_prod_ofPNatMultiset"))
        except Exception:
            pass
    return results


def _r0099_prod_ofNatList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.prod_ofNatList
    # ((ofNatList l h).prod : ℕ) = l.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNatList_l_h_prod", 2)
    if args is not None:
        try:
            rhs = OVar("l_prod")
            results.append((rhs, "Mathlib: PrimeMultiset_prod_ofNatList"))
        except Exception:
            pass
    return results


def _r0100_toPNatMultiset_ofPNatList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.toPNatMultiset_ofPNatList
    # (ofPNatList l hl : Multiset ℕ+) = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofPNatList", 5)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: PrimeMultiset_toPNatMultiset_ofPNatList"))
        except Exception:
            pass
    return results


def _r0101_prod_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.prod_zero
    # (0 : PrimeMultiset).prod = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_PrimeMultiset_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PrimeMultiset_prod_zero"))
    except Exception:
        pass
    return results


def _r0102_prod_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.prod_smul
    # (d • u).prod = u.prod ^ d
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("d_u_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("u_prod"), OVar("d")))
            results.append((rhs, "Mathlib: PrimeMultiset_prod_smul"))
    except Exception:
        pass
    return results


def _r0103_factorMultiset_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.factorMultiset_prod
    # v.prod.factorMultiset = v
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_prod_factorMultiset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("v")
            results.append((rhs, "Mathlib: PrimeMultiset_factorMultiset_prod"))
    except Exception:
        pass
    return results


def _r0104_prod_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.prod_inf
    # (u ⊓ v).prod = PNat.gcd u.prod v.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("u_v_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("gcd", (OVar("u_prod"), OVar("v_prod"),))
            results.append((rhs, "Mathlib: PrimeMultiset_prod_inf"))
    except Exception:
        pass
    return results


def _r0105_prod_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeMultiset.prod_sup
    # (u ⊔ v).prod = PNat.lcm u.prod v.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("u_v_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("lcm", (OVar("u_prod"), OVar("v_prod"),))
            results.append((rhs, "Mathlib: PrimeMultiset_prod_sup"))
    except Exception:
        pass
    return results


def _r0106_val_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.val_zero
    # ∀ {n}, (0 : ZMod n).val = 0   | 0 => rfl   | _ + 1 => rfl  @[simp] theorem val_one' : (1 : ZMod 0).val = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_ZMod_n_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("+", (OOp("_0", (OVar("pipe"), OLit(0), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"),)), OOp("_1", (OVar("eq_gt"), OVar("rfl_at_simp_theorem"), OVar("val_one_prime"), OVar("colon"), OVar("_1_colon_ZMod_0_val"),)))), OLit(1)))
            results.append((rhs, "Mathlib: ZMod_val_zero"))
    except Exception:
        pass
    return results


def _r0107_val_natCast_of_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.val_natCast_of_lt
    # (a : ZMod n).val = a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_ZMod_n_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: ZMod_val_natCast_of_lt"))
    except Exception:
        pass
    return results


def _r0108_val_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.val_ofNat
    # (ofNat(a) : ZMod n).val = ofNat(a) % n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_a_colon_ZMod_n_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ofNat_a", (OVar("_unknown"), OVar("n"),))
            results.append((rhs, "Mathlib: ZMod_val_ofNat"))
    except Exception:
        pass
    return results


def _r0109_val_ofNat_of_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.val_ofNat_of_lt
    # (ofNat(a) : ZMod n).val = ofNat(a)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_a_colon_ZMod_n_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofNat_a")
            results.append((rhs, "Mathlib: ZMod_val_ofNat_of_lt"))
    except Exception:
        pass
    return results


def _r0110_eq_one_of_isUnit_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.eq_one_of_isUnit_natCast
    # n = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_eq_one_of_isUnit_natCast"))
    except Exception:
        pass
    return results


def _r0111_addOrderOf_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.addOrderOf_one
    # addOrderOf (1 : ZMod n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "addOrderOf", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ZMod_addOrderOf_one"))
        except Exception:
            pass
    return results


def _r0112_addOrderOf_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.addOrderOf_coe
    # addOrderOf (a : ZMod n) = n / n.gcd a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "addOrderOf", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("n"), OOp("n_gcd", (OVar("a"),))))
            results.append((rhs, "Mathlib: ZMod_addOrderOf_coe"))
        except Exception:
            pass
    return results


def _r0113_ringChar_zmod_n(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.ringChar_zmod_n
    # ringChar (ZMod n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ringChar", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ZMod_ringChar_zmod_n"))
        except Exception:
            pass
    return results


def _r0114_natCast_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.natCast_self
    # (n : ZMod n) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ZMod_natCast_self"))
        except Exception:
            pass
    return results


def _r0115_cast_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.cast_zero
    # (cast (0 : ZMod n) : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cast", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ZMod_cast_zero"))
        except Exception:
            pass
    return results


def _r0116_cast_eq_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.cast_eq_val
    # (cast a : R) = a.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cast", 3)
    if args is not None:
        try:
            rhs = OVar("a_val")
            results.append((rhs, "Mathlib: ZMod_cast_eq_val"))
        except Exception:
            pass
    return results


def _r0117_fst_zmod_cast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_zmod_cast
    # (cast a : R × S).fst = cast a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cast_a_colon_R_times_S_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("cast", (OVar("a"),))
            results.append((rhs, "Mathlib: Prod_fst_zmod_cast"))
    except Exception:
        pass
    return results


def _r0118_snd_zmod_cast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_zmod_cast
    # (cast a : R × S).snd = cast a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cast_a_colon_R_times_S_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("cast", (OVar("a"),))
            results.append((rhs, "Mathlib: Prod_snd_zmod_cast"))
    except Exception:
        pass
    return results


def _r0119_ringHom_map_cast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.ringHom_map_cast
    # f (cast k) = k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("k")
            results.append((rhs, "Mathlib: ZMod_ringHom_map_cast"))
        except Exception:
            pass
    return results


def _r0120_castHom_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.castHom_self
    # ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ZMod_castHom", 2)
    if args is not None:
        try:
            rhs = OOp("RingHom_id", (OOp("ZMod", (OVar("n"),)),))
            results.append((rhs, "Mathlib: ZMod_castHom_self"))
        except Exception:
            pass
    return results


def _r0121_lift_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.lift_coe
    # lift n f (x : ZMod n) = f.val x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 3)
    if args is not None:
        try:
            rhs = OOp("f_val", (OVar("x"),))
            results.append((rhs, "Mathlib: ZMod_lift_coe"))
        except Exception:
            pass
    return results


def _r0122_char_nsmul_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZModModule.char_nsmul_eq_zero
    # n • x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ZModModule_char_nsmul_eq_zero"))
        except Exception:
            pass
    return results


def _r0123_periodicPts_add_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZModModule.periodicPts_add_left
    # periodicPts (x + ·) = .univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "periodicPts", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: ZModModule_periodicPts_add_left"))
        except Exception:
            pass
    return results


def _r0124_add_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZModModule.add_self
    # x + x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ZModModule_add_self"))
        except Exception:
            pass
    return results


def _r0125_neg_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZModModule.neg_eq_self
    # -x = x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x")
            results.append((rhs, "Mathlib: ZModModule_neg_eq_self"))
    except Exception:
        pass
    return results


def _r0126_sub_eq_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZModModule.sub_eq_add
    # x - y = x + y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: ZModModule_sub_eq_add"))
        except Exception:
            pass
    return results


def _r0127_add_add_add_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZModModule.add_add_add_cancel
    # (x + y) + (y + z) = x + z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("x"), OVar("z")))
            results.append((rhs, "Mathlib: ZModModule_add_add_add_cancel"))
        except Exception:
            pass
    return results


def _r0128_eq_zero_iff_gcd_ne_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.eq_zero_iff_gcd_ne_one
    # (a : ZMod p) = 0 ↔ a.gcd p ≠ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OLit(0), OOp("a_gcd", (args[2],)))), OLit(1)))
            results.append((rhs, "Mathlib: ZMod_eq_zero_iff_gcd_ne_one"))
        except Exception:
            pass
    return results


def _r0129_eq_zero_of_gcd_ne_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.eq_zero_of_gcd_ne_one
    # (a : ZMod p) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ZMod_eq_zero_of_gcd_ne_one"))
        except Exception:
            pass
    return results


def _r0130_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.card
    # Fintype.card (ZMod n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fintype_card", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ZMod_card"))
        except Exception:
            pass
    return results


def _r0131_cast_descFactorial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.cast_descFactorial
    # (descFactorial (p - 1) n : ZMod p) = (-1) ^ n * n !
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "descFactorial", 5)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), args[1])), OOp("n", (OOp("not", (OVar("_"),)),))))
            results.append((rhs, "Mathlib: ZMod_cast_descFactorial"))
        except Exception:
            pass
    return results


def _r0132_smul_units_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.smul_units_def
    # z • au = z.val • au
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z", 2)
    if args is not None:
        try:
            rhs = OOp("z_val", (args[0], args[1],))
            results.append((rhs, "Mathlib: ZMod_smul_units_def"))
        except Exception:
            pass
    return results


def _r0133_natCast_smul_units(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.natCast_smul_units
    # (n : ZMod 2) • au = n • au
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_colon_ZMod_2", 2)
    if args is not None:
        try:
            rhs = OOp("n", (args[0], args[1],))
            results.append((rhs, "Mathlib: ZMod_natCast_smul_units"))
        except Exception:
            pass
    return results


def _r0134_unitsMap_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.unitsMap_def
    # unitsMap hm = Units.map (castHom hm (ZMod n))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unitsMap", 1)
    if args is not None:
        try:
            rhs = OOp("Units_map", (OOp("castHom", (args[0], OOp("ZMod", (OVar("n"),)),)),))
            results.append((rhs, "Mathlib: ZMod_unitsMap_def"))
        except Exception:
            pass
    return results


def _r0135_unitsMap_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.unitsMap_comp
    # (unitsMap hm).comp (unitsMap hd) = unitsMap (dvd_trans hm hd)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unitsMap_hm_comp", 1)
    if args is not None:
        try:
            rhs = OOp("unitsMap", (OOp("dvd_trans", (OVar("hm"), OVar("hd"),)),))
            results.append((rhs, "Mathlib: ZMod_unitsMap_comp"))
        except Exception:
            pass
    return results


def _r0136_unitsMap_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.unitsMap_self
    # unitsMap (dvd_refl n) = MonoidHom.id _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unitsMap", 1)
    if args is not None:
        try:
            rhs = OOp("MonoidHom_id", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: ZMod_unitsMap_self"))
        except Exception:
            pass
    return results


def _r0137_unitsMap_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.unitsMap_val
    # ↑(unitsMap h a) = ((a : ZMod m).cast : ZMod n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("unitsMap_h_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a_colon_ZMod_m_cast", (OVar("colon"), OVar("ZMod"), OVar("n"),))
            results.append((rhs, "Mathlib: ZMod_unitsMap_val"))
    except Exception:
        pass
    return results


def _r0138_eq_unit_mul_divisor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.eq_unit_mul_divisor
    # ∃ d : ℕ, d ∣ N ∧ ∃ (u : ZMod N), IsUnit u ∧ a = u * d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("u"), OVar("d")))
            results.append((rhs, "Mathlib: ZMod_eq_unit_mul_divisor"))
        except Exception:
            pass
    return results


def _r0139_coe_int_mul_inv_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.coe_int_mul_inv_eq_one
    # (x : ZMod n) * (x : ZMod n)⁻¹ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_coe_int_mul_inv_eq_one"))
        except Exception:
            pass
    return results


def _r0140_coe_int_inv_mul_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.coe_int_inv_mul_eq_one
    # (x : ZMod n)⁻¹ * (x : ZMod n) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_coe_int_inv_mul_eq_one"))
        except Exception:
            pass
    return results


def _r0141_coe_int_mul_val_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.coe_int_mul_val_inv
    # (m * (m⁻¹ : ZMod n).val : ZMod n) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_coe_int_mul_val_inv"))
        except Exception:
            pass
    return results


def _r0142_coe_int_val_inv_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.coe_int_val_inv_mul
    # ((m⁻¹ : ZMod n).val : ZMod n) * m = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_coe_int_val_inv_mul"))
        except Exception:
            pass
    return results


def _r0143_coe_unitOfIsCoprime(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.coe_unitOfIsCoprime
    # (unitOfIsCoprime n h : ZMod m) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unitOfIsCoprime", 5)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ZMod_coe_unitOfIsCoprime"))
        except Exception:
            pass
    return results


def _r0144_valMinAbs_def_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_def_zero
    # valMinAbs x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "valMinAbs", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ZMod_valMinAbs_def_zero"))
        except Exception:
            pass
    return results


def _r0145_coe_valMinAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.coe_valMinAbs
    # ∀ {n : ℕ} (x : ZMod n), (x.valMinAbs : ZMod n) = x   | 0, _ => Int.cast_id   | k@(n + 1), x =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_valMinAbs", 3)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("pipe"), OVar("_0"), OVar("_unknown"), OVar("eq_gt"), OVar("Int_cast_id"), OVar("pipe"), OVar("kat_n_plus_1"), OVar("x"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: ZMod_coe_valMinAbs"))
        except Exception:
            pass
    return results


def _r0146_valMinAbs_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_inj
    # a.valMinAbs = b.valMinAbs ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_valMinAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("b_valMinAbs"), OVar("a"))), OVar("b")))
            results.append((rhs, "Mathlib: ZMod_valMinAbs_inj"))
    except Exception:
        pass
    return results


def _r0147_valMinAbs_mul_two_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_mul_two_eq_iff
    # a.valMinAbs * 2 = n ↔ 2 * a.val = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("n"), OOp("*", (OLit(2), OVar("a_val"))))), OVar("n")))
            results.append((rhs, "Mathlib: ZMod_valMinAbs_mul_two_eq_iff"))
        except Exception:
            pass
    return results


def _r0148_valMinAbs_spec(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_spec
    # x.valMinAbs = y ↔ x = y ∧ y * 2 ∈ Set.Ioc (-n : ℤ) n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_valMinAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("y"), OVar("x"))), OOp("and", (OVar("y"), OOp("*", (OVar("y"), OOp("in", (OLit(2), OOp("Set_Ioc", (OOp("minus_n", (OVar("colon"), OVar("_unknown"),)), OVar("n"),))))))))))
            results.append((rhs, "Mathlib: ZMod_valMinAbs_spec"))
    except Exception:
        pass
    return results


def _r0149_eq_neg_of_valMinAbs_eq_neg_valMinAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.eq_neg_of_valMinAbs_eq_neg_valMinAbs
    # a = -b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_b")
            results.append((rhs, "Mathlib: ZMod_eq_neg_of_valMinAbs_eq_neg_valMinAbs"))
    except Exception:
        pass
    return results


def _r0150_valMinAbs_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_zero
    # ∀ n, (0 : ZMod n).valMinAbs = 0   | 0 =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_ZMod_n_valMinAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_0", (OVar("pipe"), OLit(0), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: ZMod_valMinAbs_zero"))
    except Exception:
        pass
    return results


def _r0151_valMinAbs_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_eq_zero
    # x.valMinAbs = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_valMinAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("x"))), OLit(0)))
            results.append((rhs, "Mathlib: ZMod_valMinAbs_eq_zero"))
    except Exception:
        pass
    return results


def _r0152_valMinAbs_neg_of_ne_half(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_neg_of_ne_half
    # (-a).valMinAbs = -a.valMinAbs
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_a_valMinAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_a_valMinAbs")
            results.append((rhs, "Mathlib: ZMod_valMinAbs_neg_of_ne_half"))
    except Exception:
        pass
    return results


def _r0153_natAbs_valMinAbs_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.natAbs_valMinAbs_neg
    # (-a).valMinAbs.natAbs = a.valMinAbs.natAbs
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_a_valMinAbs_natAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a_valMinAbs_natAbs")
            results.append((rhs, "Mathlib: ZMod_natAbs_valMinAbs_neg"))
    except Exception:
        pass
    return results


def _r0154_natAbs_valMinAbs_eq_natAbs_valMinAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs
    # a.valMinAbs.natAbs = b.valMinAbs.natAbs ↔ a = b ∨ a = -b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_valMinAbs_natAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("b_valMinAbs_natAbs"), OVar("a"))), OOp("==", (OOp("or", (OVar("b"), OVar("a"))), OVar("minus_b")))))
            results.append((rhs, "Mathlib: ZMod_natAbs_valMinAbs_eq_natAbs_valMinAbs"))
    except Exception:
        pass
    return results


def _r0155_abs_valMinAbs_eq_abs_valMinAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.abs_valMinAbs_eq_abs_valMinAbs
    # |a.valMinAbs| = |b.valMinAbs| ↔ a = b ∨ a = -b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_a_valMinAbspipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("pipe_b_valMinAbspipe"), OVar("a"))), OOp("==", (OOp("or", (OVar("b"), OVar("a"))), OVar("minus_b")))))
            results.append((rhs, "Mathlib: ZMod_abs_valMinAbs_eq_abs_valMinAbs"))
    except Exception:
        pass
    return results


def _r0156_val_eq_ite_valMinAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.val_eq_ite_valMinAbs
    # (a.val : ℤ) = a.valMinAbs + if a.val ≤ n / 2 then 0 else n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_val", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("+", (OVar("a_valMinAbs"), OOp("if", (OVar("a_val"),)))), OOp("//", (OVar("n"), OOp("_2", (OVar("then"), OLit(0), OVar("else"), OVar("n"),))))))
            results.append((rhs, "Mathlib: ZMod_val_eq_ite_valMinAbs"))
        except Exception:
            pass
    return results


def _r0157_valMinAbs_natAbs_eq_min(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_natAbs_eq_min
    # a.valMinAbs.natAbs = min a.val (n - a.val)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_valMinAbs_natAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("min", (OVar("a_val"), OOp("-", (OVar("n"), OVar("a_val"))),))
            results.append((rhs, "Mathlib: ZMod_valMinAbs_natAbs_eq_min"))
    except Exception:
        pass
    return results


def _r0158_valMinAbs_natCast_of_le_half(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_natCast_of_le_half
    # (a : ZMod n).valMinAbs = a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_ZMod_n_valMinAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: ZMod_valMinAbs_natCast_of_le_half"))
    except Exception:
        pass
    return results


def _r0159_valMinAbs_natCast_of_half_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_natCast_of_half_lt
    # (a : ZMod n).valMinAbs = a - n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_ZMod_n_valMinAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("a"), OVar("n")))
            results.append((rhs, "Mathlib: ZMod_valMinAbs_natCast_of_half_lt"))
    except Exception:
        pass
    return results


def _r0160_valMinAbs_natCast_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.valMinAbs_natCast_eq_self
    # (a : ZMod n).valMinAbs = a ↔ a ≤ n / 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_ZMod_n_valMinAbs")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("iff", (OVar("a"), OVar("a"))), OOp("//", (OVar("n"), OLit(2)))))
            results.append((rhs, "Mathlib: ZMod_valMinAbs_natCast_eq_self"))
    except Exception:
        pass
    return results


def _r0161_sq_add_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.sq_add_sq
    # ∃ a b : ZMod p, a ^ 2 + b ^ 2 = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: ZMod_sq_add_sq"))
        except Exception:
            pass
    return results


def _r0162_pow_totient(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.pow_totient
    # x ^ φ n = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_pow_totient"))
        except Exception:
            pass
    return results


def _r0163_fieldRange_castHom_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.fieldRange_castHom_eq_bot
    # (ZMod.castHom (m := p) dvd_rfl K).fieldRange = (⊥ : Subfield K)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ZMod_castHom_m_colon_eq_p_dvd_rfl_K_fieldRange")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("bot", (OVar("colon"), OVar("Subfield"), OVar("K"),))
            results.append((rhs, "Mathlib: ZMod_fieldRange_castHom_eq_bot"))
    except Exception:
        pass
    return results


def _r0164_pow_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.pow_card
    # x ^ p = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ZMod_pow_card"))
        except Exception:
            pass
    return results


def _r0165_frobenius_zmod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.frobenius_zmod
    # frobenius (ZMod p) p = RingHom.id _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frobenius", 2)
    if args is not None:
        try:
            rhs = OOp("RingHom_id", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: ZMod_frobenius_zmod"))
        except Exception:
            pass
    return results


def _r0166_card_units(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.card_units
    # Fintype.card (ZMod p)ˣ = p - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fintype_card", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("p"), OLit(1)))
            results.append((rhs, "Mathlib: ZMod_card_units"))
        except Exception:
            pass
    return results


def _r0167_units_pow_card_sub_one_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.units_pow_card_sub_one_eq_one
    # a ^ (p - 1) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_units_pow_card_sub_one_eq_one"))
        except Exception:
            pass
    return results


def _r0168_pow_card_sub_one_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.pow_card_sub_one_eq_one
    # a ^ (p - 1) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_pow_card_sub_one_eq_one"))
        except Exception:
            pass
    return results


def _r0169_pow_card_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.pow_card_sub_one
    # a ^ (p - 1) = if a ≠ 0 then 1 else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("if", (args[0],)), OOp("_0", (OVar("then"), OLit(1), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: ZMod_pow_card_sub_one"))
        except Exception:
            pass
    return results


def _r0170_expand_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.expand_card
    # expand (ZMod p) p f = f ^ p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "expand", 3)
    if args is not None:
        try:
            rhs = OOp("**", (args[2], args[1]))
            results.append((rhs, "Mathlib: ZMod_expand_card"))
        except Exception:
            pass
    return results


def _r0171_eq_one_or_isUnit_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.eq_one_or_isUnit_sub_one
    # a = 1 ∨ IsUnit (a - 1)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("or", (OLit(1), OOp("IsUnit", (OOp("-", (OVar("a"), OLit(1))),))))
            results.append((rhs, "Mathlib: ZMod_eq_one_or_isUnit_sub_one"))
    except Exception:
        pass
    return results


def _r0172_minOrder(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.minOrder
    # minOrder (ZMod n) = n.minFac
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minOrder", 1)
    if args is not None:
        try:
            rhs = OVar("n_minFac")
            results.append((rhs, "Mathlib: ZMod_minOrder"))
        except Exception:
            pass
    return results


def _r0173_minOrder_of_prime(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.minOrder_of_prime
    # minOrder (ZMod p) = p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minOrder", 1)
    if args is not None:
        try:
            rhs = OVar("p")
            results.append((rhs, "Mathlib: ZMod_minOrder_of_prime"))
        except Exception:
            pass
    return results


def _r0174_exponent(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.exponent
    # AddMonoid.exponent (ZMod n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "AddMonoid_exponent", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ZMod_exponent"))
        except Exception:
            pass
    return results


def _r0175_charpoly_pow_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.charpoly_pow_card
    # (M ^ p).charpoly = M.charpoly
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("M_pow_p_charpoly")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("M_charpoly")
            results.append((rhs, "Mathlib: ZMod_charpoly_pow_card"))
    except Exception:
        pass
    return results


def _r0176_trace_pow_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.trace_pow_card
    # trace (M ^ p) = trace M ^ p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trace", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("trace", (OVar("M"),)), OVar("p")))
            results.append((rhs, "Mathlib: ZMod_trace_pow_card"))
        except Exception:
            pass
    return results


def _r0177_LFunction_modOne_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_modOne_eq
    # LFunction Φ s = Φ 0 * riemannZeta s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("_unknown", (OLit(0),)), OOp("riemannZeta", (args[1],))))
            results.append((rhs, "Mathlib: ZMod_LFunction_modOne_eq"))
        except Exception:
            pass
    return results


def _r0178_LFunction_eq_LSeries(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_eq_LSeries
    # LFunction Φ s = LSeries (Φ ·) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("LSeries", (OOp("_unknown", (args[0],)), args[1],))
            results.append((rhs, "Mathlib: ZMod_LFunction_eq_LSeries"))
        except Exception:
            pass
    return results


def _r0179_LFunction_stdAddChar_eq_expZeta_of_one_l(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_stdAddChar_eq_expZeta_of_one_lt_re
    # LFunction (fun k ↦ 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("expZeta", (OOp("ZMod_toAddCircle", (OVar("j"),)), args[1],))
            results.append((rhs, "Mathlib: ZMod_LFunction_stdAddChar_eq_expZeta_of_one_lt_re"))
        except Exception:
            pass
    return results


def _r0180_LFunction_stdAddChar_eq_expZeta(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_stdAddChar_eq_expZeta
    # LFunction (fun k ↦ 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("expZeta", (OOp("ZMod_toAddCircle", (OVar("j"),)), args[1],))
            results.append((rhs, "Mathlib: ZMod_LFunction_stdAddChar_eq_expZeta"))
        except Exception:
            pass
    return results


def _r0181_LFunction_dft(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_dft
    # LFunction (𝓕 Φ) s = ∑ j : ZMod N, Φ j * expZeta (toAddCircle (-j)) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("_unknown", (OVar("j"), OVar("colon"), OVar("ZMod"), OVar("N"), OVar("_unknown"), OVar("j"),)), OOp("expZeta", (OOp("toAddCircle", (OVar("minus_j"),)), args[1],))))
            results.append((rhs, "Mathlib: ZMod_LFunction_dft"))
        except Exception:
            pass
    return results


def _r0182_LFunction_one_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_one_sub
    # LFunction Φ (1 - s) = N ^ (s - 1) * (2 * π) ^ (-s) * Gamma s *       (cexp (π * I * s / 2) * LFunction (𝓕 Φ) s        + 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("N"), OOp("-", (OVar("s"), OLit(1))))), OOp("*", (OOp("**", (OOp("*", (OLit(2), OVar("pi"))), OVar("minus_s"))), OOp("*", (OOp("Gamma", (OVar("s"),)), OOp("+", (OOp("*", (OOp("cexp", (OOp("*", (OVar("pi"), OOp("*", (OVar("I"), OOp("//", (OVar("s"), OLit(2))))))),)), OOp("LFunction", (OOp("_unknown", (args[0],)), OVar("s"),)))), OOp("*", (OOp("cexp", (OOp("*", (OVar("minus_pi"), OOp("*", (OVar("I"), OOp("//", (OVar("s"), OLit(2))))))),)), OOp("LFunction", (OOp("_unknown", (OVar("fun"), OVar("x"), args[0], args[0], OVar("minus_x"),)), OVar("s"),))))))))))))
            results.append((rhs, "Mathlib: ZMod_LFunction_one_sub"))
        except Exception:
            pass
    return results


def _r0183_LFunction_def_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_def_even
    # LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("N"), OVar("minus_s"))), OOp("*", (OOp("_unknown", (OVar("j"), OVar("colon"), OVar("ZMod"), OVar("N"), args[0], OVar("j"),)), OOp("hurwitzZetaEven", (OOp("toAddCircle", (OVar("j"),)), args[1],))))))
            results.append((rhs, "Mathlib: ZMod_LFunction_def_even"))
        except Exception:
            pass
    return results


def _r0184_LFunction_def_odd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_def_odd
    # LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("N"), OVar("minus_s"))), OOp("*", (OOp("_unknown", (OVar("j"), OVar("colon"), OVar("ZMod"), OVar("N"), args[0], OVar("j"),)), OOp("hurwitzZetaOdd", (OOp("toAddCircle", (OVar("j"),)), args[1],))))))
            results.append((rhs, "Mathlib: ZMod_LFunction_def_odd"))
        except Exception:
            pass
    return results


def _r0185_LFunction_apply_zero_of_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_apply_zero_of_even
    # LFunction Φ 0 = -Φ 0 / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("minus", (OLit(0),)), OLit(2)))
            results.append((rhs, "Mathlib: ZMod_LFunction_apply_zero_of_even"))
        except Exception:
            pass
    return results


def _r0186_LFunction_neg_two_mul_nat_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_neg_two_mul_nat_add_one
    # LFunction Φ (-(2 * (n + 1))) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ZMod_LFunction_neg_two_mul_nat_add_one"))
        except Exception:
            pass
    return results


def _r0187_LFunction_neg_two_mul_nat_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_neg_two_mul_nat_sub_one
    # LFunction Φ (-(2 * n) - 1) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ZMod_LFunction_neg_two_mul_nat_sub_one"))
        except Exception:
            pass
    return results


def _r0188_completedLFunction_def_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.completedLFunction_def_even
    # completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completedLFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("N"), OVar("minus_s"))), OOp("*", (OOp("_unknown", (OVar("j"), args[0], OVar("j"),)), OOp("completedHurwitzZetaEven", (OOp("toAddCircle", (OVar("j"),)), args[1],))))))
            results.append((rhs, "Mathlib: ZMod_completedLFunction_def_even"))
        except Exception:
            pass
    return results


def _r0189_completedLFunction_def_odd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.completedLFunction_def_odd
    # completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completedLFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("N"), OVar("minus_s"))), OOp("*", (OOp("_unknown", (OVar("j"), args[0], OVar("j"),)), OOp("completedHurwitzZetaOdd", (OOp("toAddCircle", (OVar("j"),)), args[1],))))))
            results.append((rhs, "Mathlib: ZMod_completedLFunction_def_odd"))
        except Exception:
            pass
    return results


def _r0190_completedLFunction_modOne_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.completedLFunction_modOne_eq
    # completedLFunction Φ s = Φ 1 * completedRiemannZeta s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completedLFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("_unknown", (OLit(1),)), OOp("completedRiemannZeta", (args[1],))))
            results.append((rhs, "Mathlib: ZMod_completedLFunction_modOne_eq"))
        except Exception:
            pass
    return results


def _r0191_completedLFunction_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.completedLFunction_eq
    # completedLFunction Φ s =       completedLFunction₀ Φ s - N ^ (-s) * Φ 0 / s - N ^ (-s) * (∑ j, Φ j) / (1 - s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completedLFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("-", (OOp("completedLFunction_0", (args[0], args[1],)), OOp("**", (OVar("N"), OVar("minus_s"))))), OOp("*", (OOp("-", (OOp("//", (OOp("_unknown", (OLit(0),)), args[1])), OOp("**", (OVar("N"), OVar("minus_s"))))), OOp("//", (OOp("_unknown", (OVar("j"), args[0], OVar("j"),)), OOp("-", (OLit(1), args[1]))))))))
            results.append((rhs, "Mathlib: ZMod_completedLFunction_eq"))
        except Exception:
            pass
    return results


def _r0192_LFunction_eq_completed_div_gammaFactor_e(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_eq_completed_div_gammaFactor_even
    # LFunction Φ s = completedLFunction Φ s / Gammaℝ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("completedLFunction", (args[0], args[1],)), OOp("Gamma", (args[1],))))
            results.append((rhs, "Mathlib: ZMod_LFunction_eq_completed_div_gammaFactor_even"))
        except Exception:
            pass
    return results


def _r0193_LFunction_eq_completed_div_gammaFactor_o(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.LFunction_eq_completed_div_gammaFactor_odd
    # LFunction Φ s = completedLFunction Φ s / Gammaℝ (s + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LFunction", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("completedLFunction", (args[0], args[1],)), OOp("Gamma", (OOp("+", (args[1], OLit(1))),))))
            results.append((rhs, "Mathlib: ZMod_LFunction_eq_completed_div_gammaFactor_odd"))
        except Exception:
            pass
    return results


def _r0194_completedLFunction_one_sub_of_one_lt_eve(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.completedLFunction_one_sub_of_one_lt_even
    # completedLFunction Φ (1 - s) = N ^ (s - 1) * completedLFunction (𝓕 Φ) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completedLFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("N"), OOp("-", (OVar("s"), OLit(1))))), OOp("completedLFunction", (OOp("_unknown", (args[0],)), OVar("s"),))))
            results.append((rhs, "Mathlib: ZMod_completedLFunction_one_sub_of_one_lt_even"))
        except Exception:
            pass
    return results


def _r0195_completedLFunction_one_sub_of_one_lt_odd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.completedLFunction_one_sub_of_one_lt_odd
    # completedLFunction Φ (1 - s) = N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completedLFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("N"), OOp("-", (OVar("s"), OLit(1))))), OOp("*", (OVar("I"), OOp("completedLFunction", (OOp("_unknown", (args[0],)), OVar("s"),))))))
            results.append((rhs, "Mathlib: ZMod_completedLFunction_one_sub_of_one_lt_odd"))
        except Exception:
            pass
    return results


def _r0196_completedLFunction_one_sub_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.completedLFunction_one_sub_even
    # completedLFunction Φ (1 - s) = N ^ (s - 1) * completedLFunction (𝓕 Φ) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completedLFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("N"), OOp("-", (OVar("s"), OLit(1))))), OOp("completedLFunction", (OOp("_unknown", (args[0],)), OVar("s"),))))
            results.append((rhs, "Mathlib: ZMod_completedLFunction_one_sub_even"))
        except Exception:
            pass
    return results


def _r0197_completedLFunction_one_sub_odd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.completedLFunction_one_sub_odd
    # completedLFunction Φ (1 - s) = N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completedLFunction", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("N"), OOp("-", (OVar("s"), OLit(1))))), OOp("*", (OVar("I"), OOp("completedLFunction", (OOp("_unknown", (args[0],)), OVar("s"),))))))
            results.append((rhs, "Mathlib: ZMod_completedLFunction_one_sub_odd"))
        except Exception:
            pass
    return results


def _r0198_euler_criterion_units(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.euler_criterion_units
    # (∃ y : (ZMod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_euler_criterion_units"))
        except Exception:
            pass
    return results


def _r0199_euler_criterion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.euler_criterion
    # IsSquare (a : ZMod p) ↔ a ^ (p / 2) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_euler_criterion"))
        except Exception:
            pass
    return results


def _r0200_pow_div_two_eq_neg_one_or_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.pow_div_two_eq_neg_one_or_one
    # a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(1), OOp("**", (args[0], OOp("//", (OVar("p"), OLit(2))))))), OVar("minus_1")))
            results.append((rhs, "Mathlib: ZMod_pow_div_two_eq_neg_one_or_one"))
        except Exception:
            pass
    return results


def _r0201_Ico_map_valMinAbs_natAbs_eq_Ico_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.Ico_map_valMinAbs_natAbs_eq_Ico_map_id
    # ((Ico 1 (p / 2).succ).1.map fun (x : ℕ) => (a * x).valMinAbs.natAbs) =     (Ico 1 (p / 2).succ).1.map fun a => a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico_1_p_slash_2_succ_1_map", 4)
    if args is not None:
        try:
            rhs = OOp("Ico_1_p_slash_2_succ_1_map", (args[0], OVar("a"), args[2], OVar("a"),))
            results.append((rhs, "Mathlib: ZMod_Ico_map_valMinAbs_natAbs_eq_Ico_map_id"))
        except Exception:
            pass
    return results


def _r0202_gauss_lemma_aux_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.gauss_lemma_aux₁
    # (a ^ (p / 2) * (p / 2)! : ZMod p) =      (-1 : ZMod p) ^ #{x ∈ Ico 1 (p / 2).succ | ¬ (a * x.cast : ZMod p).val ≤ p / 2}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OOp("minus_1", (OVar("colon"), OVar("ZMod"), OVar("p"),)), OVar("hash_x_in_Ico_1_p_slash_2_succ_pipe_not_a_star_x_cast_colon_ZMod_p_val_le_p_slash_2"))), OVar("p_slash_2_bang")))
            results.append((rhs, "Mathlib: ZMod_gauss_lemma_aux_1"))
        except Exception:
            pass
    return results


def _r0203_gauss_lemma_aux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.gauss_lemma_aux
    # (a ^ (p / 2) : ZMod p) =       ((-1) ^ #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} :)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("minus_1"), OOp("hash_x_in_Ico_1_p_slash_2_succ_pipe_p_slash_2_lt_a_star_x_cast_colon_ZMod_p_val", (OVar("colon"),))))
            results.append((rhs, "Mathlib: ZMod_gauss_lemma_aux"))
        except Exception:
            pass
    return results


def _r0204_gauss_lemma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.gauss_lemma
    # legendreSym p a = (-1) ^ #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "legendreSym", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("minus_1"), OVar("hash_x_in_Ico_1_p_slash_2_succ_pipe_p_slash_2_lt_a_star_x_cast_colon_ZMod_p_val")))
            results.append((rhs, "Mathlib: ZMod_gauss_lemma"))
        except Exception:
            pass
    return results


def _r0205_eisenstein_lemma_aux_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.eisenstein_lemma_aux₁
    # ((∑ x ∈ Ico 1 (p / 2).succ, a * x : ℕ) : ZMod 2) =       #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} +
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_in_Ico_1_p_slash_2_succ_a_star_x_colon", 3)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("hash_x_in_Ico_1_p_slash_2_succ_pipe_p_slash_2_lt_a_star_x_cast_colon_ZMod_p_val"), OOp("+", (OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("Ico", (OLit(1), OVar("p_slash_2_succ"), OVar("x"),)))), OOp("*", (OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("Ico", (OLit(1), OVar("p_slash_2_succ"), OVar("a"),)))), OOp("//", (OVar("x"), OOp("p", (args[0], OVar("_unknown"),))))))))))
            results.append((rhs, "Mathlib: ZMod_eisenstein_lemma_aux_1"))
        except Exception:
            pass
    return results


def _r0206_div_eq_filter_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.div_eq_filter_card
    # a / b = #{x ∈ Ico 1 c.succ | x * b ≤ a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OVar("hash_x_in_Ico_1_c_succ_pipe_x_star_b_le_a")
            results.append((rhs, "Mathlib: ZMod_div_eq_filter_card"))
        except Exception:
            pass
    return results


def _r0207_sum_Ico_eq_card_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.sum_Ico_eq_card_lt
    # ∑ a ∈ Ico 1 (p / 2).succ, a * q / p =       #{x ∈ Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p ≤ x.1 * q}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("hash_x_in_Ico_1_p_slash_2_succ_times_Ico_1_q_slash_2_succ_pipe_x_2_star_p_le_x_1_star_q")
            results.append((rhs, "Mathlib: ZMod_sum_Ico_eq_card_lt"))
        except Exception:
            pass
    return results


def _r0208_sum_mul_div_add_sum_mul_div_eq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.sum_mul_div_add_sum_mul_div_eq_mul
    # ∑ a ∈ Ico 1 (p / 2).succ, a * q / p + ∑ a ∈ Ico 1 (q / 2).succ, a * p / q =     p / 2 * (q / 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("//", (OVar("p"), OLit(2))), OOp("//", (OVar("q"), OLit(2)))))
            results.append((rhs, "Mathlib: ZMod_sum_mul_div_add_sum_mul_div_eq_mul"))
        except Exception:
            pass
    return results


def _r0209_eisenstein_lemma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.eisenstein_lemma
    # legendreSym p a = (-1) ^ ∑ x ∈ Ico 1 (p / 2).succ, x * a / p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "legendreSym", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("in", (OOp("**", (OVar("minus_1"), OOp("_unknown", (OVar("x"),)))), OOp("Ico", (OLit(1), OVar("p_slash_2_succ"), OVar("x"),)))), OOp("//", (args[1], args[0]))))
            results.append((rhs, "Mathlib: ZMod_eisenstein_lemma"))
        except Exception:
            pass
    return results


def _r0210_nonsquare_iff_jacobiSym_eq_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.nonsquare_iff_jacobiSym_eq_neg_one
    # J(a | p) = -1 ↔ ¬IsSquare (a : ZMod p)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("J_a_pipe_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("minus_1"), OOp("not_IsSquare", (OOp("a", (OVar("colon"), OVar("ZMod"), OVar("p"),)),))))
            results.append((rhs, "Mathlib: ZMod_nonsquare_iff_jacobiSym_eq_neg_one"))
    except Exception:
        pass
    return results


def _r0211_exists_sq_eq_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.exists_sq_eq_two_iff
    # IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(1), OOp("p", (OVar("_unknown"), OLit(8),)))), OLit(7)))
            results.append((rhs, "Mathlib: ZMod_exists_sq_eq_two_iff"))
        except Exception:
            pass
    return results


def _r0212_exists_sq_eq_neg_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.exists_sq_eq_neg_two_iff
    # IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(1), OOp("p", (OVar("_unknown"), OLit(8),)))), OLit(3)))
            results.append((rhs, "Mathlib: ZMod_exists_sq_eq_neg_two_iff"))
        except Exception:
            pass
    return results


def _r0213_chi_4_nat_mod_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₄_nat_mod_four
    # χ₄ n = χ₄ (n % 4 : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_4", 1)
    if args is not None:
        try:
            rhs = OOp("chi_4", (OOp("n", (OVar("_unknown"), OLit(4), OVar("colon"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: ZMod_chi_4_nat_mod_four"))
        except Exception:
            pass
    return results


def _r0214_chi_4_int_mod_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₄_int_mod_four
    # χ₄ n = χ₄ (n % 4 : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_4", 1)
    if args is not None:
        try:
            rhs = OOp("chi_4", (OOp("n", (OVar("_unknown"), OLit(4), OVar("colon"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: ZMod_chi_4_int_mod_four"))
        except Exception:
            pass
    return results


def _r0215_chi_4_int_eq_if_mod_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₄_int_eq_if_mod_four
    # χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_4", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0], OVar("_unknown"), OLit(2),)), OOp("==", (OOp("_0", (OVar("then"), OLit(0), OVar("else"), OVar("if"), args[0], OVar("_unknown"), OLit(4),)), OOp("_1", (OVar("then"), OLit(1), OVar("else"), OVar("minus_1"),))))))
            results.append((rhs, "Mathlib: ZMod_chi_4_int_eq_if_mod_four"))
        except Exception:
            pass
    return results


def _r0216_chi_4_nat_eq_if_mod_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₄_nat_eq_if_mod_four
    # χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_4", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0], OVar("_unknown"), OLit(2),)), OOp("==", (OOp("_0", (OVar("then"), OLit(0), OVar("else"), OVar("if"), args[0], OVar("_unknown"), OLit(4),)), OOp("_1", (OVar("then"), OLit(1), OVar("else"), OVar("minus_1"),))))))
            results.append((rhs, "Mathlib: ZMod_chi_4_nat_eq_if_mod_four"))
        except Exception:
            pass
    return results


def _r0217_chi_4_eq_neg_one_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₄_eq_neg_one_pow
    # χ₄ n = (-1) ^ (n / 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_4", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("minus_1"), OOp("//", (args[0], OLit(2)))))
            results.append((rhs, "Mathlib: ZMod_chi_4_eq_neg_one_pow"))
        except Exception:
            pass
    return results


def _r0218_chi_4_nat_one_mod_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₄_nat_one_mod_four
    # χ₄ n = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_4", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_chi_4_nat_one_mod_four"))
        except Exception:
            pass
    return results


def _r0219_chi_4_nat_three_mod_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₄_nat_three_mod_four
    # χ₄ n = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_4", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: ZMod_chi_4_nat_three_mod_four"))
        except Exception:
            pass
    return results


def _r0220_chi_4_int_one_mod_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₄_int_one_mod_four
    # χ₄ n = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_4", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_chi_4_int_one_mod_four"))
        except Exception:
            pass
    return results


def _r0221_chi_4_int_three_mod_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₄_int_three_mod_four
    # χ₄ n = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_4", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: ZMod_chi_4_int_three_mod_four"))
        except Exception:
            pass
    return results


def _r0222_neg_one_pow_div_two_of_one_mod_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.neg_one_pow_div_two_of_one_mod_four
    # (-1 : ℤ) ^ (n / 2) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ZMod_neg_one_pow_div_two_of_one_mod_four"))
        except Exception:
            pass
    return results


def _r0223_neg_one_pow_div_two_of_three_mod_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.neg_one_pow_div_two_of_three_mod_four
    # (-1 : ℤ) ^ (n / 2) = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: ZMod_neg_one_pow_div_two_of_three_mod_four"))
        except Exception:
            pass
    return results


def _r0224_chi_8_nat_mod_eight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₈_nat_mod_eight
    # χ₈ n = χ₈ (n % 8 : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_8", 1)
    if args is not None:
        try:
            rhs = OOp("chi_8", (OOp("n", (OVar("_unknown"), OLit(8), OVar("colon"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: ZMod_chi_8_nat_mod_eight"))
        except Exception:
            pass
    return results


def _r0225_chi_8_int_mod_eight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₈_int_mod_eight
    # χ₈ n = χ₈ (n % 8 : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_8", 1)
    if args is not None:
        try:
            rhs = OOp("chi_8", (OOp("n", (OVar("_unknown"), OLit(8), OVar("colon"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: ZMod_chi_8_int_mod_eight"))
        except Exception:
            pass
    return results


def _r0226_chi_8_int_eq_if_mod_eight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₈_int_eq_if_mod_eight
    # χ₈ n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_8", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0], OVar("_unknown"), OLit(2),)), OOp("==", (OOp("_0", (OVar("then"), OLit(0), OVar("else"), OVar("if"), args[0], OVar("_unknown"), OLit(8),)), OOp("==", (OOp("or", (OLit(1), OOp("n", (OVar("_unknown"), OLit(8),)))), OOp("_7", (OVar("then"), OLit(1), OVar("else"), OVar("minus_1"),))))))))
            results.append((rhs, "Mathlib: ZMod_chi_8_int_eq_if_mod_eight"))
        except Exception:
            pass
    return results


def _r0227_chi_8_nat_eq_if_mod_eight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.χ₈_nat_eq_if_mod_eight
    # χ₈ n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "chi_8", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0], OVar("_unknown"), OLit(2),)), OOp("==", (OOp("_0", (OVar("then"), OLit(0), OVar("else"), OVar("if"), args[0], OVar("_unknown"), OLit(8),)), OOp("==", (OOp("or", (OLit(1), OOp("n", (OVar("_unknown"), OLit(8),)))), OOp("_7", (OVar("then"), OLit(1), OVar("else"), OVar("minus_1"),))))))))
            results.append((rhs, "Mathlib: ZMod_chi_8_nat_eq_if_mod_eight"))
        except Exception:
            pass
    return results


def _r0228_addChar_of_value_at_one_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.addChar_of_value_at_one_def
    # addChar_of_value_at_one r hr (1 : ℤ_[p]) = 1 + r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "addChar_of_value_at_one", 3)
    if args is not None:
        try:
            rhs = OOp("+", (OLit(1), args[0]))
            results.append((rhs, "Mathlib: PadicInt_addChar_of_value_at_one_def"))
        except Exception:
            pass
    return results


def _r0229_eq_addChar_of_value_at_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.eq_addChar_of_value_at_one
    # κ = addChar_of_value_at_one r hr
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("k")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("addChar_of_value_at_one", (OVar("r"), OVar("hr"),))
            results.append((rhs, "Mathlib: PadicInt_eq_addChar_of_value_at_one"))
    except Exception:
        pass
    return results


def _r0230_continuousAddCharEquiv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.continuousAddCharEquiv_apply
    # continuousAddCharEquiv p R ⟨κ, hκ⟩ = κ 1 - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "continuousAddCharEquiv", 3)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("k", (OLit(1),)), OLit(1)))
            results.append((rhs, "Mathlib: PadicInt_continuousAddCharEquiv_apply"))
        except Exception:
            pass
    return results


def _r0231_continuousAddCharEquiv_of_norm_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.continuousAddCharEquiv_of_norm_mul_apply
    # continuousAddCharEquiv_of_norm_mul p R ⟨κ, hκ⟩ = κ 1 - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "continuousAddCharEquiv_of_norm_mul", 3)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("k", (OLit(1),)), OLit(1)))
            results.append((rhs, "Mathlib: PadicInt_continuousAddCharEquiv_of_norm_mul_apply"))
        except Exception:
            pass
    return results


def _r0232_spectralNorm_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicAlgCl.spectralNorm_eq
    # spectralNorm ℚ_[p] (PadicAlgCl p) x = ‖x‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "spectralNorm", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: PadicAlgCl_spectralNorm_eq"))
        except Exception:
            pass
    return results


def _r0233_valuation_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicAlgCl.valuation_def
    # Valued.v x = ‖x‖₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Valued_v", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: PadicAlgCl_valuation_def"))
        except Exception:
            pass
    return results


def _r0234_valuation_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicAlgCl.valuation_coe
    # ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Valued_v_x_colon_ge_0", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: PadicAlgCl_valuation_coe"))
        except Exception:
            pass
    return results


def _r0235_valuation_extends(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicComplex.valuation_extends
    # Valued.v (x : ℂ_[p]) = Valued.v x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Valued_v", 1)
    if args is not None:
        try:
            rhs = OOp("Valued_v", (OVar("x"),))
            results.append((rhs, "Mathlib: PadicComplex_valuation_extends"))
        except Exception:
            pass
    return results


def _r0236_coe_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicComplex.coe_eq
    # (x : ℂ_[p]) = algebraMap (PadicAlgCl p) ℂ_[p] x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("algebraMap", (OOp("PadicAlgCl", (args[1],)), args[1], OVar("x"),))
            results.append((rhs, "Mathlib: PadicComplex_coe_eq"))
        except Exception:
            pass
    return results


def _r0237_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicComplex.coe_zero
    # ((0 : PadicAlgCl p) : ℂ_[p]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_PadicAlgCl_p", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PadicComplex_coe_zero"))
        except Exception:
            pass
    return results


def _r0238_valuation_p(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicComplex.valuation_p
    # Valued.v (p : ℂ_[p]) = 1 / (p : ℝ≥0)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Valued_v", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OLit(1), OOp("p", (OVar("colon"), OVar("ge_0"),))))
            results.append((rhs, "Mathlib: PadicComplex_valuation_p"))
        except Exception:
            pass
    return results


def _r0239_hom_eq_embedding(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicComplex.RankOne.hom_eq_embedding
    # RankOne.hom (PadicComplex.valued p).v = embedding
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "RankOne_hom", 1)
    if args is not None:
        try:
            rhs = OVar("embedding")
            results.append((rhs, "Mathlib: PadicComplex_RankOne_hom_eq_embedding"))
        except Exception:
            pass
    return results


def _r0240_norm_extends(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicComplex.norm_extends
    # ‖(x : ℂ_[p])‖ = ‖x‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x")
            results.append((rhs, "Mathlib: PadicComplex_norm_extends"))
    except Exception:
        pass
    return results


def _r0241_norm_eq_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicComplex.norm_eq_norm
    # ‖x‖ = Valued.v.norm x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Valued_v_norm", (OVar("x"),))
            results.append((rhs, "Mathlib: PadicComplex_norm_eq_norm"))
    except Exception:
        pass
    return results


def _r0242_nnnorm_extends(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicComplex.nnnorm_extends
    # ‖(x : ℂ_[p])‖₊ = ‖x‖₊
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x")
            results.append((rhs, "Mathlib: PadicComplex_nnnorm_extends"))
    except Exception:
        pass
    return results


def _r0243_coe_adicCompletionIntegersEquiv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_adicCompletionIntegersEquiv_apply
    # (adicCompletionIntegersEquiv R p x) = adicCompletionEquiv R p x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adicCompletionIntegersEquiv", 3)
    if args is not None:
        try:
            rhs = OOp("adicCompletionEquiv", (args[0], args[1], args[2],))
            results.append((rhs, "Mathlib: PadicInt_coe_adicCompletionIntegersEquiv_apply"))
        except Exception:
            pass
    return results


def _r0244_coe_adicCompletionIntegersEquiv_symm_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_adicCompletionIntegersEquiv_symm_apply
    # (adicCompletionIntegersEquiv R p).symm x = (adicCompletionEquiv R p).symm x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adicCompletionIntegersEquiv_R_p_symm", 1)
    if args is not None:
        try:
            rhs = OOp("adicCompletionEquiv_R_p_symm", (args[0],))
            results.append((rhs, "Mathlib: PadicInt_coe_adicCompletionIntegersEquiv_symm_apply"))
        except Exception:
            pass
    return results


def _r0245_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.ext
    # (x : ℚ_[p]) = y → x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: PadicInt_ext"))
    except Exception:
        pass
    return results


def _r0246_mk_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.mk_zero
    # (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_h", 2)
    if args is not None:
        try:
            rhs = OOp("_0", (args[0], args[1],))
            results.append((rhs, "Mathlib: PadicInt_mk_zero"))
        except Exception:
            pass
    return results


def _r0247_coe_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_sum
    # (((∑ z ∈ s, f z) : ℤ_[p]) : ℚ_[p]) = ∑ z ∈ s, (f z : ℚ_[p])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z_in_s_f_z_colon_p", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("z"),)), OOp("s", (OOp("f", (OVar("z"), args[0], args[1],)),))))
            results.append((rhs, "Mathlib: PadicInt_coe_sum"))
        except Exception:
            pass
    return results


def _r0248_intCast_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.intCast_eq
    # (z1 : ℤ_[p]) = z2 ↔ z1 = z2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z1", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("z2"), OVar("z1"))), OVar("z2")))
            results.append((rhs, "Mathlib: PadicInt_intCast_eq"))
        except Exception:
            pass
    return results


def _r0249_norm_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_def
    # ‖z‖ = ‖(z : ℚ_[p])‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z_colon_p")
            results.append((rhs, "Mathlib: PadicInt_norm_def"))
    except Exception:
        pass
    return results


def _r0250_norm_add_eq_max_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_add_eq_max_of_ne
    # ‖q‖ ≠ ‖r‖ → ‖q + r‖ = max ‖q‖ ‖r‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("max", (args[0], args[1],))
            results.append((rhs, "Mathlib: PadicInt_norm_add_eq_max_of_ne"))
        except Exception:
            pass
    return results


def _r0251_norm_eq_of_norm_add_lt_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_eq_of_norm_add_lt_right
    # ‖z1‖ = ‖z2‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z2")
            results.append((rhs, "Mathlib: PadicInt_norm_eq_of_norm_add_lt_right"))
    except Exception:
        pass
    return results


def _r0252_norm_eq_of_norm_add_lt_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_eq_of_norm_add_lt_left
    # ‖z1‖ = ‖z2‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z2")
            results.append((rhs, "Mathlib: PadicInt_norm_eq_of_norm_add_lt_left"))
    except Exception:
        pass
    return results


def _r0253_padic_norm_e_of_padicInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.padic_norm_e_of_padicInt
    # ‖(z : ℚ_[p])‖ = ‖z‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z")
            results.append((rhs, "Mathlib: PadicInt_padic_norm_e_of_padicInt"))
    except Exception:
        pass
    return results


def _r0254_norm_eq_padic_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_eq_padic_norm
    # @norm ℤ_[p] _ ⟨q, hq⟩ = ‖q‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_norm", 3)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: PadicInt_norm_eq_padic_norm"))
        except Exception:
            pass
    return results


def _r0255_one_le_norm_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.one_le_norm_iff
    # 1 ≤ ‖x‖ ↔ ‖x‖ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PadicInt_one_le_norm_iff"))
        except Exception:
            pass
    return results


def _r0256_norm_natCast_p_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_natCast_p_sub_one
    # ‖((p - 1 : ℕ) : ℤ_[p])‖ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_minus_1_colon_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PadicInt_norm_natCast_p_sub_one"))
    except Exception:
        pass
    return results


def _r0257_norm_natCast_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_natCast_eq_one_iff
    # ‖(n : ℤ_[p])‖ = 1 ↔ p.Coprime n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OLit(1), OOp("p_Coprime", (OVar("n"),))))
            results.append((rhs, "Mathlib: PadicInt_norm_natCast_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0258_norm_intCast_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_intCast_eq_one_iff
    # ‖(z : ℤ_[p])‖ = 1 ↔ IsCoprime z p
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OLit(1), OOp("IsCoprime", (OVar("z"), OVar("p"),))))
            results.append((rhs, "Mathlib: PadicInt_norm_intCast_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0259_valuation_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.valuation_coe
    # (x : ℚ_[p]).valuation = x.valuation
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_colon_p_valuation")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_valuation")
            results.append((rhs, "Mathlib: PadicInt_valuation_coe"))
    except Exception:
        pass
    return results


def _r0260_valuation_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.valuation_mul
    # (x * y).valuation = x.valuation + y.valuation
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_star_y_valuation")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("x_valuation"), OVar("y_valuation")))
            results.append((rhs, "Mathlib: PadicInt_valuation_mul"))
    except Exception:
        pass
    return results


def _r0261_valuation_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.valuation_pow
    # (x ^ n).valuation = n * x.valuation
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pow_n_valuation")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("n"), OVar("x_valuation")))
            results.append((rhs, "Mathlib: PadicInt_valuation_pow"))
    except Exception:
        pass
    return results


def _r0262_valuation_p_pow_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.valuation_p_pow_mul
    # ((p : ℤ_[p]) ^ n * c).valuation = n + c.valuation
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_colon_p_pow_n_star_c_valuation")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("n"), OVar("c_valuation")))
            results.append((rhs, "Mathlib: PadicInt_valuation_p_pow_mul"))
    except Exception:
        pass
    return results


def _r0263_mul_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.mul_inv
    # ∀ {z : ℤ_[p]}, ‖z‖ = 1 → z * z.inv = 1   | ⟨k, _⟩, h =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("pipe"), OVar("k"), OVar("h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: PadicInt_mul_inv"))
        except Exception:
            pass
    return results


def _r0264_inv_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.inv_mul
    # z.inv * z = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PadicInt_inv_mul"))
        except Exception:
            pass
    return results


def _r0265_isUnit_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.isUnit_iff
    # IsUnit z ↔ ‖z‖ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PadicInt_isUnit_iff"))
        except Exception:
            pass
    return results


def _r0266_val_mkUnits(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.val_mkUnits
    # (mkUnits h).val = ⟨u, h.le⟩
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mkUnits_h_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("u_h_le")
            results.append((rhs, "Mathlib: PadicInt_val_mkUnits"))
    except Exception:
        pass
    return results


def _r0267_norm_units(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_units
    # ‖(u : ℤ_[p])‖ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("u_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PadicInt_norm_units"))
    except Exception:
        pass
    return results


def _r0268_unitCoeff_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.unitCoeff_coe
    # (unitCoeff hx : ℚ_[p]) = x * (p : ℚ_[p]) ^ (-x.valuation : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unitCoeff", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("x"), OOp("**", (OOp("p", (args[1], args[2],)), OOp("minus_x_valuation", (args[1], OVar("_unknown"),))))))
            results.append((rhs, "Mathlib: PadicInt_unitCoeff_coe"))
        except Exception:
            pass
    return results


def _r0269_stationary(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.stationary
    # ∃ N, ∀ m n, N ≤ m → N ≤ n → padicNorm p (f n) = padicNorm p (f m)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "padicNorm", 2)
    if args is not None:
        try:
            rhs = OOp("padicNorm", (args[0], OOp("f", (OVar("m"),)),))
            results.append((rhs, "Mathlib: PadicSeq_stationary"))
        except Exception:
            pass
    return results


def _r0270_stationaryPoint_spec(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.stationaryPoint_spec
    # ∀ {m n},       stationaryPoint hf ≤ m → stationaryPoint hf ≤ n → padicNorm p (f n) = padicNorm p (f m)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "padicNorm", 2)
    if args is not None:
        try:
            rhs = OOp("padicNorm", (args[0], OOp("f", (OVar("m"),)),))
            results.append((rhs, "Mathlib: PadicSeq_stationaryPoint_spec"))
        except Exception:
            pass
    return results


def _r0271_norm_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.norm_zero_iff
    # f.norm = 0 ↔ f ≈ 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_norm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OLit(0), OOp("f", (OVar("_unknown"), OLit(0),))))
            results.append((rhs, "Mathlib: PadicSeq_norm_zero_iff"))
    except Exception:
        pass
    return results


def _r0272_norm_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.norm_mul
    # (f * g).norm = f.norm * g.norm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_star_g_norm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("f_norm"), OVar("g_norm")))
            results.append((rhs, "Mathlib: PadicSeq_norm_mul"))
    except Exception:
        pass
    return results


def _r0273_eq_zero_iff_equiv_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.eq_zero_iff_equiv_zero
    # mk f = 0 ↔ f ≈ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OOp("f", (OVar("_unknown"), OLit(0),))))
            results.append((rhs, "Mathlib: PadicSeq_eq_zero_iff_equiv_zero"))
        except Exception:
            pass
    return results


def _r0274_norm_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.norm_const
    # norm (const (padicNorm p) q) = padicNorm p q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "norm", 1)
    if args is not None:
        try:
            rhs = OOp("padicNorm", (OVar("p"), OVar("q"),))
            results.append((rhs, "Mathlib: PadicSeq_norm_const"))
        except Exception:
            pass
    return results


def _r0275_norm_values_discrete(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.norm_values_discrete
    # ∃ z : ℤ, a.norm = (p : ℚ) ^ (-z)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 4)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("p", (args[1], args[2],)), OVar("minus_z")))
            results.append((rhs, "Mathlib: PadicSeq_norm_values_discrete"))
        except Exception:
            pass
    return results


def _r0276_norm_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.norm_one
    # norm (1 : PadicSeq p) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "norm", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PadicSeq_norm_one"))
        except Exception:
            pass
    return results


def _r0277_norm_eq_of_equiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.norm_eq_of_equiv
    # padicNorm p (f (stationaryPoint hf)) = padicNorm p (g (stationaryPoint hg))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "padicNorm", 2)
    if args is not None:
        try:
            rhs = OOp("padicNorm", (args[0], OOp("g", (OOp("stationaryPoint", (OVar("hg"),)),)),))
            results.append((rhs, "Mathlib: PadicSeq_norm_eq_of_equiv"))
        except Exception:
            pass
    return results


def _r0278_norm_equiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.norm_equiv
    # f.norm = g.norm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_norm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_norm")
            results.append((rhs, "Mathlib: PadicSeq_norm_equiv"))
    except Exception:
        pass
    return results


def _r0279_norm_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.norm_eq
    # f.norm = g.norm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_norm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_norm")
            results.append((rhs, "Mathlib: PadicSeq_norm_eq"))
    except Exception:
        pass
    return results


def _r0280_norm_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.norm_neg
    # (-a).norm = a.norm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_a_norm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a_norm")
            results.append((rhs, "Mathlib: PadicSeq_norm_neg"))
    except Exception:
        pass
    return results


def _r0281_norm_eq_of_add_equiv_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.norm_eq_of_add_equiv_zero
    # f.norm = g.norm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_norm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_norm")
            results.append((rhs, "Mathlib: PadicSeq_norm_eq_of_add_equiv_zero"))
    except Exception:
        pass
    return results


def _r0282_add_eq_max_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicSeq.add_eq_max_of_ne
    # (f + g).norm = max f.norm g.norm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_plus_g_norm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("max", (OVar("f_norm"), OVar("g_norm"),))
            results.append((rhs, "Mathlib: PadicSeq_add_eq_max_of_ne"))
    except Exception:
        pass
    return results


def _r0283_zero_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.zero_def
    # (0 : ℚ_[p]) = ⟦0⟧
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0", 2)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Padic_zero_def"))
        except Exception:
            pass
    return results


def _r0284_mk_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.mk_eq
    # mk f = mk g ↔ f ≈ g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("pair", (OVar("g"),)), OOp("f", (OVar("_unknown"), OVar("g"),))))
            results.append((rhs, "Mathlib: Padic_mk_eq"))
        except Exception:
            pass
    return results


def _r0285_const_equiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.const_equiv
    # const (padicNorm p) q ≈ const (padicNorm p) r ↔ q = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("r")
            results.append((rhs, "Mathlib: Padic_const_equiv"))
        except Exception:
            pass
    return results


def _r0286_coe_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.coe_inj
    # (↑q : ℚ_[p]) = ↑r ↔ q = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "q", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("r"), OVar("q"))), OVar("r")))
            results.append((rhs, "Mathlib: Padic_coe_inj"))
        except Exception:
            pass
    return results


def _r0287_coe_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.coe_add
    # ∀ {x y : ℚ}, (↑(x + y) : ℚ_[p]) = ↑x + ↑y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_plus_y", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Padic_coe_add"))
        except Exception:
            pass
    return results


def _r0288_coe_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.coe_neg
    # ∀ {x : ℚ}, (↑(-x) : ℚ_[p]) = -↑x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_x", 2)
    if args is not None:
        try:
            rhs = OVar("minus_x")
            results.append((rhs, "Mathlib: Padic_coe_neg"))
        except Exception:
            pass
    return results


def _r0289_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.coe_mul
    # ∀ {x y : ℚ}, (↑(x * y) : ℚ_[p]) = ↑x * ↑y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_star_y", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Padic_coe_mul"))
        except Exception:
            pass
    return results


def _r0290_coe_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.coe_sub
    # ∀ {x y : ℚ}, (↑(x - y) : ℚ_[p]) = ↑x - ↑y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_minus_y", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Padic_coe_sub"))
        except Exception:
            pass
    return results


def _r0291_coe_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.coe_div
    # ∀ {x y : ℚ}, (↑(x / y) : ℚ_[p]) = ↑x / ↑y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_slash_y", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Padic_coe_div"))
        except Exception:
            pass
    return results


def _r0292_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.coe_one
    # (↑(1 : ℚ) : ℚ_[p]) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Padic_coe_one"))
        except Exception:
            pass
    return results


def _r0293_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.coe_zero
    # (↑(0 : ℚ) : ℚ_[p]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Padic_coe_zero"))
        except Exception:
            pass
    return results


def _r0294_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.padicNormE.mul
    # ‖q * r‖ = ‖q‖ * ‖r‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (args[0], args[1]))
            results.append((rhs, "Mathlib: Padic_padicNormE_mul"))
        except Exception:
            pass
    return results


def _r0295_is_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.padicNormE.is_norm
    # ↑(padicNormE q) = ‖q‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("padicNormE_q")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q")
            results.append((rhs, "Mathlib: Padic_padicNormE_is_norm"))
    except Exception:
        pass
    return results


def _r0296_add_eq_max_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.add_eq_max_of_ne
    # ‖q + r‖ = max ‖q‖ ‖r‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("max", (args[0], args[1],))
            results.append((rhs, "Mathlib: Padic_add_eq_max_of_ne"))
        except Exception:
            pass
    return results


def _r0297_eq_padicNorm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.eq_padicNorm
    # ‖(q : ℚ_[p])‖ = padicNorm p q
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("padicNorm", (OVar("p"), OVar("q"),))
            results.append((rhs, "Mathlib: Padic_eq_padicNorm"))
    except Exception:
        pass
    return results


def _r0298_norm_p(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_p
    # ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_colon_inv")
            results.append((rhs, "Mathlib: Padic_norm_p"))
    except Exception:
        pass
    return results


def _r0299_norm_p_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_p_zpow
    # ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("p", (OVar("colon"), OVar("_unknown"),)), OVar("minus_n")))
            results.append((rhs, "Mathlib: Padic_norm_p_zpow"))
        except Exception:
            pass
    return results


def _r0300_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.padicNormE.image
    # q ≠ 0 → ∃ n : ℤ, ‖q‖ = ↑((p : ℚ) ^ (-n))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 4)
    if args is not None:
        try:
            rhs = OVar("p_colon_pow_minus_n")
            results.append((rhs, "Mathlib: Padic_padicNormE_image"))
        except Exception:
            pass
    return results


def _r0301_is_rat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.padicNormE.is_rat
    # ∃ q' : ℚ, ‖q‖ = q'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 4)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Padic_padicNormE_is_rat"))
        except Exception:
            pass
    return results


def _r0302_eq_ratNorm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.eq_ratNorm
    # ‖q‖ = ratNorm q
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ratNorm", (OVar("q"),))
            results.append((rhs, "Mathlib: Padic_eq_ratNorm"))
    except Exception:
        pass
    return results


def _r0303_norm_rat_le_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_rat_le_one
    # ∀ {q : ℚ} (_ : ¬p ∣ q.den), ‖(q : ℚ_[p])‖ ≤ 1   | ⟨n, d, hn, hd⟩ => fun hq : ¬p ∣ d ↦     if hnz : n = 0 then
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("gt", (OVar("fun"), OVar("hq"), OVar("colon"), OOp("not", (OVar("p"),)), OVar("_unknown"), OVar("d"), OVar("_unknown"), OVar("if"), OVar("hnz"), OVar("colon"), OVar("n"),)), OOp("_0", (OVar("then"),))))
            results.append((rhs, "Mathlib: Padic_norm_rat_le_one"))
        except Exception:
            pass
    return results


def _r0304_norm_intCast_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_intCast_eq_one_iff
    # ‖(z : ℚ_[p])‖ = 1 ↔ IsCoprime z p
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OLit(1), OOp("IsCoprime", (OVar("z"), OVar("p"),))))
            results.append((rhs, "Mathlib: Padic_norm_intCast_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0305_norm_natCast_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_natCast_eq_one_iff
    # ‖(n : ℚ_[p])‖ = 1 ↔ p.Coprime n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OLit(1), OOp("p_Coprime", (OVar("n"),))))
            results.append((rhs, "Mathlib: Padic_norm_natCast_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0306_norm_eq_of_norm_add_lt_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_eq_of_norm_add_lt_right
    # ‖z1‖ = ‖z2‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z2")
            results.append((rhs, "Mathlib: Padic_norm_eq_of_norm_add_lt_right"))
    except Exception:
        pass
    return results


def _r0307_norm_eq_of_norm_add_lt_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_eq_of_norm_add_lt_left
    # ‖z1‖ = ‖z2‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z2")
            results.append((rhs, "Mathlib: Padic_norm_eq_of_norm_add_lt_left"))
    except Exception:
        pass
    return results


def _r0308_norm_eq_of_norm_sub_lt_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_eq_of_norm_sub_lt_right
    # ‖z1‖ = ‖z2‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z2")
            results.append((rhs, "Mathlib: Padic_norm_eq_of_norm_sub_lt_right"))
    except Exception:
        pass
    return results


def _r0309_norm_eq_of_norm_sub_lt_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_eq_of_norm_sub_lt_left
    # ‖z1‖ = ‖z2‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z2")
            results.append((rhs, "Mathlib: Padic_norm_eq_of_norm_sub_lt_left"))
    except Exception:
        pass
    return results


def _r0310_norm_natCast_p_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.norm_natCast_p_sub_one
    # ‖((p - 1 : ℕ) : ℚ_[p])‖ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_minus_1_colon_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Padic_norm_natCast_p_sub_one"))
    except Exception:
        pass
    return results


def _r0311_zmod_congr_of_sub_mem_span_aux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmod_congr_of_sub_mem_span_aux
    # (a : ZMod (p ^ n)) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: PadicInt_zmod_congr_of_sub_mem_span_aux"))
        except Exception:
            pass
    return results


def _r0312_zmod_congr_of_sub_mem_span(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmod_congr_of_sub_mem_span
    # (a : ZMod (p ^ n)) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: PadicInt_zmod_congr_of_sub_mem_span"))
        except Exception:
            pass
    return results


def _r0313_zmod_congr_of_sub_mem_max_ideal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmod_congr_of_sub_mem_max_ideal
    # (m : ZMod p) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 3)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: PadicInt_zmod_congr_of_sub_mem_max_ideal"))
        except Exception:
            pass
    return results


def _r0314_zmodRepr_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmodRepr_unique
    # zmodRepr x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zmodRepr", 1)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: PadicInt_zmodRepr_unique"))
        except Exception:
            pass
    return results


def _r0315_zmodRepr_eq_zero_of_dvd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmodRepr_eq_zero_of_dvd
    # x.zmodRepr = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_zmodRepr")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PadicInt_zmodRepr_eq_zero_of_dvd"))
    except Exception:
        pass
    return results


def _r0316_zmodRepr_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmodRepr_zero
    # (0 : ℤ_[p]).zmodRepr = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_p_zmodRepr")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PadicInt_zmodRepr_zero"))
    except Exception:
        pass
    return results


def _r0317_norm_natCast_zmodRepr_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_natCast_zmodRepr_eq_one_iff
    # ‖(x.zmodRepr : ℤ_[p])‖ = 1 ↔ ‖x‖ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_zmodRepr_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("x"))), OLit(1)))
            results.append((rhs, "Mathlib: PadicInt_norm_natCast_zmodRepr_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0318_zmodRepr_eq_zero_iff_dvd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmodRepr_eq_zero_iff_dvd
    # x.zmodRepr = 0 ↔ (p : ℤ_[p]) ∣ x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_zmodRepr")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OLit(0), OOp("p_colon_p", (OVar("_unknown"), OVar("x"),))))
            results.append((rhs, "Mathlib: PadicInt_zmodRepr_eq_zero_iff_dvd"))
    except Exception:
        pass
    return results


def _r0319_norm_natCast_zmodRepr_eq_one_iff_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_natCast_zmodRepr_eq_one_iff_ne
    # ‖(x.zmodRepr : ℤ_[p])‖ = 1 ↔ x.zmodRepr ≠ 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_zmodRepr_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("!=", (OOp("iff", (OLit(1), OVar("x_zmodRepr"))), OLit(0)))
            results.append((rhs, "Mathlib: PadicInt_norm_natCast_zmodRepr_eq_one_iff_ne"))
    except Exception:
        pass
    return results


def _r0320_norm_natCast_zmodRepr_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_natCast_zmodRepr_eq
    # ‖(x.zmodRepr : ℤ_[p])‖ = 1 ∨ x.zmodRepr = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_zmodRepr_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("or", (OLit(1), OVar("x_zmodRepr"))), OLit(0)))
            results.append((rhs, "Mathlib: PadicInt_norm_natCast_zmodRepr_eq"))
    except Exception:
        pass
    return results


def _r0321_zmodRepr_natCast_zmodRepr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmodRepr_natCast_zmodRepr
    # (x.zmodRepr : ℤ_[p]).zmodRepr = x.zmodRepr
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_zmodRepr_colon_p_zmodRepr")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_zmodRepr")
            results.append((rhs, "Mathlib: PadicInt_zmodRepr_natCast_zmodRepr"))
    except Exception:
        pass
    return results


def _r0322_norm_natCast_zmodRepr_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.norm_natCast_zmodRepr_eq_iff
    # ‖(x.zmodRepr : ℤ_[p])‖ = ‖x‖ ↔ ‖x‖ = 1 ∨ x = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_zmodRepr_colon_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("x"), OVar("x"))), OOp("==", (OOp("or", (OLit(1), OVar("x"))), OLit(0)))))
            results.append((rhs, "Mathlib: PadicInt_norm_natCast_zmodRepr_eq_iff"))
    except Exception:
        pass
    return results


def _r0323_zmodRepr_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmodRepr_natCast
    # zmodRepr (n : ℤ_[p]) = n % p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zmodRepr", 1)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("p"),))
            results.append((rhs, "Mathlib: PadicInt_zmodRepr_natCast"))
        except Exception:
            pass
    return results


def _r0324_zmodRepr_natCast_of_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmodRepr_natCast_of_lt
    # zmodRepr (n : ℤ_[p]) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zmodRepr", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: PadicInt_zmodRepr_natCast_of_lt"))
        except Exception:
            pass
    return results


def _r0325_zmodRepr_natCast_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmodRepr_natCast_ofNat
    # zmodRepr (ofNat(n) : ℤ_[p]) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zmodRepr", 1)
    if args is not None:
        try:
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: PadicInt_zmodRepr_natCast_ofNat"))
        except Exception:
            pass
    return results


def _r0326_val_toZMod_eq_zmodRepr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.val_toZMod_eq_zmodRepr
    # (toZMod x).val = x.zmodRepr
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toZMod_x_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_zmodRepr")
            results.append((rhs, "Mathlib: PadicInt_val_toZMod_eq_zmodRepr"))
    except Exception:
        pass
    return results


def _r0327_zmodRepr_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmodRepr_mul
    # (x * y).zmodRepr = x.zmodRepr * y.zmodRepr % p
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_star_y_zmodRepr")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("x_zmodRepr"), OOp("y_zmodRepr", (OVar("_unknown"), OVar("p"),))))
            results.append((rhs, "Mathlib: PadicInt_zmodRepr_mul"))
    except Exception:
        pass
    return results


def _r0328_toZMod_eq_residueField_comp_residue(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.toZMod_eq_residueField_comp_residue
    # toZMod (p := p) = residueField.toRingHom.comp (IsLocalRing.residue _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toZMod", 1)
    if args is not None:
        try:
            rhs = OOp("residueField_toRingHom_comp", (OOp("IsLocalRing_residue", (OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: PadicInt_toZMod_eq_residueField_comp_residue"))
        except Exception:
            pass
    return results


def _r0329_zmod_cast_comp_toZModPow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.zmod_cast_comp_toZModPow
    # (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (@toZModPow p _ n) = @toZModPow p _ m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ZMod_castHom_pow_dvd_pow_p_h_ZMod_p_pow_m_comp", 1)
    if args is not None:
        try:
            rhs = OOp("at_toZModPow", (OVar("p"), OVar("_unknown"), OVar("m"),))
            results.append((rhs, "Mathlib: PadicInt_zmod_cast_comp_toZModPow"))
        except Exception:
            pass
    return results


def _r0330_cast_toZModPow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.cast_toZModPow
    # ZMod.cast (toZModPow n x) = toZModPow m x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ZMod_cast", 1)
    if args is not None:
        try:
            rhs = OOp("toZModPow", (OVar("m"), OVar("x"),))
            results.append((rhs, "Mathlib: PadicInt_cast_toZModPow"))
        except Exception:
            pass
    return results


def _r0331_coe_withValRingEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.coe_withValRingEquiv
    # ⇑(Padic.withValRingEquiv (p := p)) = Completion.extension       ((↑) ∘ (WithVal.equiv (Rat.padicValuation p)))
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Padic_withValRingEquiv_p_colon_eq_p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Completion_extension", (OOp("comp", (OVar("_unknown"), OOp("WithVal_equiv", (OOp("Rat_padicValuation", (OVar("p"),)),)))),))
            results.append((rhs, "Mathlib: Padic_coe_withValRingEquiv"))
    except Exception:
        pass
    return results


def _r0332_coe_withValRingEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.coe_withValRingEquiv_symm
    # ⇑(Padic.withValRingEquiv (p := p)).symm =       Padic.isDenseInducing_cast_withVal.extend Completion.coe'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Padic_withValRingEquiv_p_colon_eq_p_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Padic_isDenseInducing_cast_withVal_extend", (OVar("Completion_coe_prime"),))
            results.append((rhs, "Mathlib: Padic_coe_withValRingEquiv_symm"))
    except Exception:
        pass
    return results


def _r0333_toEquiv_withValUniformEquiv_eq_toEquiv_w(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv
    # (withValUniformEquiv (p := p) : (Rat.padicValuation p).Completion ≃ ℚ_[p]) =       (withValRingEquiv (p := p) :)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "withValUniformEquiv", 5)
    if args is not None:
        try:
            rhs = OOp("withValRingEquiv", (OOp("p", (OVar("colon_eq"), args[4],)), args[1],))
            results.append((rhs, "Mathlib: Padic_toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv"))
        except Exception:
            pass
    return results


def _r0334_withValUniformEquiv_cast_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Padic.withValUniformEquiv_cast_apply
    # Padic.withValUniformEquiv (p := p) x = WithVal.equiv (Rat.padicValuation p) x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Padic_withValUniformEquiv", 2)
    if args is not None:
        try:
            rhs = OOp("WithVal_equiv", (OOp("Rat_padicValuation", (OVar("p"),)), args[1],))
            results.append((rhs, "Mathlib: Padic_withValUniformEquiv_cast_apply"))
        except Exception:
            pass
    return results


def _r0335_wilsons_lemma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.wilsons_lemma
    # ((p - 1)! : ZMod p) = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_minus_1_bang", 3)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: ZMod_wilsons_lemma"))
        except Exception:
            pass
    return results


def _r0336_prod_Ico_one_prime(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZMod.prod_Ico_one_prime
    # ∏ x ∈ Ico 1 p, (x : ZMod p) = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: ZMod_prod_Ico_one_prime"))
        except Exception:
            pass
    return results


def _r0337_re_ofInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_ofInt
    # (ofInt n : ℤ√d).re = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofInt_n_colon_d_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Zsqrtd_re_ofInt"))
    except Exception:
        pass
    return results


def _r0338_im_ofInt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_ofInt
    # (ofInt n : ℤ√d).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofInt_n_colon_d_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Zsqrtd_im_ofInt"))
    except Exception:
        pass
    return results


def _r0339_re_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_zero
    # (0 : ℤ√d).re = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_d_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Zsqrtd_re_zero"))
    except Exception:
        pass
    return results


def _r0340_re_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_one
    # (1 : ℤ√d).re = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_d_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Zsqrtd_re_one"))
    except Exception:
        pass
    return results


def _r0341_re_sqrtd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_sqrtd
    # (sqrtd : ℤ√d).re = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sqrtd_colon_d_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Zsqrtd_re_sqrtd"))
    except Exception:
        pass
    return results


def _r0342_add_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.add_def
    # (⟨x, y⟩ + ⟨x', y'⟩ : ℤ√d) = ⟨x + x', y + y'⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("x_plus_x_prime_y_plus_y_prime")
            results.append((rhs, "Mathlib: Zsqrtd_add_def"))
        except Exception:
            pass
    return results


def _r0343_re_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_neg
    # (-z).re = -z.re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_z_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_z_re")
            results.append((rhs, "Mathlib: Zsqrtd_re_neg"))
    except Exception:
        pass
    return results


def _r0344_re_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_mul
    # (z * w).re = z.re * w.re + d * z.im * w.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_star_w_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OOp("*", (OVar("z_re"), OVar("w_re"))), OOp("*", (OVar("d"), OOp("*", (OVar("z_im"), OVar("w_im")))))))
            results.append((rhs, "Mathlib: Zsqrtd_re_mul"))
    except Exception:
        pass
    return results


def _r0345_re_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_sub
    # (z - w).re = z.re - w.re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_minus_w_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("z_re"), OVar("w_re")))
            results.append((rhs, "Mathlib: Zsqrtd_re_sub"))
    except Exception:
        pass
    return results


def _r0346_star_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.star_mk
    # star (⟨x, y⟩ : ℤ√d) = ⟨x, -y⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "star", 1)
    if args is not None:
        try:
            rhs = OVar("x_minus_y")
            results.append((rhs, "Mathlib: Zsqrtd_star_mk"))
        except Exception:
            pass
    return results


def _r0347_re_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_natCast
    # (n : ℤ√d).re = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_d_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Zsqrtd_re_natCast"))
    except Exception:
        pass
    return results


def _r0348_re_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.re_intCast
    # (n : ℤ√d).re = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_d_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Zsqrtd_re_intCast"))
    except Exception:
        pass
    return results


def _r0349_ofInt_eq_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.ofInt_eq_intCast
    # (ofInt n : ℤ√d) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofInt", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Zsqrtd_ofInt_eq_intCast"))
        except Exception:
            pass
    return results


def _r0350_im_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.im_smul
    # (↑a * b).im = a * b.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_star_b_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("a"), OVar("b_im")))
            results.append((rhs, "Mathlib: Zsqrtd_im_smul"))
    except Exception:
        pass
    return results


def _r0351_muld_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.muld_val
    # sqrtd (d := d) * ⟨x, y⟩ = ⟨d * y, x⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("d_star_y_x")
            results.append((rhs, "Mathlib: Zsqrtd_muld_val"))
        except Exception:
            pass
    return results


def _r0352_mul_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.mul_star
    # (⟨x, y⟩ * star ⟨x, y⟩ : ℤ√d) = x * x - d * y * y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("x"), OOp("*", (OOp("-", (OVar("x"), OVar("d"))), OOp("*", (OVar("y"), OVar("y")))))))
            results.append((rhs, "Mathlib: Zsqrtd_mul_star"))
        except Exception:
            pass
    return results


def _r0353_eq_of_smul_eq_smul_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.eq_of_smul_eq_smul_left
    # b = c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("c")
            results.append((rhs, "Mathlib: Zsqrtd_eq_of_smul_eq_smul_left"))
    except Exception:
        pass
    return results


def _r0354_gcd_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.gcd_eq_zero_iff
    # Int.gcd a.re a.im = 0 ↔ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Int_gcd", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("a"))), OLit(0)))
            results.append((rhs, "Mathlib: Zsqrtd_gcd_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0355_exists_coprime_of_gcd_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Zsqrtd.exists_coprime_of_gcd_pos
    # ∃ b : ℤ√d, a = ((Int.gcd a.re a.im : ℤ) : ℤ√d) * b ∧ IsCoprime b.re b.im
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 4)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("*", (OOp("Int_gcd_a_re_a_im_colon", (args[1], args[2],)), args[0])), OOp("IsCoprime", (OVar("b_re"), OVar("b_im"),))))
            results.append((rhs, "Mathlib: Zsqrtd_exists_coprime_of_gcd_pos"))
        except Exception:
            pass
    return results


def _r0356_dividedPowers_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.dividedPowers_eq
    # (dividedPowers p).dpow n x = open Classical in       if hx : x ∈ Ideal.span {(p : ℤ_[p])} then ⟨dpow' p n x, dpow'_int p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dividedPowers_p_dpow", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("open", (OVar("Classical"), OVar("in"), OVar("if"), OVar("hx"), OVar("colon"), args[1],)), OOp("Ideal_span", (OVar("p_colon_p"), OVar("then"), OVar("dpow_prime_p_n_x_dpow_prime_int_p_n_hx"), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: PadicInt_dividedPowers_eq"))
        except Exception:
            pass
    return results


def _r0357_coe_dpow_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PadicInt.coe_dpow_eq
    # ((dividedPowers p).dpow n x : ℚ_[p]) = open Classical in       if _ : x ∈ Ideal.span {(p : ℤ_[p])} then inverse (n ! : ℚ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dividedPowers_p_dpow", 4)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("in", (OOp("open", (OVar("Classical"), OVar("in"), OVar("if"), OVar("_unknown"), args[2], args[1],)), OOp("Ideal_span", (OVar("p_colon_p"), OVar("then"), OVar("inverse"), OOp("n", (OOp("not", (OVar("_"),)), args[2], args[3],)),)))), OOp("**", (args[1], OOp("n", (OVar("else"), OLit(0),))))))
            results.append((rhs, "Mathlib: PadicInt_coe_dpow_eq"))
        except Exception:
            pass
    return results


def _r0358_iInf_localization_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.iInf_localization_eq_bot
    # ⨅ v : PrimeSpectrum R,     Localization.subalgebra.ofField K _ (v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 8)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: PrimeSpectrum_iInf_localization_eq_bot"))
        except Exception:
            pass
    return results


def _r0359_piLocalizationToMaximal_comp_toPiLocaliz(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.piLocalizationToMaximal_comp_toPiLocalization
    # (piLocalizationToMaximal R).comp (toPiLocalization R) = MaximalSpectrum.toPiLocalization R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "piLocalizationToMaximal_R_comp", 1)
    if args is not None:
        try:
            rhs = OOp("MaximalSpectrum_toPiLocalization", (OVar("R"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_piLocalizationToMaximal_comp_toPiLocalization"))
        except Exception:
            pass
    return results


def _r0360_mapPiLocalization_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.mapPiLocalization_naturality
    # (mapPiLocalization f).comp (toPiLocalization R) = (toPiLocalization S).comp f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapPiLocalization_f_comp", 1)
    if args is not None:
        try:
            rhs = OOp("toPiLocalization_S_comp", (OVar("f"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_mapPiLocalization_naturality"))
        except Exception:
            pass
    return results


def _r0361_mapPiLocalization_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.mapPiLocalization_id
    # mapPiLocalization (.id R) = .id _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapPiLocalization", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_mapPiLocalization_id"))
        except Exception:
            pass
    return results


def _r0362_mapPiLocalization_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.mapPiLocalization_comp
    # mapPiLocalization (g.comp f) = (mapPiLocalization g).comp (mapPiLocalization f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapPiLocalization", 1)
    if args is not None:
        try:
            rhs = OOp("mapPiLocalization_g_comp", (OOp("mapPiLocalization", (OVar("f"),)),))
            results.append((rhs, "Mathlib: PrimeSpectrum_mapPiLocalization_comp"))
        except Exception:
            pass
    return results


def _r0363_range_asIdeal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.range_asIdeal
    # Set.range PrimeSpectrum.asIdeal = {J : Ideal R | J.IsPrime}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OVar("J_colon_Ideal_R_pipe_J_IsPrime")
            results.append((rhs, "Mathlib: PrimeSpectrum_range_asIdeal"))
        except Exception:
            pass
    return results


def _r0364_primeSpectrumProd_symm_inl_asIdeal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.primeSpectrumProd_symm_inl_asIdeal
    # ((primeSpectrumProd R S).symm <| Sum.inl x).asIdeal = Ideal.prod x.asIdeal ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("primeSpectrumProd_R_S_symm_lt_pipe_Sum_inl_x_asIdeal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ideal_prod", (OVar("x_asIdeal"), OVar("top"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_primeSpectrumProd_symm_inl_asIdeal"))
    except Exception:
        pass
    return results


def _r0365_primeSpectrumProd_symm_inr_asIdeal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.primeSpectrumProd_symm_inr_asIdeal
    # ((primeSpectrumProd R S).symm <| Sum.inr x).asIdeal = Ideal.prod ⊤ x.asIdeal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("primeSpectrumProd_R_S_symm_lt_pipe_Sum_inr_x_asIdeal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ideal_prod", (OVar("top"), OVar("x_asIdeal"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_primeSpectrumProd_symm_inr_asIdeal"))
    except Exception:
        pass
    return results


def _r0366_coe_vanishingIdeal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.coe_vanishingIdeal
    # (vanishingIdeal t : Set R) = { f : R | ∀ x ∈ t, f ∈ x.asIdeal }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "vanishingIdeal", 4)
    if args is not None:
        try:
            rhs = OVar("f_colon_R_pipe_forall_x_in_t_f_in_x_asIdeal")
            results.append((rhs, "Mathlib: PrimeSpectrum_coe_vanishingIdeal"))
        except Exception:
            pass
    return results


def _r0367_vanishingIdeal_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.vanishingIdeal_singleton
    # vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "vanishingIdeal", 1)
    if args is not None:
        try:
            rhs = OVar("x_asIdeal")
            results.append((rhs, "Mathlib: PrimeSpectrum_vanishingIdeal_singleton"))
        except Exception:
            pass
    return results


def _r0368_gc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.gc
    # @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun I => zeroLocus I) fun t =>       vanishingIdeal t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_GaloisConnection", 7)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("vanishingIdeal"), args[6],))
            results.append((rhs, "Mathlib: PrimeSpectrum_gc"))
        except Exception:
            pass
    return results


def _r0369_gc_set(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.gc_set
    # @GaloisConnection (Set R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t =>       vanishingIdeal t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_GaloisConnection", 7)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("vanishingIdeal"), args[6],))
            results.append((rhs, "Mathlib: PrimeSpectrum_gc_set"))
        except Exception:
            pass
    return results


def _r0370_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.BasicConstructibleSetData.map_id
    # C.map (.id _) = C
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "C_map", 1)
    if args is not None:
        try:
            rhs = OVar("C")
            results.append((rhs, "Mathlib: PrimeSpectrum_BasicConstructibleSetData_map_id"))
        except Exception:
            pass
    return results


def _r0371_toSet_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.BasicConstructibleSetData.toSet_map
    # (C.map φ).toSet = comap φ ⁻¹' C.toSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("C_map_phi_toSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comap", (OVar("phi"), OVar("inv_prime"), OVar("C_toSet"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_BasicConstructibleSetData_toSet_map"))
    except Exception:
        pass
    return results


def _r0372_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.ConstructibleSetData.map_id
    # s.map (.id _) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_map", 1)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: PrimeSpectrum_ConstructibleSetData_map_id"))
        except Exception:
            pass
    return results


def _r0373_toSet_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.ConstructibleSetData.toSet_map
    # (s.map f).toSet = comap f ⁻¹' s.toSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_map_f_toSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comap", (OVar("f"), OVar("inv_prime"), OVar("s_toSet"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_ConstructibleSetData_toSet_map"))
    except Exception:
        pass
    return results


def _r0374_exist_ltSeries_mem_one_of_mem_last(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last
    # ∃ q : LTSeries (PrimeSpectrum R),     x ∈ (q 1).asIdeal ∧ p.length = q.length ∧ p.head = q.head ∧ p.last = q.last
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OVar("q_length"), OVar("p_head"))), OOp("==", (OOp("and", (OVar("q_head"), OVar("p_last"))), OVar("q_last")))))
            results.append((rhs, "Mathlib: PrimeSpectrum_exist_ltSeries_mem_one_of_mem_last"))
        except Exception:
            pass
    return results


def _r0375_exists_image_comap_of_finite_of_free(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.exists_image_comap_of_finite_of_free
    # ∃ t : Finset R, comap (algebraMap R A) '' (zeroLocus s \\ zeroLocus {f}) = (zeroLocus t)ᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 8)
    if args is not None:
        try:
            rhs = OVar("zeroLocus_t")
            results.append((rhs, "Mathlib: PrimeSpectrum_exists_image_comap_of_finite_of_free"))
        except Exception:
            pass
    return results


def _r0376_comap_asIdeal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.comap_asIdeal
    # (comap f y).asIdeal = Ideal.comap f y.asIdeal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("comap_f_y_asIdeal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ideal_comap", (OVar("f"), OVar("y_asIdeal"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_comap_asIdeal"))
    except Exception:
        pass
    return results


def _r0377_comap_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.comap_id
    # comap (RingHom.id R) = fun x => x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 1)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("x"), OVar("eq_gt"), OVar("x"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_comap_id"))
        except Exception:
            pass
    return results


def _r0378_comap_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.comap_comp
    # comap (g.comp f) = (comap f).comp (comap g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 1)
    if args is not None:
        try:
            rhs = OOp("comap_f_comp", (OOp("comap", (OVar("g"),)),))
            results.append((rhs, "Mathlib: PrimeSpectrum_comap_comp"))
        except Exception:
            pass
    return results


def _r0379_comap_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.comap_comp_apply
    # comap (g.comp f) x = comap f (comap g x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 2)
    if args is not None:
        try:
            rhs = OOp("comap", (OVar("f"), OOp("comap", (OVar("g"), args[1],)),))
            results.append((rhs, "Mathlib: PrimeSpectrum_comap_comp_apply"))
        except Exception:
            pass
    return results


def _r0380_preimage_comap_zeroLocus_aux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.preimage_comap_zeroLocus_aux
    # comap f ⁻¹' zeroLocus s = zeroLocus (f '' s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 4)
    if args is not None:
        try:
            rhs = OOp("zeroLocus", (OOp("f", (OVar("prime_prime"), args[3],)),))
            results.append((rhs, "Mathlib: PrimeSpectrum_preimage_comap_zeroLocus_aux"))
        except Exception:
            pass
    return results


def _r0381_preimage_comap_zeroLocus(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.preimage_comap_zeroLocus
    # comap f ⁻¹' zeroLocus s = zeroLocus (f '' s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 4)
    if args is not None:
        try:
            rhs = OOp("zeroLocus", (OOp("f", (OVar("prime_prime"), args[3],)),))
            results.append((rhs, "Mathlib: PrimeSpectrum_preimage_comap_zeroLocus"))
        except Exception:
            pass
    return results


def _r0382_comapEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.comapEquiv_symm
    # (comapEquiv e).symm = comapEquiv e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("comapEquiv_e_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comapEquiv", (OVar("e_symm"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_comapEquiv_symm"))
    except Exception:
        pass
    return results


def _r0383_exists_comap_evalRingHom_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.exists_comap_evalRingHom_eq
    # ∃ (i : ι) (q : PrimeSpectrum (R i)), comap (Pi.evalRingHom R i) q = p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 5)
    if args is not None:
        try:
            rhs = OVar("p")
            results.append((rhs, "Mathlib: PrimeSpectrum_exists_comap_evalRingHom_eq"))
        except Exception:
            pass
    return results


def _r0384_iUnion_range_comap_comp_evalRingHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.iUnion_range_comap_comp_evalRingHom
    # ⋃ i, Set.range (comap ((Pi.evalRingHom R i).comp f)) = Set.range (comap f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("Set_range", (OOp("comap", (OVar("f"),)),))
            results.append((rhs, "Mathlib: PrimeSpectrum_iUnion_range_comap_comp_evalRingHom"))
        except Exception:
            pass
    return results


def _r0385_mem_range_comap_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.mem_range_comap_iff
    # p ∈ Set.range (comap f) ↔ (p.asIdeal.map f).comap f = p.asIdeal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("p_asIdeal")
            results.append((rhs, "Mathlib: PrimeSpectrum_mem_range_comap_iff"))
        except Exception:
            pass
    return results


def _r0386_residueField_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.residueField_comap
    # Set.range (comap (algebraMap R I.asIdeal.ResidueField)) = {I}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OVar("I")
            results.append((rhs, "Mathlib: PrimeSpectrum_residueField_comap"))
        except Exception:
            pass
    return results


def _r0387_isOpen_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.isOpen_iff
    # IsOpen U ↔ ∃ s, Uᶜ = zeroLocus s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("zeroLocus", (OVar("s"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_isOpen_iff"))
        except Exception:
            pass
    return results


def _r0388_isClosed_iff_zeroLocus(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.isClosed_iff_zeroLocus
    # IsClosed Z ↔ ∃ s, Z = zeroLocus s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("zeroLocus", (OVar("s"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_isClosed_iff_zeroLocus"))
        except Exception:
            pass
    return results


def _r0389_isClosed_iff_zeroLocus_ideal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    # IsClosed Z ↔ ∃ I : Ideal R, Z = zeroLocus I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("zeroLocus", (OVar("I"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_isClosed_iff_zeroLocus_ideal"))
        except Exception:
            pass
    return results


def _r0390_isClosed_iff_zeroLocus_radical_ideal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal
    # IsClosed Z ↔ ∃ I : Ideal R, I.IsRadical ∧ Z = zeroLocus I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("zeroLocus", (OVar("I"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_isClosed_iff_zeroLocus_radical_ideal"))
        except Exception:
            pass
    return results


def _r0391_zeroLocus_vanishingIdeal_eq_closure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure
    # zeroLocus (vanishingIdeal t : Set R) = closure t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zeroLocus", 1)
    if args is not None:
        try:
            rhs = OOp("closure", (OVar("t"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_zeroLocus_vanishingIdeal_eq_closure"))
        except Exception:
            pass
    return results


def _r0392_vanishingIdeal_closure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.vanishingIdeal_closure
    # vanishingIdeal (closure t) = vanishingIdeal t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "vanishingIdeal", 1)
    if args is not None:
        try:
            rhs = OOp("vanishingIdeal", (OVar("t"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_vanishingIdeal_closure"))
        except Exception:
            pass
    return results


def _r0393_closure_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.closure_singleton
    # closure ({x} : Set (PrimeSpectrum R)) = zeroLocus x.asIdeal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("zeroLocus", (OVar("x_asIdeal"),))
            results.append((rhs, "Mathlib: PrimeSpectrum_closure_singleton"))
        except Exception:
            pass
    return results


def _r0394_zeroLocus_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.zeroLocus_eq_iff
    # zeroLocus (I : Set R) = zeroLocus J ↔ I.radical = J.radical
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zeroLocus", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("zeroLocus", (OVar("J"),)), OVar("I_radical"))), OVar("J_radical")))
            results.append((rhs, "Mathlib: PrimeSpectrum_zeroLocus_eq_iff"))
        except Exception:
            pass
    return results


def _r0395_vanishingIdeal_isIrreducible(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.vanishingIdeal_isIrreducible
    # vanishingIdeal (R := R) '' {s | IsIrreducible s} = {P | P.IsPrime}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "vanishingIdeal", 3)
    if args is not None:
        try:
            rhs = OVar("P_pipe_P_IsPrime")
            results.append((rhs, "Mathlib: PrimeSpectrum_vanishingIdeal_isIrreducible"))
        except Exception:
            pass
    return results


def _r0396_vanishingIdeal_isClosed_isIrreducible(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible
    # vanishingIdeal (R := R) '' {s | IsClosed s ∧ IsIrreducible s} = {P | P.IsPrime}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "vanishingIdeal", 3)
    if args is not None:
        try:
            rhs = OVar("P_pipe_P_IsPrime")
            results.append((rhs, "Mathlib: PrimeSpectrum_vanishingIdeal_isClosed_isIrreducible"))
        except Exception:
            pass
    return results


def _r0397_comap_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.comap_apply
    # comap f x = comap f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 2)
    if args is not None:
        try:
            rhs = OOp("comap", (args[0], args[1],))
            results.append((rhs, "Mathlib: PrimeSpectrum_comap_apply"))
        except Exception:
            pass
    return results


def _r0398_localization_comap_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PrimeSpectrum.localization_comap_range
    # Set.range (comap (algebraMap R S)) = { p | Disjoint (M : Set R) p.asIdeal }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OVar("p_pipe_Disjoint_M_colon_Set_R_p_asIdeal")
            results.append((rhs, "Mathlib: PrimeSpectrum_localization_comap_range"))
        except Exception:
            pass
    return results


def _r0399_asIdeal_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsLocalRing.PrimeSpectrum.asIdeal_top
    # (⊤ : PrimeSpectrum R).asIdeal = IsLocalRing.maximalIdeal R
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_PrimeSpectrum_R_asIdeal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("IsLocalRing_maximalIdeal", (OVar("R"),))
            results.append((rhs, "Mathlib: IsLocalRing_PrimeSpectrum_asIdeal_top"))
    except Exception:
        pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_number_theory rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "**", "+", "-", "//", "<", "<=", "==", "AddMonoid_exponent", "C_map", "Even", "Fintype_card", "I", "Ico", "Ico_1_p_slash_2_succ_1_map", "Ideal", "Ideal_span", "Int_castAddHom", "Int_gcd", "IsClosed", "IsOpen", "IsSquare", "IsUnit", "LFunction", "PadicAlgCl", "Padic_withValUniformEquiv", "Pi_evalRingHom", "Pi_evalRingHom_R_i_comp", "PrimeSpectrum", "R", "RankOne_hom", "RingHom_id", "Set", "Set_range", "Valued_v", "Valued_v_x_colon_ge_0", "ZMod", "ZMod_cast", "ZMod_castHom", "ZMod_castHom_pow_dvd_pow_p_h_ZMod_p_pow_m_comp", "ZMod_lift_n_f_comp", "_0", "_0_colon", "_0_colon_PadicAlgCl_p", "_0_colon_p", "_0_h", "_1", "_1_colon", "_1_colon_p",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_number_theory axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_number_theory rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_prod_ofPNatList(term, ctx))
    results.extend(_r0001_prod_add(term, ctx))
    results.extend(_r0002_val_natCast(term, ctx))
    results.extend(_r0003_natCast_pow_eq_zero_of_le(term, ctx))
    results.extend(_r0004_castHom_comp(term, ctx))
    results.extend(_r0005_lift_castAddHom(term, ctx))
    results.extend(_r0006_lift_comp_castAddHom(term, ctx))
    results.extend(_r0007_lift_injective(term, ctx))
    results.extend(_r0008_valMinAbs_def_pos(term, ctx))
    results.extend(_r0009_natCast_natAbs_valMinAbs(term, ctx))
    results.extend(_r0010_pow_card_pow(term, ctx))
    results.extend(_r0011_completedLFunction_const_mul(term, ctx))
    results.extend(_r0012_continuousAddCharEquiv_symm_apply(term, ctx))
    results.extend(_r0013_continuousAddCharEquiv_of_norm_mul_symm(term, ctx))
    results.extend(_r0014_norm_extends(term, ctx))
    results.extend(_r0015_valuation_p(term, ctx))
    results.extend(_r0016_coe_natCast(term, ctx))
    results.extend(_r0017_coe_add(term, ctx))
    results.extend(_r0018_coe_mul(term, ctx))
    results.extend(_r0019_coe_neg(term, ctx))
    results.extend(_r0020_coe_sub(term, ctx))
    results.extend(_r0021_coe_one(term, ctx))
    results.extend(_r0022_coe_zero(term, ctx))
    results.extend(_r0023_coe_eq_zero(term, ctx))
    results.extend(_r0024_coe_natCast(term, ctx))
    results.extend(_r0025_coe_intCast(term, ctx))
    results.extend(_r0026_coe_pow(term, ctx))
    results.extend(_r0027_mk_coe(term, ctx))
    results.extend(_r0028_norm_intCast_eq_padic_norm(term, ctx))
    results.extend(_r0029_norm_p(term, ctx))
    results.extend(_r0030_norm_p_pow(term, ctx))
    results.extend(_r0031_valuation_zero(term, ctx))
    results.extend(_r0032_valuation_one(term, ctx))
    results.extend(_r0033_valuation_p(term, ctx))
    results.extend(_r0034_norm_eq_zpow_neg_valuation(term, ctx))
    results.extend(_r0035_mkUnits_eq(term, ctx))
    results.extend(_r0036_unitCoeff_spec(term, ctx))
    results.extend(_r0037_norm_p_pow(term, ctx))
    results.extend(_r0038_im_zero(term, ctx))
    results.extend(_r0039_im_one(term, ctx))
    results.extend(_r0040_im_sqrtd(term, ctx))
    results.extend(_r0041_re_add(term, ctx))
    results.extend(_r0042_im_add(term, ctx))
    results.extend(_r0043_im_neg(term, ctx))
    results.extend(_r0044_im_mul(term, ctx))
    results.extend(_r0045_im_sub(term, ctx))
    results.extend(_r0046_re_star(term, ctx))
    results.extend(_r0047_im_star(term, ctx))
    results.extend(_r0048_re_ofNat(term, ctx))
    results.extend(_r0049_im_natCast(term, ctx))
    results.extend(_r0050_im_ofNat(term, ctx))
    results.extend(_r0051_natCast_val(term, ctx))
    results.extend(_r0052_im_intCast(term, ctx))
    results.extend(_r0053_intCast_val(term, ctx))
    results.extend(_r0054_nsmul_val(term, ctx))
    results.extend(_r0055_smul_val(term, ctx))
    results.extend(_r0056_re_smul(term, ctx))
    results.extend(_r0057_dmuld(term, ctx))
    results.extend(_r0058_smuld_val(term, ctx))
    results.extend(_r0059_decompose(term, ctx))
    results.extend(_r0060_zeroLocus_span(term, ctx))
    results.extend(_r0061_map_comp(term, ctx))
    results.extend(_r0062_map_comp(term, ctx))
    results.extend(_r0063_toAddCircle_eq_zero(term, ctx))
    results.extend(_r0064_valMinAbs_nonneg_iff(term, ctx))
    results.extend(_r0065_coe_ne_zero(term, ctx))
    results.extend(_r0066_subset_zeroLocus_iff_le_vanishingIdeal(term, ctx))
    results.extend(_r0067_asIdeal_lt_asIdeal(term, ctx))
    results.extend(_r0068_mul_inv_cancel_aux(term, ctx))
    results.extend(_r0069_map_smul(term, ctx))
    results.extend(_r0070_auxDFT_neg(term, ctx))
    results.extend(_r0071_auxDFT_auxDFT(term, ctx))
    results.extend(_r0072_auxDFT_smul(term, ctx))
    results.extend(_r0073_toCircle_intCast(term, ctx))
    results.extend(_r0074_toCircle_natCast(term, ctx))
    results.extend(_r0075_toCircle_apply(term, ctx))
    results.extend(_r0076_toCircle_eq_circleExp(term, ctx))
    results.extend(_r0077_stdAddChar_coe(term, ctx))
    results.extend(_r0078_stdAddChar_apply(term, ctx))
    results.extend(_r0079_rootsOfUnityAddChar_val(term, ctx))
    results.extend(_r0080_erdos_ginzburg_ziv_prime(term, ctx))
    results.extend(_r0081_erdos_ginzburg_ziv(term, ctx))
    results.extend(_r0082_erdos_ginzburg_ziv_multiset(term, ctx))
    results.extend(_r0083_even_iff(term, ctx))
    results.extend(_r0084_mod_two_eq_one_iff_ne_two(term, ctx))
    results.extend(_r0085_eq_one_of_pow(term, ctx))
    results.extend(_r0086_pow_eq_iff(term, ctx))
    results.extend(_r0087_mul_eq_prime_sq_iff(term, ctx))
    results.extend(_r0088_coe_nat_inj(term, ctx))
    results.extend(_r0089_card_ofPrime(term, ctx))
    results.extend(_r0090_coeNat_ofPrime(term, ctx))
    results.extend(_r0091_coePNat_ofPrime(term, ctx))
    results.extend(_r0092_coePNat_nat(term, ctx))
    results.extend(_r0093_coe_prod(term, ctx))
    results.extend(_r0094_prod_ofPrime(term, ctx))
    results.extend(_r0095_to_ofNatMultiset(term, ctx))
    results.extend(_r0096_prod_ofNatMultiset(term, ctx))
    results.extend(_r0097_to_ofPNatMultiset(term, ctx))
    results.extend(_r0098_prod_ofPNatMultiset(term, ctx))
    results.extend(_r0099_prod_ofNatList(term, ctx))
    results.extend(_r0100_toPNatMultiset_ofPNatList(term, ctx))
    results.extend(_r0101_prod_zero(term, ctx))
    results.extend(_r0102_prod_smul(term, ctx))
    results.extend(_r0103_factorMultiset_prod(term, ctx))
    results.extend(_r0104_prod_inf(term, ctx))
    results.extend(_r0105_prod_sup(term, ctx))
    results.extend(_r0106_val_zero(term, ctx))
    results.extend(_r0107_val_natCast_of_lt(term, ctx))
    results.extend(_r0108_val_ofNat(term, ctx))
    results.extend(_r0109_val_ofNat_of_lt(term, ctx))
    results.extend(_r0110_eq_one_of_isUnit_natCast(term, ctx))
    results.extend(_r0111_addOrderOf_one(term, ctx))
    results.extend(_r0112_addOrderOf_coe(term, ctx))
    results.extend(_r0113_ringChar_zmod_n(term, ctx))
    results.extend(_r0114_natCast_self(term, ctx))
    results.extend(_r0115_cast_zero(term, ctx))
    results.extend(_r0116_cast_eq_val(term, ctx))
    results.extend(_r0117_fst_zmod_cast(term, ctx))
    results.extend(_r0118_snd_zmod_cast(term, ctx))
    results.extend(_r0119_ringHom_map_cast(term, ctx))
    results.extend(_r0120_castHom_self(term, ctx))
    results.extend(_r0121_lift_coe(term, ctx))
    results.extend(_r0122_char_nsmul_eq_zero(term, ctx))
    results.extend(_r0123_periodicPts_add_left(term, ctx))
    results.extend(_r0124_add_self(term, ctx))
    results.extend(_r0125_neg_eq_self(term, ctx))
    results.extend(_r0126_sub_eq_add(term, ctx))
    results.extend(_r0127_add_add_add_cancel(term, ctx))
    results.extend(_r0128_eq_zero_iff_gcd_ne_one(term, ctx))
    results.extend(_r0129_eq_zero_of_gcd_ne_one(term, ctx))
    results.extend(_r0130_card(term, ctx))
    results.extend(_r0131_cast_descFactorial(term, ctx))
    results.extend(_r0132_smul_units_def(term, ctx))
    results.extend(_r0133_natCast_smul_units(term, ctx))
    results.extend(_r0134_unitsMap_def(term, ctx))
    results.extend(_r0135_unitsMap_comp(term, ctx))
    results.extend(_r0136_unitsMap_self(term, ctx))
    results.extend(_r0137_unitsMap_val(term, ctx))
    results.extend(_r0138_eq_unit_mul_divisor(term, ctx))
    results.extend(_r0139_coe_int_mul_inv_eq_one(term, ctx))
    results.extend(_r0140_coe_int_inv_mul_eq_one(term, ctx))
    results.extend(_r0141_coe_int_mul_val_inv(term, ctx))
    results.extend(_r0142_coe_int_val_inv_mul(term, ctx))
    results.extend(_r0143_coe_unitOfIsCoprime(term, ctx))
    results.extend(_r0144_valMinAbs_def_zero(term, ctx))
    results.extend(_r0145_coe_valMinAbs(term, ctx))
    results.extend(_r0146_valMinAbs_inj(term, ctx))
    results.extend(_r0147_valMinAbs_mul_two_eq_iff(term, ctx))
    results.extend(_r0148_valMinAbs_spec(term, ctx))
    results.extend(_r0149_eq_neg_of_valMinAbs_eq_neg_valMinAbs(term, ctx))
    results.extend(_r0150_valMinAbs_zero(term, ctx))
    results.extend(_r0151_valMinAbs_eq_zero(term, ctx))
    results.extend(_r0152_valMinAbs_neg_of_ne_half(term, ctx))
    results.extend(_r0153_natAbs_valMinAbs_neg(term, ctx))
    results.extend(_r0154_natAbs_valMinAbs_eq_natAbs_valMinAbs(term, ctx))
    results.extend(_r0155_abs_valMinAbs_eq_abs_valMinAbs(term, ctx))
    results.extend(_r0156_val_eq_ite_valMinAbs(term, ctx))
    results.extend(_r0157_valMinAbs_natAbs_eq_min(term, ctx))
    results.extend(_r0158_valMinAbs_natCast_of_le_half(term, ctx))
    results.extend(_r0159_valMinAbs_natCast_of_half_lt(term, ctx))
    results.extend(_r0160_valMinAbs_natCast_eq_self(term, ctx))
    results.extend(_r0161_sq_add_sq(term, ctx))
    results.extend(_r0162_pow_totient(term, ctx))
    results.extend(_r0163_fieldRange_castHom_eq_bot(term, ctx))
    results.extend(_r0164_pow_card(term, ctx))
    results.extend(_r0165_frobenius_zmod(term, ctx))
    results.extend(_r0166_card_units(term, ctx))
    results.extend(_r0167_units_pow_card_sub_one_eq_one(term, ctx))
    results.extend(_r0168_pow_card_sub_one_eq_one(term, ctx))
    results.extend(_r0169_pow_card_sub_one(term, ctx))
    results.extend(_r0170_expand_card(term, ctx))
    results.extend(_r0171_eq_one_or_isUnit_sub_one(term, ctx))
    results.extend(_r0172_minOrder(term, ctx))
    results.extend(_r0173_minOrder_of_prime(term, ctx))
    results.extend(_r0174_exponent(term, ctx))
    results.extend(_r0175_charpoly_pow_card(term, ctx))
    results.extend(_r0176_trace_pow_card(term, ctx))
    results.extend(_r0177_LFunction_modOne_eq(term, ctx))
    results.extend(_r0178_LFunction_eq_LSeries(term, ctx))
    results.extend(_r0179_LFunction_stdAddChar_eq_expZeta_of_one_l(term, ctx))
    results.extend(_r0180_LFunction_stdAddChar_eq_expZeta(term, ctx))
    results.extend(_r0181_LFunction_dft(term, ctx))
    results.extend(_r0182_LFunction_one_sub(term, ctx))
    results.extend(_r0183_LFunction_def_even(term, ctx))
    results.extend(_r0184_LFunction_def_odd(term, ctx))
    results.extend(_r0185_LFunction_apply_zero_of_even(term, ctx))
    results.extend(_r0186_LFunction_neg_two_mul_nat_add_one(term, ctx))
    results.extend(_r0187_LFunction_neg_two_mul_nat_sub_one(term, ctx))
    results.extend(_r0188_completedLFunction_def_even(term, ctx))
    results.extend(_r0189_completedLFunction_def_odd(term, ctx))
    results.extend(_r0190_completedLFunction_modOne_eq(term, ctx))
    results.extend(_r0191_completedLFunction_eq(term, ctx))
    results.extend(_r0192_LFunction_eq_completed_div_gammaFactor_e(term, ctx))
    results.extend(_r0193_LFunction_eq_completed_div_gammaFactor_o(term, ctx))
    results.extend(_r0194_completedLFunction_one_sub_of_one_lt_eve(term, ctx))
    results.extend(_r0195_completedLFunction_one_sub_of_one_lt_odd(term, ctx))
    results.extend(_r0196_completedLFunction_one_sub_even(term, ctx))
    results.extend(_r0197_completedLFunction_one_sub_odd(term, ctx))
    results.extend(_r0198_euler_criterion_units(term, ctx))
    results.extend(_r0199_euler_criterion(term, ctx))
    results.extend(_r0200_pow_div_two_eq_neg_one_or_one(term, ctx))
    results.extend(_r0201_Ico_map_valMinAbs_natAbs_eq_Ico_map_id(term, ctx))
    results.extend(_r0202_gauss_lemma_aux_1(term, ctx))
    results.extend(_r0203_gauss_lemma_aux(term, ctx))
    results.extend(_r0204_gauss_lemma(term, ctx))
    results.extend(_r0205_eisenstein_lemma_aux_1(term, ctx))
    results.extend(_r0206_div_eq_filter_card(term, ctx))
    results.extend(_r0207_sum_Ico_eq_card_lt(term, ctx))
    results.extend(_r0208_sum_mul_div_add_sum_mul_div_eq_mul(term, ctx))
    results.extend(_r0209_eisenstein_lemma(term, ctx))
    results.extend(_r0210_nonsquare_iff_jacobiSym_eq_neg_one(term, ctx))
    results.extend(_r0211_exists_sq_eq_two_iff(term, ctx))
    results.extend(_r0212_exists_sq_eq_neg_two_iff(term, ctx))
    results.extend(_r0213_chi_4_nat_mod_four(term, ctx))
    results.extend(_r0214_chi_4_int_mod_four(term, ctx))
    results.extend(_r0215_chi_4_int_eq_if_mod_four(term, ctx))
    results.extend(_r0216_chi_4_nat_eq_if_mod_four(term, ctx))
    results.extend(_r0217_chi_4_eq_neg_one_pow(term, ctx))
    results.extend(_r0218_chi_4_nat_one_mod_four(term, ctx))
    results.extend(_r0219_chi_4_nat_three_mod_four(term, ctx))
    results.extend(_r0220_chi_4_int_one_mod_four(term, ctx))
    results.extend(_r0221_chi_4_int_three_mod_four(term, ctx))
    results.extend(_r0222_neg_one_pow_div_two_of_one_mod_four(term, ctx))
    results.extend(_r0223_neg_one_pow_div_two_of_three_mod_four(term, ctx))
    results.extend(_r0224_chi_8_nat_mod_eight(term, ctx))
    results.extend(_r0225_chi_8_int_mod_eight(term, ctx))
    results.extend(_r0226_chi_8_int_eq_if_mod_eight(term, ctx))
    results.extend(_r0227_chi_8_nat_eq_if_mod_eight(term, ctx))
    results.extend(_r0228_addChar_of_value_at_one_def(term, ctx))
    results.extend(_r0229_eq_addChar_of_value_at_one(term, ctx))
    results.extend(_r0230_continuousAddCharEquiv_apply(term, ctx))
    results.extend(_r0231_continuousAddCharEquiv_of_norm_mul_apply(term, ctx))
    results.extend(_r0232_spectralNorm_eq(term, ctx))
    results.extend(_r0233_valuation_def(term, ctx))
    results.extend(_r0234_valuation_coe(term, ctx))
    results.extend(_r0235_valuation_extends(term, ctx))
    results.extend(_r0236_coe_eq(term, ctx))
    results.extend(_r0237_coe_zero(term, ctx))
    results.extend(_r0238_valuation_p(term, ctx))
    results.extend(_r0239_hom_eq_embedding(term, ctx))
    results.extend(_r0240_norm_extends(term, ctx))
    results.extend(_r0241_norm_eq_norm(term, ctx))
    results.extend(_r0242_nnnorm_extends(term, ctx))
    results.extend(_r0243_coe_adicCompletionIntegersEquiv_apply(term, ctx))
    results.extend(_r0244_coe_adicCompletionIntegersEquiv_symm_app(term, ctx))
    results.extend(_r0245_ext(term, ctx))
    results.extend(_r0246_mk_zero(term, ctx))
    results.extend(_r0247_coe_sum(term, ctx))
    results.extend(_r0248_intCast_eq(term, ctx))
    results.extend(_r0249_norm_def(term, ctx))
    results.extend(_r0250_norm_add_eq_max_of_ne(term, ctx))
    results.extend(_r0251_norm_eq_of_norm_add_lt_right(term, ctx))
    results.extend(_r0252_norm_eq_of_norm_add_lt_left(term, ctx))
    results.extend(_r0253_padic_norm_e_of_padicInt(term, ctx))
    results.extend(_r0254_norm_eq_padic_norm(term, ctx))
    results.extend(_r0255_one_le_norm_iff(term, ctx))
    results.extend(_r0256_norm_natCast_p_sub_one(term, ctx))
    results.extend(_r0257_norm_natCast_eq_one_iff(term, ctx))
    results.extend(_r0258_norm_intCast_eq_one_iff(term, ctx))
    results.extend(_r0259_valuation_coe(term, ctx))
    results.extend(_r0260_valuation_mul(term, ctx))
    results.extend(_r0261_valuation_pow(term, ctx))
    results.extend(_r0262_valuation_p_pow_mul(term, ctx))
    results.extend(_r0263_mul_inv(term, ctx))
    results.extend(_r0264_inv_mul(term, ctx))
    results.extend(_r0265_isUnit_iff(term, ctx))
    results.extend(_r0266_val_mkUnits(term, ctx))
    results.extend(_r0267_norm_units(term, ctx))
    results.extend(_r0268_unitCoeff_coe(term, ctx))
    results.extend(_r0269_stationary(term, ctx))
    results.extend(_r0270_stationaryPoint_spec(term, ctx))
    results.extend(_r0271_norm_zero_iff(term, ctx))
    results.extend(_r0272_norm_mul(term, ctx))
    results.extend(_r0273_eq_zero_iff_equiv_zero(term, ctx))
    results.extend(_r0274_norm_const(term, ctx))
    results.extend(_r0275_norm_values_discrete(term, ctx))
    results.extend(_r0276_norm_one(term, ctx))
    results.extend(_r0277_norm_eq_of_equiv(term, ctx))
    results.extend(_r0278_norm_equiv(term, ctx))
    results.extend(_r0279_norm_eq(term, ctx))
    results.extend(_r0280_norm_neg(term, ctx))
    results.extend(_r0281_norm_eq_of_add_equiv_zero(term, ctx))
    results.extend(_r0282_add_eq_max_of_ne(term, ctx))
    results.extend(_r0283_zero_def(term, ctx))
    results.extend(_r0284_mk_eq(term, ctx))
    results.extend(_r0285_const_equiv(term, ctx))
    results.extend(_r0286_coe_inj(term, ctx))
    results.extend(_r0287_coe_add(term, ctx))
    results.extend(_r0288_coe_neg(term, ctx))
    results.extend(_r0289_coe_mul(term, ctx))
    results.extend(_r0290_coe_sub(term, ctx))
    results.extend(_r0291_coe_div(term, ctx))
    results.extend(_r0292_coe_one(term, ctx))
    results.extend(_r0293_coe_zero(term, ctx))
    results.extend(_r0294_mul(term, ctx))
    results.extend(_r0295_is_norm(term, ctx))
    results.extend(_r0296_add_eq_max_of_ne(term, ctx))
    results.extend(_r0297_eq_padicNorm(term, ctx))
    results.extend(_r0298_norm_p(term, ctx))
    results.extend(_r0299_norm_p_zpow(term, ctx))
    results.extend(_r0300_image(term, ctx))
    results.extend(_r0301_is_rat(term, ctx))
    results.extend(_r0302_eq_ratNorm(term, ctx))
    results.extend(_r0303_norm_rat_le_one(term, ctx))
    results.extend(_r0304_norm_intCast_eq_one_iff(term, ctx))
    results.extend(_r0305_norm_natCast_eq_one_iff(term, ctx))
    results.extend(_r0306_norm_eq_of_norm_add_lt_right(term, ctx))
    results.extend(_r0307_norm_eq_of_norm_add_lt_left(term, ctx))
    results.extend(_r0308_norm_eq_of_norm_sub_lt_right(term, ctx))
    results.extend(_r0309_norm_eq_of_norm_sub_lt_left(term, ctx))
    results.extend(_r0310_norm_natCast_p_sub_one(term, ctx))
    results.extend(_r0311_zmod_congr_of_sub_mem_span_aux(term, ctx))
    results.extend(_r0312_zmod_congr_of_sub_mem_span(term, ctx))
    results.extend(_r0313_zmod_congr_of_sub_mem_max_ideal(term, ctx))
    results.extend(_r0314_zmodRepr_unique(term, ctx))
    results.extend(_r0315_zmodRepr_eq_zero_of_dvd(term, ctx))
    results.extend(_r0316_zmodRepr_zero(term, ctx))
    results.extend(_r0317_norm_natCast_zmodRepr_eq_one_iff(term, ctx))
    results.extend(_r0318_zmodRepr_eq_zero_iff_dvd(term, ctx))
    results.extend(_r0319_norm_natCast_zmodRepr_eq_one_iff_ne(term, ctx))
    results.extend(_r0320_norm_natCast_zmodRepr_eq(term, ctx))
    results.extend(_r0321_zmodRepr_natCast_zmodRepr(term, ctx))
    results.extend(_r0322_norm_natCast_zmodRepr_eq_iff(term, ctx))
    results.extend(_r0323_zmodRepr_natCast(term, ctx))
    results.extend(_r0324_zmodRepr_natCast_of_lt(term, ctx))
    results.extend(_r0325_zmodRepr_natCast_ofNat(term, ctx))
    results.extend(_r0326_val_toZMod_eq_zmodRepr(term, ctx))
    results.extend(_r0327_zmodRepr_mul(term, ctx))
    results.extend(_r0328_toZMod_eq_residueField_comp_residue(term, ctx))
    results.extend(_r0329_zmod_cast_comp_toZModPow(term, ctx))
    results.extend(_r0330_cast_toZModPow(term, ctx))
    results.extend(_r0331_coe_withValRingEquiv(term, ctx))
    results.extend(_r0332_coe_withValRingEquiv_symm(term, ctx))
    results.extend(_r0333_toEquiv_withValUniformEquiv_eq_toEquiv_w(term, ctx))
    results.extend(_r0334_withValUniformEquiv_cast_apply(term, ctx))
    results.extend(_r0335_wilsons_lemma(term, ctx))
    results.extend(_r0336_prod_Ico_one_prime(term, ctx))
    results.extend(_r0337_re_ofInt(term, ctx))
    results.extend(_r0338_im_ofInt(term, ctx))
    results.extend(_r0339_re_zero(term, ctx))
    results.extend(_r0340_re_one(term, ctx))
    results.extend(_r0341_re_sqrtd(term, ctx))
    results.extend(_r0342_add_def(term, ctx))
    results.extend(_r0343_re_neg(term, ctx))
    results.extend(_r0344_re_mul(term, ctx))
    results.extend(_r0345_re_sub(term, ctx))
    results.extend(_r0346_star_mk(term, ctx))
    results.extend(_r0347_re_natCast(term, ctx))
    results.extend(_r0348_re_intCast(term, ctx))
    results.extend(_r0349_ofInt_eq_intCast(term, ctx))
    results.extend(_r0350_im_smul(term, ctx))
    results.extend(_r0351_muld_val(term, ctx))
    results.extend(_r0352_mul_star(term, ctx))
    results.extend(_r0353_eq_of_smul_eq_smul_left(term, ctx))
    results.extend(_r0354_gcd_eq_zero_iff(term, ctx))
    results.extend(_r0355_exists_coprime_of_gcd_pos(term, ctx))
    results.extend(_r0356_dividedPowers_eq(term, ctx))
    results.extend(_r0357_coe_dpow_eq(term, ctx))
    results.extend(_r0358_iInf_localization_eq_bot(term, ctx))
    results.extend(_r0359_piLocalizationToMaximal_comp_toPiLocaliz(term, ctx))
    results.extend(_r0360_mapPiLocalization_naturality(term, ctx))
    results.extend(_r0361_mapPiLocalization_id(term, ctx))
    results.extend(_r0362_mapPiLocalization_comp(term, ctx))
    results.extend(_r0363_range_asIdeal(term, ctx))
    results.extend(_r0364_primeSpectrumProd_symm_inl_asIdeal(term, ctx))
    results.extend(_r0365_primeSpectrumProd_symm_inr_asIdeal(term, ctx))
    results.extend(_r0366_coe_vanishingIdeal(term, ctx))
    results.extend(_r0367_vanishingIdeal_singleton(term, ctx))
    results.extend(_r0368_gc(term, ctx))
    results.extend(_r0369_gc_set(term, ctx))
    results.extend(_r0370_map_id(term, ctx))
    results.extend(_r0371_toSet_map(term, ctx))
    results.extend(_r0372_map_id(term, ctx))
    results.extend(_r0373_toSet_map(term, ctx))
    results.extend(_r0374_exist_ltSeries_mem_one_of_mem_last(term, ctx))
    results.extend(_r0375_exists_image_comap_of_finite_of_free(term, ctx))
    results.extend(_r0376_comap_asIdeal(term, ctx))
    results.extend(_r0377_comap_id(term, ctx))
    results.extend(_r0378_comap_comp(term, ctx))
    results.extend(_r0379_comap_comp_apply(term, ctx))
    results.extend(_r0380_preimage_comap_zeroLocus_aux(term, ctx))
    results.extend(_r0381_preimage_comap_zeroLocus(term, ctx))
    results.extend(_r0382_comapEquiv_symm(term, ctx))
    results.extend(_r0383_exists_comap_evalRingHom_eq(term, ctx))
    results.extend(_r0384_iUnion_range_comap_comp_evalRingHom(term, ctx))
    results.extend(_r0385_mem_range_comap_iff(term, ctx))
    results.extend(_r0386_residueField_comap(term, ctx))
    results.extend(_r0387_isOpen_iff(term, ctx))
    results.extend(_r0388_isClosed_iff_zeroLocus(term, ctx))
    results.extend(_r0389_isClosed_iff_zeroLocus_ideal(term, ctx))
    results.extend(_r0390_isClosed_iff_zeroLocus_radical_ideal(term, ctx))
    results.extend(_r0391_zeroLocus_vanishingIdeal_eq_closure(term, ctx))
    results.extend(_r0392_vanishingIdeal_closure(term, ctx))
    results.extend(_r0393_closure_singleton(term, ctx))
    results.extend(_r0394_zeroLocus_eq_iff(term, ctx))
    results.extend(_r0395_vanishingIdeal_isIrreducible(term, ctx))
    results.extend(_r0396_vanishingIdeal_isClosed_isIrreducible(term, ctx))
    results.extend(_r0397_comap_apply(term, ctx))
    results.extend(_r0398_localization_comap_range(term, ctx))
    results.extend(_r0399_asIdeal_top(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_number_theory rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Prime_exists_mem_multiset_dvd", "p_s_prod_to_exists_a_in_s_p_a", "Not an equality or iff proposition"),
    ("Prime_exists_mem_multiset_map_dvd", "p_s_map_f_prod_to_exists_a_in_s_p_f_a", "Not an equality or iff proposition"),
    ("Prime_exists_mem_finset_dvd", "p_s_prod_f_to_exists_i_in_s_p_f_i", "Not an equality or iff proposition"),
    ("Prime_not_dvd_finset_prod", "not_p_S_prod_g", "Not an equality or iff proposition"),
    ("Prime_not_dvd_finsuppProd", "not_p_f_prod_g", "Not an equality or iff proposition"),
    ("Prime_dvd_or_dvd_of_dvd_lcm", "p_a_or_p_b", "Not an equality or iff proposition"),
    ("Prime_not_dvd_lcm", "not_p_lcm_a_b", "Not an equality or iff proposition"),
    ("Prime_associated_of_dvd", "Associated_p_q", "Not an equality or iff proposition"),
    ("Prime_le_or_le", "p_le_a_or_p_le_b", "Not an equality or iff proposition"),
    ("Prime_isPrimePow", "IsPrimePow_p", "Not an equality or iff proposition"),
    ("ZMod_smul_mem", "c_x_in_K", "Not an equality or iff proposition"),
    ("ZModModule_exists_submodule_subset_card_le", "exists_H_prime_colon_Submodule_ZMod_p_G_Nat_card_H_prime_le_k_and_k_lt_p_star_Nat_card_H_prime_and_H_prime_le_H", "Not an equality or iff proposition"),
    ("Prime_ne_zero", "p_ne_0", "Not an equality or iff proposition"),
    ("Prime_not_unit", "not_IsUnit_p", "Not an equality or iff proposition"),
    ("Prime_not_dvd_one", "not_p_1", "Not an equality or iff proposition"),
    ("Prime_ne_one", "p_ne_1", "Not an equality or iff proposition"),
    ("Prime_dvd_or_dvd", "p_a_or_p_b", "Not an equality or iff proposition"),
    ("Prime_isPrimal", "IsPrimal_p", "Not an equality or iff proposition"),
    ("Prime_not_dvd_mul", "not_p_a_star_b", "Not an equality or iff proposition"),
    ("Prime_dvd_of_dvd_pow", "p_a", "Not an equality or iff proposition"),
    ("Prime_irreducible", "Irreducible_p", "Not an equality or iff proposition"),
    ("Prime_left_dvd_or_dvd_right_of_dvd_mul", "a_p_star_b_to_p_a_or_a_b", "Not an equality or iff proposition"),
    ("Prime_pow_dvd_of_dvd_mul_left", "p_pow_n_b", "Not an equality or iff proposition"),
    ("Prime_pow_dvd_of_dvd_mul_right", "p_pow_n_a", "Not an equality or iff proposition"),
    ("Prime_dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd", "p_a", "Not an equality or iff proposition"),
    ("Prime_not_isSquare", "not_IsSquare_p", "Not an equality or iff proposition"),
    ("Prime_squarefree", "Squarefree_x", "Not an equality or iff proposition"),
    ("ZMod_injective_toCircle", "Injective_toCircle_colon_ZMod_N_to_Circle", "Not an equality or iff proposition"),
    ("ZMod_injective_stdAddChar", "Injective_stdAddChar_colon_AddChar_ZMod_N", "Not an equality or iff proposition"),
    ("ZMod_isPrimitive_stdAddChar", "stdAddChar_N_colon_eq_N_IsPrimitive", "Not an equality or iff proposition"),
    ("ZMod_cauchy_davenport", "min_p_hash_s_plus_hash_t_minus_1_le_hash_s_plus_t", "Not an equality or iff proposition"),
    ("Prime_not_dvd_prod", "not_p_L_prod", "Not an equality or iff proposition"),
    ("Prime_pred_pos", "_0_lt_pred_p", "Not an equality or iff proposition"),
    ("Prime_odd_of_ne_two", "Odd_p", "Not an equality or iff proposition"),
    ("Prime_even_sub_one", "Even_p_minus_1", "Not an equality or iff proposition"),
    ("Prime_not_dvd_mul", "not_p_m_star_n", "Not an equality or iff proposition"),
    ("Prime_dvd_of_dvd_pow", "p_m", "Not an equality or iff proposition"),
    ("Prime_not_prime_pow", "_unknown", "Empty proposition"),
    ("Prime_not_prime_pow", "not_x_pow_n_Prime", "Not an equality or iff proposition"),
    ("Prime_coprime_pow_of_not_dvd", "Coprime_a_p_pow_m", "Not an equality or iff proposition"),
    ("Prime_dvd_mul_of_dvd_ne", "p1_star_p2_n", "Not an equality or iff proposition"),
    ("Primes_coe_nat_injective", "Function_Injective_colon_Nat_Primes_to", "Not an equality or iff proposition"),
    ("PrimeMultiset_coe_coeNatMonoidHom", "coeNatMonoidHom_colon_PrimeMultiset_to_Multiset_eq", "Not an equality or iff proposition"),
    ("PrimeMultiset_coeNat_injective", "Function_Injective_colon_PrimeMultiset_to_Multiset", "Not an equality or iff proposition"),
    ("PrimeMultiset_coeNat_prime", "p_Prime", "Not an equality or iff proposition"),
    ("PrimeMultiset_coe_coePNatMonoidHom", "coePNatMonoidHom_colon_PrimeMultiset_to_Multiset_plus_eq", "Not an equality or iff proposition"),
    ("PrimeMultiset_coePNat_injective", "Function_Injective_colon_PrimeMultiset_to_Multiset_plus", "Not an equality or iff proposition"),
    ("PrimeMultiset_coePNat_prime", "p_Prime", "Not an equality or iff proposition"),
    ("PrimeMultiset_prod_dvd_iff", "_unknown", "Empty proposition"),
    ("PNat_Prime_one_lt", "p_Prime_to_1_lt_p", "Not an equality or iff proposition"),
    ("PNat_Prime_ne_one", "p_Prime_to_p_ne_1", "Not an equality or iff proposition"),
    ("PNat_Prime_not_dvd_one", "p_Prime_to_not_p_1", "Not an equality or iff proposition"),
    ("ZMod_val_lt", "a_val_lt_n", "Not an equality or iff proposition"),
    ("ZMod_val_le", "a_val_le_n", "Not an equality or iff proposition"),
    ("ZMod_val_one", "_unknown", "Empty proposition"),
    ("ZMod_val_neg", "_unknown", "Empty proposition"),
    ("ZMod_val_mul", "_unknown", "Empty proposition"),
    ("ZMod_val_unit", "_unknown", "Empty proposition"),
    ("ZMod_addOrderOf_coe", "_unknown", "Empty proposition"),
    ("ZMod_natCast_self", "_unknown", "Empty proposition"),
    ("ZMod_ringHom_rightInverse", "Function_RightInverse_cast_colon_ZMod_n_to_R_f", "Not an equality or iff proposition"),
    ("ZMod_ringHom_surjective", "Function_Surjective_f", "Not an equality or iff proposition"),
    ("ZMod_lift_comp_coe", "ZMod_lift_n_f_comp_colon_to_eq_f", "Not an equality or iff proposition"),
    ("ZModModule_char_ne_one", "n_ne_1", "Not an equality or iff proposition"),
    ("ZModModule_two_le_char", "_2_le_n", "Not an equality or iff proposition"),
    ("ZMod_ne_zero_of_gcd_eq_one", "a_colon_ZMod_p_ne_0", "Not an equality or iff proposition"),
    ("ZMod_isUnit_cast_of_dvd", "IsUnit_cast_a_colon_ZMod_m_colon_ZMod_n", "Not an equality or iff proposition"),
    ("ZMod_unitsMap_surjective", "Function_Surjective_unitsMap_h", "Not an equality or iff proposition"),
    ("ZMod_not_isUnit_of_mem_primeFactors", "not_IsUnit_p_colon_ZMod_n", "Not an equality or iff proposition"),
    ("ZMod_isUnit_inv", "IsUnit_n_colon_ZMod_m_inv", "Not an equality or iff proposition"),
    ("ZMod_injective_valMinAbs", "valMinAbs_colon_ZMod_n_to_Injective", "Not an equality or iff proposition"),
    ("ZMod_valMinAbs_mem_Ioc", "x_valMinAbs_star_2_in_Set_Ioc_minus_n_colon_n", "Not an equality or iff proposition"),
    ("ZMod_natAbs_valMinAbs_le", "x_valMinAbs_natAbs_le_n_slash_2", "Not an equality or iff proposition"),
    ("ZMod_prime_ne_zero", "q_colon_ZMod_p_ne_0", "Not an equality or iff proposition"),
    ("ZMod_natAbs_valMinAbs_add_le", "a_plus_b_valMinAbs_natAbs_le_a_valMinAbs_plus_b_valMinAbs_natAbs", "Not an equality or iff proposition"),
    ("ZMod_orderOf_units_dvd_card_sub_one", "orderOf_u_p_minus_1", "Not an equality or iff proposition"),
    ("ZMod_orderOf_dvd_card_sub_one", "orderOf_a_p_minus_1", "Not an equality or iff proposition"),
    ("ZModModule_isPGroup_multiplicative", "IsPGroup_n_Multiplicative_G", "Not an equality or iff proposition"),
    ("ZMod_LSeriesSummable_of_one_lt_re", "LSeriesSummable_s", "Not an equality or iff proposition"),
    ("ZMod_differentiableAt_LFunction", "DifferentiableAt_LFunction_s", "Not an equality or iff proposition"),
    ("ZMod_differentiable_LFunction_of_sum_zero", "Differentiable_LFunction", "Not an equality or iff proposition"),
    ("ZMod_LFunction_residue_one", "Tendsto_fun_s_s_minus_1_star_LFunction_s_ne_1_j_j_slash_N", "Not an equality or iff proposition"),
    ("ZMod_completedLFunction_zero", "completedLFunction_0_colon_ZMod_N_to_s_eq_0", "Not an equality or iff proposition"),
    ("ZMod_differentiable_completedLFunction_0", "Differentiable_completedLFunction_0", "Not an equality or iff proposition"),
    ("ZMod_differentiableAt_completedLFunction", "DifferentiableAt_completedLFunction_s", "Not an equality or iff proposition"),
    ("ZMod_differentiable_completedLFunction", "Differentiable_completedLFunction", "Not an equality or iff proposition"),
    ("ZMod_mod_four_ne_three_of_sq_eq_neg_one", "p_4_ne_3", "Not an equality or iff proposition"),
    ("ZMod_mod_four_ne_three_of_sq_eq_neg_sq", "_unknown", "Empty proposition"),
    ("ZMod_mod_four_ne_three_of_sq_eq_neg_sq", "p_4_ne_3", "Not an equality or iff proposition"),
    ("ZMod_eisenstein_lemma_aux", "hash_x_in_Ico_1_p_slash_2_succ_pipe_p_slash_2_lt_a_star_x_cast_colon_ZMod_p_val_x_in_Ico", "Not an equality or iff proposition"),
    ("ZMod_nonsquare_of_jacobiSym_eq_neg_one", "not_IsSquare_a_colon_ZMod_b", "Not an equality or iff proposition"),
    ("ZMod_isSquare_of_jacobiSym_eq_one", "IsSquare_a_colon_ZMod_p", "Not an equality or iff proposition"),
    ("ZMod_isQuadratic_chi_4", "chi_4_IsQuadratic", "Not an equality or iff proposition"),
    ("ZMod_isQuadratic_chi_8", "chi_8_IsQuadratic", "Not an equality or iff proposition"),
    ("ZMod_isQuadratic_chi_8", "_unknown", "Empty proposition"),
    ("ZMod_chi_8", "_unknown", "Empty proposition"),
    ("ZMod_chi_8", "_unknown", "Empty proposition"),
    ("ZMod_chi_8", "_unknown", "Empty proposition"),
    ("ZMod_chi_8", "_unknown", "Empty proposition"),
    ("PadicInt_continuous_addChar_of_value_at_one", "Continuous_addChar_of_value_at_one_r_hr_colon_p_to_R", "Not an equality or iff proposition"),
    ("PadicInt_coe_addChar_of_value_at_one", "addChar_of_value_at_one_r_hr_colon_p_to_R_eq_mahlerSeries_r_pow", "Not an equality or iff proposition"),
    ("PadicAlgCl_coe_eq", "Coe_coe_colon_p_to_PadicAlgCl_p_eq_algebraMap_p_PadicAlgCl_p", "Not an equality or iff proposition"),
    ("PadicAlgCl_isNonarchimedean", "IsNonarchimedean_norm_colon_PadicAlgCl_p_to", "Not an equality or iff proposition"),
    ("PadicComplex_norm_extends", "_unknown", "Empty proposition"),
    ("PadicComplex_isNonarchimedean", "IsNonarchimedean_Norm_norm_colon_p_to", "Not an equality or iff proposition"),
    ("PadicComplex_norm_eq_norm", "_unknown", "Empty proposition"),
    ("PadicComplex_nnnorm_extends", "_unknown", "Empty proposition"),
    ("PadicComplexInt_integers", "Valuation_Integers_PadicComplex_valued_p_v_p", "Not an equality or iff proposition"),
    ("PadicInt_norm_ascPochhammer_le", "ascPochhammer_p_k_eval_x_le_k_factorial_colon_p", "Not an equality or iff proposition"),
    ("PadicInt_continuous_multichoose", "Continuous_fun_x_colon_p_Ring_multichoose_x_k", "Not an equality or iff proposition"),
    ("PadicInt_continuous_choose", "Continuous_fun_x_colon_p_Ring_choose_x_k", "Not an equality or iff proposition"),
    ("PadicInt_bojanic_mahler_step2", "D_1_pow_n_plus_p_pow_t_f_0_le_max_Finset_range_p_pow_t_minus_1_sup_fun_j_D", "Not an equality or iff proposition"),
    ("PadicInt_fwdDiff_iter_le_of_forall_le", "D_1_pow_n_plus_s_star_p_pow_t_f_0_le_f_slash_p_pow_s", "Not an equality or iff proposition"),
    ("PadicInt_fwdDiff_tendsto_zero", "Tendsto_D_1_pow_f_0_atTop_0", "Not an equality or iff proposition"),
    ("PadicInt_isOpenEmbedding_coe", "IsOpenEmbedding_colon_p_to_p", "Not an equality or iff proposition"),
    ("PadicInt_norm_le_one", "z_le_1", "Not an equality or iff proposition"),
    ("PadicInt_nonarchimedean", "q_plus_r_le_max_q_r", "Not an equality or iff proposition"),
    ("PadicInt_exists_pow_neg_lt", "exists_k_colon_p_colon_pow_minus_k_colon_lt_e", "Not an equality or iff proposition"),
    ("PadicInt_exists_pow_neg_lt_rat", "exists_k_colon_p_colon_pow_minus_k_colon_lt_e", "Not an equality or iff proposition"),
    ("PadicInt_valuation_coe_nonneg", "_0_le_x_colon_p_valuation", "Not an equality or iff proposition"),
    ("PadicInt_le_valuation_add", "min_x_valuation_y_valuation_le_x_plus_y_valuation", "Not an equality or iff proposition"),
    ("PadicInt_norm_lt_one_add", "z1_plus_z2_lt_1", "Not an equality or iff proposition"),
    ("PadicInt_norm_lt_one_mul", "z1_star_z2_lt_1", "Not an equality or iff proposition"),
    ("PadicInt_isUnit_den", "IsUnit_r_den_colon_p", "Not an equality or iff proposition"),
    ("PadicSeq_norm_eq_of_equiv_aux", "False", "Not an equality or iff proposition"),
    ("PadicSeq_norm_nonarchimedean_aux", "f_plus_g_norm_le_max_f_norm_g_norm", "Not an equality or iff proposition"),
    ("PadicSeq_norm_nonarchimedean", "f_plus_g_norm_le_max_f_norm_g_norm", "Not an equality or iff proposition"),
    ("Padic_rat_dense", "_unknown", "Empty proposition"),
    ("Padic_div_nat_pos", "_0_lt_1_slash_n_plus_1_colon", "Not an equality or iff proposition"),
    ("Padic_exi_rat_seq_conv", "exists_N_forall_i_ge_N_padicNormE_f_i_minus_limSeq_f_i_colon_p_colon_p_lt_e", "Not an equality or iff proposition"),
    ("Padic_exi_rat_seq_conv_cauchy", "IsCauSeq_padicNorm_p_limSeq_f", "Not an equality or iff proposition"),
    ("Padic_complete", "_unknown", "Empty proposition"),
    ("Padic_complete", "_unknown", "Empty proposition"),
    ("Padic_nonarchimedean", "q_plus_r_le_max_q_r", "Not an equality or iff proposition"),
    ("Padic_norm_p_lt_one", "p_colon_p_lt_1", "Not an equality or iff proposition"),
    ("Padic_norm_int_le_one", "z_colon_p_le_1", "Not an equality or iff proposition"),
    ("PadicInt_totallyBounded_univ", "TotallyBounded_Set_univ_colon_Set_p", "Not an equality or iff proposition"),
    ("PadicInt_modPart_lt_p", "modPart_p_r_lt_p", "Not an equality or iff proposition"),
    ("PadicInt_modPart_nonneg", "_0_le_modPart_p_r", "Not an equality or iff proposition"),
    ("PadicInt_norm_sub_modPart_aux", "p_r_num_minus_r_num_star_r_den_gcdA_p_p_star_r_den", "Not an equality or iff proposition"),
    ("PadicInt_norm_sub_modPart", "r_h_minus_modPart_p_r_colon_p_lt_1", "Not an equality or iff proposition"),
    ("PadicInt_exists_mem_range_of_norm_rat_le_one", "exists_n_colon_0_le_n_and_n_lt_p_and_r_h_minus_n_colon_p_lt_1", "Not an equality or iff proposition"),
    ("PadicInt_exists_mem_range", "exists_n_colon_n_lt_p_and_x_minus_n_in_maximalIdeal_p", "Not an equality or iff proposition"),
    ("PadicInt_existsUnique_mem_range", "exists_bang_n_colon_n_lt_p_and_x_minus_n_in_maximalIdeal_p", "Not an equality or iff proposition"),
    ("PadicInt_zmodRepr_spec", "zmodRepr_x_lt_p_and_x_minus_zmodRepr_x_in_maximalIdeal_p", "Not an equality or iff proposition"),
    ("PadicInt_zmodRepr_lt_p", "zmodRepr_x_lt_p", "Not an equality or iff proposition"),
    ("PadicInt_sub_zmodRepr_mem", "x_minus_zmodRepr_x_in_maximalIdeal_p", "Not an equality or iff proposition"),
    ("PadicInt_norm_sub_zmodRepr_lt_one", "x_minus_x_zmodRepr_lt_1", "Not an equality or iff proposition"),
    ("PadicInt_zmodRepr_units_ne_zero", "x_val_zmodRepr_ne_0", "Not an equality or iff proposition"),
    ("PadicInt_toZMod_spec", "x_minus_ZMod_cast_toZMod_x_colon_p_in_maximalIdeal_p", "Not an equality or iff proposition"),
    ("PadicInt_ker_toZMod", "RingHom_ker_toZMod_colon_p_to_plus_star_ZMod_p_eq_maximalIdeal_p", "Not an equality or iff proposition"),
    ("PadicInt_appr_lt", "x_appr_n_lt_p_pow_n", "Not an equality or iff proposition"),
    ("PadicInt_appr_mono", "Monotone_x_appr", "Not an equality or iff proposition"),
    ("PadicInt_dvd_appr_sub_appr", "p_pow_m_x_appr_n_minus_x_appr_m", "Not an equality or iff proposition"),
    ("PadicInt_appr_spec", "forall_x_colon_p_x_minus_appr_x_n_in_Ideal_span_p_colon_p_pow_n", "Not an equality or iff proposition"),
    ("PadicInt_ker_toZModPow", "RingHom_ker_toZModPow_n_colon_p_to_plus_star_ZMod_p_pow_n_eq_Ideal_span_p_colon_p_pow_n", "Not an equality or iff proposition"),
    ("PadicInt_denseRange_natCast", "DenseRange_Nat_cast_colon_to_p", "Not an equality or iff proposition"),
    ("PadicInt_denseRange_intCast", "DenseRange_Int_cast_colon_to_p", "Not an equality or iff proposition"),
    ("Padic_valuation_p_ne_zero", "v_p_ne_0", "Not an equality or iff proposition"),
    ("Padic_valuation_p_lt_one", "v_p_lt_1", "Not an equality or iff proposition"),
    ("Padic_isUniformInducing_cast_withVal", "IsUniformInducing_Rat_castHom_p_comp_WithVal_equiv_Rat_padicValuati", "Not an equality or iff proposition"),
    ("Padic_isDenseInducing_cast_withVal", "IsDenseInducing_Rat_castHom_p_comp_WithVal_equiv_Rat_padicValuation", "Not an equality or iff proposition"),
    ("ZMod_isSquare_neg_one_of_dvd", "IsSquare_minus_1_colon_ZMod_m", "Not an equality or iff proposition"),
    ("ZMod_isSquare_neg_one_mul", "IsSquare_minus_1_colon_ZMod_m_star_n", "Not an equality or iff proposition"),
    ("ZMod_isSquare_neg_one_iff", "_unknown", "Empty proposition"),
    ("ZMod_isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime", "IsSquare_minus_1_colon_ZMod_n_natAbs", "Not an equality or iff proposition"),
    ("ZMod_isSquare_neg_one_of_eq_sq_add_sq_of_coprime", "IsSquare_minus_1_colon_ZMod_n", "Not an equality or iff proposition"),
    ("Zsqrtd_isCoprime_of_dvd_isCoprime", "IsCoprime_b_re_b_im", "Not an equality or iff proposition"),
    ("Zsqrtd_toReal_injective", "Function_Injective_toReal_h0d", "Not an equality or iff proposition"),
    ("PadicInt_dpow", "_unknown", "Empty proposition"),
    ("PadicInt_dpow", "_unknown", "Empty proposition"),
    ("PadicInt_dpow", "_unknown", "Empty proposition"),
    ("ZMod_orderOf_lt", "orderOf_a_lt_n", "Not an equality or iff proposition"),
    ("PrimeSpectrum_comap_surjective_of_faithfullyFlat", "Function_Surjective_comap_algebraMap_A_B", "Not an equality or iff proposition"),
    ("Prime_finiteMultiplicity_mul", "FiniteMultiplicity_p_a_to_FiniteMultiplicity_p_b_to_FiniteMultiplicity_p_a_star_b", "Not an equality or iff proposition"),
    ("Prime_isRadical", "IsRadical_y", "Not an equality or iff proposition"),
    ("Prime_neg", "Prime_minus_p", "Not an equality or iff proposition"),
    ("Prime_abs", "Prime_abs_p", "Not an equality or iff proposition"),
    ("ZMod_exists_monoidHom_apply_ne_one", "exists_phi_colon_Multiplicative_ZMod_n_to_star_M_phi_Multiplicative_ofAdd_a_ne_1", "Not an equality or iff proposition"),
    ("PrimeSpectrum_toPiLocalization_injective", "Function_Injective_toPiLocalization_R", "Not an equality or iff proposition"),
    ("PrimeSpectrum_piLocalizationToMaximal_surjective", "Function_Surjective_piLocalizationToMaximal_R", "Not an equality or iff proposition"),
    ("PrimeSpectrum_piLocalizationToMaximal_bijective", "Function_Bijective_piLocalizationToMaximal_R", "Not an equality or iff proposition"),
    ("PrimeSpectrum_isMaximal_of_toPiLocalization_surjective", "I_1_IsMaximal", "Not an equality or iff proposition"),
    ("PrimeSpectrum_mapPiLocalization_bijective", "Function_Bijective_mapPiLocalization_f", "Not an equality or iff proposition"),
    ("PrimeSpectrum_toPiLocalization_not_surjective_of_infinite", "not_Function_Surjective_toPiLocalization_Pi_i_R_i", "Not an equality or iff proposition"),
    ("PrimeSpectrum_finite_of_toPiLocalization_pi_surjective", "Finite_i", "Not an equality or iff proposition"),
    ("PrimeSpectrum_nontrivial", "Nontrivial_R", "Not an equality or iff proposition"),
    ("PrimeSpectrum_isConstructible_comap_C", "IsConstructible_comap_Polynomial_C_prime_prime_s", "Not an equality or iff proposition"),
    ("PrimeSpectrum_isConstructible_comap_image", "IsConstructible_comap_f_prime_prime_s", "Not an equality or iff proposition"),
    ("PrimeSpectrum_isConstructible_range_comap", "IsConstructible_Set_range_lt_pipe_comap_f", "Not an equality or iff proposition"),
    ("PrimeSpectrum_isOpenMap_comap_of_hasGoingDown_of_finitePresentation", "IsOpenMap_comap_algebraMap_R_S", "Not an equality or iff proposition"),
    ("PrimeSpectrum_isOpenMap_comap_algebraMap_tensorProduct_of_field", "IsOpenMap_PrimeSpectrum_comap_algebraMap_A_A_K_B", "Not an equality or iff proposition"),
    ("PrimeSpectrum_BasicConstructibleSetData_map_id", "_unknown", "Empty proposition"),
    ("PrimeSpectrum_BasicConstructibleSetData_map_comp", "_unknown", "Empty proposition"),
    ("PrimeSpectrum_ConstructibleSetData_isConstructible_toSet", "IsConstructible_S_toSet", "Not an equality or iff proposition"),
    ("PrimeSpectrum_exists_range_eq_of_isConstructible", "exists_S_colon_Type_u_colon_CommRing_S_f_colon_R_to_plus_star_S_Set_range_comap_f_eq_s", "Not an equality or iff proposition"),
    ("PrimeSpectrum_isClosed_of_stableUnderSpecialization_of_isConstructible", "IsClosed_s", "Not an equality or iff proposition"),
    ("PrimeSpectrum_isOpen_of_stableUnderGeneralization_of_isConstructible", "IsOpen_s", "Not an equality or iff proposition"),
    ("PrimeSpectrum_isHomeomorph_comap", "IsHomeomorph_comap_f", "Not an equality or iff proposition"),
    ("PrimeSpectrum_isHomeomorph_comap_of_isPurelyInseparable", "IsHomeomorph_comap_lt_pipe_algebraMap_R_R_k_K", "Not an equality or iff proposition"),
]
