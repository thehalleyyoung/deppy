"""Mathlib: Logic Basic — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 1106 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_logic_basic"
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

def _r0000_right_vsub_pointReflection(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.right_vsub_pointReflection
    # y -ᵥ pointReflection x y = 2 • (y -ᵥ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "y", 4)
    if args is not None:
        try:
            rhs = OOp("_2", (OVar("_unknown"), OOp("y", (args[0], args[2],)),))
            results.append((rhs, "Mathlib: Equiv_right_vsub_pointReflection"))
        except Exception:
            pass
    return results


def _r0001_coe_vaddConst_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.coe_vaddConst_symm
    # ⇑(vaddConst p).symm = fun p' => p' -ᵥ p
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("vaddConst_p_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("fun", (OVar("p_prime"), OVar("eq_gt"), OVar("p_prime"), OVar("minus"), OVar("p"),))
            results.append((rhs, "Mathlib: Equiv_coe_vaddConst_symm"))
    except Exception:
        pass
    return results


def _r0002_coe_constVSub_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.coe_constVSub_symm
    # ⇑(constVSub p).symm = fun (v : G) => -v +ᵥ p
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("constVSub_p_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("fun", (OOp("v", (OVar("colon"), OVar("G"),)), OVar("eq_gt"), OVar("minus_v"), OVar("plus"), OVar("p"),))
            results.append((rhs, "Mathlib: Equiv_coe_constVSub_symm"))
    except Exception:
        pass
    return results


def _r0003_pointReflection_vsub_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.pointReflection_vsub_right
    # pointReflection x y -ᵥ y = 2 • (x -ᵥ y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pointReflection", 4)
    if args is not None:
        try:
            rhs = OOp("_2", (OVar("_unknown"), OOp("x", (args[2], args[3],)),))
            results.append((rhs, "Mathlib: Equiv_pointReflection_vsub_right"))
        except Exception:
            pass
    return results


def _r0004_pointReflection_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.pointReflection_symm
    # (pointReflection x).symm = pointReflection x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pointReflection_x_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("pointReflection", (OVar("x"),))
            results.append((rhs, "Mathlib: Equiv_pointReflection_symm"))
    except Exception:
        pass
    return results


def _r0005_pointReflection_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.pointReflection_self
    # pointReflection x x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pointReflection", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Equiv_pointReflection_self"))
        except Exception:
            pass
    return results


def _r0006_down_nnratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.down_nnratCast
    # down (q : ULift α) = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "down", 1)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: ULift_down_nnratCast"))
        except Exception:
            pass
    return results


def _r0007_up_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.up_ratCast
    # up (q : α) = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "up", 1)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: ULift_up_ratCast"))
        except Exception:
            pass
    return results


def _r0008_down_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.down_ratCast
    # down (q : ULift α) = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "down", 1)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: ULift_down_ratCast"))
        except Exception:
            pass
    return results


def _r0009_source_restr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equidecomp.source_restr
    # (f.restr A).source = A
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_restr_A_source")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("A")
            results.append((rhs, "Mathlib: Equidecomp_source_restr"))
    except Exception:
        pass
    return results


def _r0010_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.mul_apply
    # (f * g) x = f (g x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_star_g", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("g", (args[0],)),))
            results.append((rhs, "Mathlib: Equiv_Perm_mul_apply"))
        except Exception:
            pass
    return results


def _r0011_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.coe_one
    # ⇑(1 : Perm α) = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Perm_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Equiv_Perm_coe_one"))
    except Exception:
        pass
    return results


def _r0012_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.coe_mul
    # ⇑(f * g) = f ∘ g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_star_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("f"), OVar("g")))
            results.append((rhs, "Mathlib: Equiv_Perm_coe_mul"))
    except Exception:
        pass
    return results


def _r0013_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.coe_pow
    # ⇑(f ^ n) = f^[n]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("fpow_n")
            results.append((rhs, "Mathlib: Equiv_Perm_coe_pow"))
    except Exception:
        pass
    return results


def _r0014_iterate_eq_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.iterate_eq_pow
    # f^[n] = ⇑(f ^ n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fpow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_pow_n")
            results.append((rhs, "Mathlib: Equiv_Perm_iterate_eq_pow"))
    except Exception:
        pass
    return results


def _r0015_eq_inv_iff_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.eq_inv_iff_eq
    # x = f⁻¹ y ↔ f x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("finv", (OVar("y"),)), OOp("f", (OVar("x"),)))), OVar("y")))
            results.append((rhs, "Mathlib: Equiv_Perm_eq_inv_iff_eq"))
    except Exception:
        pass
    return results


def _r0016_mul_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.mul_refl
    # e * Equiv.refl α = e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Equiv_Perm_mul_refl"))
        except Exception:
            pass
    return results


def _r0017_one_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.one_symm
    # (1 : Perm α).symm = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Perm_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Equiv_Perm_one_symm"))
    except Exception:
        pass
    return results


def _r0018_refl_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.refl_inv
    # (Equiv.refl α : Perm α)⁻¹ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Equiv_refl_a_colon_Perm_a_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Equiv_Perm_refl_inv"))
    except Exception:
        pass
    return results


def _r0019_one_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.one_trans
    # (1 : Perm α).trans e = e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_Perm_a_trans", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Equiv_Perm_one_trans"))
        except Exception:
            pass
    return results


def _r0020_refl_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.refl_mul
    # Equiv.refl α * e = e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Equiv_Perm_refl_mul"))
        except Exception:
            pass
    return results


def _r0021_inv_trans_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.inv_trans_self
    # e⁻¹.trans e = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "einv_trans", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Equiv_Perm_inv_trans_self"))
        except Exception:
            pass
    return results


def _r0022_mul_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.mul_symm
    # e * e.symm = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Equiv_Perm_mul_symm"))
        except Exception:
            pass
    return results


def _r0023_self_trans_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.self_trans_inv
    # e.trans e⁻¹ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_trans", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Equiv_Perm_self_trans_inv"))
        except Exception:
            pass
    return results


def _r0024_symm_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.symm_mul
    # e.symm * e = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Equiv_Perm_symm_mul"))
        except Exception:
            pass
    return results


def _r0025_permCongr_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.permCongr_mul
    # e.permCongr (p * q) = e.permCongr p * e.permCongr q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_permCongr", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("e_permCongr", (OVar("p"),)), OOp("e_permCongr", (OVar("q"),))))
            results.append((rhs, "Mathlib: Equiv_permCongr_mul"))
        except Exception:
            pass
    return results


def _r0026_extendDomain_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.extendDomain_inv
    # (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_extendDomain_f_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("einv_extendDomain", (OVar("f"),))
            results.append((rhs, "Mathlib: Equiv_Perm_extendDomain_inv"))
    except Exception:
        pass
    return results


def _r0027_extendDomain_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.extendDomain_mul
    # e.extendDomain f * e'.extendDomain f = (e * e').extendDomain f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("e_star_e_prime_extendDomain", (OVar("f"),))
            results.append((rhs, "Mathlib: Equiv_Perm_extendDomain_mul"))
        except Exception:
            pass
    return results


def _r0028_extendDomain_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.extendDomain_pow
    # (e ^ n).extendDomain f = e.extendDomain f ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_pow_n_extendDomain", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("e_extendDomain", (args[0],)), OVar("n")))
            results.append((rhs, "Mathlib: Equiv_Perm_extendDomain_pow"))
        except Exception:
            pass
    return results


def _r0029_extendDomain_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.extendDomain_zpow
    # (e ^ n).extendDomain f = e.extendDomain f ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_pow_n_extendDomain", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("e_extendDomain", (args[0],)), OVar("n")))
            results.append((rhs, "Mathlib: Equiv_Perm_extendDomain_zpow"))
        except Exception:
            pass
    return results


def _r0030_mulRight_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.mulRight_symm
    # (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Equiv_mulRight_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Equiv_mulRight", (OVar("ainv"),))
            results.append((rhs, "Mathlib: Equiv_mulRight_symm"))
    except Exception:
        pass
    return results


def _r0031_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidHom.copy_eq
    # f.copy f' h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_copy", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderMonoidHom_copy_eq"))
        except Exception:
            pass
    return results


def _r0032_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidHom.comp_apply
    # (f.comp g) a = f (g a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp_g", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("g", (args[0],)),))
            results.append((rhs, "Mathlib: OrderMonoidHom_comp_apply"))
        except Exception:
            pass
    return results


def _r0033_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidHom.id_comp
    # (OrderMonoidHom.id β).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OrderMonoidHom_id_b_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: OrderMonoidHom_id_comp"))
        except Exception:
            pass
    return results


def _r0034_cancel_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidHom.cancel_right
    # g₁.comp f = g₂.comp f ↔ g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_1_comp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("g_2_comp", (args[0],)), OVar("g_1"))), OVar("g_2")))
            results.append((rhs, "Mathlib: OrderMonoidHom_cancel_right"))
        except Exception:
            pass
    return results


def _r0035_mk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.mk_coe
    # OrderMonoidIso.mk (f : α ≃* β) h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OrderMonoidIso_mk", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderMonoidIso_mk_coe"))
        except Exception:
            pass
    return results


def _r0036_trans_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.trans_apply
    # (f.trans g) a = g (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_trans_g", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: OrderMonoidIso_trans_apply"))
        except Exception:
            pass
    return results


def _r0037_coe_trans_mulEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.coe_trans_mulEquiv
    # (f.trans g : α ≃* γ) = (f : α ≃* β).trans g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_trans", 5)
    if args is not None:
        try:
            rhs = OOp("f_colon_a_star_b_trans", (args[4],))
            results.append((rhs, "Mathlib: OrderMonoidIso_coe_trans_mulEquiv"))
        except Exception:
            pass
    return results


def _r0038_refl_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.refl_trans
    # (OrderMonoidIso.refl α).trans f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OrderMonoidIso_refl_a_trans", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: OrderMonoidIso_refl_trans"))
        except Exception:
            pass
    return results


def _r0039_cancel_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.cancel_right
    # g₁.trans f = g₂.trans f ↔ g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_1_trans", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("g_2_trans", (args[0],)), OVar("g_1"))), OVar("g_2")))
            results.append((rhs, "Mathlib: OrderMonoidIso_cancel_right"))
        except Exception:
            pass
    return results


def _r0040_toOrderIso_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.toOrderIso_eq_coe
    # f.toOrderIso = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toOrderIso")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderMonoidIso_toOrderIso_eq_coe"))
    except Exception:
        pass
    return results


def _r0041_equivLike_inv_eq_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.equivLike_inv_eq_symm
    # EquivLike.inv f = f.symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "EquivLike_inv", 1)
    if args is not None:
        try:
            rhs = OVar("f_symm")
            results.append((rhs, "Mathlib: OrderMonoidIso_equivLike_inv_eq_symm"))
        except Exception:
            pass
    return results


def _r0042_toEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.toEquiv_symm
    # (f.symm : β ≃ α) = (f : α ≃ β).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_symm", 4)
    if args is not None:
        try:
            rhs = OVar("f_colon_a_b_symm")
            results.append((rhs, "Mathlib: OrderMonoidIso_toEquiv_symm"))
        except Exception:
            pass
    return results


def _r0043_symm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.symm_symm
    # f.symm.symm = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_symm_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderMonoidIso_symm_symm"))
    except Exception:
        pass
    return results


def _r0044_apply_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.apply_symm_apply
    # e (e.symm y) = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: OrderMonoidIso_apply_symm_apply"))
        except Exception:
            pass
    return results


def _r0045_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.symm_apply_apply
    # e.symm (e x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: OrderMonoidIso_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0046_self_comp_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.self_comp_symm
    # e ∘ e.symm = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: OrderMonoidIso_self_comp_symm"))
        except Exception:
            pass
    return results


def _r0047_apply_eq_iff_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidIso.apply_eq_iff_symm_apply
    # e x = y ↔ x = e.symm y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("y"), args[0])), OOp("e_symm", (OVar("y"),))))
            results.append((rhs, "Mathlib: OrderMonoidIso_apply_eq_iff_symm_apply"))
        except Exception:
            pass
    return results


def _r0048_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidWithZeroHom.copy_eq
    # f.copy f' h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_copy", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderMonoidWithZeroHom_copy_eq"))
        except Exception:
            pass
    return results


def _r0049_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidWithZeroHom.comp_apply
    # (f.comp g) a = f (g a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp_g", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("g", (args[0],)),))
            results.append((rhs, "Mathlib: OrderMonoidWithZeroHom_comp_apply"))
        except Exception:
            pass
    return results


def _r0050_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidWithZeroHom.id_comp
    # (OrderMonoidWithZeroHom.id β).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OrderMonoidWithZeroHom_id_b_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: OrderMonoidWithZeroHom_id_comp"))
        except Exception:
            pass
    return results


def _r0051_cancel_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidWithZeroHom.cancel_right
    # g₁.comp f = g₂.comp f ↔ g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_1_comp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("g_2_comp", (args[0],)), OVar("g_1"))), OVar("g_2")))
            results.append((rhs, "Mathlib: OrderMonoidWithZeroHom_cancel_right"))
        except Exception:
            pass
    return results


def _r0052_toOrderAddMonoidHom_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingHom.toOrderAddMonoidHom_eq_coe
    # f.toOrderAddMonoidHom = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toOrderAddMonoidHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderRingHom_toOrderAddMonoidHom_eq_coe"))
    except Exception:
        pass
    return results


def _r0053_toOrderMonoidWithZeroHom_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingHom.toOrderMonoidWithZeroHom_eq_coe
    # f.toOrderMonoidWithZeroHom = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toOrderMonoidWithZeroHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderRingHom_toOrderMonoidWithZeroHom_eq_coe"))
    except Exception:
        pass
    return results


def _r0054_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingHom.copy_eq
    # f.copy f' h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_copy", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderRingHom_copy_eq"))
        except Exception:
            pass
    return results


def _r0055_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingHom.comp_apply
    # f.comp g a = f (g a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("g", (args[1],)),))
            results.append((rhs, "Mathlib: OrderRingHom_comp_apply"))
        except Exception:
            pass
    return results


def _r0056_comp_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingHom.comp_assoc
    # (f.comp g).comp h = f.comp (g.comp h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp_g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("f_comp", (OOp("g_comp", (args[0],)),))
            results.append((rhs, "Mathlib: OrderRingHom_comp_assoc"))
        except Exception:
            pass
    return results


def _r0057_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingHom.id_comp
    # (OrderRingHom.id β).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OrderRingHom_id_b_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: OrderRingHom_id_comp"))
        except Exception:
            pass
    return results


def _r0058_cancel_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingHom.cancel_right
    # f₁.comp g = f₂.comp g ↔ f₁ = f₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_1_comp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("f_2_comp", (args[0],)), OVar("f_1"))), OVar("f_2")))
            results.append((rhs, "Mathlib: OrderRingHom_cancel_right"))
        except Exception:
            pass
    return results


def _r0059_mk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingIso.mk_coe
    # (⟨e, h⟩ : α ≃+*o β) = e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_h", 4)
    if args is not None:
        try:
            rhs = OVar("e")
            results.append((rhs, "Mathlib: OrderRingIso_mk_coe"))
        except Exception:
            pass
    return results


def _r0060_toRingEquiv_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingIso.toRingEquiv_eq_coe
    # f.toRingEquiv = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toRingEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderRingIso_toRingEquiv_eq_coe"))
    except Exception:
        pass
    return results


def _r0061_coe_toRingEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingIso.coe_toRingEquiv
    # ⇑(f : α ≃+* β) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_colon_a_plus_star_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderRingIso_coe_toRingEquiv"))
    except Exception:
        pass
    return results


def _r0062_coe_toOrderIso(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingIso.coe_toOrderIso
    # DFunLike.coe (f : α ≃o β) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "DFunLike_coe", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderRingIso_coe_toOrderIso"))
        except Exception:
            pass
    return results


def _r0063_coe_ringEquiv_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingIso.coe_ringEquiv_refl
    # (OrderRingIso.refl α : α ≃+* α) = RingEquiv.refl α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OrderRingIso_refl", 5)
    if args is not None:
        try:
            rhs = OOp("RingEquiv_refl", (args[4],))
            results.append((rhs, "Mathlib: OrderRingIso_coe_ringEquiv_refl"))
        except Exception:
            pass
    return results


def _r0064_coe_orderIso_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingIso.coe_orderIso_refl
    # (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OrderRingIso_refl", 5)
    if args is not None:
        try:
            rhs = OOp("OrderIso_refl", (args[4],))
            results.append((rhs, "Mathlib: OrderRingIso_coe_orderIso_refl"))
        except Exception:
            pass
    return results


def _r0065_apply_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingIso.apply_symm_apply
    # e (e.symm b) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: OrderRingIso_apply_symm_apply"))
        except Exception:
            pass
    return results


def _r0066_self_trans_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingIso.self_trans_symm
    # e.trans e.symm = OrderRingIso.refl α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_trans", 1)
    if args is not None:
        try:
            rhs = OOp("OrderRingIso_refl", (OVar("a"),))
            results.append((rhs, "Mathlib: OrderRingIso_self_trans_symm"))
        except Exception:
            pass
    return results


def _r0067_symm_trans_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderRingIso.symm_trans_self
    # e.symm.trans e = OrderRingIso.refl β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm_trans", 1)
    if args is not None:
        try:
            rhs = OOp("OrderRingIso_refl", (OVar("b"),))
            results.append((rhs, "Mathlib: OrderRingIso_symm_trans_self"))
        except Exception:
            pass
    return results


def _r0068_fst_comp_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidHom.fstₗ_comp_inlₗ
    # (fstₗ α β).comp (inlₗ α β) = .id α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_a_b_comp", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("a"),))
            results.append((rhs, "Mathlib: OrderMonoidHom_fst_comp_inl"))
        except Exception:
            pass
    return results


def _r0069_snd_comp_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidHom.snd_comp_inl
    # (snd α β).comp (inl α β) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_a_b_comp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: OrderMonoidHom_snd_comp_inl"))
        except Exception:
            pass
    return results


def _r0070_fst_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidHom.fst_comp_inr
    # (fst α β).comp (inr α β) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_a_b_comp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: OrderMonoidHom_fst_comp_inr"))
        except Exception:
            pass
    return results


def _r0071_snd_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidHom.snd_comp_inr
    # (snd α β).comp (inr α β) = .id β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_a_b_comp", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("b"),))
            results.append((rhs, "Mathlib: OrderMonoidHom_snd_comp_inr"))
        except Exception:
            pass
    return results


def _r0072_inl_mul_inr_eq_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderMonoidHom.inl_mul_inr_eq_mk
    # inl α β m * inr α β n = (m, n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("m", (OVar("n"),))
            results.append((rhs, "Mathlib: OrderMonoidHom_inl_mul_inr_eq_mk"))
        except Exception:
            pass
    return results


def _r0073_succ_toMul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.succ_toMul
    # succ x.toMul = (succ x).toMul
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 1)
    if args is not None:
        try:
            rhs = OVar("succ_x_toMul")
            results.append((rhs, "Mathlib: Order_succ_toMul"))
        except Exception:
            pass
    return results


def _r0074_succ_ofAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.succ_ofAdd
    # succ (ofAdd x) = ofAdd (succ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 1)
    if args is not None:
        try:
            rhs = OOp("ofAdd", (OOp("succ", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Order_succ_ofAdd"))
        except Exception:
            pass
    return results


def _r0075_succ_toAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.succ_toAdd
    # succ x.toAdd = (succ x).toAdd
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "succ", 1)
    if args is not None:
        try:
            rhs = OVar("succ_x_toAdd")
            results.append((rhs, "Mathlib: Order_succ_toAdd"))
        except Exception:
            pass
    return results


def _r0076_pred_ofMul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.pred_ofMul
    # pred (ofMul x) = ofMul (pred x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pred", 1)
    if args is not None:
        try:
            rhs = OOp("ofMul", (OOp("pred", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Order_pred_ofMul"))
        except Exception:
            pass
    return results


def _r0077_pred_toMul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.pred_toMul
    # pred x.toMul = (pred x).toMul
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pred", 1)
    if args is not None:
        try:
            rhs = OVar("pred_x_toMul")
            results.append((rhs, "Mathlib: Order_pred_toMul"))
        except Exception:
            pass
    return results


def _r0078_pred_ofAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.pred_ofAdd
    # pred (ofAdd x) = ofAdd (pred x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pred", 1)
    if args is not None:
        try:
            rhs = OOp("ofAdd", (OOp("pred", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Order_pred_ofAdd"))
        except Exception:
            pass
    return results


def _r0079_pred_toAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.pred_toAdd
    # pred x.toAdd = (pred x).toAdd
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pred", 1)
    if args is not None:
        try:
            rhs = OVar("pred_x_toAdd")
            results.append((rhs, "Mathlib: Order_pred_toAdd"))
        except Exception:
            pass
    return results


def _r0080_up_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.up_ofNat
    # up (ofNat(n) : R) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "up", 1)
    if args is not None:
        try:
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: ULift_up_ofNat"))
        except Exception:
            pass
    return results


def _r0081_down_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.down_natCast
    # down (n : ULift R) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "down", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ULift_down_natCast"))
        except Exception:
            pass
    return results


def _r0082_down_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.down_ofNat
    # down (ofNat(n) : ULift R) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "down", 1)
    if args is not None:
        try:
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: ULift_down_ofNat"))
        except Exception:
            pass
    return results


def _r0083_extend_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderedFinpartition.extend_some
    # c.extend i = c.extendMiddle i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_extend", 1)
    if args is not None:
        try:
            rhs = OOp("c_extendMiddle", (args[0],))
            results.append((rhs, "Mathlib: OrderedFinpartition_extend_some"))
        except Exception:
            pass
    return results


def _r0084_nnnorm_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrthonormalBasis.nnnorm_eq_one
    # ‖b i‖₊ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: OrthonormalBasis_nnnorm_eq_one"))
        except Exception:
            pass
    return results


def _r0085_enorm_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrthonormalBasis.enorm_eq_one
    # ‖b i‖ₑ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: OrthonormalBasis_enorm_eq_one"))
        except Exception:
            pass
    return results


def _r0086_inner_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrthonormalBasis.inner_eq_zero
    # ⟪b i, b j⟫ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: OrthonormalBasis_inner_eq_zero"))
        except Exception:
            pass
    return results


def _r0087_inner_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrthonormalBasis.inner_eq_one
    # ⟪b i, b i⟫ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b", 3)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: OrthonormalBasis_inner_eq_one"))
        except Exception:
            pass
    return results


def _r0088_coe_toBasis_repr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrthonormalBasis.coe_toBasis_repr
    # b.toBasis.equivFun = b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (ι → 𝕜))
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b_toBasis_equivFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("b_repr_toLinearEquiv_trans", (OOp("WithLp_linearEquiv", (OLit(2), OVar("_unknown"), OOp("implies", (OVar("i"), OVar("_unknown"))),)),))
            results.append((rhs, "Mathlib: OrthonormalBasis_coe_toBasis_repr"))
    except Exception:
        pass
    return results


def _r0089_singleton_repr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrthonormalBasis.singleton_repr
    # (OrthonormalBasis.singleton ι 𝕜).repr x i = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OrthonormalBasis_singleton_i_repr", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: OrthonormalBasis_singleton_repr"))
        except Exception:
            pass
    return results


def _r0090_coe_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrthonormalBasis.coe_singleton
    # ⇑(OrthonormalBasis.singleton ι 𝕜) = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("OrthonormalBasis_singleton_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: OrthonormalBasis_coe_singleton"))
    except Exception:
        pass
    return results


def _r0091_toBasis_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrthonormalBasis.toBasis_singleton
    # (OrthonormalBasis.singleton ι 𝕜).toBasis = Basis.singleton ι 𝕜
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("OrthonormalBasis_singleton_i_toBasis")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Basis_singleton", (OVar("i"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: OrthonormalBasis_toBasis_singleton"))
    except Exception:
        pass
    return results


def _r0092_areaForm_rightAngleRotation_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.areaForm_rightAngleRotation_right
    # ω x (J y) = ⟪x, y⟫
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "omega", 2)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("y"),))
            results.append((rhs, "Mathlib: Orientation_areaForm_rightAngleRotation_right"))
        except Exception:
            pass
    return results


def _r0093_areaForm_comp_rightAngleRotation(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.areaForm_comp_rightAngleRotation
    # ω (J x) (J y) = ω x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "omega", 2)
    if args is not None:
        try:
            rhs = OOp("omega", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: Orientation_areaForm_comp_rightAngleRotation"))
        except Exception:
            pass
    return results


def _r0094_rightAngleRotation_neg_orientation(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.rightAngleRotation_neg_orientation
    # (-o).rightAngleRotation x = -o.rightAngleRotation x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_o_rightAngleRotation", 1)
    if args is not None:
        try:
            rhs = OOp("minus_o_rightAngleRotation", (args[0],))
            results.append((rhs, "Mathlib: Orientation_rightAngleRotation_neg_orientation"))
        except Exception:
            pass
    return results


def _r0095_kahler_rightAngleRotation_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.kahler_rightAngleRotation_left
    # o.kahler (J x) y = -Complex.I * o.kahler x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "o_kahler", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("minus_Complex_I"), OOp("o_kahler", (OVar("x"), args[1],))))
            results.append((rhs, "Mathlib: Orientation_kahler_rightAngleRotation_left"))
        except Exception:
            pass
    return results


def _r0096_kahler_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.kahler_mul
    # o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("a"), OLit(2))), OOp("o_kahler", (OVar("x"), OVar("y"),))))
            results.append((rhs, "Mathlib: Orientation_kahler_mul"))
        except Exception:
            pass
    return results


def _r0097_norm_down(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.norm_down
    # ‖x.down‖ = ‖x‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_down")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x")
            results.append((rhs, "Mathlib: ULift_norm_down"))
    except Exception:
        pass
    return results


def _r0098_commMonToLaxBraidedObj_mu(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommMon.EquivLaxBraidedFunctorPUnit.commMonToLaxBraidedObj_μ
    # «μ» (commMonToLaxBraidedObj A) X Y = μ[A.X]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu", 3)
    if args is not None:
        try:
            rhs = OVar("mu_A_X")
            results.append((rhs, "Mathlib: CommMon_EquivLaxBraidedFunctorPUnit_commMonToLaxBraidedObj_mu"))
        except Exception:
            pass
    return results


def _r0099_map_eta_comp_eta(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equivalence.map_η_comp_η
    # e.functor.map (η e.inverse) ≫ η e.functor = e.counit.app (𝟙_ D)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_functor_map", 4)
    if args is not None:
        try:
            rhs = OOp("e_counit_app", (OOp("_1", (OVar("D"),)),))
            results.append((rhs, "Mathlib: Equivalence_map_eta_comp_eta"))
        except Exception:
            pass
    return results


def _r0100_monToLaxMonoidalObj_mu(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Mon.EquivLaxMonoidalFunctorPUnit.monToLaxMonoidalObj_μ
    # «μ» (monToLaxMonoidalObj A) X Y = μ[A.X]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu", 3)
    if args is not None:
        try:
            rhs = OVar("mu_A_X")
            results.append((rhs, "Mathlib: Mon_EquivLaxMonoidalFunctorPUnit_monToLaxMonoidalObj_mu"))
        except Exception:
            pass
    return results


def _r0101_toIso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.toIso_inv
    # e.toIso.inv = e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toIso_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm")
            results.append((rhs, "Mathlib: Equiv_toIso_inv"))
    except Exception:
        pass
    return results


def _r0102_mapEquiv_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EquivFunctor.mapEquiv_symm_apply
    # (mapEquiv f e).symm y = EquivFunctor.map e.symm y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapEquiv_f_e_symm", 1)
    if args is not None:
        try:
            rhs = OOp("fmap", (OVar("e_symm"), args[0],))
            results.append((rhs, "Mathlib: EquivFunctor_mapEquiv_symm_apply"))
        except Exception:
            pass
    return results


def _r0103_mapEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EquivFunctor.mapEquiv_symm
    # (mapEquiv f e).symm = mapEquiv f e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mapEquiv_f_e_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("mapEquiv", (OVar("f"), OVar("e_symm"),))
            results.append((rhs, "Mathlib: EquivFunctor_mapEquiv_symm"))
    except Exception:
        pass
    return results


def _r0104_finsetCongr_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.finsetCongr_refl
    # (Equiv.refl α).finsetCongr = Equiv.refl _
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Equiv_refl_a_finsetCongr")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Equiv_refl", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: Equiv_finsetCongr_refl"))
    except Exception:
        pass
    return results


def _r0105_finsetCongr_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.finsetCongr_trans
    # e.finsetCongr.trans e'.finsetCongr = (e.trans e').finsetCongr
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_finsetCongr_trans", 1)
    if args is not None:
        try:
            rhs = OVar("e_trans_e_prime_finsetCongr")
            results.append((rhs, "Mathlib: Equiv_finsetCongr_trans"))
        except Exception:
            pass
    return results


def _r0106_inv_apply_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EquivLike.inv_apply_eq
    # inv e b = a ↔ b = e a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inv", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("a"), args[1])), OOp("e", (OVar("a"),))))
            results.append((rhs, "Mathlib: EquivLike_inv_apply_eq"))
        except Exception:
            pass
    return results


def _r0107_apply_inv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EquivLike.apply_inv_apply
    # e (inv e b) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: EquivLike_apply_inv_apply"))
        except Exception:
            pass
    return results


def _r0108_mapMatrix_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.mapMatrix_symm
    # f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ _)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_mapMatrix_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_symm_mapMatrix", (OVar("colon"), OVar("Matrix"), OVar("m"), OVar("n"), OVar("b"), OVar("_unknown"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: Equiv_mapMatrix_symm"))
    except Exception:
        pass
    return results


def _r0109_mapMatrix_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.mapMatrix_trans
    # f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_mapMatrix_trans", 1)
    if args is not None:
        try:
            rhs = OOp("f_trans_g_mapMatrix", (OVar("colon"), OVar("Matrix"), OVar("m"), OVar("n"), OVar("a"), OVar("_unknown"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: Equiv_mapMatrix_trans"))
        except Exception:
            pass
    return results


def _r0110_compares_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordering.compares_eq
    # Compares eq a b = (a = b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Compares", 3)
    if args is not None:
        try:
            rhs = OOp("==", (args[1], args[2]))
            results.append((rhs, "Mathlib: Ordering_compares_eq"))
        except Exception:
            pass
    return results


def _r0111_compares_gt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordering.compares_gt
    # Compares gt a b = (a > b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Compares", 3)
    if args is not None:
        try:
            rhs = OOp(">", (args[1], args[2]))
            results.append((rhs, "Mathlib: Ordering_compares_gt"))
        except Exception:
            pass
    return results


def _r0112_toList_node(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordnode.toList_node
    # toList (@node α s l x r) = toList l ++ x :: toList r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("toList", (OVar("l"),)), OOp("x", (OVar("colon_colon"), OVar("toList"), OVar("r"),))))
            results.append((rhs, "Mathlib: Ordnode_toList_node"))
        except Exception:
            pass
    return results


def _r0113_merge_nil_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordnode.merge_nil_right
    # merge nil t = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "merge", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Ordnode_merge_nil_right"))
        except Exception:
            pass
    return results


def _r0114_merge_node(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordnode.merge_node
    # merge (@node α ls ll lx lr) (node rs rl rx rr) =       if delta * ls < rs then balanceL (merge (node ls ll lx lr) rl) rx
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "merge", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("*", (OOp("if", (OVar("delta"),)), OVar("ls"))), OOp("<", (OOp("*", (OOp("rs", (OVar("then"), OVar("balanceL"), OOp("merge", (OOp("node", (OVar("ls"), OVar("ll"), OVar("lx"), OVar("lr"),)), OVar("rl"),)), OVar("rx"), OVar("rr"), OVar("else"), OVar("if"), OVar("delta"),)), OVar("rs"))), OOp("ls", (OVar("then"), OVar("balanceR"), OVar("ll"), OVar("lx"), OOp("merge", (OVar("lr"), OOp("node", (OVar("rs"), OVar("rl"), OVar("rx"), OVar("rr"),)),)), OVar("else"), OVar("glue"), OOp("node", (OVar("ls"), OVar("ll"), OVar("lx"), OVar("lr"),)), OOp("node", (OVar("rs"), OVar("rl"), OVar("rx"), OVar("rr"),)),))))))
            results.append((rhs, "Mathlib: Ordnode_merge_node"))
        except Exception:
            pass
    return results


def _r0115_size_node(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordnode.size_node
    # size (node sz l x r) = sz
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "size", 1)
    if args is not None:
        try:
            rhs = OVar("sz")
            results.append((rhs, "Mathlib: Ordnode_size_node"))
        except Exception:
            pass
    return results


def _r0116_toPEquiv_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.toPEquiv_trans
    # (f.trans g).toPEquiv = f.toPEquiv.trans g.toPEquiv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_trans_g_toPEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_toPEquiv_trans", (OVar("g_toPEquiv"),))
            results.append((rhs, "Mathlib: Equiv_toPEquiv_trans"))
    except Exception:
        pass
    return results


def _r0117_sumComm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumComm_symm
    # (OrderIso.sumComm α β).symm = OrderIso.sumComm β α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("OrderIso_sumComm_a_b_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("OrderIso_sumComm", (OVar("b"), OVar("a"),))
            results.append((rhs, "Mathlib: OrderIso_sumComm_symm"))
    except Exception:
        pass
    return results


def _r0118_sumAssoc_apply_inl_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumAssoc_apply_inl_inr
    # sumAssoc α β γ (inl (inr b)) = inr (inl b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumAssoc", 4)
    if args is not None:
        try:
            rhs = OOp("inr", (OOp("inl", (args[1],)),))
            results.append((rhs, "Mathlib: OrderIso_sumAssoc_apply_inl_inr"))
        except Exception:
            pass
    return results


def _r0119_sumAssoc_apply_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumAssoc_apply_inr
    # sumAssoc α β γ (inr c) = inr (inr c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumAssoc", 4)
    if args is not None:
        try:
            rhs = OOp("inr", (OOp("inr", (OVar("c"),)),))
            results.append((rhs, "Mathlib: OrderIso_sumAssoc_apply_inr"))
        except Exception:
            pass
    return results


def _r0120_sumAssoc_symm_apply_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumAssoc_symm_apply_inl
    # (sumAssoc α β γ).symm (inl a) = inl (inl a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumAssoc_a_b_g_symm", 1)
    if args is not None:
        try:
            rhs = OOp("inl", (OOp("inl", (OVar("a"),)),))
            results.append((rhs, "Mathlib: OrderIso_sumAssoc_symm_apply_inl"))
        except Exception:
            pass
    return results


def _r0121_sumAssoc_symm_apply_inr_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumAssoc_symm_apply_inr_inl
    # (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumAssoc_a_b_g_symm", 1)
    if args is not None:
        try:
            rhs = OOp("inl", (OOp("inr", (OVar("b"),)),))
            results.append((rhs, "Mathlib: OrderIso_sumAssoc_symm_apply_inr_inl"))
        except Exception:
            pass
    return results


def _r0122_sumAssoc_symm_apply_inr_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumAssoc_symm_apply_inr_inr
    # (sumAssoc α β γ).symm (inr (inr c)) = inr c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumAssoc_a_b_g_symm", 1)
    if args is not None:
        try:
            rhs = OOp("inr", (OVar("c"),))
            results.append((rhs, "Mathlib: OrderIso_sumAssoc_symm_apply_inr_inr"))
        except Exception:
            pass
    return results


def _r0123_sumDualDistrib_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumDualDistrib_inr
    # sumDualDistrib α β (toDual (inr b)) = inr (toDual b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumDualDistrib", 3)
    if args is not None:
        try:
            rhs = OOp("inr", (OOp("toDual", (args[1],)),))
            results.append((rhs, "Mathlib: OrderIso_sumDualDistrib_inr"))
        except Exception:
            pass
    return results


def _r0124_sumDualDistrib_symm_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumDualDistrib_symm_inl
    # (sumDualDistrib α β).symm (inl (toDual a)) = toDual (inl a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumDualDistrib_a_b_symm", 1)
    if args is not None:
        try:
            rhs = OOp("toDual", (OOp("inl", (OVar("a"),)),))
            results.append((rhs, "Mathlib: OrderIso_sumDualDistrib_symm_inl"))
        except Exception:
            pass
    return results


def _r0125_sumDualDistrib_symm_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumDualDistrib_symm_inr
    # (sumDualDistrib α β).symm (inr (toDual b)) = toDual (inr b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumDualDistrib_a_b_symm", 1)
    if args is not None:
        try:
            rhs = OOp("toDual", (OOp("inr", (OVar("b"),)),))
            results.append((rhs, "Mathlib: OrderIso_sumDualDistrib_symm_inr"))
        except Exception:
            pass
    return results


def _r0126_sumLexAssoc_symm_apply_inr_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumLexAssoc_symm_apply_inr_inl
    # (sumLexAssoc α β γ).symm (inr (inl b)) = inl (inr b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumLexAssoc_a_b_g_symm", 1)
    if args is not None:
        try:
            rhs = OOp("inl", (OOp("inr", (OVar("b"),)),))
            results.append((rhs, "Mathlib: OrderIso_sumLexAssoc_symm_apply_inr_inl"))
        except Exception:
            pass
    return results


def _r0127_sumLexAssoc_symm_apply_inr_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumLexAssoc_symm_apply_inr_inr
    # (sumLexAssoc α β γ).symm (inr (inr c)) = inr c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumLexAssoc_a_b_g_symm", 1)
    if args is not None:
        try:
            rhs = OOp("inr", (OVar("c"),))
            results.append((rhs, "Mathlib: OrderIso_sumLexAssoc_symm_apply_inr_inr"))
        except Exception:
            pass
    return results


def _r0128_emptySumLex_apply_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.emptySumLex_apply_inr
    # emptySumLex (β := β) (toLex <| .inr x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "emptySumLex", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: OrderIso_emptySumLex_apply_inr"))
        except Exception:
            pass
    return results


def _r0129_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.ext
    # x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: ULift_ext"))
    except Exception:
        pass
    return results


def _r0130_oangle_zero_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.oangle_zero_right
    # o.oangle x 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "o_oangle", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Orientation_oangle_zero_right"))
        except Exception:
            pass
    return results


def _r0131_oangle_neg_left_eq_neg_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.oangle_neg_left_eq_neg_right
    # o.oangle (-x) y = o.oangle x (-y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "o_oangle", 2)
    if args is not None:
        try:
            rhs = OOp("o_oangle", (OVar("x"), OVar("minus_y"),))
            results.append((rhs, "Mathlib: Orientation_oangle_neg_left_eq_neg_right"))
        except Exception:
            pass
    return results


def _r0132_rotation_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.rotation_pi
    # o.rotation π = LinearIsometryEquiv.neg ℝ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "o_rotation", 1)
    if args is not None:
        try:
            rhs = OOp("LinearIsometryEquiv_neg", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: Orientation_rotation_pi"))
        except Exception:
            pass
    return results


def _r0133_one_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OreLocalization.one_smul
    # (1 : R[S⁻¹]) • x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_R_Sinv", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: OreLocalization_one_smul"))
        except Exception:
            pass
    return results


def _r0134_one_div_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OreLocalization.one_div_mul
    # (1 /ₒ t) * (r /ₒ s) = r /ₒ (s * t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("slash"), OOp("*", (OVar("s"), OVar("t"))),))
            results.append((rhs, "Mathlib: OreLocalization_one_div_mul"))
        except Exception:
            pass
    return results


def _r0135_smul_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OreLocalization.smul_cancel
    # ((s : R) /ₒ t) • (r /ₒ s) = r /ₒ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_colon_R_slash_t", 2)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("slash"), OVar("t"),))
            results.append((rhs, "Mathlib: OreLocalization_smul_cancel"))
        except Exception:
            pass
    return results


def _r0136_mul_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OreLocalization.mul_cancel
    # ((s : R) /ₒ t) * (r /ₒ s) = r /ₒ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("slash"), OVar("t"),))
            results.append((rhs, "Mathlib: OreLocalization_mul_cancel"))
        except Exception:
            pass
    return results


def _r0137_mul_div_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OreLocalization.mul_div_one
    # (p /ₒ s) * (r /ₒ 1) = (p * r) /ₒ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("p_star_r", (OVar("slash"), OVar("s"),))
            results.append((rhs, "Mathlib: OreLocalization_mul_div_one"))
        except Exception:
            pass
    return results


def _r0138_oreSetComm_oreDenom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OreLocalization.oreSetComm_oreDenom
    # oreDenom r s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "oreDenom", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: OreLocalization_oreSetComm_oreDenom"))
        except Exception:
            pass
    return results


def _r0139_toList_eq_nil_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.toList_eq_nil_iff
    # toList p x = [] ↔ x ∉ p.support
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OSeq(()), OOp("not_in", (args[1], OVar("p_support")))))
            results.append((rhs, "Mathlib: Equiv_Perm_toList_eq_nil_iff"))
        except Exception:
            pass
    return results


def _r0140_length_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.length_toList
    # length (toList p x) = (cycleOf p x).support.card
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OVar("cycleOf_p_x_support_card")
            results.append((rhs, "Mathlib: Equiv_Perm_length_toList"))
        except Exception:
            pass
    return results


def _r0141_cycleOf_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.IsCycle.cycleOf_eq
    # cycleOf f x = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleOf", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Equiv_Perm_IsCycle_cycleOf_eq"))
        except Exception:
            pass
    return results


def _r0142_cycleType_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.cycleType_one
    # (1 : Perm α).cycleType = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Perm_a_cycleType")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Equiv_Perm_cycleType_one"))
    except Exception:
        pass
    return results


def _r0143_card_cycleType_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.card_cycleType_eq_zero
    # Multiset.card σ.cycleType = 0 ↔ σ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("sig"))), OLit(1)))
            results.append((rhs, "Mathlib: Equiv_Perm_card_cycleType_eq_zero"))
        except Exception:
            pass
    return results


def _r0144_decomposeFin_symm_apply_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.decomposeFin_symm_apply_succ
    # Equiv.Perm.decomposeFin.symm (p, e) x.succ = swap 0 p (e x).succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_Perm_decomposeFin_symm", 2)
    if args is not None:
        try:
            rhs = OOp("swap", (OLit(0), OVar("p"), OVar("e_x_succ"),))
            results.append((rhs, "Mathlib: Equiv_Perm_decomposeFin_symm_apply_succ"))
        except Exception:
            pass
    return results


def _r0145_optionCongr_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.optionCongr_swap
    # optionCongr (swap x y) = swap (some x) (some y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "optionCongr", 1)
    if args is not None:
        try:
            rhs = OOp("swap", (OOp("some", (OVar("x"),)), OOp("some", (OVar("y"),)),))
            results.append((rhs, "Mathlib: Equiv_optionCongr_swap"))
        except Exception:
            pass
    return results


def _r0146_sign_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.sign_trans
    # sign (f.trans g) = sign g * sign f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sign", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("sign", (OVar("g"),)), OOp("sign", (OVar("f"),))))
            results.append((rhs, "Mathlib: Equiv_Perm_sign_trans"))
        except Exception:
            pass
    return results


def _r0147_sign_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.sign_one
    # sign (1 : Perm α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sign", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Equiv_Perm_sign_one"))
        except Exception:
            pass
    return results


def _r0148_sign_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.sign_refl
    # sign (Equiv.refl α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sign", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Equiv_Perm_sign_refl"))
        except Exception:
            pass
    return results


def _r0149_sign_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.sign_inv
    # sign f⁻¹ = sign f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sign", 1)
    if args is not None:
        try:
            rhs = OOp("sign", (OVar("f"),))
            results.append((rhs, "Mathlib: Equiv_Perm_sign_inv"))
        except Exception:
            pass
    return results


def _r0150_sign_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.sign_symm
    # sign e.symm = sign e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sign", 1)
    if args is not None:
        try:
            rhs = OOp("sign", (OVar("e"),))
            results.append((rhs, "Mathlib: Equiv_Perm_sign_symm"))
        except Exception:
            pass
    return results


def _r0151_sign_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.sign_swap
    # sign (swap x y) = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sign", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Equiv_Perm_sign_swap"))
        except Exception:
            pass
    return results


def _r0152_sign_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.IsSwap.sign_eq
    # sign f = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sign", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Equiv_Perm_IsSwap_sign_eq"))
        except Exception:
            pass
    return results


def _r0153_sign_sumCongr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.sign_sumCongr
    # sign (sumCongr σa σb) = sign σa * sign σb
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sign", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("sign", (OVar("siga"),)), OOp("sign", (OVar("sigb"),))))
            results.append((rhs, "Mathlib: Equiv_Perm_sign_sumCongr"))
        except Exception:
            pass
    return results


def _r0154_disjoint_iff_eq_or_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.disjoint_iff_eq_or_eq
    # Disjoint f g ↔ ∀ x : α, f x = x ∨ g x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OVar("x"), OOp("g", (OVar("x"),)))), OVar("x")))
            results.append((rhs, "Mathlib: Equiv_Perm_disjoint_iff_eq_or_eq"))
        except Exception:
            pass
    return results


def _r0155_reverse_v(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CliffordAlgebra.EquivEven.reverse_v
    # reverse (Q := Q' Q) (v Q m) = v Q m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reverse", 2)
    if args is not None:
        try:
            rhs = OOp("v", (OVar("Q"), OVar("m"),))
            results.append((rhs, "Mathlib: CliffordAlgebra_EquivEven_reverse_v"))
        except Exception:
            pass
    return results


def _r0156_involute_v(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CliffordAlgebra.EquivEven.involute_v
    # involute (v Q m) = -v Q m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "involute", 1)
    if args is not None:
        try:
            rhs = OOp("minus_v", (OVar("Q"), OVar("m"),))
            results.append((rhs, "Mathlib: CliffordAlgebra_EquivEven_involute_v"))
        except Exception:
            pass
    return results


def _r0157_reverse_e0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CliffordAlgebra.EquivEven.reverse_e0
    # reverse (Q := Q' Q) (e0 Q) = e0 Q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reverse", 2)
    if args is not None:
        try:
            rhs = OOp("e0", (OVar("Q"),))
            results.append((rhs, "Mathlib: CliffordAlgebra_EquivEven_reverse_e0"))
        except Exception:
            pass
    return results


def _r0158_involute_e0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CliffordAlgebra.EquivEven.involute_e0
    # involute (e0 Q) = -e0 Q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "involute", 1)
    if args is not None:
        try:
            rhs = OOp("minus_e0", (OVar("Q"),))
            results.append((rhs, "Mathlib: CliffordAlgebra_EquivEven_involute_e0"))
        except Exception:
            pass
    return results


def _r0159_map_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.map_symm
    # (Orientation.map ι e).symm = Orientation.map ι e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Orientation_map_i_e_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Orientation_map", (OVar("i"), OVar("e_symm"),))
            results.append((rhs, "Mathlib: Orientation_map_symm"))
    except Exception:
        pass
    return results


def _r0160_reindex_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.reindex_symm
    # (Orientation.reindex R M e).symm = Orientation.reindex R M e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Orientation_reindex_R_M_e_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Orientation_reindex", (OVar("R"), OVar("M"), OVar("e_symm"),))
            results.append((rhs, "Mathlib: Orientation_reindex_symm"))
    except Exception:
        pass
    return results


def _r0161_map_of_isEmpty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Orientation.map_of_isEmpty
    # Orientation.map ι f x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Orientation_map", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Orientation_map_of_isEmpty"))
        except Exception:
            pass
    return results


def _r0162_sigPos_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Equivalent.sigPos_eq
    # sigPos Q = sigPos Q'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sigPos", 1)
    if args is not None:
        try:
            rhs = OOp("sigPos", (OVar("Q_prime"),))
            results.append((rhs, "Mathlib: QuadraticMap_Equivalent_sigPos_eq"))
        except Exception:
            pass
    return results


def _r0163_root_indexEquiv_eq_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RootPairing.Equiv.root_indexEquiv_eq_smul
    # P.root (g.indexEquiv i) = g • P.root i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "P_root", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("_unknown"), OVar("P_root"), OVar("i"),))
            results.append((rhs, "Mathlib: RootPairing_Equiv_root_indexEquiv_eq_smul"))
        except Exception:
            pass
    return results


def _r0164_toEmbedding_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.toEmbedding_apply
    # f.toEmbedding a = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toEmbedding", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: Equiv_toEmbedding_apply"))
        except Exception:
            pass
    return results


def _r0165_trans_toEmbedding(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.trans_toEmbedding
    # (e.trans f).toEmbedding = e.toEmbedding.trans f.toEmbedding
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_trans_f_toEmbedding")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("e_toEmbedding_trans", (OVar("f_toEmbedding"),))
            results.append((rhs, "Mathlib: Equiv_trans_toEmbedding"))
    except Exception:
        pass
    return results


def _r0166_left_apply_subtype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.subtypeCongr.left_apply_subtype
    # ep.subtypeCongr en a = ep a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ep_subtypeCongr", 2)
    if args is not None:
        try:
            rhs = OOp("ep", (args[1],))
            results.append((rhs, "Mathlib: Equiv_Perm_subtypeCongr_left_apply_subtype"))
        except Exception:
            pass
    return results


def _r0167_right_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.subtypeCongr.right_apply
    # ep.subtypeCongr en a = en ⟨a, h⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ep_subtypeCongr", 2)
    if args is not None:
        try:
            rhs = OOp("en", (OVar("a_h"),))
            results.append((rhs, "Mathlib: Equiv_Perm_subtypeCongr_right_apply"))
        except Exception:
            pass
    return results


def _r0168_right_apply_subtype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.subtypeCongr.right_apply_subtype
    # ep.subtypeCongr en a = en a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ep_subtypeCongr", 2)
    if args is not None:
        try:
            rhs = OOp("en", (args[1],))
            results.append((rhs, "Mathlib: Equiv_Perm_subtypeCongr_right_apply_subtype"))
        except Exception:
            pass
    return results


def _r0169_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.subtypeCongr.refl
    # Perm.subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl ε
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Perm_subtypeCongr", 2)
    if args is not None:
        try:
            rhs = OOp("Equiv_refl", (OVar("e"),))
            results.append((rhs, "Mathlib: Equiv_Perm_subtypeCongr_refl"))
        except Exception:
            pass
    return results


def _r0170_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.subtypeCongr.trans
    # (ep.subtypeCongr en).trans (ep'.subtypeCongr en')     = Perm.subtypeCongr (ep.trans ep') (en.trans en')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ep_subtypeCongr_en_trans", 1)
    if args is not None:
        try:
            rhs = OOp("Perm_subtypeCongr", (OOp("ep_trans", (OVar("ep_prime"),)), OOp("en_trans", (OVar("en_prime"),)),))
            results.append((rhs, "Mathlib: Equiv_Perm_subtypeCongr_trans"))
        except Exception:
            pass
    return results


def _r0171_coe_fn_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.coe_fn_injective
    # @Function.Injective (α ≃ β) (α → β) (fun e => e)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b_fun", 1)
    if args is not None:
        try:
            rhs = OOp("gt", (args[0],))
            results.append((rhs, "Mathlib: Equiv_coe_fn_injective"))
        except Exception:
            pass
    return results


def _r0172_invFun_as_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.invFun_as_coe
    # e.invFun = e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_invFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm")
            results.append((rhs, "Mathlib: Equiv_invFun_as_coe"))
    except Exception:
        pass
    return results


def _r0173_trans_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.trans_apply
    # (f.trans g) a = g (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_trans_g", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: Equiv_trans_apply"))
        except Exception:
            pass
    return results


def _r0174_apply_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.apply_symm_apply
    # e (e.symm x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Equiv_apply_symm_apply"))
        except Exception:
            pass
    return results


def _r0175_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.symm_apply_apply
    # e.symm (e x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Equiv_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0176_symm_comp_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.symm_comp_self
    # e.symm ∘ e = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Equiv_symm_comp_self"))
        except Exception:
            pass
    return results


def _r0177_self_comp_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.self_comp_symm
    # e ∘ e.symm = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Equiv_self_comp_symm"))
        except Exception:
            pass
    return results


def _r0178_apply_coe_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EquivLike.apply_coe_symm_apply
    # e ((e : α ≃ β).symm x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: EquivLike_apply_coe_symm_apply"))
        except Exception:
            pass
    return results


def _r0179_coe_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EquivLike.coe_symm_apply_apply
    # (e : α ≃ β).symm (e x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_colon_a_b_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: EquivLike_coe_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0180_coe_symm_comp_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EquivLike.coe_symm_comp_self
    # (e : α ≃ β).symm ∘ e = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: EquivLike_coe_symm_comp_self"))
        except Exception:
            pass
    return results


def _r0181_self_comp_coe_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EquivLike.self_comp_coe_symm
    # e ∘ (e : α ≃ β).symm = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: EquivLike_self_comp_coe_symm"))
        except Exception:
            pass
    return results


def _r0182_symm_trans_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.symm_trans_apply
    # (f.trans g).symm a = f.symm (g.symm a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_trans_g_symm", 1)
    if args is not None:
        try:
            rhs = OOp("f_symm", (OOp("g_symm", (args[0],)),))
            results.append((rhs, "Mathlib: Equiv_symm_trans_apply"))
        except Exception:
            pass
    return results


def _r0183_symm_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.symm_symm_apply
    # f.symm.symm b = f b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_symm_symm", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: Equiv_symm_symm_apply"))
        except Exception:
            pass
    return results


def _r0184_cast_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.cast_symm
    # Equiv.cast h.symm = (Equiv.cast h).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_cast", 1)
    if args is not None:
        try:
            rhs = OVar("Equiv_cast_h_symm")
            results.append((rhs, "Mathlib: Equiv_cast_symm"))
        except Exception:
            pass
    return results


def _r0185_cast_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.cast_refl
    # Equiv.cast h = Equiv.refl α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_cast", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_refl", (OVar("a"),))
            results.append((rhs, "Mathlib: Equiv_cast_refl"))
        except Exception:
            pass
    return results


def _r0186_cast_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.cast_trans
    # Equiv.cast (h.trans h2) = (Equiv.cast h).trans (Equiv.cast h2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_cast", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_cast_h_trans", (OOp("Equiv_cast", (OVar("h2"),)),))
            results.append((rhs, "Mathlib: Equiv_cast_trans"))
        except Exception:
            pass
    return results


def _r0187_refl_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.refl_symm
    # (Equiv.refl α).symm = Equiv.refl α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Equiv_refl_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Equiv_refl", (OVar("a"),))
            results.append((rhs, "Mathlib: Equiv_refl_symm"))
    except Exception:
        pass
    return results


def _r0188_refl_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.refl_trans
    # (Equiv.refl α).trans e = e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_refl_a_trans", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Equiv_refl_trans"))
        except Exception:
            pass
    return results


def _r0189_symm_trans_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.symm_trans_self
    # e.symm.trans e = Equiv.refl β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm_trans", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_refl", (OVar("b"),))
            results.append((rhs, "Mathlib: Equiv_symm_trans_self"))
        except Exception:
            pass
    return results


def _r0190_self_trans_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.self_trans_symm
    # e.trans e.symm = Equiv.refl α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_trans", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_refl", (OVar("a"),))
            results.append((rhs, "Mathlib: Equiv_self_trans_symm"))
        except Exception:
            pass
    return results


def _r0191_trans_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.trans_assoc
    # (ab.trans bc).trans cd = ab.trans (bc.trans cd)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ab_trans_bc_trans", 1)
    if args is not None:
        try:
            rhs = OOp("ab_trans", (OOp("bc_trans", (args[0],)),))
            results.append((rhs, "Mathlib: Equiv_trans_assoc"))
        except Exception:
            pass
    return results


def _r0192_equivCongr_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.equivCongr_symm
    # (ab.equivCongr cd).symm = ab.symm.equivCongr cd.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ab_equivCongr_cd_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ab_symm_equivCongr", (OVar("cd_symm"),))
            results.append((rhs, "Mathlib: Equiv_equivCongr_symm"))
    except Exception:
        pass
    return results


def _r0193_equivCongr_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.equivCongr_refl
    # (Equiv.refl α).equivCongr (Equiv.refl β) = Equiv.refl (α ≃ β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_refl_a_equivCongr", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_refl", (OOp("a", (OVar("_unknown"), OVar("b"),)),))
            results.append((rhs, "Mathlib: Equiv_equivCongr_refl"))
        except Exception:
            pass
    return results


def _r0194_equivCongr_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.equivCongr_trans
    # (ab.equivCongr de).trans (bc.equivCongr ef) = (ab.trans bc).equivCongr (de.trans ef)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ab_equivCongr_de_trans", 1)
    if args is not None:
        try:
            rhs = OOp("ab_trans_bc_equivCongr", (OOp("de_trans", (OVar("ef"),)),))
            results.append((rhs, "Mathlib: Equiv_equivCongr_trans"))
        except Exception:
            pass
    return results


def _r0195_equivCongr_refl_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.equivCongr_refl_left
    # (Equiv.refl α).equivCongr bg e = e.trans bg
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_refl_a_equivCongr", 2)
    if args is not None:
        try:
            rhs = OOp("e_trans", (args[0],))
            results.append((rhs, "Mathlib: Equiv_equivCongr_refl_left"))
        except Exception:
            pass
    return results


def _r0196_equivCongr_refl_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.equivCongr_refl_right
    # ab.equivCongr (Equiv.refl β) e = ab.symm.trans e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ab_equivCongr", 2)
    if args is not None:
        try:
            rhs = OOp("ab_symm_trans", (args[1],))
            results.append((rhs, "Mathlib: Equiv_equivCongr_refl_right"))
        except Exception:
            pass
    return results


def _r0197_permCongr_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.permCongr_symm
    # e.permCongr.symm = e.symm.permCongr
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_permCongr_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm_permCongr")
            results.append((rhs, "Mathlib: Equiv_permCongr_symm"))
    except Exception:
        pass
    return results


def _r0198_permCongr_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.permCongr_apply
    # e.permCongr p x = e (p (e.symm x))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_permCongr", 2)
    if args is not None:
        try:
            rhs = OOp("e", (OOp("p", (OOp("e_symm", (args[1],)),)),))
            results.append((rhs, "Mathlib: Equiv_permCongr_apply"))
        except Exception:
            pass
    return results


def _r0199_permCongr_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.permCongr_symm_apply
    # e.permCongr.symm p x = e.symm (p (e x))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_permCongr_symm", 2)
    if args is not None:
        try:
            rhs = OOp("e_symm", (OOp("p", (OOp("e", (args[1],)),)),))
            results.append((rhs, "Mathlib: Equiv_permCongr_symm_apply"))
        except Exception:
            pass
    return results


def _r0200_embeddingFinSucc_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.embeddingFinSucc_snd
    # ((Equiv.embeddingFinSucc n ι e).2 : ι) = e 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_embeddingFinSucc_n_i_e_2", 2)
    if args is not None:
        try:
            rhs = OOp("e", (OLit(0),))
            results.append((rhs, "Mathlib: Equiv_embeddingFinSucc_snd"))
        except Exception:
            pass
    return results


def _r0201_natSumNatEquivNat_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.natSumNatEquivNat_apply
    # ⇑natSumNatEquivNat = Sum.elim (2 * ·) (2 * · + 1)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("natSumNatEquivNat")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Sum_elim", (OOp("*", (OLit(2), OVar("_unknown"))), OOp("+", (OOp("*", (OLit(2), OVar("_unknown"))), OLit(1))),))
            results.append((rhs, "Mathlib: Equiv_natSumNatEquivNat_apply"))
    except Exception:
        pass
    return results


def _r0202_optionCongr_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.optionCongr_symm
    # optionCongr e.symm = (optionCongr e).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "optionCongr", 1)
    if args is not None:
        try:
            rhs = OVar("optionCongr_e_symm")
            results.append((rhs, "Mathlib: Equiv_optionCongr_symm"))
        except Exception:
            pass
    return results


def _r0203_optionCongr_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.optionCongr_trans
    # optionCongr (e₁.trans e₂) = (optionCongr e₁).trans (optionCongr e₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "optionCongr", 1)
    if args is not None:
        try:
            rhs = OOp("optionCongr_e_1_trans", (OOp("optionCongr", (OVar("e_2"),)),))
            results.append((rhs, "Mathlib: Equiv_optionCongr_trans"))
        except Exception:
            pass
    return results


def _r0204_symm_toPartialEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.symm_toPartialEquiv
    # e.symm.toPartialEquiv = e.toPartialEquiv.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_toPartialEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_toPartialEquiv_symm")
            results.append((rhs, "Mathlib: Equiv_symm_toPartialEquiv"))
    except Exception:
        pass
    return results


def _r0205_trans_toPartialEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.trans_toPartialEquiv
    # (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_trans_e_prime_toPartialEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("e_toPartialEquiv_trans", (OVar("e_prime_toPartialEquiv"),))
            results.append((rhs, "Mathlib: Equiv_trans_toPartialEquiv"))
    except Exception:
        pass
    return results


def _r0206_prodComm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.prodComm_apply
    # prodComm α β x = x.swap
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prodComm", 3)
    if args is not None:
        try:
            rhs = OVar("x_swap")
            results.append((rhs, "Mathlib: Equiv_prodComm_apply"))
        except Exception:
            pass
    return results


def _r0207_prodComm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.prodComm_symm
    # (prodComm α β).symm = prodComm β α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("prodComm_a_b_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("prodComm", (OVar("b"), OVar("a"),))
            results.append((rhs, "Mathlib: Equiv_prodComm_symm"))
    except Exception:
        pass
    return results


def _r0208_prodUnique_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.prodUnique_apply
    # prodUnique α β x = x.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prodUnique", 3)
    if args is not None:
        try:
            rhs = OVar("x_1")
            results.append((rhs, "Mathlib: Equiv_prodUnique_apply"))
        except Exception:
            pass
    return results


def _r0209_uniqueProd_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.uniqueProd_apply
    # uniqueProd α β x = x.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uniqueProd", 3)
    if args is not None:
        try:
            rhs = OVar("x_2")
            results.append((rhs, "Mathlib: Equiv_uniqueProd_apply"))
        except Exception:
            pass
    return results


def _r0210_eq_image_iff_symm_image_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.eq_image_iff_symm_image_eq
    # t = e '' s ↔ e.symm '' t = s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("e", (OVar("prime_prime"), OVar("s"),)), OOp("e_symm", (OVar("prime_prime"), OVar("t"),)))), OVar("s")))
            results.append((rhs, "Mathlib: Equiv_eq_image_iff_symm_image_eq"))
    except Exception:
        pass
    return results


def _r0211_image_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.image_preimage
    # e '' (e ⁻¹' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Equiv_image_preimage"))
        except Exception:
            pass
    return results


def _r0212_preimage_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.preimage_image
    # e ⁻¹' (e '' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Equiv_preimage_image"))
        except Exception:
            pass
    return results


def _r0213_image_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.image_compl
    # f '' sᶜ = (f '' s)ᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OVar("f_prime_prime_s")
            results.append((rhs, "Mathlib: Equiv_image_compl"))
        except Exception:
            pass
    return results


def _r0214_preimage_symm_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.preimage_symm_preimage
    # e ⁻¹' (e.symm ⁻¹' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Equiv_preimage_symm_preimage"))
        except Exception:
            pass
    return results


def _r0215_preimage_eq_iff_eq_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.preimage_eq_iff_eq_image
    # e ⁻¹' s = t ↔ s = e '' t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("t"), args[1])), OOp("e", (OVar("prime_prime"), OVar("t"),))))
            results.append((rhs, "Mathlib: Equiv_preimage_eq_iff_eq_image"))
        except Exception:
            pass
    return results


def _r0216_sumCongr_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.sumCongr_trans
    # (Equiv.sumCongr e f).trans (Equiv.sumCongr g h) = Equiv.sumCongr (e.trans g) (f.trans h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_sumCongr_e_f_trans", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_sumCongr", (OOp("e_trans", (OVar("g"),)), OOp("f_trans", (OVar("h"),)),))
            results.append((rhs, "Mathlib: Equiv_sumCongr_trans"))
        except Exception:
            pass
    return results


def _r0217_sumCongr_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.Perm.sumCongr_trans
    # (sumCongr e f).trans (sumCongr g h) = sumCongr (e.trans g) (f.trans h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumCongr_e_f_trans", 1)
    if args is not None:
        try:
            rhs = OOp("sumCongr", (OOp("e_trans", (OVar("g"),)), OOp("f_trans", (OVar("h"),)),))
            results.append((rhs, "Mathlib: Equiv_Perm_sumCongr_trans"))
        except Exception:
            pass
    return results


def _r0218_sumComm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.sumComm_symm
    # (sumComm α β).symm = sumComm β α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sumComm_a_b_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sumComm", (OVar("b"), OVar("a"),))
            results.append((rhs, "Mathlib: Equiv_sumComm_symm"))
    except Exception:
        pass
    return results


def _r0219_sumAssoc_apply_inl_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.sumAssoc_apply_inl_inr
    # sumAssoc α β γ (inl (inr b)) = inr (inl b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumAssoc", 4)
    if args is not None:
        try:
            rhs = OOp("inr", (OOp("inl", (args[1],)),))
            results.append((rhs, "Mathlib: Equiv_sumAssoc_apply_inl_inr"))
        except Exception:
            pass
    return results


def _r0220_sumAssoc_apply_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.sumAssoc_apply_inr
    # sumAssoc α β γ (inr c) = inr (inr c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumAssoc", 4)
    if args is not None:
        try:
            rhs = OOp("inr", (OOp("inr", (OVar("c"),)),))
            results.append((rhs, "Mathlib: Equiv_sumAssoc_apply_inr"))
        except Exception:
            pass
    return results


def _r0221_sumAssoc_symm_apply_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.sumAssoc_symm_apply_inl
    # (sumAssoc α β γ).symm (inl a) = inl (inl a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumAssoc_a_b_g_symm", 1)
    if args is not None:
        try:
            rhs = OOp("inl", (OOp("inl", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Equiv_sumAssoc_symm_apply_inl"))
        except Exception:
            pass
    return results


def _r0222_sumAssoc_symm_apply_inr_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.sumAssoc_symm_apply_inr_inl
    # (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumAssoc_a_b_g_symm", 1)
    if args is not None:
        try:
            rhs = OOp("inl", (OOp("inr", (OVar("b"),)),))
            results.append((rhs, "Mathlib: Equiv_sumAssoc_symm_apply_inr_inl"))
        except Exception:
            pass
    return results


def _r0223_emptySum_apply_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.emptySum_apply_inr
    # emptySum α β (Sum.inr b) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "emptySum", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Equiv_emptySum_apply_inr"))
        except Exception:
            pass
    return results


def _r0224_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Equiv.symm_apply_apply
    # f.symm (f a) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_symm", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: FirstOrder_Language_Equiv_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0225_map_fun(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Equiv.map_fun
    # φ (funMap f x) = funMap f (φ ∘ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 1)
    if args is not None:
        try:
            rhs = OOp("funMap", (OVar("f"), OOp("comp", (OVar("phi"), OVar("x"))),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Equiv_map_fun"))
        except Exception:
            pass
    return results


def _r0226_comp_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Equiv.comp_refl
    # g.comp (refl L M) = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 1)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: FirstOrder_Language_Equiv_comp_refl"))
        except Exception:
            pass
    return results


def _r0227_refl_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Equiv.refl_comp
    # (refl L N).comp g = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "refl_L_N_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: FirstOrder_Language_Equiv_refl_comp"))
        except Exception:
            pass
    return results


def _r0228_refl_toEmbedding(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Equiv.refl_toEmbedding
    # (refl L M).toEmbedding = Embedding.refl L M
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("refl_L_M_toEmbedding")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Embedding_refl", (OVar("L"), OVar("M"),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Equiv_refl_toEmbedding"))
    except Exception:
        pass
    return results


def _r0229_refl_toHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Equiv.refl_toHom
    # (refl L M).toHom = Hom.id L M
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("refl_L_M_toHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Hom_id", (OVar("L"), OVar("M"),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Equiv_refl_toHom"))
    except Exception:
        pass
    return results


def _r0230_symm_comp_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Equiv.symm_comp_self
    # f.symm.comp f = refl L M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_symm_comp", 1)
    if args is not None:
        try:
            rhs = OOp("refl", (OVar("L"), OVar("M"),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Equiv_symm_comp_self"))
        except Exception:
            pass
    return results


def _r0231_symm_comp_self_toEmbedding(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Language.Equiv.symm_comp_self_toEmbedding
    # f.symm.toEmbedding.comp f.toEmbedding = Embedding.refl L M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_symm_toEmbedding_comp", 1)
    if args is not None:
        try:
            rhs = OOp("Embedding_refl", (OVar("L"), OVar("M"),))
            results.append((rhs, "Mathlib: FirstOrder_Language_Equiv_symm_comp_self_toEmbedding"))
        except Exception:
            pass
    return results


def _r0232_infIrredUpperSet_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderEmbedding.infIrredUpperSet_apply
    # infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "infIrredUpperSet", 1)
    if args is not None:
        try:
            rhs = OVar("Ici_a_infIrred_Ici")
            results.append((rhs, "Mathlib: OrderEmbedding_infIrredUpperSet_apply"))
        except Exception:
            pass
    return results


def _r0233_infIrredUpperSet_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.infIrredUpperSet_apply
    # infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "infIrredUpperSet", 1)
    if args is not None:
        try:
            rhs = OVar("Ici_a_infIrred_Ici")
            results.append((rhs, "Mathlib: OrderIso_infIrredUpperSet_apply"))
        except Exception:
            pass
    return results


def _r0234_birkhoffSet_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderEmbedding.birkhoffSet_inf
    # birkhoffSet (a ⊓ b) = birkhoffSet a ∩ birkhoffSet b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "birkhoffSet", 1)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("birkhoffSet", (OVar("a"),)), OOp("birkhoffSet", (OVar("b"),))))
            results.append((rhs, "Mathlib: OrderEmbedding_birkhoffSet_inf"))
        except Exception:
            pass
    return results


def _r0235_birkhoffSet_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderEmbedding.birkhoffSet_apply
    # birkhoffSet a = OrderIso.lowerSetSupIrred a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "birkhoffSet", 1)
    if args is not None:
        try:
            rhs = OOp("OrderIso_lowerSetSupIrred", (args[0],))
            results.append((rhs, "Mathlib: OrderEmbedding_birkhoffSet_apply"))
        except Exception:
            pass
    return results


def _r0236_toDual_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.toDual_top
    # toDual (⊤ : α) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: OrderDual_toDual_top"))
        except Exception:
            pass
    return results


def _r0237_ofDual_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.ofDual_eq_top
    # ofDual a = ⊤ ↔ a = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OVar("bot")))
            results.append((rhs, "Mathlib: OrderDual_ofDual_eq_top"))
        except Exception:
            pass
    return results


def _r0238_toDual_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.toDual_eq_top
    # toDual a = ⊤ ↔ a = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OVar("bot")))
            results.append((rhs, "Mathlib: OrderDual_toDual_eq_top"))
        except Exception:
            pass
    return results


def _r0239_down_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.down_top
    # down (⊤ : ULift α) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "down", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: ULift_down_top"))
        except Exception:
            pass
    return results


def _r0240_isExtent_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.isExtent_iff
    # IsExtent r s ↔ lowerPolar r (upperPolar r s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Order_isExtent_iff"))
        except Exception:
            pass
    return results


def _r0241_isIntent_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.isIntent_iff
    # IsIntent r t ↔ upperPolar r (lowerPolar r t) = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("t")
            results.append((rhs, "Mathlib: Order_isIntent_iff"))
        except Exception:
            pass
    return results


def _r0242_comap_atBot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.comap_atBot
    # comap e atBot = atBot
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: OrderIso_comap_atBot"))
        except Exception:
            pass
    return results


def _r0243_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHom.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: OrderHom_ext"))
    except Exception:
        pass
    return results


def _r0244_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHom.copy_eq
    # f.copy f' h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_copy", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OrderHom_copy_eq"))
        except Exception:
            pass
    return results


def _r0245_curry_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHom.curry_symm_apply
    # curry.symm f x = f x.1 x.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "curry_symm", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x_1"), OVar("x_2"),))
            results.append((rhs, "Mathlib: OrderHom_curry_symm_apply"))
        except Exception:
            pass
    return results


def _r0246_comp_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHom.comp_id
    # comp f id = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: OrderHom_comp_id"))
        except Exception:
            pass
    return results


def _r0247_comp_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHom.comp_const
    # f.comp (const γ c) = const γ (f c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp", 1)
    if args is not None:
        try:
            rhs = OOp("const", (OVar("g"), OOp("f", (OVar("c"),)),))
            results.append((rhs, "Mathlib: OrderHom_comp_const"))
        except Exception:
            pass
    return results


def _r0248_snd_comp_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHom.snd_comp_prod
    # snd.comp (f.prod g) = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_comp", 1)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: OrderHom_snd_comp_prod"))
        except Exception:
            pass
    return results


def _r0249_dual_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHom.dual_comp
    # (g.comp f).dual = g.dual.comp f.dual
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_comp_f_dual")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g_dual_comp", (OVar("f_dual"),))
            results.append((rhs, "Mathlib: OrderHom_dual_comp"))
    except Exception:
        pass
    return results


def _r0250_symm_dual_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHom.symm_dual_comp
    # OrderHom.dual.symm (g.comp f) = (OrderHom.dual.symm g).comp (OrderHom.dual.symm f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OrderHom_dual_symm", 1)
    if args is not None:
        try:
            rhs = OOp("OrderHom_dual_symm_g_comp", (OOp("OrderHom_dual_symm", (OVar("f"),)),))
            results.append((rhs, "Mathlib: OrderHom_symm_dual_comp"))
        except Exception:
            pass
    return results


def _r0251_uliftLeftMap_uliftRightMap_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHom.uliftLeftMap_uliftRightMap_eq
    # f.uliftLeftMap.uliftRightMap = f.uliftMap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_uliftLeftMap_uliftRightMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_uliftMap")
            results.append((rhs, "Mathlib: OrderHom_uliftLeftMap_uliftRightMap_eq"))
    except Exception:
        pass
    return results


def _r0252_uliftRightMap_uliftLeftMap_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHom.uliftRightMap_uliftLeftMap_eq
    # f.uliftRightMap.uliftLeftMap = f.uliftMap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_uliftRightMap_uliftLeftMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_uliftMap")
            results.append((rhs, "Mathlib: OrderHom_uliftRightMap_uliftLeftMap_eq"))
    except Exception:
        pass
    return results


def _r0253_eq_iff_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderEmbedding.eq_iff_eq
    # f a = f b ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("f", (OVar("b"),)), args[0])), OVar("b")))
            results.append((rhs, "Mathlib: OrderEmbedding_eq_iff_eq"))
        except Exception:
            pass
    return results


def _r0254_refl_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.refl_apply
    # refl α x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "refl", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: OrderIso_refl_apply"))
        except Exception:
            pass
    return results


def _r0255_refl_toEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.refl_toEquiv
    # (refl α).toEquiv = Equiv.refl α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("refl_a_toEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Equiv_refl", (OVar("a"),))
            results.append((rhs, "Mathlib: OrderIso_refl_toEquiv"))
    except Exception:
        pass
    return results


def _r0256_apply_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.apply_symm_apply
    # e (e.symm x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: OrderIso_apply_symm_apply"))
        except Exception:
            pass
    return results


def _r0257_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.symm_apply_apply
    # e.symm (e x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: OrderIso_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0258_symm_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.symm_refl
    # (refl α).symm = refl α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("refl_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("refl", (OVar("a"),))
            results.append((rhs, "Mathlib: OrderIso_symm_refl"))
    except Exception:
        pass
    return results


def _r0259_apply_eq_iff_eq_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.apply_eq_iff_eq_symm_apply
    # e x = y ↔ x = e.symm y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("y"), args[0])), OOp("e_symm", (OVar("y"),))))
            results.append((rhs, "Mathlib: OrderIso_apply_eq_iff_eq_symm_apply"))
        except Exception:
            pass
    return results


def _r0260_coe_toEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.coe_toEquiv
    # ⇑e.toEquiv = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: OrderIso_coe_toEquiv"))
    except Exception:
        pass
    return results


def _r0261_coe_symm_toEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.coe_symm_toEquiv
    # ⇑e.toEquiv.symm = e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toEquiv_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm")
            results.append((rhs, "Mathlib: OrderIso_coe_symm_toEquiv"))
    except Exception:
        pass
    return results


def _r0262_trans_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.trans_apply
    # e.trans e' x = e' (e x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_trans", 2)
    if args is not None:
        try:
            rhs = OOp("e_prime", (OOp("e", (args[1],)),))
            results.append((rhs, "Mathlib: OrderIso_trans_apply"))
        except Exception:
            pass
    return results


def _r0263_refl_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.refl_trans
    # (refl α).trans e = e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "refl_a_trans", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: OrderIso_refl_trans"))
        except Exception:
            pass
    return results


def _r0264_symm_trans_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.symm_trans_self
    # e.symm.trans e = OrderIso.refl β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm_trans", 1)
    if args is not None:
        try:
            rhs = OOp("OrderIso_refl", (OVar("b"),))
            results.append((rhs, "Mathlib: OrderIso_symm_trans_self"))
        except Exception:
            pass
    return results


def _r0265_prodComm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.prodComm_symm
    # (prodComm : α × β ≃o β × α).symm = prodComm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("prodComm_colon_a_times_b_o_b_times_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("prodComm")
            results.append((rhs, "Mathlib: OrderIso_prodComm_symm"))
    except Exception:
        pass
    return results


def _r0266_coe_dualDual_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.coe_dualDual_symm
    # ⇑(dualDual α).symm = ofDual ∘ ofDual
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("dualDual_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("ofDual"), OVar("ofDual")))
            results.append((rhs, "Mathlib: OrderIso_coe_dualDual_symm"))
    except Exception:
        pass
    return results


def _r0267_dualDual_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.dualDual_symm_apply
    # (dualDual α).symm a = ofDual (ofDual a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dualDual_a_symm", 1)
    if args is not None:
        try:
            rhs = OOp("ofDual", (OOp("ofDual", (args[0],)),))
            results.append((rhs, "Mathlib: OrderIso_dualDual_symm_apply"))
        except Exception:
            pass
    return results


def _r0268_dual_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.dual_symm_apply
    # f.dual.symm x = .toDual (f.symm x.ofDual)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_dual_symm", 1)
    if args is not None:
        try:
            rhs = OOp("toDual", (OOp("f_symm", (OVar("x_ofDual"),)),))
            results.append((rhs, "Mathlib: OrderIso_dual_symm_apply"))
        except Exception:
            pass
    return results


def _r0269_symm_dual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.symm_dual
    # f.symm.dual = f.dual.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_symm_dual")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_dual_symm")
            results.append((rhs, "Mathlib: OrderIso_symm_dual"))
    except Exception:
        pass
    return results


def _r0270_to_lattice_hom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderHomClass.to_lattice_hom_apply
    # toLatticeHom α β f a = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toLatticeHom", 4)
    if args is not None:
        try:
            rhs = OOp("f", (args[3],))
            results.append((rhs, "Mathlib: OrderHomClass_to_lattice_hom_apply"))
        except Exception:
            pass
    return results


def _r0271_sumLexIioIci_apply_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumLexIioIci_apply_inr
    # sumLexIioIci x (toLex <| Sum.inr a) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumLexIioIci", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: OrderIso_sumLexIioIci_apply_inr"))
        except Exception:
            pass
    return results


def _r0272_sumLexIioIci_symm_apply_of_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumLexIioIci_symm_apply_of_lt
    # (sumLexIioIci x).symm y = toLex (Sum.inl ⟨y, h⟩)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumLexIioIci_x_symm", 1)
    if args is not None:
        try:
            rhs = OOp("toLex", (OOp("Sum_inl", (OVar("y_h"),)),))
            results.append((rhs, "Mathlib: OrderIso_sumLexIioIci_symm_apply_of_lt"))
        except Exception:
            pass
    return results


def _r0273_sumLexIioIci_symm_apply_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumLexIioIci_symm_apply_Ici
    # (sumLexIioIci x).symm a = toLex (Sum.inr a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumLexIioIci_x_symm", 1)
    if args is not None:
        try:
            rhs = OOp("toLex", (OOp("Sum_inr", (args[0],)),))
            results.append((rhs, "Mathlib: OrderIso_sumLexIioIci_symm_apply_Ici"))
        except Exception:
            pass
    return results


def _r0274_sumLexIicIoi_apply_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumLexIicIoi_apply_inr
    # sumLexIicIoi x (toLex <| Sum.inr a) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumLexIicIoi", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: OrderIso_sumLexIicIoi_apply_inr"))
        except Exception:
            pass
    return results


def _r0275_sumLexIicIoi_symm_apply_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumLexIicIoi_symm_apply_of_le
    # (sumLexIicIoi x).symm y = toLex (Sum.inl ⟨y, h⟩)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumLexIicIoi_x_symm", 1)
    if args is not None:
        try:
            rhs = OOp("toLex", (OOp("Sum_inl", (OVar("y_h"),)),))
            results.append((rhs, "Mathlib: OrderIso_sumLexIicIoi_symm_apply_of_le"))
        except Exception:
            pass
    return results


def _r0276_sumLexIicIoi_symm_apply_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.sumLexIicIoi_symm_apply_Ioi
    # (sumLexIicIoi x).symm a = Sum.inr a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumLexIicIoi_x_symm", 1)
    if args is not None:
        try:
            rhs = OOp("Sum_inr", (args[0],))
            results.append((rhs, "Mathlib: OrderIso_sumLexIicIoi_symm_apply_Ioi"))
        except Exception:
            pass
    return results


def _r0277_image_symm_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.image_symm_image
    # e '' (e.symm '' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: OrderIso_image_symm_image"))
        except Exception:
            pass
    return results


def _r0278_image_eq_preimage_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.image_eq_preimage_symm
    # e '' s = e.symm ⁻¹' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 2)
    if args is not None:
        try:
            rhs = OOp("e_symm", (OVar("inv_prime"), args[1],))
            results.append((rhs, "Mathlib: OrderIso_image_eq_preimage_symm"))
        except Exception:
            pass
    return results


def _r0279_symm_preimage_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.symm_preimage_preimage
    # e.symm ⁻¹' (e ⁻¹' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: OrderIso_symm_preimage_preimage"))
        except Exception:
            pass
    return results


def _r0280_image_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.image_preimage
    # e '' (e ⁻¹' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: OrderIso_image_preimage"))
        except Exception:
            pass
    return results


def _r0281_preimage_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.preimage_image
    # e ⁻¹' (e '' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: OrderIso_preimage_image"))
        except Exception:
            pass
    return results


def _r0282_withTopCongr_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.withTopCongr_symm
    # e.symm.withTopCongr = e.withTopCongr.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_withTopCongr")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_withTopCongr_symm")
            results.append((rhs, "Mathlib: OrderIso_withTopCongr_symm"))
    except Exception:
        pass
    return results


def _r0283_withTopCongr_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.withTopCongr_trans
    # (e₁.trans e₂).withTopCongr = e₁.withTopCongr.trans e₂.withTopCongr
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_1_trans_e_2_withTopCongr")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("e_1_withTopCongr_trans", (OVar("e_2_withTopCongr"),))
            results.append((rhs, "Mathlib: OrderIso_withTopCongr_trans"))
    except Exception:
        pass
    return results


def _r0284_withBotCongr_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.withBotCongr_symm
    # e.symm.withBotCongr = e.withBotCongr.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_withBotCongr")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_withBotCongr_symm")
            results.append((rhs, "Mathlib: OrderIso_withBotCongr_symm"))
    except Exception:
        pass
    return results


def _r0285_withBotCongr_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.withBotCongr_trans
    # (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_1_trans_e_2_withBotCongr")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("e_1_withBotCongr_trans", (OVar("e_2_withBotCongr"),))
            results.append((rhs, "Mathlib: OrderIso_withBotCongr_trans"))
    except Exception:
        pass
    return results


def _r0286_coe_toLowerSet(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.Ideal.coe_toLowerSet
    # (s.toLowerSet : Set P) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_toLowerSet", 3)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Order_Ideal_coe_toLowerSet"))
        except Exception:
            pass
    return results


def _r0287_coe_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.coe_top
    # ((⊤ : Ideal P) : Set P) = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Ideal_P", 3)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Order_coe_top"))
        except Exception:
            pass
    return results


def _r0288_preimage_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderEmbedding.preimage_Ioi
    # e ⁻¹' Ioi (e x) = Ioi x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("x"),))
            results.append((rhs, "Mathlib: OrderEmbedding_preimage_Ioi"))
        except Exception:
            pass
    return results


def _r0289_preimage_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderEmbedding.preimage_Icc
    # e ⁻¹' Icc (e x) (e y) = Icc x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: OrderEmbedding_preimage_Icc"))
        except Exception:
            pass
    return results


def _r0290_preimage_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderEmbedding.preimage_Ico
    # e ⁻¹' Ico (e x) (e y) = Ico x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: OrderEmbedding_preimage_Ico"))
        except Exception:
            pass
    return results


def _r0291_preimage_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderEmbedding.preimage_Ioc
    # e ⁻¹' Ioc (e x) (e y) = Ioc x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: OrderEmbedding_preimage_Ioc"))
        except Exception:
            pass
    return results


def _r0292_preimage_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderEmbedding.preimage_Ioo
    # e ⁻¹' Ioo (e x) (e y) = Ioo x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: OrderEmbedding_preimage_Ioo"))
        except Exception:
            pass
    return results


def _r0293_preimage_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.preimage_Ico
    # e ⁻¹' Ico a b = Ico (e.symm a) (e.symm b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("e_symm", (args[2],)), OOp("e_symm", (args[3],)),))
            results.append((rhs, "Mathlib: OrderIso_preimage_Ico"))
        except Exception:
            pass
    return results


def _r0294_preimage_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.preimage_Ioo
    # e ⁻¹' Ioo a b = Ioo (e.symm a) (e.symm b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("e_symm", (args[2],)), OOp("e_symm", (args[3],)),))
            results.append((rhs, "Mathlib: OrderIso_preimage_Ioo"))
        except Exception:
            pass
    return results


def _r0295_image_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.image_Iic
    # e '' Iic a = Iic (e a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OOp("e", (args[2],)),))
            results.append((rhs, "Mathlib: OrderIso_image_Iic"))
        except Exception:
            pass
    return results


def _r0296_image_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.image_Iio
    # e '' Iio a = Iio (e a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OOp("e", (args[2],)),))
            results.append((rhs, "Mathlib: OrderIso_image_Iio"))
        except Exception:
            pass
    return results


def _r0297_image_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.image_Ioo
    # e '' Ioo a b = Ioo (e a) (e b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("e", (args[2],)), OOp("e", (args[3],)),))
            results.append((rhs, "Mathlib: OrderIso_image_Ioo"))
        except Exception:
            pass
    return results


def _r0298_image_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.image_Ioc
    # e '' Ioc a b = Ioc (e a) (e b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("e", (args[2],)), OOp("e", (args[3],)),))
            results.append((rhs, "Mathlib: OrderIso_image_Ioc"))
        except Exception:
            pass
    return results


def _r0299_image_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.image_Icc
    # e '' Icc a b = Icc (e a) (e b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("e", (args[2],)), OOp("e", (args[3],)),))
            results.append((rhs, "Mathlib: OrderIso_image_Icc"))
        except Exception:
            pass
    return results


def _r0300_apply_blimsup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderIso.apply_blimsup
    # e (blimsup u f p) = blimsup (e ∘ u) f p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OOp("blimsup", (OOp("comp", (OVar("e"), OVar("u"))), OVar("f"), OVar("p"),))
            results.append((rhs, "Mathlib: OrderIso_apply_blimsup"))
        except Exception:
            pass
    return results


def _r0301_ofDual_symm_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.ofDual_symm_eq
    # (@ofDual α).symm = toDual
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("at_ofDual_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("toDual")
            results.append((rhs, "Mathlib: OrderDual_ofDual_symm_eq"))
    except Exception:
        pass
    return results


def _r0302_toDual_ofDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.toDual_ofDual
    # toDual (ofDual a) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: OrderDual_toDual_ofDual"))
        except Exception:
            pass
    return results


def _r0303_ofDual_toDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.ofDual_toDual
    # ofDual (toDual a) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: OrderDual_ofDual_toDual"))
        except Exception:
            pass
    return results


def _r0304_toDual_trans_ofDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.toDual_trans_ofDual
    # (toDual (α := α)).trans ofDual = Equiv.refl _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual_a_colon_eq_a_trans", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_refl", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: OrderDual_toDual_trans_ofDual"))
        except Exception:
            pass
    return results


def _r0305_ofDual_trans_toDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.ofDual_trans_toDual
    # (ofDual (α := α)).trans toDual = Equiv.refl _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual_a_colon_eq_a_trans", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_refl", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: OrderDual_ofDual_trans_toDual"))
        except Exception:
            pass
    return results


def _r0306_toDual_comp_ofDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.toDual_comp_ofDual
    # (toDual (α := α)) ∘ ofDual = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: OrderDual_toDual_comp_ofDual"))
        except Exception:
            pass
    return results


def _r0307_ofDual_comp_toDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.ofDual_comp_toDual
    # (ofDual (α := α)) ∘ toDual = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: OrderDual_ofDual_comp_toDual"))
        except Exception:
            pass
    return results


def _r0308_toDual_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.toDual_inj
    # toDual a = toDual b ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toDual", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("toDual", (OVar("b"),)), args[0])), OVar("b")))
            results.append((rhs, "Mathlib: OrderDual_toDual_inj"))
        except Exception:
            pass
    return results


def _r0309_ofDual_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderDual.ofDual_inj
    # ofDual a = ofDual b ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("ofDual", (OVar("b"),)), args[0])), OVar("b")))
            results.append((rhs, "Mathlib: OrderDual_ofDual_inj"))
        except Exception:
            pass
    return results


def _r0310_Icc_succ_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.Icc_succ_left
    # Icc (succ a) b = Ioc a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc", 2)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("a"), args[1],))
            results.append((rhs, "Mathlib: Order_Icc_succ_left"))
        except Exception:
            pass
    return results


def _r0311_Ico_succ_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.Ico_succ_left
    # Ico (succ a) b = Ioo a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("a"), args[1],))
            results.append((rhs, "Mathlib: Order_Ico_succ_left"))
        except Exception:
            pass
    return results


def _r0312_type_eq_type(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderType.type_eq_type
    # type α = type β ↔ Nonempty (α ≃o β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "type", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("type", (OVar("b"),)), OOp("Nonempty", (OOp("a", (OVar("o"), OVar("b"),)),))))
            results.append((rhs, "Mathlib: OrderType_type_eq_type"))
        except Exception:
            pass
    return results


def _r0313_type_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderType.type_eq_zero
    # type α = 0 ↔ IsEmpty α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "type", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OOp("IsEmpty", (args[0],))))
            results.append((rhs, "Mathlib: OrderType_type_eq_zero"))
        except Exception:
            pass
    return results


def _r0314_type_of_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderType.type_of_unique
    # type α = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "type", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: OrderType_type_of_unique"))
        except Exception:
            pass
    return results


def _r0315__unknown(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OrderType.lift_lift.
    # lift.{u} (lift.{v} o) = lift.{max v u} o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("lift_max_v_u", (OVar("o"),))
            results.append((rhs, "Mathlib: OrderType_lift_lift"))
        except Exception:
            pass
    return results


def _r0316_up_beq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.up_beq
    # (up a == up b) = (a == b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "up", 4)
    if args is not None:
        try:
            rhs = OOp("a", (args[1], args[3],))
            results.append((rhs, "Mathlib: ULift_up_beq"))
        except Exception:
            pass
    return results


def _r0317_down_beq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.down_beq
    # (down a == down b) = (a == b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "down", 4)
    if args is not None:
        try:
            rhs = OOp("a", (args[1], args[3],))
            results.append((rhs, "Mathlib: ULift_down_beq"))
        except Exception:
            pass
    return results


def _r0318_up_compare(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.up_compare
    # compare (up a) (up b) = compare a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "compare", 2)
    if args is not None:
        try:
            rhs = OOp("compare", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: ULift_up_compare"))
        except Exception:
            pass
    return results


def _r0319_down_compare(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.down_compare
    # compare (down a) (down b) = compare a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "compare", 2)
    if args is not None:
        try:
            rhs = OOp("compare", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: ULift_down_compare"))
        except Exception:
            pass
    return results


def _r0320_down_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.down_sup
    # down (a ⊔ b) = down a ⊔ down b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "down", 1)
    if args is not None:
        try:
            rhs = OOp("down", (OVar("a"), OVar("_unknown"), OVar("down"), OVar("b"),))
            results.append((rhs, "Mathlib: ULift_down_sup"))
        except Exception:
            pass
    return results


def _r0321_down_sdiff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.down_sdiff
    # down (a \\ b) = down a \\ down b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "down", 1)
    if args is not None:
        try:
            rhs = OOp("down", (OVar("a"), OVar("bsl"), OVar("down"), OVar("b"),))
            results.append((rhs, "Mathlib: ULift_down_sdiff"))
        except Exception:
            pass
    return results


def _r0322_up_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.up_compl
    # up (aᶜ) = (up a)ᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "up", 1)
    if args is not None:
        try:
            rhs = OVar("up_a")
            results.append((rhs, "Mathlib: ULift_up_compl"))
        except Exception:
            pass
    return results


def _r0323_down_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ULift.down_compl
    # down aᶜ = (down a)ᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "down", 1)
    if args is not None:
        try:
            rhs = OVar("down_a")
            results.append((rhs, "Mathlib: ULift_down_compl"))
        except Exception:
            pass
    return results


def _r0324_withBotCongr_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.withBotCongr_symm
    # withBotCongr e.symm = (withBotCongr e).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "withBotCongr", 1)
    if args is not None:
        try:
            rhs = OVar("withBotCongr_e_symm")
            results.append((rhs, "Mathlib: Equiv_withBotCongr_symm"))
        except Exception:
            pass
    return results


def _r0325_withBotCongr_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.withBotCongr_trans
    # withBotCongr (e₁.trans e₂) = (withBotCongr e₁).trans (withBotCongr e₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "withBotCongr", 1)
    if args is not None:
        try:
            rhs = OOp("withBotCongr_e_1_trans", (OOp("withBotCongr", (OVar("e_2"),)),))
            results.append((rhs, "Mathlib: Equiv_withBotCongr_trans"))
        except Exception:
            pass
    return results


def _r0326_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.ext
    # φ = ψ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("psi")
            results.append((rhs, "Mathlib: Equiv_ext"))
    except Exception:
        pass
    return results


def _r0327_toLinearMap_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.toLinearMap_refl
    # (refl ρ).toLinearMap = LinearMap.id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("refl_rho_toLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("LinearMap_id")
            results.append((rhs, "Mathlib: Equiv_toLinearMap_refl"))
    except Exception:
        pass
    return results


def _r0328_refl_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.refl_apply
    # refl ρ v = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "refl", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Equiv_refl_apply"))
        except Exception:
            pass
    return results


def _r0329_coe_toIntertwiningMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.coe_toIntertwiningMap
    # ⇑φ.toIntertwiningMap = φ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_toIntertwiningMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("phi")
            results.append((rhs, "Mathlib: Equiv_coe_toIntertwiningMap"))
    except Exception:
        pass
    return results


def _r0330_coe_toLinearMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.coe_toLinearMap
    # ⇑φ.toLinearMap = φ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_toLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("phi")
            results.append((rhs, "Mathlib: Equiv_coe_toLinearMap"))
    except Exception:
        pass
    return results


def _r0331_coe_invFun(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.coe_invFun
    # φ.invFun = φ.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_invFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("phi_symm")
            results.append((rhs, "Mathlib: Equiv_coe_invFun"))
    except Exception:
        pass
    return results


def _r0332_toLinearEquiv_toLinearMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.toLinearEquiv_toLinearMap
    # φ.toLinearEquiv.toLinearMap = φ.toIntertwiningMap.toLinearMap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_toLinearEquiv_toLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("phi_toIntertwiningMap_toLinearMap")
            results.append((rhs, "Mathlib: Equiv_toLinearEquiv_toLinearMap"))
    except Exception:
        pass
    return results


def _r0333_toLinearMap_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.toLinearMap_symm
    # (symm φ).toLinearMap = φ.toLinearEquiv.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("symm_phi_toLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("phi_toLinearEquiv_symm")
            results.append((rhs, "Mathlib: Equiv_toLinearMap_symm"))
    except Exception:
        pass
    return results


def _r0334_toLinearMap_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.toLinearMap_trans
    # (trans φ ψ).toLinearMap = ψ.toLinearMap ∘ₗ φ.toLinearMap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("trans_phi_psi_toLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("psi_toLinearMap", (OVar("comp"), OVar("phi_toLinearMap"),))
            results.append((rhs, "Mathlib: Equiv_toLinearMap_trans"))
    except Exception:
        pass
    return results


def _r0335_trans_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.trans_apply
    # trans φ ψ v = ψ (φ v)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trans", 3)
    if args is not None:
        try:
            rhs = OOp("psi", (OOp("phi", (args[2],)),))
            results.append((rhs, "Mathlib: Equiv_trans_apply"))
        except Exception:
            pass
    return results


def _r0336_apply_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.apply_symm_apply
    # φ (φ.symm v) = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 1)
    if args is not None:
        try:
            rhs = OVar("v")
            results.append((rhs, "Mathlib: Equiv_apply_symm_apply"))
        except Exception:
            pass
    return results


def _r0337_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.symm_apply_apply
    # φ.symm (φ v) = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi_symm", 1)
    if args is not None:
        try:
            rhs = OVar("v")
            results.append((rhs, "Mathlib: Equiv_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0338_trans_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.trans_symm
    # φ.trans φ.symm = .refl ρ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi_trans", 1)
    if args is not None:
        try:
            rhs = OOp("refl", (OVar("rho"),))
            results.append((rhs, "Mathlib: Equiv_trans_symm"))
        except Exception:
            pass
    return results


def _r0339_symm_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.symm_trans
    # φ.symm.trans φ = .refl σ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi_symm_trans", 1)
    if args is not None:
        try:
            rhs = OOp("refl", (OVar("sig"),))
            results.append((rhs, "Mathlib: Equiv_symm_trans"))
        except Exception:
            pass
    return results


def _r0340_omega_one_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.omega_one_eq_lift
    # ω₁ = lift.{v} o ↔ ω₁ = o
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("omega_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("lift_v", (OVar("o"),)), OVar("omega_1"))), OVar("o")))
            results.append((rhs, "Mathlib: Ordinal_omega_one_eq_lift"))
    except Exception:
        pass
    return results


def _r0341_lift_eq_omega_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_eq_omega_one
    # lift.{v} o = ω₁ ↔ o = ω₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("omega_1"), args[0])), OVar("omega_1")))
            results.append((rhs, "Mathlib: Ordinal_lift_eq_omega_one"))
        except Exception:
            pass
    return results


def _r0342_omega_natCast_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.omega_natCast_eq_lift
    # ω_ n = lift.{v} o ↔ ω_ n = o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "omega", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("lift_v", (OVar("o"),)), OOp("omega", (args[0],)))), OVar("o")))
            results.append((rhs, "Mathlib: Ordinal_omega_natCast_eq_lift"))
        except Exception:
            pass
    return results


def _r0343_lift_eq_omega_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_eq_omega_natCast
    # lift.{v} o = ω_ n ↔ o = ω_ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("omega", (OVar("n"),)), args[0])), OOp("omega", (OVar("n"),))))
            results.append((rhs, "Mathlib: Ordinal_lift_eq_omega_natCast"))
        except Exception:
            pass
    return results


def _r0344_omega_ofNat_eq_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.omega_ofNat_eq_lift
    # ω_ ofNat(n) = lift.{v} o ↔ ω_ ofNat(n) = o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "omega", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("lift_v", (OVar("o"),)), OOp("omega", (args[0],)))), OVar("o")))
            results.append((rhs, "Mathlib: Ordinal_omega_ofNat_eq_lift"))
        except Exception:
            pass
    return results


def _r0345_lift_eq_omega_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_eq_omega_ofNat
    # lift.{v} o = ω_ ofNat(n) ↔ o = ω_ ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_v", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("omega", (OVar("ofNat_n"),)), args[0])), OOp("omega", (OVar("ofNat_n"),))))
            results.append((rhs, "Mathlib: Ordinal_lift_eq_omega_ofNat"))
        except Exception:
            pass
    return results


def _r0346_cof_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Order.cof_eq_one_iff
    # cof α = 1 ↔ ∃ x : α, IsTop x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cof", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(1), OOp("exists", (OVar("x"), OVar("colon"), args[0], OVar("IsTop"), OVar("x"),))))
            results.append((rhs, "Mathlib: Order_cof_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0347_cof_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.cof_zero
    # cof 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cof", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Ordinal_cof_zero"))
        except Exception:
            pass
    return results


def _r0348_cof_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.cof_eq_one_iff
    # cof o = 1 ↔ o ∈ range succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cof", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(1), OOp("in", (args[0], OOp("range", (OVar("succ"),))))))
            results.append((rhs, "Mathlib: Ordinal_cof_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0349_limitRecOn_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.limitRecOn_succ
    # @limitRecOn motive (succ o) H₁ H₂ H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_limitRecOn", 5)
    if args is not None:
        try:
            rhs = OOp("H_2", (OVar("o"), OOp("at_limitRecOn", (args[0], OVar("o"), args[2], args[3], args[4],)),))
            results.append((rhs, "Mathlib: Ordinal_limitRecOn_succ"))
        except Exception:
            pass
    return results


def _r0350_zero_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.zero_sub
    # 0 - a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Ordinal_zero_sub"))
        except Exception:
            pass
    return results


def _r0351_sub_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.sub_self
    # a - a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Ordinal_sub_self"))
        except Exception:
            pass
    return results


def _r0352_sub_eq_zero_iff_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.sub_eq_zero_iff_le
    # a - b = 0 ↔ a ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OLit(0), args[0])), args[1]))
            results.append((rhs, "Mathlib: Ordinal_sub_eq_zero_iff_le"))
        except Exception:
            pass
    return results


def _r0353_mul_add_div_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.mul_add_div_mul
    # (a * b + c) / (a * d) = b / d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("b"), OVar("d")))
            results.append((rhs, "Mathlib: Ordinal_mul_add_div_mul"))
        except Exception:
            pass
    return results


def _r0354_div_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.div_self
    # a / a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Ordinal_div_self"))
        except Exception:
            pass
    return results


def _r0355_mul_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.mul_sub
    # a * (b - c) = a * b - a * c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (args[0], OOp("*", (OOp("-", (OVar("b"), args[0])), OVar("c")))))
            results.append((rhs, "Mathlib: Ordinal_mul_sub"))
        except Exception:
            pass
    return results


def _r0356_mod_eq_of_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.mod_eq_of_lt
    # a % b = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Ordinal_mod_eq_of_lt"))
        except Exception:
            pass
    return results


def _r0357_div_add_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.div_add_mod
    # b * (a / b) + a % b = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Ordinal_div_add_mod"))
        except Exception:
            pass
    return results


def _r0358_mul_add_mod_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.mul_add_mod_mul
    # (x * y + w) % (x * z) = x * (y % z) + w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_star_y_plus_w", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (OVar("x"), OOp("y", (args[0], OVar("z"),)))), OVar("w")))
            results.append((rhs, "Mathlib: Ordinal_mul_add_mod_mul"))
        except Exception:
            pass
    return results


def _r0359_lt_mul_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lt_mul_iff
    # a < b * c ↔ ∃ q < c, ∃ r < b, a = b * q + r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (OVar("b"), OVar("q"))), OVar("r")))
            results.append((rhs, "Mathlib: Ordinal_lt_mul_iff"))
        except Exception:
            pass
    return results


def _r0360_eq_natCast_of_le_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.eq_natCast_of_le_natCast
    # ∃ c : ℕ, a = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 4)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Ordinal_eq_natCast_of_le_natCast"))
        except Exception:
            pass
    return results


def _r0361_one_add_of_omega0_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.one_add_of_omega0_le
    # 1 + o = o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Ordinal_one_add_of_omega0_le"))
        except Exception:
            pass
    return results


def _r0362_type_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.type_eq
    # type r = type s ↔ Nonempty (r ≃r s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "type", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("type", (OVar("s"),)), OOp("Nonempty", (OOp("r", (args[0], OVar("s"),)),))))
            results.append((rhs, "Mathlib: Ordinal_type_eq"))
        except Exception:
            pass
    return results


def _r0363_le_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.le_zero
    # o ≤ 0 ↔ o = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Ordinal_le_zero"))
        except Exception:
            pass
    return results


def _r0364_typein_enum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.typein_enum
    # typein r (enum r ⟨o, h⟩) = o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "typein", 2)
    if args is not None:
        try:
            rhs = OVar("o")
            results.append((rhs, "Mathlib: Ordinal_typein_enum"))
        except Exception:
            pass
    return results


def _r0365_card_typein(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.card_typein
    # (typein r x).card = #{ y // r y x }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("typein_r_x_card")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_y_slash_slash_r_y_x")
            results.append((rhs, "Mathlib: Ordinal_card_typein"))
    except Exception:
        pass
    return results


def _r0366_card_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.card_one
    # card 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Ordinal_card_one"))
        except Exception:
            pass
    return results


def _r0367_lift_typein_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_typein_top
    # lift.{u} (typein s f.top) = lift (type r)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_u", 1)
    if args is not None:
        try:
            rhs = OOp("lift", (OOp("type", (OVar("r"),)),))
            results.append((rhs, "Mathlib: Ordinal_lift_typein_top"))
        except Exception:
            pass
    return results


def _r0368_lift_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_lift
    # lift.{w} (lift.{v} a) = lift.{max v w} a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_w", 1)
    if args is not None:
        try:
            rhs = OOp("lift_max_v_w", (OVar("a"),))
            results.append((rhs, "Mathlib: Ordinal_lift_lift"))
        except Exception:
            pass
    return results


def _r0369_lift_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_zero
    # lift 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Ordinal_lift_zero"))
        except Exception:
            pass
    return results


def _r0370_lift_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_one
    # lift 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Ordinal_lift_one"))
        except Exception:
            pass
    return results


def _r0371_lift_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_card
    # Cardinal.lift.{u, v} (card a) = card (lift.{u} a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Cardinal_lift_u_v", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OOp("lift_u", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Ordinal_lift_card"))
        except Exception:
            pass
    return results


def _r0372_card_omega0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.card_omega0
    # card ω = ℵ₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: Ordinal_card_omega0"))
        except Exception:
            pass
    return results


def _r0373_lift_omega0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.lift_omega0
    # lift ω = ω
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Ordinal_lift_omega0"))
        except Exception:
            pass
    return results


def _r0374_card_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.card_add_one
    # card (o + 1) = card o + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("len", (OVar("o"),)), OLit(1)))
            results.append((rhs, "Mathlib: Ordinal_card_add_one"))
        except Exception:
            pass
    return results


def _r0375_card_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.card_ofNat
    # card.{u} ofNat(n) = OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "card_u", 1)
    if args is not None:
        try:
            rhs = OOp("OfNat_ofNat", (OVar("n"),))
            results.append((rhs, "Mathlib: Ordinal_card_ofNat"))
        except Exception:
            pass
    return results


def _r0376_sInf_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.sInf_empty
    # sInf (∅ : Set Ordinal) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sInf", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Ordinal_sInf_empty"))
        except Exception:
            pass
    return results


def _r0377_card_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.card_eq_zero
    # card o = 0 ↔ o = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Ordinal_card_eq_zero"))
        except Exception:
            pass
    return results


def _r0378_card_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.card_eq_one
    # card o = 1 ↔ o = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: Ordinal_card_eq_one"))
        except Exception:
            pass
    return results


def _r0379_type_fin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.type_fin
    # typeLT (Fin n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "typeLT", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Ordinal_type_fin"))
        except Exception:
            pass
    return results


def _r0380_coeff_one_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.CNF.coeff_one_left
    # coeff 1 o = single 0 o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coeff", 2)
    if args is not None:
        try:
            rhs = OOp("single", (OLit(0), args[1],))
            results.append((rhs, "Mathlib: Ordinal_CNF_coeff_one_left"))
        except Exception:
            pass
    return results


def _r0381_coeff_opow_mul_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.CNF.coeff_opow_mul_add
    # coeff b (b ^ e * x + y) = single e x + coeff b y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coeff", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("single", (OVar("e"), OVar("x"),)), OOp("coeff", (args[0], OVar("y"),))))
            results.append((rhs, "Mathlib: Ordinal_CNF_coeff_opow_mul_add"))
        except Exception:
            pass
    return results


def _r0382_eval_single_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.CNF.eval_single_add
    # eval b (.single e x + f) = b ^ e * x + eval b f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eval", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (OOp("**", (args[0], OVar("e"))), OVar("x"))), OOp("eval", (args[0], OVar("f"),))))
            results.append((rhs, "Mathlib: Ordinal_CNF_eval_single_add"))
        except Exception:
            pass
    return results


def _r0383_opow_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.opow_zero
    # a ^ (0 : Ordinal) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Ordinal_opow_zero"))
        except Exception:
            pass
    return results


def _r0384_one_opow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.one_opow
    # (1 : Ordinal) ^ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Ordinal_one_opow"))
        except Exception:
            pass
    return results


def _r0385_opow_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.opow_natCast
    # a ^ (n : Ordinal) = a ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("n")))
            results.append((rhs, "Mathlib: Ordinal_opow_natCast"))
        except Exception:
            pass
    return results


def _r0386_opow_right_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.opow_right_inj
    # a ^ b = a ^ c ↔ b = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("**", (args[0], OVar("c"))), args[1])), OVar("c")))
            results.append((rhs, "Mathlib: Ordinal_opow_right_inj"))
        except Exception:
            pass
    return results


def _r0387_apply_omega0_of_isNormal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.apply_omega0_of_isNormal
    # ⨆ n : ℕ, f n = f ω
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 5)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("omega"),))
            results.append((rhs, "Mathlib: Ordinal_apply_omega0_of_isNormal"))
        except Exception:
            pass
    return results


def _r0388_iSup_add_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.iSup_add_natCast
    # ⨆ n : ℕ, o + n = o + ω
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("o"), OVar("omega")))
            results.append((rhs, "Mathlib: Ordinal_iSup_add_natCast"))
        except Exception:
            pass
    return results


def _r0389_univ_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.univ_id
    # univ.{u, u + 1} = typeLT Ordinal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("univ_u_u_plus_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("typeLT", (OVar("Ordinal"),))
            results.append((rhs, "Mathlib: Ordinal_univ_id"))
    except Exception:
        pass
    return results


def _r0390_univ_umax(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.univ_umax
    # univ.{u, max (u + 1) v} = univ.{u, v}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("univ_u_max_u_plus_1_v")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("univ_u_v")
            results.append((rhs, "Mathlib: Ordinal_univ_umax"))
    except Exception:
        pass
    return results


def _r0391_veblenWith_of_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.veblenWith_of_ne_zero
    # veblenWith f o = derivFamily fun x : Iio o ↦ veblenWith f x.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "veblenWith", 2)
    if args is not None:
        try:
            rhs = OOp("derivFamily", (OVar("fun"), OVar("x"), OVar("colon"), OVar("Iio"), args[1], OVar("_unknown"), OVar("veblenWith"), args[0], OVar("x_1"),))
            results.append((rhs, "Mathlib: Ordinal_veblenWith_of_ne_zero"))
        except Exception:
            pass
    return results


def _r0392_veblenWith_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.veblenWith_succ
    # veblenWith f (succ o) = deriv (veblenWith f o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "veblenWith", 2)
    if args is not None:
        try:
            rhs = OOp("deriv", (OOp("veblenWith", (args[0], OVar("o"),)),))
            results.append((rhs, "Mathlib: Ordinal_veblenWith_succ"))
        except Exception:
            pass
    return results


def _r0393_mem_toZFSet_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.mem_toZFSet_iff
    # x ∈ o.toZFSet ↔ ∃ a < o, a.toZFSet = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Ordinal_mem_toZFSet_iff"))
        except Exception:
            pass
    return results


def _r0394_coe_toZFSet(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.coe_toZFSet
    # o.toZFSet = toZFSet '' Iio o
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("o_toZFSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("toZFSet", (OVar("prime_prime"), OVar("Iio"), OVar("o"),))
            results.append((rhs, "Mathlib: Ordinal_coe_toZFSet"))
    except Exception:
        pass
    return results


def _r0395_toZFSet_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.toZFSet_add_one
    # toZFSet (o + 1) = insert (toZFSet o) (toZFSet o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toZFSet", 1)
    if args is not None:
        try:
            rhs = OOp("insert", (OOp("toZFSet", (OVar("o"),)), OOp("toZFSet", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Ordinal_toZFSet_add_one"))
        except Exception:
            pass
    return results


def _r0396_toZFSet_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ordinal.toZFSet_succ
    # toZFSet (Order.succ o) = insert (toZFSet o) (toZFSet o)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toZFSet", 1)
    if args is not None:
        try:
            rhs = OOp("insert", (OOp("toZFSet", (OVar("o"),)), OOp("toZFSet", (OVar("o"),)),))
            results.append((rhs, "Mathlib: Ordinal_toZFSet_succ"))
        except Exception:
            pass
    return results


def _r0397_toHomeomorph_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.toHomeomorph_apply
    # e.toHomeomorph he x = e x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_toHomeomorph", 2)
    if args is not None:
        try:
            rhs = OOp("e", (args[1],))
            results.append((rhs, "Mathlib: Equiv_toHomeomorph_apply"))
        except Exception:
            pass
    return results


def _r0398_toHomeomorph_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.toHomeomorph_refl
    # (Equiv.refl X).toHomeomorph (fun _s ↦ Iff.rfl) = Homeomorph.refl _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_refl_X_toHomeomorph", 1)
    if args is not None:
        try:
            rhs = OOp("Homeomorph_refl", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: Equiv_toHomeomorph_refl"))
        except Exception:
            pass
    return results


def _r0399_symm_toHomeomorph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.symm_toHomeomorph
    # (e.toHomeomorph he).symm = e.symm.toHomeomorph fun s ↦
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toHomeomorph_he_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("e_symm_toHomeomorph", (OVar("fun"), OVar("s"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: Equiv_symm_toHomeomorph"))
    except Exception:
        pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_logic_basic rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "**", "+", "-", "//", "<", "<=", "Cardinal_lift_u_v", "Compares", "DFunLike_coe", "Disjoint", "EquivLike_inv", "Equiv_Perm_decomposeFin_symm", "Equiv_cast", "Equiv_embeddingFinSucc_n_i_e_2", "Equiv_refl", "Equiv_refl_X_toHomeomorph", "Equiv_refl_a_equivCongr", "Equiv_refl_a_trans", "Equiv_sumCongr", "Equiv_sumCongr_e_f_trans", "Fin", "Icc", "Ico", "IsExtent", "IsIntent", "J", "OrderHom_dual_symm", "OrderMonoidHom_id_b_comp", "OrderMonoidIso_mk", "OrderMonoidIso_refl_a_trans", "OrderMonoidWithZeroHom_id_b_comp", "OrderRingHom_id_b_comp", "OrderRingIso_refl", "Order_succ", "Orientation_map", "OrthonormalBasis_singleton_i_repr", "P_root", "Perm_subtypeCongr", "Q", "Sum_inr", "_0", "_1", "_1_colon_Perm_a_trans", "_1_colon_R_Sinv", "_unknown", "a", "ab_equivCongr", "ab_equivCongr_de_trans", "ab_trans_bc_trans",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_logic_basic axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_logic_basic rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_right_vsub_pointReflection(term, ctx))
    results.extend(_r0001_coe_vaddConst_symm(term, ctx))
    results.extend(_r0002_coe_constVSub_symm(term, ctx))
    results.extend(_r0003_pointReflection_vsub_right(term, ctx))
    results.extend(_r0004_pointReflection_symm(term, ctx))
    results.extend(_r0005_pointReflection_self(term, ctx))
    results.extend(_r0006_down_nnratCast(term, ctx))
    results.extend(_r0007_up_ratCast(term, ctx))
    results.extend(_r0008_down_ratCast(term, ctx))
    results.extend(_r0009_source_restr(term, ctx))
    results.extend(_r0010_mul_apply(term, ctx))
    results.extend(_r0011_coe_one(term, ctx))
    results.extend(_r0012_coe_mul(term, ctx))
    results.extend(_r0013_coe_pow(term, ctx))
    results.extend(_r0014_iterate_eq_pow(term, ctx))
    results.extend(_r0015_eq_inv_iff_eq(term, ctx))
    results.extend(_r0016_mul_refl(term, ctx))
    results.extend(_r0017_one_symm(term, ctx))
    results.extend(_r0018_refl_inv(term, ctx))
    results.extend(_r0019_one_trans(term, ctx))
    results.extend(_r0020_refl_mul(term, ctx))
    results.extend(_r0021_inv_trans_self(term, ctx))
    results.extend(_r0022_mul_symm(term, ctx))
    results.extend(_r0023_self_trans_inv(term, ctx))
    results.extend(_r0024_symm_mul(term, ctx))
    results.extend(_r0025_permCongr_mul(term, ctx))
    results.extend(_r0026_extendDomain_inv(term, ctx))
    results.extend(_r0027_extendDomain_mul(term, ctx))
    results.extend(_r0028_extendDomain_pow(term, ctx))
    results.extend(_r0029_extendDomain_zpow(term, ctx))
    results.extend(_r0030_mulRight_symm(term, ctx))
    results.extend(_r0031_copy_eq(term, ctx))
    results.extend(_r0032_comp_apply(term, ctx))
    results.extend(_r0033_id_comp(term, ctx))
    results.extend(_r0034_cancel_right(term, ctx))
    results.extend(_r0035_mk_coe(term, ctx))
    results.extend(_r0036_trans_apply(term, ctx))
    results.extend(_r0037_coe_trans_mulEquiv(term, ctx))
    results.extend(_r0038_refl_trans(term, ctx))
    results.extend(_r0039_cancel_right(term, ctx))
    results.extend(_r0040_toOrderIso_eq_coe(term, ctx))
    results.extend(_r0041_equivLike_inv_eq_symm(term, ctx))
    results.extend(_r0042_toEquiv_symm(term, ctx))
    results.extend(_r0043_symm_symm(term, ctx))
    results.extend(_r0044_apply_symm_apply(term, ctx))
    results.extend(_r0045_symm_apply_apply(term, ctx))
    results.extend(_r0046_self_comp_symm(term, ctx))
    results.extend(_r0047_apply_eq_iff_symm_apply(term, ctx))
    results.extend(_r0048_copy_eq(term, ctx))
    results.extend(_r0049_comp_apply(term, ctx))
    results.extend(_r0050_id_comp(term, ctx))
    results.extend(_r0051_cancel_right(term, ctx))
    results.extend(_r0052_toOrderAddMonoidHom_eq_coe(term, ctx))
    results.extend(_r0053_toOrderMonoidWithZeroHom_eq_coe(term, ctx))
    results.extend(_r0054_copy_eq(term, ctx))
    results.extend(_r0055_comp_apply(term, ctx))
    results.extend(_r0056_comp_assoc(term, ctx))
    results.extend(_r0057_id_comp(term, ctx))
    results.extend(_r0058_cancel_right(term, ctx))
    results.extend(_r0059_mk_coe(term, ctx))
    results.extend(_r0060_toRingEquiv_eq_coe(term, ctx))
    results.extend(_r0061_coe_toRingEquiv(term, ctx))
    results.extend(_r0062_coe_toOrderIso(term, ctx))
    results.extend(_r0063_coe_ringEquiv_refl(term, ctx))
    results.extend(_r0064_coe_orderIso_refl(term, ctx))
    results.extend(_r0065_apply_symm_apply(term, ctx))
    results.extend(_r0066_self_trans_symm(term, ctx))
    results.extend(_r0067_symm_trans_self(term, ctx))
    results.extend(_r0068_fst_comp_inl(term, ctx))
    results.extend(_r0069_snd_comp_inl(term, ctx))
    results.extend(_r0070_fst_comp_inr(term, ctx))
    results.extend(_r0071_snd_comp_inr(term, ctx))
    results.extend(_r0072_inl_mul_inr_eq_mk(term, ctx))
    results.extend(_r0073_succ_toMul(term, ctx))
    results.extend(_r0074_succ_ofAdd(term, ctx))
    results.extend(_r0075_succ_toAdd(term, ctx))
    results.extend(_r0076_pred_ofMul(term, ctx))
    results.extend(_r0077_pred_toMul(term, ctx))
    results.extend(_r0078_pred_ofAdd(term, ctx))
    results.extend(_r0079_pred_toAdd(term, ctx))
    results.extend(_r0080_up_ofNat(term, ctx))
    results.extend(_r0081_down_natCast(term, ctx))
    results.extend(_r0082_down_ofNat(term, ctx))
    results.extend(_r0083_extend_some(term, ctx))
    results.extend(_r0084_nnnorm_eq_one(term, ctx))
    results.extend(_r0085_enorm_eq_one(term, ctx))
    results.extend(_r0086_inner_eq_zero(term, ctx))
    results.extend(_r0087_inner_eq_one(term, ctx))
    results.extend(_r0088_coe_toBasis_repr(term, ctx))
    results.extend(_r0089_singleton_repr(term, ctx))
    results.extend(_r0090_coe_singleton(term, ctx))
    results.extend(_r0091_toBasis_singleton(term, ctx))
    results.extend(_r0092_areaForm_rightAngleRotation_right(term, ctx))
    results.extend(_r0093_areaForm_comp_rightAngleRotation(term, ctx))
    results.extend(_r0094_rightAngleRotation_neg_orientation(term, ctx))
    results.extend(_r0095_kahler_rightAngleRotation_left(term, ctx))
    results.extend(_r0096_kahler_mul(term, ctx))
    results.extend(_r0097_norm_down(term, ctx))
    results.extend(_r0098_commMonToLaxBraidedObj_mu(term, ctx))
    results.extend(_r0099_map_eta_comp_eta(term, ctx))
    results.extend(_r0100_monToLaxMonoidalObj_mu(term, ctx))
    results.extend(_r0101_toIso_inv(term, ctx))
    results.extend(_r0102_mapEquiv_symm_apply(term, ctx))
    results.extend(_r0103_mapEquiv_symm(term, ctx))
    results.extend(_r0104_finsetCongr_refl(term, ctx))
    results.extend(_r0105_finsetCongr_trans(term, ctx))
    results.extend(_r0106_inv_apply_eq(term, ctx))
    results.extend(_r0107_apply_inv_apply(term, ctx))
    results.extend(_r0108_mapMatrix_symm(term, ctx))
    results.extend(_r0109_mapMatrix_trans(term, ctx))
    results.extend(_r0110_compares_eq(term, ctx))
    results.extend(_r0111_compares_gt(term, ctx))
    results.extend(_r0112_toList_node(term, ctx))
    results.extend(_r0113_merge_nil_right(term, ctx))
    results.extend(_r0114_merge_node(term, ctx))
    results.extend(_r0115_size_node(term, ctx))
    results.extend(_r0116_toPEquiv_trans(term, ctx))
    results.extend(_r0117_sumComm_symm(term, ctx))
    results.extend(_r0118_sumAssoc_apply_inl_inr(term, ctx))
    results.extend(_r0119_sumAssoc_apply_inr(term, ctx))
    results.extend(_r0120_sumAssoc_symm_apply_inl(term, ctx))
    results.extend(_r0121_sumAssoc_symm_apply_inr_inl(term, ctx))
    results.extend(_r0122_sumAssoc_symm_apply_inr_inr(term, ctx))
    results.extend(_r0123_sumDualDistrib_inr(term, ctx))
    results.extend(_r0124_sumDualDistrib_symm_inl(term, ctx))
    results.extend(_r0125_sumDualDistrib_symm_inr(term, ctx))
    results.extend(_r0126_sumLexAssoc_symm_apply_inr_inl(term, ctx))
    results.extend(_r0127_sumLexAssoc_symm_apply_inr_inr(term, ctx))
    results.extend(_r0128_emptySumLex_apply_inr(term, ctx))
    results.extend(_r0129_ext(term, ctx))
    results.extend(_r0130_oangle_zero_right(term, ctx))
    results.extend(_r0131_oangle_neg_left_eq_neg_right(term, ctx))
    results.extend(_r0132_rotation_pi(term, ctx))
    results.extend(_r0133_one_smul(term, ctx))
    results.extend(_r0134_one_div_mul(term, ctx))
    results.extend(_r0135_smul_cancel(term, ctx))
    results.extend(_r0136_mul_cancel(term, ctx))
    results.extend(_r0137_mul_div_one(term, ctx))
    results.extend(_r0138_oreSetComm_oreDenom(term, ctx))
    results.extend(_r0139_toList_eq_nil_iff(term, ctx))
    results.extend(_r0140_length_toList(term, ctx))
    results.extend(_r0141_cycleOf_eq(term, ctx))
    results.extend(_r0142_cycleType_one(term, ctx))
    results.extend(_r0143_card_cycleType_eq_zero(term, ctx))
    results.extend(_r0144_decomposeFin_symm_apply_succ(term, ctx))
    results.extend(_r0145_optionCongr_swap(term, ctx))
    results.extend(_r0146_sign_trans(term, ctx))
    results.extend(_r0147_sign_one(term, ctx))
    results.extend(_r0148_sign_refl(term, ctx))
    results.extend(_r0149_sign_inv(term, ctx))
    results.extend(_r0150_sign_symm(term, ctx))
    results.extend(_r0151_sign_swap(term, ctx))
    results.extend(_r0152_sign_eq(term, ctx))
    results.extend(_r0153_sign_sumCongr(term, ctx))
    results.extend(_r0154_disjoint_iff_eq_or_eq(term, ctx))
    results.extend(_r0155_reverse_v(term, ctx))
    results.extend(_r0156_involute_v(term, ctx))
    results.extend(_r0157_reverse_e0(term, ctx))
    results.extend(_r0158_involute_e0(term, ctx))
    results.extend(_r0159_map_symm(term, ctx))
    results.extend(_r0160_reindex_symm(term, ctx))
    results.extend(_r0161_map_of_isEmpty(term, ctx))
    results.extend(_r0162_sigPos_eq(term, ctx))
    results.extend(_r0163_root_indexEquiv_eq_smul(term, ctx))
    results.extend(_r0164_toEmbedding_apply(term, ctx))
    results.extend(_r0165_trans_toEmbedding(term, ctx))
    results.extend(_r0166_left_apply_subtype(term, ctx))
    results.extend(_r0167_right_apply(term, ctx))
    results.extend(_r0168_right_apply_subtype(term, ctx))
    results.extend(_r0169_refl(term, ctx))
    results.extend(_r0170_trans(term, ctx))
    results.extend(_r0171_coe_fn_injective(term, ctx))
    results.extend(_r0172_invFun_as_coe(term, ctx))
    results.extend(_r0173_trans_apply(term, ctx))
    results.extend(_r0174_apply_symm_apply(term, ctx))
    results.extend(_r0175_symm_apply_apply(term, ctx))
    results.extend(_r0176_symm_comp_self(term, ctx))
    results.extend(_r0177_self_comp_symm(term, ctx))
    results.extend(_r0178_apply_coe_symm_apply(term, ctx))
    results.extend(_r0179_coe_symm_apply_apply(term, ctx))
    results.extend(_r0180_coe_symm_comp_self(term, ctx))
    results.extend(_r0181_self_comp_coe_symm(term, ctx))
    results.extend(_r0182_symm_trans_apply(term, ctx))
    results.extend(_r0183_symm_symm_apply(term, ctx))
    results.extend(_r0184_cast_symm(term, ctx))
    results.extend(_r0185_cast_refl(term, ctx))
    results.extend(_r0186_cast_trans(term, ctx))
    results.extend(_r0187_refl_symm(term, ctx))
    results.extend(_r0188_refl_trans(term, ctx))
    results.extend(_r0189_symm_trans_self(term, ctx))
    results.extend(_r0190_self_trans_symm(term, ctx))
    results.extend(_r0191_trans_assoc(term, ctx))
    results.extend(_r0192_equivCongr_symm(term, ctx))
    results.extend(_r0193_equivCongr_refl(term, ctx))
    results.extend(_r0194_equivCongr_trans(term, ctx))
    results.extend(_r0195_equivCongr_refl_left(term, ctx))
    results.extend(_r0196_equivCongr_refl_right(term, ctx))
    results.extend(_r0197_permCongr_symm(term, ctx))
    results.extend(_r0198_permCongr_apply(term, ctx))
    results.extend(_r0199_permCongr_symm_apply(term, ctx))
    results.extend(_r0200_embeddingFinSucc_snd(term, ctx))
    results.extend(_r0201_natSumNatEquivNat_apply(term, ctx))
    results.extend(_r0202_optionCongr_symm(term, ctx))
    results.extend(_r0203_optionCongr_trans(term, ctx))
    results.extend(_r0204_symm_toPartialEquiv(term, ctx))
    results.extend(_r0205_trans_toPartialEquiv(term, ctx))
    results.extend(_r0206_prodComm_apply(term, ctx))
    results.extend(_r0207_prodComm_symm(term, ctx))
    results.extend(_r0208_prodUnique_apply(term, ctx))
    results.extend(_r0209_uniqueProd_apply(term, ctx))
    results.extend(_r0210_eq_image_iff_symm_image_eq(term, ctx))
    results.extend(_r0211_image_preimage(term, ctx))
    results.extend(_r0212_preimage_image(term, ctx))
    results.extend(_r0213_image_compl(term, ctx))
    results.extend(_r0214_preimage_symm_preimage(term, ctx))
    results.extend(_r0215_preimage_eq_iff_eq_image(term, ctx))
    results.extend(_r0216_sumCongr_trans(term, ctx))
    results.extend(_r0217_sumCongr_trans(term, ctx))
    results.extend(_r0218_sumComm_symm(term, ctx))
    results.extend(_r0219_sumAssoc_apply_inl_inr(term, ctx))
    results.extend(_r0220_sumAssoc_apply_inr(term, ctx))
    results.extend(_r0221_sumAssoc_symm_apply_inl(term, ctx))
    results.extend(_r0222_sumAssoc_symm_apply_inr_inl(term, ctx))
    results.extend(_r0223_emptySum_apply_inr(term, ctx))
    results.extend(_r0224_symm_apply_apply(term, ctx))
    results.extend(_r0225_map_fun(term, ctx))
    results.extend(_r0226_comp_refl(term, ctx))
    results.extend(_r0227_refl_comp(term, ctx))
    results.extend(_r0228_refl_toEmbedding(term, ctx))
    results.extend(_r0229_refl_toHom(term, ctx))
    results.extend(_r0230_symm_comp_self(term, ctx))
    results.extend(_r0231_symm_comp_self_toEmbedding(term, ctx))
    results.extend(_r0232_infIrredUpperSet_apply(term, ctx))
    results.extend(_r0233_infIrredUpperSet_apply(term, ctx))
    results.extend(_r0234_birkhoffSet_inf(term, ctx))
    results.extend(_r0235_birkhoffSet_apply(term, ctx))
    results.extend(_r0236_toDual_top(term, ctx))
    results.extend(_r0237_ofDual_eq_top(term, ctx))
    results.extend(_r0238_toDual_eq_top(term, ctx))
    results.extend(_r0239_down_top(term, ctx))
    results.extend(_r0240_isExtent_iff(term, ctx))
    results.extend(_r0241_isIntent_iff(term, ctx))
    results.extend(_r0242_comap_atBot(term, ctx))
    results.extend(_r0243_ext(term, ctx))
    results.extend(_r0244_copy_eq(term, ctx))
    results.extend(_r0245_curry_symm_apply(term, ctx))
    results.extend(_r0246_comp_id(term, ctx))
    results.extend(_r0247_comp_const(term, ctx))
    results.extend(_r0248_snd_comp_prod(term, ctx))
    results.extend(_r0249_dual_comp(term, ctx))
    results.extend(_r0250_symm_dual_comp(term, ctx))
    results.extend(_r0251_uliftLeftMap_uliftRightMap_eq(term, ctx))
    results.extend(_r0252_uliftRightMap_uliftLeftMap_eq(term, ctx))
    results.extend(_r0253_eq_iff_eq(term, ctx))
    results.extend(_r0254_refl_apply(term, ctx))
    results.extend(_r0255_refl_toEquiv(term, ctx))
    results.extend(_r0256_apply_symm_apply(term, ctx))
    results.extend(_r0257_symm_apply_apply(term, ctx))
    results.extend(_r0258_symm_refl(term, ctx))
    results.extend(_r0259_apply_eq_iff_eq_symm_apply(term, ctx))
    results.extend(_r0260_coe_toEquiv(term, ctx))
    results.extend(_r0261_coe_symm_toEquiv(term, ctx))
    results.extend(_r0262_trans_apply(term, ctx))
    results.extend(_r0263_refl_trans(term, ctx))
    results.extend(_r0264_symm_trans_self(term, ctx))
    results.extend(_r0265_prodComm_symm(term, ctx))
    results.extend(_r0266_coe_dualDual_symm(term, ctx))
    results.extend(_r0267_dualDual_symm_apply(term, ctx))
    results.extend(_r0268_dual_symm_apply(term, ctx))
    results.extend(_r0269_symm_dual(term, ctx))
    results.extend(_r0270_to_lattice_hom_apply(term, ctx))
    results.extend(_r0271_sumLexIioIci_apply_inr(term, ctx))
    results.extend(_r0272_sumLexIioIci_symm_apply_of_lt(term, ctx))
    results.extend(_r0273_sumLexIioIci_symm_apply_Ici(term, ctx))
    results.extend(_r0274_sumLexIicIoi_apply_inr(term, ctx))
    results.extend(_r0275_sumLexIicIoi_symm_apply_of_le(term, ctx))
    results.extend(_r0276_sumLexIicIoi_symm_apply_Ioi(term, ctx))
    results.extend(_r0277_image_symm_image(term, ctx))
    results.extend(_r0278_image_eq_preimage_symm(term, ctx))
    results.extend(_r0279_symm_preimage_preimage(term, ctx))
    results.extend(_r0280_image_preimage(term, ctx))
    results.extend(_r0281_preimage_image(term, ctx))
    results.extend(_r0282_withTopCongr_symm(term, ctx))
    results.extend(_r0283_withTopCongr_trans(term, ctx))
    results.extend(_r0284_withBotCongr_symm(term, ctx))
    results.extend(_r0285_withBotCongr_trans(term, ctx))
    results.extend(_r0286_coe_toLowerSet(term, ctx))
    results.extend(_r0287_coe_top(term, ctx))
    results.extend(_r0288_preimage_Ioi(term, ctx))
    results.extend(_r0289_preimage_Icc(term, ctx))
    results.extend(_r0290_preimage_Ico(term, ctx))
    results.extend(_r0291_preimage_Ioc(term, ctx))
    results.extend(_r0292_preimage_Ioo(term, ctx))
    results.extend(_r0293_preimage_Ico(term, ctx))
    results.extend(_r0294_preimage_Ioo(term, ctx))
    results.extend(_r0295_image_Iic(term, ctx))
    results.extend(_r0296_image_Iio(term, ctx))
    results.extend(_r0297_image_Ioo(term, ctx))
    results.extend(_r0298_image_Ioc(term, ctx))
    results.extend(_r0299_image_Icc(term, ctx))
    results.extend(_r0300_apply_blimsup(term, ctx))
    results.extend(_r0301_ofDual_symm_eq(term, ctx))
    results.extend(_r0302_toDual_ofDual(term, ctx))
    results.extend(_r0303_ofDual_toDual(term, ctx))
    results.extend(_r0304_toDual_trans_ofDual(term, ctx))
    results.extend(_r0305_ofDual_trans_toDual(term, ctx))
    results.extend(_r0306_toDual_comp_ofDual(term, ctx))
    results.extend(_r0307_ofDual_comp_toDual(term, ctx))
    results.extend(_r0308_toDual_inj(term, ctx))
    results.extend(_r0309_ofDual_inj(term, ctx))
    results.extend(_r0310_Icc_succ_left(term, ctx))
    results.extend(_r0311_Ico_succ_left(term, ctx))
    results.extend(_r0312_type_eq_type(term, ctx))
    results.extend(_r0313_type_eq_zero(term, ctx))
    results.extend(_r0314_type_of_unique(term, ctx))
    results.extend(_r0315__unknown(term, ctx))
    results.extend(_r0316_up_beq(term, ctx))
    results.extend(_r0317_down_beq(term, ctx))
    results.extend(_r0318_up_compare(term, ctx))
    results.extend(_r0319_down_compare(term, ctx))
    results.extend(_r0320_down_sup(term, ctx))
    results.extend(_r0321_down_sdiff(term, ctx))
    results.extend(_r0322_up_compl(term, ctx))
    results.extend(_r0323_down_compl(term, ctx))
    results.extend(_r0324_withBotCongr_symm(term, ctx))
    results.extend(_r0325_withBotCongr_trans(term, ctx))
    results.extend(_r0326_ext(term, ctx))
    results.extend(_r0327_toLinearMap_refl(term, ctx))
    results.extend(_r0328_refl_apply(term, ctx))
    results.extend(_r0329_coe_toIntertwiningMap(term, ctx))
    results.extend(_r0330_coe_toLinearMap(term, ctx))
    results.extend(_r0331_coe_invFun(term, ctx))
    results.extend(_r0332_toLinearEquiv_toLinearMap(term, ctx))
    results.extend(_r0333_toLinearMap_symm(term, ctx))
    results.extend(_r0334_toLinearMap_trans(term, ctx))
    results.extend(_r0335_trans_apply(term, ctx))
    results.extend(_r0336_apply_symm_apply(term, ctx))
    results.extend(_r0337_symm_apply_apply(term, ctx))
    results.extend(_r0338_trans_symm(term, ctx))
    results.extend(_r0339_symm_trans(term, ctx))
    results.extend(_r0340_omega_one_eq_lift(term, ctx))
    results.extend(_r0341_lift_eq_omega_one(term, ctx))
    results.extend(_r0342_omega_natCast_eq_lift(term, ctx))
    results.extend(_r0343_lift_eq_omega_natCast(term, ctx))
    results.extend(_r0344_omega_ofNat_eq_lift(term, ctx))
    results.extend(_r0345_lift_eq_omega_ofNat(term, ctx))
    results.extend(_r0346_cof_eq_one_iff(term, ctx))
    results.extend(_r0347_cof_zero(term, ctx))
    results.extend(_r0348_cof_eq_one_iff(term, ctx))
    results.extend(_r0349_limitRecOn_succ(term, ctx))
    results.extend(_r0350_zero_sub(term, ctx))
    results.extend(_r0351_sub_self(term, ctx))
    results.extend(_r0352_sub_eq_zero_iff_le(term, ctx))
    results.extend(_r0353_mul_add_div_mul(term, ctx))
    results.extend(_r0354_div_self(term, ctx))
    results.extend(_r0355_mul_sub(term, ctx))
    results.extend(_r0356_mod_eq_of_lt(term, ctx))
    results.extend(_r0357_div_add_mod(term, ctx))
    results.extend(_r0358_mul_add_mod_mul(term, ctx))
    results.extend(_r0359_lt_mul_iff(term, ctx))
    results.extend(_r0360_eq_natCast_of_le_natCast(term, ctx))
    results.extend(_r0361_one_add_of_omega0_le(term, ctx))
    results.extend(_r0362_type_eq(term, ctx))
    results.extend(_r0363_le_zero(term, ctx))
    results.extend(_r0364_typein_enum(term, ctx))
    results.extend(_r0365_card_typein(term, ctx))
    results.extend(_r0366_card_one(term, ctx))
    results.extend(_r0367_lift_typein_top(term, ctx))
    results.extend(_r0368_lift_lift(term, ctx))
    results.extend(_r0369_lift_zero(term, ctx))
    results.extend(_r0370_lift_one(term, ctx))
    results.extend(_r0371_lift_card(term, ctx))
    results.extend(_r0372_card_omega0(term, ctx))
    results.extend(_r0373_lift_omega0(term, ctx))
    results.extend(_r0374_card_add_one(term, ctx))
    results.extend(_r0375_card_ofNat(term, ctx))
    results.extend(_r0376_sInf_empty(term, ctx))
    results.extend(_r0377_card_eq_zero(term, ctx))
    results.extend(_r0378_card_eq_one(term, ctx))
    results.extend(_r0379_type_fin(term, ctx))
    results.extend(_r0380_coeff_one_left(term, ctx))
    results.extend(_r0381_coeff_opow_mul_add(term, ctx))
    results.extend(_r0382_eval_single_add(term, ctx))
    results.extend(_r0383_opow_zero(term, ctx))
    results.extend(_r0384_one_opow(term, ctx))
    results.extend(_r0385_opow_natCast(term, ctx))
    results.extend(_r0386_opow_right_inj(term, ctx))
    results.extend(_r0387_apply_omega0_of_isNormal(term, ctx))
    results.extend(_r0388_iSup_add_natCast(term, ctx))
    results.extend(_r0389_univ_id(term, ctx))
    results.extend(_r0390_univ_umax(term, ctx))
    results.extend(_r0391_veblenWith_of_ne_zero(term, ctx))
    results.extend(_r0392_veblenWith_succ(term, ctx))
    results.extend(_r0393_mem_toZFSet_iff(term, ctx))
    results.extend(_r0394_coe_toZFSet(term, ctx))
    results.extend(_r0395_toZFSet_add_one(term, ctx))
    results.extend(_r0396_toZFSet_succ(term, ctx))
    results.extend(_r0397_toHomeomorph_apply(term, ctx))
    results.extend(_r0398_toHomeomorph_refl(term, ctx))
    results.extend(_r0399_symm_toHomeomorph(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_logic_basic rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Equiv_pointReflection_involutive", "Involutive_pointReflection_x_colon_P_to_P", "Not an equality or iff proposition"),
    ("ULift_algebraMap_apply", "_unknown", "Empty proposition"),
    ("Equiv_algebraMap_def", "letI", "Not an equality or iff proposition"),
    ("Equiv_algEquiv_symm_apply", "_unknown", "Empty proposition"),
    ("Equiv_Perm_prod_comp", "_unknown", "Empty proposition"),
    ("EqualCharZero_of_algebraRat", "forall_I_colon_Ideal_R_I_ne_top_to_CharZero_R_I", "Not an equality or iff proposition"),
    ("EqualCharZero_PNat_isUnit_natCast", "IsUnit_n_colon_R", "Not an equality or iff proposition"),
    ("Equidecomp_isDecompOn", "IsDecompOn_f_f_source_f_witness", "Not an equality or iff proposition"),
    ("Equidecomp_apply_mem_target", "f_x_in_f_target", "Not an equality or iff proposition"),
    ("Equidecomp_toPartialEquiv_injective", "Injective_lt_pipe_toPartialEquiv_X_colon_eq_X_G_colon_eq_G", "Not an equality or iff proposition"),
    ("Equidecomp_IsDecompOn_mono", "IsDecompOn_f_prime_A_prime_S", "Not an equality or iff proposition"),
    ("Equiv_smulCommClass", "letI", "Not an equality or iff proposition"),
    ("Equiv_isScalarTower", "letI", "Not an equality or iff proposition"),
    ("Equiv_isCentralScalar", "letI", "Not an equality or iff proposition"),
    ("Equiv_faithfulSMul", "letI", "Not an equality or iff proposition"),
    ("Equiv_Perm_sumCongrHom_injective", "Function_Injective_sumCongrHom_a_b", "Not an equality or iff proposition"),
    ("Equiv_Perm_sigmaCongrRightHom_injective", "Function_Injective_sigmaCongrRightHom_b", "Not an equality or iff proposition"),
    ("Equiv_Perm_subtypeCongrHom_injective", "Function_Injective_subtypeCongrHom_p", "Not an equality or iff proposition"),
    ("Equiv_Perm_extendDomainHom_injective", "Function_Injective_extendDomainHom_f", "Not an equality or iff proposition"),
    ("Equiv_one_def", "letI", "Not an equality or iff proposition"),
    ("Equiv_mul_def", "letI", "Not an equality or iff proposition"),
    ("Equiv_div_def", "letI", "Not an equality or iff proposition"),
    ("Equiv_inv_def", "letI", "Not an equality or iff proposition"),
    ("Equiv_pow_def", "letI", "Not an equality or iff proposition"),
    ("Equiv_mulEquiv_symm_apply", "letI", "Not an equality or iff proposition"),
    ("Equiv_isLeftCancelMul", "letI", "Not an equality or iff proposition"),
    ("Equiv_isRightCancelMul", "letI", "Not an equality or iff proposition"),
    ("Equiv_isCancelMul", "letI", "Not an equality or iff proposition"),
    ("Equiv_mulLeft_symm_apply", "Equiv_mulLeft_a_symm_colon_G_to_G_eq_ainv_star", "Not an equality or iff proposition"),
    ("Group_mulLeft_bijective", "Function_Bijective_a_star", "Not an equality or iff proposition"),
    ("Equiv_mulRight_symm_apply", "Equiv_mulRight_a_symm_colon_G_to_G_eq_fun_x_eq_gt_x_star_ainv", "Not an equality or iff proposition"),
    ("Group_mulRight_bijective", "Function_Bijective_star_a", "Not an equality or iff proposition"),
    ("mulLeft_bijective_0", "Function_Bijective_a_star_colon_G_0_to_G_0", "Not an equality or iff proposition"),
    ("mulRight_bijective_0", "Function_Bijective_star_a_colon_G_0_to_G_0", "Not an equality or iff proposition"),
    ("Equiv_noZeroSMulDivisors", "let", "Not an equality or iff proposition"),
    ("Equiv_moduleIsTorsionFree", "let", "Not an equality or iff proposition"),
    ("Decidable_mul_lt_mul", "_unknown", "Empty proposition"),
    ("OrderMonoidHom_coe_mk", "OrderMonoidHom_mk_f_h_colon_a_to_b_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidHom_mk_coe", "OrderMonoidHom_mk_f_colon_a_to_star_b_h_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidHom_coe_monoidHom", "f_colon_a_to_star_b_colon_a_to_b_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidHom_coe_orderHom", "f_colon_a_to_o_b_colon_a_to_b_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidHom_toMonoidHom_injective", "Injective_toMonoidHom_colon_to_a_to_star_b", "Not an equality or iff proposition"),
    ("OrderMonoidHom_toOrderHom_injective", "Injective_toOrderHom_colon_to_a_to_o_b", "Not an equality or iff proposition"),
    ("OrderMonoidHom_coe_comp", "f_comp_g_colon_a_to_g_eq_f_comp_g", "Not an equality or iff proposition"),
    ("OrderMonoidHom_coe_comp_monoidHom", "f_comp_g_colon_a_to_star_g_eq_f_colon_b_to_star_g_comp_g", "Not an equality or iff proposition"),
    ("OrderMonoidHom_coe_comp_orderHom", "f_comp_g_colon_a_to_o_g_eq_f_colon_b_to_o_g_comp_g", "Not an equality or iff proposition"),
    ("OrderMonoidHom_coe_one", "_1_colon_a_to_star_o_b_eq_1", "Not an equality or iff proposition"),
    ("OrderMonoidHom_one_apply", "_1_colon_a_to_star_o_b_a_eq_1", "Not an equality or iff proposition"),
    ("OrderMonoidHom_one_comp", "_1_colon_b_to_star_o_g_comp_f_eq_1", "Not an equality or iff proposition"),
    ("OrderMonoidHom_comp_one", "f_comp_1_colon_a_to_star_o_b_eq_1", "Not an equality or iff proposition"),
    ("OrderMonoidIso_coe_mk", "OrderMonoidIso_mk_f_h_colon_a_to_b_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidIso_coe_mulEquiv", "f_colon_a_star_b_colon_a_to_b_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidIso_coe_orderIso", "f_colon_a_to_o_b_colon_a_to_b_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidIso_toMulEquiv_injective", "Injective_toMulEquiv_colon_to_a_star_b", "Not an equality or iff proposition"),
    ("OrderMonoidIso_toOrderIso_injective", "Injective_toOrderIso_colon_to_a_o_b", "Not an equality or iff proposition"),
    ("OrderMonoidIso_coe_trans", "f_trans_g_colon_a_to_g_eq_g_comp_f", "Not an equality or iff proposition"),
    ("OrderMonoidIso_coe_toEquiv_symm", "f_colon_a_b_symm_colon_b_to_a_eq_f_symm", "Not an equality or iff proposition"),
    ("OrderMonoidIso_symm_bijective", "Function_Bijective_symm_colon_a_star_o_b_to_b_star_o_a", "Not an equality or iff proposition"),
    ("OrderMonoidIso_strictMono", "StrictMono_f", "Not an equality or iff proposition"),
    ("OrderMonoidIso_strictMono_symm", "StrictMono_f_symm", "Not an equality or iff proposition"),
    ("OrderMonoidWithZeroHom_coe_mk", "OrderMonoidWithZeroHom_mk_f_h_colon_a_to_b_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidWithZeroHom_mk_coe", "OrderMonoidWithZeroHom_mk_f_colon_a_to_star_0_b_h_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidWithZeroHom_coe_monoidWithZeroHom", "f_colon_a_to_star_0_b_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidWithZeroHom_coe_orderMonoidHom", "f_colon_a_to_star_o_b_eq_f", "Not an equality or iff proposition"),
    ("OrderMonoidWithZeroHom_toOrderMonoidHom_injective", "Injective_toOrderMonoidHom_colon_to_a_to_star_o_b", "Not an equality or iff proposition"),
    ("OrderMonoidWithZeroHom_toMonoidWithZeroHom_injective", "Injective_toMonoidWithZeroHom_colon_to_a_to_star_0_b", "Not an equality or iff proposition"),
    ("OrderMonoidWithZeroHom_coe_comp", "f_comp_g_colon_a_to_g_eq_f_comp_g", "Not an equality or iff proposition"),
    ("OrderMonoidWithZeroHom_coe_comp_monoidWithZeroHom", "f_comp_g_colon_a_to_star_0_g_eq_f_colon_b_to_star_0_g_comp_g", "Not an equality or iff proposition"),
    ("OrderMonoidWithZeroHom_coe_comp_orderMonoidHom", "f_comp_g_colon_a_to_star_o_g_eq_f_colon_b_to_star_o_g_comp_g", "Not an equality or iff proposition"),
    ("OrderRingHom_coe_coe_ringHom", "f_colon_a_to_plus_star_b_eq_f", "Not an equality or iff proposition"),
    ("OrderRingHom_coe_coe_orderAddMonoidHom", "f_colon_a_to_plus_o_b_eq_f", "Not an equality or iff proposition"),
    ("OrderRingHom_coe_coe_orderMonoidWithZeroHom", "f_colon_a_to_star_0o_b_eq_f", "Not an equality or iff proposition"),
    ("OrderRingHom_coe_ringHom_apply", "f_colon_a_to_plus_star_b_a_eq_f_a", "Not an equality or iff proposition"),
    ("OrderRingHom_coe_orderAddMonoidHom_apply", "f_colon_a_to_plus_o_b_a_eq_f_a", "Not an equality or iff proposition"),
    ("OrderRingHom_coe_orderMonoidWithZeroHom_apply", "f_colon_a_to_star_0o_b_a_eq_f_a", "Not an equality or iff proposition"),
    ("OrderRingHom_coe_ringHom_id", "OrderRingHom_id_a_colon_a_to_plus_star_a_eq_RingHom_id_a", "Not an equality or iff proposition"),
    ("OrderRingHom_coe_orderAddMonoidHom_id", "OrderRingHom_id_a_colon_a_to_plus_o_a_eq_OrderAddMonoidHom_id_a", "Not an equality or iff proposition"),
    ("OrderRingHom_coe_orderMonoidWithZeroHom_id", "OrderRingHom_id_a_colon_a_to_star_0o_a_eq_OrderMonoidWithZeroHom_id_a", "Not an equality or iff proposition"),
    ("OrderRingIso_symm_bijective", "Bijective_OrderRingIso_symm_colon_a_plus_star_o_b_to_b_plus_star_o_a", "Not an equality or iff proposition"),
    ("OrderHomClass_of_addMonoidHom", "OrderHomClass_F_prime_E_1_prime_E_2_prime", "Not an equality or iff proposition"),
    ("OrderMonoidHom_commute_inl_inr", "Commute_inl_a_b_m_inr_a_b_n", "Not an equality or iff proposition"),
    ("OrderMonoidHom_commute_inl_inr", "Commute_inl_a_b_m_inr_a_b_n", "Not an equality or iff proposition"),
    ("Order_add_one_le_of_lt", "x_plus_1_le_y", "Not an equality or iff proposition"),
    ("Order_wcovBy_add_one", "x_x_plus_1", "Not an equality or iff proposition"),
    ("Order_covBy_add_one", "x_x_plus_1", "Not an equality or iff proposition"),
    ("Equiv_ringEquiv_symm_apply", "_unknown", "Empty proposition"),
    ("Equiv_isDomain", "letI", "Not an equality or iff proposition"),
    ("ExistsHomHomCompEqCompAux_range_g_subset", "Set_range_A_g_sub_Scheme_Pullback_diagonalCoverDiagonalRange_f_A_S_A_X", "Not an equality or iff proposition"),
    ("WeierstrassCurve_Affine_Equation_map", "W_map_f_toAffine_Equation_f_x_f_y", "Not an equality or iff proposition"),
    ("WeierstrassCurve_Affine_Equation_baseChange", "W_baseChange_B_toAffine_Equation_f_x_f_y", "Not an equality or iff proposition"),
    ("WeierstrassCurve_Jacobian_Equation_map", "W_prime_map_f_toJacobian_Equation_f_comp_P", "Not an equality or iff proposition"),
    ("WeierstrassCurve_Jacobian_Equation_baseChange", "W_prime_baseChange_B_toJacobian_Equation_f_comp_P", "Not an equality or iff proposition"),
    ("WeierstrassCurve_Projective_Equation_map", "W_prime_map_f_toProjective_Equation_f_comp_P", "Not an equality or iff proposition"),
    ("WeierstrassCurve_Projective_Equation_baseChange", "W_prime_baseChange_B_toProjective_Equation_f_comp_P", "Not an equality or iff proposition"),
    ("OrderHomClass_of_map_cstarMatrix_nonneg", "OrderHomClass_F_A_1_A_2", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_u_smooth", "ContDiff_inf_u_colon_E_to", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_u_continuous", "Continuous_u_colon_E_to", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_u_support", "support_u_colon_E_to_eq_ball_0_1", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_u_compact_support", "HasCompactSupport_u_colon_E_to", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_u_nonneg", "_0_le_u_x", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_u_le_one", "u_x_le_1", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_u_int_pos", "_0_lt_x_colon_E_u_x_mu", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_w_def", "w_D_colon_E_to_eq_fun_x_eq_gt_x_colon_E_u_x_mu_star_pipe_Dpipe_pow_finrank_E_inv_u_Dinv_x", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_w_nonneg", "_0_le_w_D_x", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_w_mul_phi_nonneg", "_0_le_w_D_y_star_phi_x_minus_y", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_w_support", "support_w_D_colon_E_to_eq_ball_0_D", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_w_compact_support", "HasCompactSupport_w_D_colon_E_to", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_y_nonneg", "_0_le_y_D_x", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_y_le_one", "y_D_x_le_1", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_y_pos_of_mem_ball", "_0_lt_y_D_x", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_y_smooth", "ContDiffOn_inf_uncurry_y_Ioo_0_colon_1_times_univ_colon_Set_E", "Not an equality or iff proposition"),
    ("ExistsContDiffBumpBase_y_support", "support_y_D_colon_E_to_eq_ball_0_colon_E_1_plus_D", "Not an equality or iff proposition"),
    ("OrderedFinpartition_length_le", "c_length_le_n", "Not an equality or iff proposition"),
    ("OrderedFinpartition_partSize_le", "c_partSize_m_le_n", "Not an equality or iff proposition"),
    ("OrderedFinpartition_injective_embSigma", "Injective_embSigma_n", "Not an equality or iff proposition"),
    ("OrderedFinpartition_emb_injective", "Injective_fun_p_colon_Sig_m_Fin_c_partSize_m_c_emb_p_1_p_2", "Not an equality or iff proposition"),
    ("OrderedFinpartition_emb_ne_emb_of_ne", "c_emb_i_a_ne_c_emb_j_b", "Not an equality or iff proposition"),
    ("OrderedFinpartition_length_pos", "_0_lt_c_length", "Not an equality or iff proposition"),
    ("OrderedFinpartition_neZero_length", "NeZero_c_length", "Not an equality or iff proposition"),
    ("OrderedFinpartition_neZero_partSize", "NeZero_c_partSize_i", "Not an equality or iff proposition"),
    ("OrderedFinpartition_one_lt_partSize_index_zero", "_1_lt_c_partSize_c_index_0", "Not an equality or iff proposition"),
    ("OrderedFinpartition_range_emb_extendMiddle_ne_singleton_zero", "range_c_extendMiddle_i_emb_j_ne_0", "Not an equality or iff proposition"),
    ("OrderedFinpartition_norm_applyOrderedFinpartition_le", "c_applyOrderedFinpartition_p_v_m_le_p_m_star_i_colon_Fin_c_partSize_m_v_c_emb", "Not an equality or iff proposition"),
    ("OrderedFinpartition_norm_compAlongOrderedFinpartition_le", "c_compAlongOrderedFinpartition_f_p_le_f_star_i_p_i", "Not an equality or iff proposition"),
    ("OrderedFinpartition_norm_compAlongOrderedFinpartitionL_le", "c_compAlongOrderedFinpartitionL_E_F_G_le_1", "Not an equality or iff proposition"),
    ("OrderedFinpartition_norm_compAlongOrderedFinpartitionL_apply_le", "c_compAlongOrderedFinpartitionL_E_F_G_f_le_f", "Not an equality or iff proposition"),
    ("OrderedFinpartition_norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le", "c_compAlongOrderedFinpartition_f_1_g_1_minus_c_compAlongOrderedFinpartition_f_2_g_2_le", "Not an equality or iff proposition"),
    ("OrderIso_strictConvexOn_symm", "StrictConvexOn_univ_f_symm", "Not an equality or iff proposition"),
    ("OrderIso_convexOn_symm", "ConvexOn_univ_f_symm", "Not an equality or iff proposition"),
    ("OrderIso_strictConcaveOn_symm", "StrictConcaveOn_univ_f_symm", "Not an equality or iff proposition"),
    ("OrderIso_concaveOn_symm", "ConcaveOn_univ_f_symm", "Not an equality or iff proposition"),
    ("OrthonormalBasis_orthonormal_adjustToOrientation", "Orthonormal_e_toBasis_adjustToOrientation_x", "Not an equality or iff proposition"),
    ("Orientation_volumeForm_robust", "_unknown", "Empty proposition"),
    ("Orientation_abs_volumeForm_apply_le", "pipe_o_volumeForm_vpipe_le_i_colon_Fin_n_v_i", "Not an equality or iff proposition"),
    ("Orientation_volumeForm_apply_le", "o_volumeForm_v_le_i_colon_Fin_n_v_i", "Not an equality or iff proposition"),
    ("OrthogonalFamily_isOrtho", "V_i_V_j", "Not an equality or iff proposition"),
    ("Orthonormal_of_isEmpty", "Orthonormal_v", "Not an equality or iff proposition"),
    ("Orthonormal_linearIndependent", "LinearIndependent_v", "Not an equality or iff proposition"),
    ("Orthonormal_comp", "Orthonormal_v_comp_f", "Not an equality or iff proposition"),
    ("Orthonormal_toSubtypeRange", "Orthonormal_Subtype_val_colon_Set_range_v_to_E", "Not an equality or iff proposition"),
    ("Orthonormal_orthonormal_of_forall_eq_or_eq_neg", "Orthonormal_w", "Not an equality or iff proposition"),
    ("Orthonormal_ne_zero", "v_i_ne_0", "Not an equality or iff proposition"),
    ("Orthonormal_comp_linearIsometry", "Orthonormal_f_comp_v", "Not an equality or iff proposition"),
    ("Orthonormal_comp_linearIsometryEquiv", "Orthonormal_f_comp_v", "Not an equality or iff proposition"),
    ("Orthonormal_mapLinearIsometryEquiv", "Orthonormal_v_map_f_toLinearEquiv", "Not an equality or iff proposition"),
    ("Orthonormal_sum_inner_products_le", "i_in_s_v_i_x_pow_2_le_x_pow_2", "Not an equality or iff proposition"),
    ("Orthonormal_tsum_inner_products_le", "prime_i_v_i_x_pow_2_le_x_pow_2", "Not an equality or iff proposition"),
    ("OrthonormalBasis_repr_injective", "Injective_repr_colon_OrthonormalBasis_i_E_to_E_EuclideanSpace_i", "Not an equality or iff proposition"),
    ("OrthonormalBasis_orthonormal", "Orthonormal_b", "Not an equality or iff proposition"),
    ("OrthonormalBasis_coe_toBasis", "b_toBasis_colon_i_to_E_eq_b", "Not an equality or iff proposition"),
    ("OrthonormalBasis_sum_repr", "_unknown", "Empty proposition"),
    ("OrthonormalBasis_norm_le_card_mul_iSup_norm_inner", "x_le_Fintype_card_i_star_i_b_i_x", "Not an equality or iff proposition"),
    ("Module_Basis_coe_toOrthonormalBasis_repr", "v_toOrthonormalBasis_hv_repr_colon_E_to_EuclideanSpace_i_eq_v_equivFun_trans", "Not an equality or iff proposition"),
    ("Module_Basis_coe_toOrthonormalBasis_repr_symm", "v_toOrthonormalBasis_hv_repr_symm_colon_EuclideanSpace_i_to_E_eq_WithLp_lin", "Not an equality or iff proposition"),
    ("Module_Basis_coe_toOrthonormalBasis", "v_toOrthonormalBasis_hv_colon_i_to_E_eq_v_colon_i_to_E", "Not an equality or iff proposition"),
    ("OrthonormalBasis_toMatrix_orthonormalBasis_mem_unitary", "a_toBasis_toMatrix_b_in_Matrix_unitaryGroup_i", "Not an equality or iff proposition"),
    ("OrthonormalBasis_toMatrix_orthonormalBasis_mem_orthogonal", "a_toBasis_toMatrix_b_in_Matrix_orthogonalGroup_i", "Not an equality or iff proposition"),
    ("Orthonormal_codRestrict", "at_Orthonormal_s_i_Set_codRestrict_v_s_hvs", "Not an equality or iff proposition"),
    ("OrthogonalFamily_independent", "iSupIndep_V", "Not an equality or iff proposition"),
    ("Orthonormal_tmul", "Orthonormal_fun_i_colon_i_1_times_i_2_b_1_i_1_b_2_i_2", "Not an equality or iff proposition"),
    ("Orthonormal_basisTensorProduct", "Orthonormal_b_1_tensorProduct_b_2", "Not an equality or iff proposition"),
    ("OrthonormalBasis_tensorProduct_apply", "_unknown", "Empty proposition"),
    ("OrthonormalBasis_tensorProduct_repr_tmul_apply", "_unknown", "Empty proposition"),
    ("Orientation_areaForm", "_unknown", "Empty proposition"),
    ("Orientation_abs_areaForm_le", "pipe_omega_x_ypipe_le_x_star_y", "Not an equality or iff proposition"),
    ("Orientation_areaForm_le", "omega_x_y_le_x_star_y", "Not an equality or iff proposition"),
    ("Orientation_inner_rightAngleRotation_swap", "_unknown", "Empty proposition"),
    ("Orientation_rightAngleRotation_map", "_unknown", "Empty proposition"),
    ("Orientation_linearIsometryEquiv_comp_rightAngleRotation", "_unknown", "Empty proposition"),
    ("Orientation_inner_mul_inner_add_areaForm_mul_areaForm", "_unknown", "Empty proposition"),
    ("Orientation_inner_mul_areaForm_sub", "_unknown", "Empty proposition"),
    ("Orientation_kahler_comp_rightAngleRotation", "_unknown", "Empty proposition"),
    ("Orientation_kahler_ne_zero", "o_kahler_x_y_ne_0", "Not an equality or iff proposition"),
    ("OrthogonalFamily_hasSum_linearIsometry", "HasSum_fun_i_eq_gt_V_i_f_i_hV_linearIsometry_f", "Not an equality or iff proposition"),
    ("OrthonormalBasis_coe_toHilbertBasis", "b_toHilbertBasis_colon_i_to_E_eq_b", "Not an equality or iff proposition"),
    ("Equalizer_i_normNoninc", "i_f_g_NormNoninc", "Not an equality or iff proposition"),
    ("Equalizer_lift_normNoninc", "lift_phi_h_NormNoninc", "Not an equality or iff proposition"),
    ("Equalizer_norm_lift_le", "lift_phi_h_le_C", "Not an equality or iff proposition"),
    ("Equalizer_map_normNoninc", "map_phi_psi_hf_hg_NormNoninc", "Not an equality or iff proposition"),
    ("Equalizer_norm_map_le", "map_phi_psi_hf_hg_le_C", "Not an equality or iff proposition"),
    ("Equivalence_isLeftAdjoint_functor", "e_functor_IsLeftAdjoint", "Not an equality or iff proposition"),
    ("Equivalence_isRightAdjoint_inverse", "e_inverse_IsRightAdjoint", "Not an equality or iff proposition"),
    ("Equivalence_isLeftAdjoint_inverse", "e_inverse_IsLeftAdjoint", "Not an equality or iff proposition"),
    ("Equivalence_isRightAdjoint_functor", "e_functor_IsRightAdjoint", "Not an equality or iff proposition"),
    ("Mon_EquivLaxMonoidalFunctorPUnit_isMonHom_counitIsoAux", "IsMonHom_counitIsoAux_C_F_hom", "Not an equality or iff proposition"),
    ("Decidable_Partrec_const", "_unknown", "Empty proposition"),
    ("Equiv_Computable_symm", "e_Computable_to_e_symm_Computable", "Not an equality or iff proposition"),
    ("Equiv_lawfulFunctor", "at_LawfulFunctor_Equiv_functor_eqv", "Not an equality or iff proposition"),
    ("Equiv_lawfulFunctor", "_unknown", "Empty proposition"),
    ("Equiv_Perm_isCyclic_of_card_le_two", "IsCyclic_Perm_a", "Not an equality or iff proposition"),
    ("EquivLike_inv_injective", "Function_Injective_EquivLike_inv_colon_E_to_b_to_a", "Not an equality or iff proposition"),
    ("EquivLike_injective", "Function_Injective_e", "Not an equality or iff proposition"),
    ("EquivLike_surjective", "Function_Surjective_e", "Not an equality or iff proposition"),
    ("EquivLike_bijective", "Function_Bijective_e_colon_a_to_b", "Not an equality or iff proposition"),
    ("EquivLike_subsingleton_dom", "Subsingleton_E", "Not an equality or iff proposition"),
    ("Equiv_Perm_map_finRange_perm", "map_sig_finRange_n_tilde_finRange_n", "Not an equality or iff proposition"),
    ("Equiv_Perm_ofFn_comp_perm", "ofFn_f_comp_sig_tilde_ofFn_f", "Not an equality or iff proposition"),
    ("Ordnode_not_le_delta", "not_s_le_delta_star_0", "Not an equality or iff proposition"),
    ("Ordnode_delta_lt_false", "False", "Not an equality or iff proposition"),
    ("Ordnode_Sized_node", "_unknown", "Empty proposition"),
]
