"""Mathlib: Set Basic — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 1247 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_set_basic"
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

def _r0000_coe_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetLike.GradeZero.coe_ofNat
    # (ofNat(n) : A 0) = (ofNat(n) : R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNat_n", 3)
    if args is not None:
        try:
            rhs = OOp("ofNat_n", (args[0], OVar("R"),))
            results.append((rhs, "Mathlib: SetLike_GradeZero_coe_ofNat"))
        except Exception:
            pass
    return results


def _r0001_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetLike.GradeZero.coe_mul
    # ↑(a * b) = (↑a * ↑b : R)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_star_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("a"), OOp("b", (OVar("colon"), OVar("R"),))))
            results.append((rhs, "Mathlib: SetLike_GradeZero_coe_mul"))
    except Exception:
        pass
    return results


def _r0002_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetLike.GradeZero.coe_pow
    # ↑(a ^ n) = (↑a : R) ^ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OOp("a", (OVar("colon"), OVar("R"),)), OVar("n")))
            results.append((rhs, "Mathlib: SetLike_GradeZero_coe_pow"))
    except Exception:
        pass
    return results


def _r0003_centralizer_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.centralizer_prod
    # (S ×ˢ T).centralizer = S.centralizer ×ˢ T.centralizer
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_times_T_centralizer")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("S_centralizer", (OVar("times"), OVar("T_centralizer"),))
            results.append((rhs, "Mathlib: Set_centralizer_prod"))
    except Exception:
        pass
    return results


def _r0004_image_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_one
    # f '' 1 = {f 1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OVar("f_1")
            results.append((rhs, "Mathlib: Set_image_one"))
        except Exception:
            pass
    return results


def _r0005_subset_one_iff_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.subset_one_iff_eq
    # s ⊆ 1 ↔ s = ∅ ∨ s = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OVar("empty"), args[1])), OLit(1)))
            results.append((rhs, "Mathlib: Set_subset_one_iff_eq"))
        except Exception:
            pass
    return results


def _r0006_image_op_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_op_one
    # (1 : Set α).image op = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_Set_a_image", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Set_image_op_one"))
        except Exception:
            pass
    return results


def _r0007_sInter_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sInter_inv
    # (⋂₀ S)⁻¹ = ⋂ s ∈ S, s⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_S_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("s"),)), OOp("S", (OVar("sinv"),))))
            results.append((rhs, "Mathlib: Set_sInter_inv"))
    except Exception:
        pass
    return results


def _r0008_iUnion_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.iUnion_inv
    # (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_s_i_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("s_i_inv"),))
            results.append((rhs, "Mathlib: Set_iUnion_inv"))
    except Exception:
        pass
    return results


def _r0009_sUnion_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sUnion_inv
    # (⋃₀ S)⁻¹ = ⋃ s ∈ S, s⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_S_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("s"),)), OOp("S", (OVar("sinv"),))))
            results.append((rhs, "Mathlib: Set_sUnion_inv"))
    except Exception:
        pass
    return results


def _r0010_image_smul_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_smul_prod
    # (fun x : α × β ↦ x.fst • x.snd) '' s ×ˢ t = s • t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_colon_a_times_b_x_fst_x_snd", 4)
    if args is not None:
        try:
            rhs = OOp("s", (OVar("_unknown"), args[3],))
            results.append((rhs, "Mathlib: Set_image_smul_prod"))
        except Exception:
            pass
    return results


def _r0011_smul_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.smul_empty
    # s • (∅ : Set β) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_smul_empty"))
        except Exception:
            pass
    return results


def _r0012_smul_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.smul_eq_empty
    # s • t = ∅ ↔ s = ∅ ∨ t = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("s"))), OOp("==", (OOp("or", (OVar("empty"), args[1])), OVar("empty")))))
            results.append((rhs, "Mathlib: Set_smul_eq_empty"))
        except Exception:
            pass
    return results


def _r0013_singleton_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_smul
    # ({a} : Set α) • t = a • t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_Set_a", 2)
    if args is not None:
        try:
            rhs = OOp("a", (args[0], args[1],))
            results.append((rhs, "Mathlib: Set_singleton_smul"))
        except Exception:
            pass
    return results


def _r0014_singleton_smul_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_smul_singleton
    # ({a} : Set α) • ({b} : Set β) = {a • b}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_Set_a", 2)
    if args is not None:
        try:
            rhs = OVar("a_b")
            results.append((rhs, "Mathlib: Set_singleton_smul_singleton"))
        except Exception:
            pass
    return results


def _r0015_mulIndicator_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mulIndicator_apply
    # mulIndicator s f a = if a ∈ s then f a else 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulIndicator", 3)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("if", (args[2],)), OOp("s", (OVar("then"), args[1], args[2], OVar("else"), OLit(1),))))
            results.append((rhs, "Mathlib: Set_mulIndicator_apply"))
        except Exception:
            pass
    return results


def _r0016_mulIndicator_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mulIndicator_of_notMem
    # mulIndicator s f a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulIndicator", 3)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Set_mulIndicator_of_notMem"))
        except Exception:
            pass
    return results


def _r0017_mulIndicator_eq_one_or_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mulIndicator_eq_one_or_self
    # mulIndicator s f a = 1 ∨ mulIndicator s f a = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulIndicator", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(1), OOp("mulIndicator", (args[0], args[1], args[2],)))), OOp("f", (args[2],))))
            results.append((rhs, "Mathlib: Set_mulIndicator_eq_one_or_self"))
        except Exception:
            pass
    return results


def _r0018_mulIndicator_range_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mulIndicator_range_comp
    # mulIndicator (range f) g ∘ f = g ∘ f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OVar("g"), args[1]))
            results.append((rhs, "Mathlib: Set_mulIndicator_range_comp"))
        except Exception:
            pass
    return results


def _r0019_mulIndicator_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mulIndicator_empty
    # mulIndicator (∅ : Set α) f = fun _ => 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulIndicator", 2)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("_unknown"), OVar("eq_gt"), OLit(1),))
            results.append((rhs, "Mathlib: Set_mulIndicator_empty"))
        except Exception:
            pass
    return results


def _r0020_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc.coe_one
    # ↑(1 : Icc (0 : R) 1) = (1 : R)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Icc_0_colon_R_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("colon"), OVar("R"),))
            results.append((rhs, "Mathlib: Set_Icc_coe_one"))
    except Exception:
        pass
    return results


def _r0021_mk_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc.mk_zero
    # (⟨0, h⟩ : Icc (0 : R) 1) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_h", 4)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Set_Icc_mk_zero"))
        except Exception:
            pass
    return results


def _r0022_mk_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc.mk_one
    # (⟨1, h⟩ : Icc (0 : R) 1) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_h", 4)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Set_Icc_mk_one"))
        except Exception:
            pass
    return results


def _r0023_coe_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc.coe_eq_zero
    # (x : R) = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("x"))), OLit(0)))
            results.append((rhs, "Mathlib: Set_Icc_coe_eq_zero"))
        except Exception:
            pass
    return results


def _r0024_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc.coe_pow
    # ↑(x ^ n) = ((x : R) ^ n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OOp("x", (OVar("colon"), OVar("R"),)), OVar("n")))
            results.append((rhs, "Mathlib: Set_Icc_coe_pow"))
    except Exception:
        pass
    return results


def _r0025_mk_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico.mk_zero
    # (⟨0, h⟩ : Ico (0 : R) 1) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_h", 4)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Set_Ico_mk_zero"))
        except Exception:
            pass
    return results


def _r0026_coe_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico.coe_eq_zero
    # (x : R) = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("x"))), OLit(0)))
            results.append((rhs, "Mathlib: Set_Ico_coe_eq_zero"))
        except Exception:
            pass
    return results


def _r0027_mk_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc.mk_one
    # (⟨1, h⟩ : Ioc (0 : R) 1) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_h", 4)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Set_Ioc_mk_one"))
        except Exception:
            pass
    return results


def _r0028_coe_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc.coe_eq_one
    # (x : R) = 1 ↔ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("x"))), OLit(1)))
            results.append((rhs, "Mathlib: Set_Ioc_coe_eq_one"))
        except Exception:
            pass
    return results


def _r0029_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc.coe_pow
    # ↑(x ^ n) = ((x : R) ^ n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OOp("x", (OVar("colon"), OVar("R"),)), OVar("n")))
            results.append((rhs, "Mathlib: Set_Ioc_coe_pow"))
    except Exception:
        pass
    return results


def _r0030_image_add_const_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_add_const_Ioi
    # (fun x => x + a) '' Ioi b = Ioi (b + a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_plus_a", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("+", (args[2], OVar("a"))),))
            results.append((rhs, "Mathlib: Set_image_add_const_Ioi"))
        except Exception:
            pass
    return results


def _r0031_image_add_const_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_add_const_Icc
    # (fun x => x + a) '' Icc b c = Icc (b + a) (c + a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_plus_a", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("+", (args[2], OVar("a"))), OOp("+", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: Set_image_add_const_Icc"))
        except Exception:
            pass
    return results


def _r0032_image_add_const_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_add_const_Ico
    # (fun x => x + a) '' Ico b c = Ico (b + a) (c + a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_plus_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("+", (args[2], OVar("a"))), OOp("+", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: Set_image_add_const_Ico"))
        except Exception:
            pass
    return results


def _r0033_image_add_const_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_add_const_Ioc
    # (fun x => x + a) '' Ioc b c = Ioc (b + a) (c + a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_plus_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("+", (args[2], OVar("a"))), OOp("+", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: Set_image_add_const_Ioc"))
        except Exception:
            pass
    return results


def _r0034_image_add_const_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_add_const_Ioo
    # (fun x => x + a) '' Ioo b c = Ioo (b + a) (c + a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_plus_a", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("+", (args[2], OVar("a"))), OOp("+", (args[3], OVar("a"))),))
            results.append((rhs, "Mathlib: Set_image_add_const_Ioo"))
        except Exception:
            pass
    return results


def _r0035_image_const_add_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_const_add_Ioi
    # (fun x => a + x) '' Ioi b = Ioi (a + b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_plus_x", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("+", (OVar("a"), args[2])),))
            results.append((rhs, "Mathlib: Set_image_const_add_Ioi"))
        except Exception:
            pass
    return results


def _r0036_image_const_add_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_const_add_Icc
    # (fun x => a + x) '' Icc b c = Icc (a + b) (a + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_plus_x", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (OOp("+", (OVar("a"), args[2])), OOp("+", (OVar("a"), args[3])),))
            results.append((rhs, "Mathlib: Set_image_const_add_Icc"))
        except Exception:
            pass
    return results


def _r0037_image_const_add_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_const_add_Ico
    # (fun x => a + x) '' Ico b c = Ico (a + b) (a + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_plus_x", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("+", (OVar("a"), args[2])), OOp("+", (OVar("a"), args[3])),))
            results.append((rhs, "Mathlib: Set_image_const_add_Ico"))
        except Exception:
            pass
    return results


def _r0038_image_const_add_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_const_add_Ioc
    # (fun x => a + x) '' Ioc b c = Ioc (a + b) (a + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_plus_x", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("+", (OVar("a"), args[2])), OOp("+", (OVar("a"), args[3])),))
            results.append((rhs, "Mathlib: Set_image_const_add_Ioc"))
        except Exception:
            pass
    return results


def _r0039_image_const_add_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_const_add_Ioo
    # (fun x => a + x) '' Ioo b c = Ioo (a + b) (a + c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_a_plus_x", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OOp("+", (OVar("a"), args[2])), OOp("+", (OVar("a"), args[3])),))
            results.append((rhs, "Mathlib: Set_image_const_add_Ioo"))
        except Exception:
            pass
    return results


def _r0040_smul_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.smul_neg
    # s • -t = -(s • t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OVar("minus_s_t")
            results.append((rhs, "Mathlib: Set_smul_neg"))
        except Exception:
            pass
    return results


def _r0041_star_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.star_univ
    # (univ : Set α)⋆ = univ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("univ_colon_Set_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Set_star_univ"))
    except Exception:
        pass
    return results


def _r0042_image_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_star
    # Star.star '' s = s⋆
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Star_star", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_image_star"))
        except Exception:
            pass
    return results


def _r0043_union_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.union_star
    # (s ∪ t)⋆ = s⋆ ∪ t⋆
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_union_t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: Set_union_star"))
    except Exception:
        pass
    return results


def _r0044_iInter_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.iInter_star
    # (⋂ i, s i)⋆ = ⋂ i, (s i)⋆
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_s_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("s_i"),))
            results.append((rhs, "Mathlib: Set_iInter_star"))
    except Exception:
        pass
    return results


def _r0045_iUnion_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.iUnion_star
    # (⋃ i, s i)⋆ = ⋃ i, (s i)⋆
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_s_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("s_i"),))
            results.append((rhs, "Mathlib: Set_iUnion_star"))
    except Exception:
        pass
    return results


def _r0046_compl_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_star
    # sᶜ⋆ = s⋆ᶜ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Set_compl_star"))
    except Exception:
        pass
    return results


def _r0047_sized_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sized_singleton
    # ({s} : Set (Finset α)).Sized r ↔ #s = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("r")
            results.append((rhs, "Mathlib: Set_sized_singleton"))
        except Exception:
            pass
    return results


def _r0048_inv_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.inv_inv
    # R.inv.inv = R
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_inv_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("R")
            results.append((rhs, "Mathlib: SetRel_inv_inv"))
    except Exception:
        pass
    return results


def _r0049_inv_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.inv_empty
    # (∅ : SetRel α β).inv = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("empty_colon_SetRel_a_b_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SetRel_inv_empty"))
    except Exception:
        pass
    return results


def _r0050_inv_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.inv_univ
    # inv (.univ : SetRel α β) = .univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inv", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: SetRel_inv_univ"))
        except Exception:
            pass
    return results


def _r0051_cod_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.cod_empty
    # (∅ : SetRel α β).cod = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("empty_colon_SetRel_a_b_cod")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SetRel_cod_empty"))
    except Exception:
        pass
    return results


def _r0052_dom_eq_empty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.dom_eq_empty_iff
    # R.dom = ∅ ↔ R = (∅ : SetRel α β)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_dom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("R"))), OOp("empty", (OVar("colon"), OVar("SetRel"), OVar("a"), OVar("b"),))))
            results.append((rhs, "Mathlib: SetRel_dom_eq_empty_iff"))
    except Exception:
        pass
    return results


def _r0053_cod_eq_empty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.cod_eq_empty_iff
    # R.cod = ∅ ↔ R = (∅ : SetRel α β)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_cod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("R"))), OOp("empty", (OVar("colon"), OVar("SetRel"), OVar("a"), OVar("b"),))))
            results.append((rhs, "Mathlib: SetRel_cod_eq_empty_iff"))
    except Exception:
        pass
    return results


def _r0054_dom_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.dom_univ
    # dom (.univ : SetRel α β) = .univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dom", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: SetRel_dom_univ"))
        except Exception:
            pass
    return results


def _r0055_cod_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.cod_univ
    # cod (.univ : SetRel α β) = .univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cod", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: SetRel_cod_univ"))
        except Exception:
            pass
    return results


def _r0056_cod_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.cod_inv
    # R.inv.cod = R.dom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_inv_cod")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("R_dom")
            results.append((rhs, "Mathlib: SetRel_cod_inv"))
    except Exception:
        pass
    return results


def _r0057_dom_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.dom_inv
    # R.inv.dom = R.cod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_inv_dom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("R_cod")
            results.append((rhs, "Mathlib: SetRel_dom_inv"))
    except Exception:
        pass
    return results


def _r0058_inv_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.inv_id
    # (.id : SetRel α α).inv = .id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("id_colon_SetRel_a_a_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: SetRel_inv_id"))
    except Exception:
        pass
    return results


def _r0059_comp_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.comp_assoc
    # (R ○ S) ○ t = R ○ (S ○ t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R_S", 2)
    if args is not None:
        try:
            rhs = OOp("R", (args[0], OOp("S", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: SetRel_comp_assoc"))
        except Exception:
            pass
    return results


def _r0060_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.id_comp
    # .id ○ R = R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "id", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: SetRel_id_comp"))
        except Exception:
            pass
    return results


def _r0061_inv_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.inv_comp
    # (R ○ S).inv = S.inv ○ R.inv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_S_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("S_inv", (OVar("_unknown"), OVar("R_inv"),))
            results.append((rhs, "Mathlib: SetRel_inv_comp"))
    except Exception:
        pass
    return results


def _r0062_comp_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.comp_empty
    # R ○ (∅ : SetRel β γ) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SetRel_comp_empty"))
        except Exception:
            pass
    return results


def _r0063_empty_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.empty_comp
    # (∅ : SetRel α β) ○ S = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "empty_colon_SetRel_a_b", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SetRel_empty_comp"))
        except Exception:
            pass
    return results


def _r0064_comp_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.comp_univ
    # R ○ (.univ : SetRel β γ) = {(a, _c) : α × γ | a ∈ R.dom}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R", 2)
    if args is not None:
        try:
            rhs = OVar("a_c_colon_a_times_g_pipe_a_in_R_dom")
            results.append((rhs, "Mathlib: SetRel_comp_univ"))
        except Exception:
            pass
    return results


def _r0065_univ_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.univ_comp
    # (.univ : SetRel α β) ○ S = {(_b, c) : α × γ | c ∈ S.cod}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "univ_colon_SetRel_a_b", 2)
    if args is not None:
        try:
            rhs = OVar("b_c_colon_a_times_g_pipe_c_in_S_cod")
            results.append((rhs, "Mathlib: SetRel_univ_comp"))
        except Exception:
            pass
    return results


def _r0066_comp_iUnion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.comp_iUnion
    # R ○ ⋃ i, S i = ⋃ i, R ○ S i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R", 5)
    if args is not None:
        try:
            rhs = OOp("_unknown", (args[4], OVar("R"), args[1], args[3], args[4],))
            results.append((rhs, "Mathlib: SetRel_comp_iUnion"))
        except Exception:
            pass
    return results


def _r0067_preimage_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.preimage_inv
    # R.inv.preimage s = image R s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R_inv_preimage", 1)
    if args is not None:
        try:
            rhs = OOp("image", (OVar("R"), args[0],))
            results.append((rhs, "Mathlib: SetRel_preimage_inv"))
        except Exception:
            pass
    return results


def _r0068_preimage_empty_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.preimage_empty_right
    # preimage R ∅ = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preimage", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: SetRel_preimage_empty_right"))
        except Exception:
            pass
    return results


def _r0069_image_univ_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.image_univ_right
    # image R .univ = R.cod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image", 2)
    if args is not None:
        try:
            rhs = OVar("R_cod")
            results.append((rhs, "Mathlib: SetRel_image_univ_right"))
        except Exception:
            pass
    return results


def _r0070_preimage_univ_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.preimage_univ_right
    # preimage R .univ = R.dom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preimage", 2)
    if args is not None:
        try:
            rhs = OVar("R_dom")
            results.append((rhs, "Mathlib: SetRel_preimage_univ_right"))
        except Exception:
            pass
    return results


def _r0071_preimage_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.preimage_id
    # preimage .id s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preimage", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: SetRel_preimage_id"))
        except Exception:
            pass
    return results


def _r0072_image_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.image_comp
    # image (R ○ S) s = image S (image R s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image", 2)
    if args is not None:
        try:
            rhs = OOp("image", (OVar("S"), OOp("image", (OVar("R"), args[1],)),))
            results.append((rhs, "Mathlib: SetRel_image_comp"))
        except Exception:
            pass
    return results


def _r0073_preimage_empty_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.preimage_empty_left
    # preimage (∅ : SetRel α β) t = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preimage", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SetRel_preimage_empty_left"))
        except Exception:
            pass
    return results


def _r0074_image_univ_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.image_univ_left
    # image (.univ : SetRel α β) s = .univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: SetRel_image_univ_left"))
        except Exception:
            pass
    return results


def _r0075_preimage_univ_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.preimage_univ_left
    # preimage (.univ : SetRel α β) t = .univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preimage", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: SetRel_preimage_univ_left"))
        except Exception:
            pass
    return results


def _r0076_image_eq_cod_of_dom_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.image_eq_cod_of_dom_subset
    # R.image s = R.cod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R_image", 1)
    if args is not None:
        try:
            rhs = OVar("R_cod")
            results.append((rhs, "Mathlib: SetRel_image_eq_cod_of_dom_subset"))
        except Exception:
            pass
    return results


def _r0077_preimage_eq_dom_of_cod_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.preimage_eq_dom_of_cod_subset
    # R.preimage t = R.dom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R_preimage", 1)
    if args is not None:
        try:
            rhs = OVar("R_dom")
            results.append((rhs, "Mathlib: SetRel_preimage_eq_dom_of_cod_subset"))
        except Exception:
            pass
    return results


def _r0078_preimage_inter_cod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.preimage_inter_cod
    # preimage R (t ∩ R.cod) = preimage R t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preimage", 2)
    if args is not None:
        try:
            rhs = OOp("preimage", (args[0], OVar("t"),))
            results.append((rhs, "Mathlib: SetRel_preimage_inter_cod"))
        except Exception:
            pass
    return results


def _r0079_core_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.core_id
    # core .id t = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "core", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: SetRel_core_id"))
        except Exception:
            pass
    return results


def _r0080_core_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.core_comp
    # core (R ○ S) u = core R (core S u)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "core", 2)
    if args is not None:
        try:
            rhs = OOp("core", (OVar("R"), OOp("core", (OVar("S"), args[1],)),))
            results.append((rhs, "Mathlib: SetRel_core_comp"))
        except Exception:
            pass
    return results


def _r0081_inv_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.inv_eq_self_iff
    # R.inv = R ↔ R.IsSymm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("R"), OVar("R_IsSymm")))
            results.append((rhs, "Mathlib: SetRel_inv_eq_self_iff"))
    except Exception:
        pass
    return results


def _r0082_isCover_empty_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetRel.isCover_empty_right
    # IsCover U s ∅ ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SetRel_isCover_empty_right"))
        except Exception:
            pass
    return results


def _r0083_accumulate_zero_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.accumulate_zero_nat
    # accumulate s 0 = s 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "accumulate", 2)
    if args is not None:
        try:
            rhs = OOp("s", (OLit(0),))
            results.append((rhs, "Mathlib: Set_accumulate_zero_nat"))
        except Exception:
            pass
    return results


def _r0084_partialSups_eq_accumulate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.partialSups_eq_accumulate
    # partialSups f = accumulate f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "partialSups", 1)
    if args is not None:
        try:
            rhs = OOp("accumulate", (args[0],))
            results.append((rhs, "Mathlib: Set_partialSups_eq_accumulate"))
        except Exception:
            pass
    return results


def _r0085_bot_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.bot_eq_empty
    # (⊥ : Set α) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot", 3)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_bot_eq_empty"))
        except Exception:
            pass
    return results


def _r0086_setOf_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.setOf_false
    # { _a : α | False } = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_a_pipe_False")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_setOf_false"))
    except Exception:
        pass
    return results


def _r0087_setOf_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.setOf_bot
    # { _x : α | ⊥ } = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_colon_a_pipe_bot")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_setOf_bot"))
    except Exception:
        pass
    return results


def _r0088_subset_empty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.subset_empty_iff
    # s ⊆ ∅ ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_subset_empty_iff"))
        except Exception:
            pass
    return results


def _r0089_eq_empty_iff_forall_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.eq_empty_iff_forall_notMem
    # s = ∅ ↔ ∀ x, x ∉ s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("empty"), OOp("not_in", (OOp("forall", (OVar("x"), OVar("x"),)), OVar("s")))))
            results.append((rhs, "Mathlib: Set_eq_empty_iff_forall_notMem"))
    except Exception:
        pass
    return results


def _r0090_isEmpty_coe_sort(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.isEmpty_coe_sort
    # IsEmpty (↥s) ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_isEmpty_coe_sort"))
        except Exception:
            pass
    return results


def _r0091_eq_empty_of_isEmpty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.eq_empty_of_isEmpty
    # s = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_eq_empty_of_isEmpty"))
    except Exception:
        pass
    return results


def _r0092_setOf_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.setOf_top
    # { _x : α | ⊤ } = univ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_colon_a_pipe_top")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Set_setOf_top"))
    except Exception:
        pass
    return results


def _r0093_univ_eq_empty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.univ_eq_empty_iff
    # (univ : Set α) = ∅ ↔ IsEmpty α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "univ_set", 3)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("empty"), OOp("IsEmpty", (args[2],))))
            results.append((rhs, "Mathlib: Set_univ_eq_empty_iff"))
        except Exception:
            pass
    return results


def _r0094_univ_subset_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.univ_subset_iff
    # univ ⊆ s ↔ s = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Set_univ_subset_iff"))
        except Exception:
            pass
    return results


def _r0095_union_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.union_self
    # a ∪ a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_union_self"))
        except Exception:
            pass
    return results


def _r0096_union_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.union_empty
    # a ∪ ∅ = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Set_union_empty"))
        except Exception:
            pass
    return results


def _r0097_empty_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.empty_union
    # ∅ ∪ a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_empty_union"))
        except Exception:
            pass
    return results


def _r0098_union_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.union_comm
    # a ∪ b = b ∪ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("union", (args[1], args[0]))
            results.append((rhs, "Mathlib: Set_union_comm"))
        except Exception:
            pass
    return results


def _r0099_union_eq_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.union_eq_right
    # s ∪ t = t ↔ s ⊆ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (args[1], OOp("subset", (args[0], args[1]))))
            results.append((rhs, "Mathlib: Set_union_eq_right"))
        except Exception:
            pass
    return results


def _r0100_union_eq_self_of_subset_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.union_eq_self_of_subset_left
    # s ∪ t = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_union_eq_self_of_subset_left"))
        except Exception:
            pass
    return results


def _r0101_univ_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.univ_union
    # univ ∪ s = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Set_univ_union"))
        except Exception:
            pass
    return results


def _r0102_inter_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inter_empty
    # a ∩ ∅ = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_inter_empty"))
        except Exception:
            pass
    return results


def _r0103_empty_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.empty_inter
    # ∅ ∩ a = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Set_empty_inter"))
        except Exception:
            pass
    return results


def _r0104_inter_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inter_comm
    # a ∩ b = b ∩ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (args[1], args[0]))
            results.append((rhs, "Mathlib: Set_inter_comm"))
        except Exception:
            pass
    return results


def _r0105_inter_eq_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inter_eq_left
    # s ∩ t = s ↔ s ⊆ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (args[0], OOp("subset", (args[0], args[1]))))
            results.append((rhs, "Mathlib: Set_inter_eq_left"))
        except Exception:
            pass
    return results


def _r0106_inter_eq_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inter_eq_right
    # s ∩ t = t ↔ t ⊆ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (args[1], OOp("subset", (args[1], args[0]))))
            results.append((rhs, "Mathlib: Set_inter_eq_right"))
        except Exception:
            pass
    return results


def _r0107_left_eq_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.left_eq_inter
    # s = s ∩ t ↔ s ⊆ t
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("inter", (OVar("s"), OVar("t"))), OOp("subset", (OVar("s"), OVar("t")))))
            results.append((rhs, "Mathlib: Set_left_eq_inter"))
    except Exception:
        pass
    return results


def _r0108_right_eq_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.right_eq_inter
    # t = s ∩ t ↔ t ⊆ s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("inter", (OVar("s"), OVar("t"))), OOp("subset", (OVar("t"), OVar("s")))))
            results.append((rhs, "Mathlib: Set_right_eq_inter"))
    except Exception:
        pass
    return results


def _r0109_inter_eq_self_of_subset_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inter_eq_self_of_subset_left
    # s ⊆ t → s ∩ t = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Set_inter_eq_self_of_subset_left"))
        except Exception:
            pass
    return results


def _r0110_univ_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.univ_inter
    # univ ∩ a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_univ_inter"))
        except Exception:
            pass
    return results


def _r0111_sep_ext_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sep_ext_iff
    # { x ∈ s | p x } = { x ∈ s | q x } ↔ ∀ x ∈ s, p x ↔ q x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_in_s_pipe_p_x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("x_in_s_pipe_q_x"), OOp("iff", (OOp("in", (OOp("forall", (OVar("x"),)), OOp("s", (OVar("p"), OVar("x"),)))), OOp("q", (OVar("x"),))))))
            results.append((rhs, "Mathlib: Set_sep_ext_iff"))
    except Exception:
        pass
    return results


def _r0112_sep_eq_empty_iff_mem_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sep_eq_empty_iff_mem_false
    # { x ∈ s | p x } = ∅ ↔ ∀ x ∈ s, ¬p x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_in_s_pipe_p_x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("empty"), OOp("in", (OOp("forall", (OVar("x"),)), OOp("s", (OOp("not", (OVar("p"),)), OVar("x"),))))))
            results.append((rhs, "Mathlib: Set_sep_eq_empty_iff_mem_false"))
    except Exception:
        pass
    return results


def _r0113_sep_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sep_true
    # { x ∈ s | True } = s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_in_s_pipe_True")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Set_sep_true"))
    except Exception:
        pass
    return results


def _r0114_sep_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sep_inter
    # { x | (x ∈ s ∧ x ∈ t) ∧ p x } = { x ∈ s | p x } ∩ { x ∈ t | p x }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pipe_x_in_s_and_x_in_t_and_p_x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OVar("x_in_s_pipe_p_x"), OVar("x_in_t_pipe_p_x")))
            results.append((rhs, "Mathlib: Set_sep_inter"))
    except Exception:
        pass
    return results


def _r0115_sep_and(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sep_and
    # { x ∈ s | p x ∧ q x } = { x ∈ s | p x } ∩ { x ∈ s | q x }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_in_s_pipe_p_x_and_q_x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OVar("x_in_s_pipe_p_x"), OVar("x_in_s_pipe_q_x")))
            results.append((rhs, "Mathlib: Set_sep_and"))
    except Exception:
        pass
    return results


def _r0116_sep_or(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sep_or
    # { x ∈ s | p x ∨ q x } = { x ∈ s | p x } ∪ { x ∈ s | q x }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_in_s_pipe_p_x_or_q_x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("x_in_s_pipe_p_x"), OVar("x_in_s_pipe_q_x")))
            results.append((rhs, "Mathlib: Set_sep_or"))
    except Exception:
        pass
    return results


def _r0117_sep_setOf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sep_setOf
    # { x ∈ { y | p y } | q x } = { x | p x ∧ q x }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_in_y_pipe_p_y_pipe_q_x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_pipe_p_x_and_q_x")
            results.append((rhs, "Mathlib: Set_sep_setOf"))
    except Exception:
        pass
    return results


def _r0118_card_coe_set_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ENat.card_coe_set_eq
    # ENat.card s = s.encard
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENat_card", 1)
    if args is not None:
        try:
            rhs = OVar("s_encard")
            results.append((rhs, "Mathlib: ENat_card_coe_set_eq"))
        except Exception:
            pass
    return results


def _r0119_encard_eq_coe_toFinset_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Finite.encard_eq_coe_toFinset_card
    # s.encard = h.toFinset.card
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_encard")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("h_toFinset_card")
            results.append((rhs, "Mathlib: Set_Finite_encard_eq_coe_toFinset_card"))
    except Exception:
        pass
    return results


def _r0120_toENat_cardinalMk_subtype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.toENat_cardinalMk_subtype
    # (Cardinal.mk {x // P x}).toENat = {x | P x}.encard
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Cardinal_mk_x_slash_slash_P_x_toENat")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_pipe_P_x_encard")
            results.append((rhs, "Mathlib: Set_toENat_cardinalMk_subtype"))
    except Exception:
        pass
    return results


def _r0121_encard_coe_eq_coe_finsetCard(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.encard_coe_eq_coe_finsetCard
    # encard (s : Set α) = s.card
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "encard", 1)
    if args is not None:
        try:
            rhs = OVar("s_card")
            results.append((rhs, "Mathlib: Set_encard_coe_eq_coe_finsetCard"))
        except Exception:
            pass
    return results


def _r0122_encard_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Infinite.encard_eq
    # s.encard = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_encard")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Set_Infinite_encard_eq"))
    except Exception:
        pass
    return results


def _r0123_encard_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.encard_eq_zero
    # s.encard = 0 ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_encard")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("s"))), OVar("empty")))
            results.append((rhs, "Mathlib: Set_encard_eq_zero"))
    except Exception:
        pass
    return results


def _r0124_encard_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.encard_empty
    # (∅ : Set α).encard = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("empty_colon_Set_a_encard")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Set_encard_empty"))
    except Exception:
        pass
    return results


def _r0125_encard_union_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.encard_union_eq
    # (s ∪ t).encard = s.encard + t.encard
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_union_t_encard")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("s_encard"), OVar("t_encard")))
            results.append((rhs, "Mathlib: Set_encard_union_eq"))
    except Exception:
        pass
    return results


def _r0126_encard_eq_top_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.encard_eq_top_iff
    # s.encard = ⊤ ↔ s.Infinite
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_encard")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("top"), OVar("s_Infinite")))
            results.append((rhs, "Mathlib: Set_encard_eq_top_iff"))
    except Exception:
        pass
    return results


def _r0127_encard_lt_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.encard_lt_one
    # s.encard < 1 ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_encard_lt_one"))
        except Exception:
            pass
    return results


def _r0128_encard_diff_add_encard_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.encard_diff_add_encard_inter
    # (s \\ t).encard + (s ∩ t).encard = s.encard
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("s_encard")
            results.append((rhs, "Mathlib: Set_encard_diff_add_encard_inter"))
        except Exception:
            pass
    return results


def _r0129_univ_disjoint(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.univ_disjoint
    # Disjoint univ s ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_univ_disjoint"))
        except Exception:
            pass
    return results


def _r0130_disjoint_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.disjoint_univ
    # Disjoint s univ ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_disjoint_univ"))
        except Exception:
            pass
    return results


def _r0131_dissipate_zero_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.dissipate_zero_nat
    # dissipate s 0 = s 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dissipate", 2)
    if args is not None:
        try:
            rhs = OOp("s", (OLit(0),))
            results.append((rhs, "Mathlib: Set_dissipate_zero_nat"))
        except Exception:
            pass
    return results


def _r0132_coe_toFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Finite.coe_toFinset
    # (hs.toFinset : Set α) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hs_toFinset", 3)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Set_Finite_coe_toFinset"))
        except Exception:
            pass
    return results


def _r0133_toFinset_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Finite.toFinset_empty
    # h.toFinset = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_Finite_toFinset_empty"))
    except Exception:
        pass
    return results


def _r0134_eqOn_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.eqOn_singleton
    # Set.EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("f_2", (OVar("a"),))
            results.append((rhs, "Mathlib: Set_eqOn_singleton"))
        except Exception:
            pass
    return results


def _r0135_eqOn_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.eqOn_univ
    # EqOn f₁ f₂ univ ↔ f₁ = f₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("f_2")
            results.append((rhs, "Mathlib: Set_eqOn_univ"))
        except Exception:
            pass
    return results


def _r0136_seq_eq_set_seq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.seq_eq_set_seq
    # s <*> t = s.seq t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("s_seq", (args[1],))
            results.append((rhs, "Mathlib: Set_seq_eq_set_seq"))
        except Exception:
            pass
    return results


def _r0137_seqLeft_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.seqLeft_def
    # s <* t = {a | a ∈ s ∧ t.Nonempty}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OVar("a_pipe_a_in_s_and_t_Nonempty")
            results.append((rhs, "Mathlib: Set_seqLeft_def"))
        except Exception:
            pass
    return results


def _r0138_seqRight_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.seqRight_def
    # s *> t = {a | s.Nonempty ∧ a ∈ t}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OVar("a_pipe_s_Nonempty_and_a_in_t")
            results.append((rhs, "Mathlib: Set_seqRight_def"))
        except Exception:
            pass
    return results


def _r0139_pure_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.pure_def
    # (pure a : Set α) = {a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pure", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: Set_pure_def"))
        except Exception:
            pass
    return results


def _r0140_failure_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.failure_def
    # (failure : Set α) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "failure", 3)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_failure_def"))
        except Exception:
            pass
    return results


def _r0141_orElse_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.orElse_def
    # (s <|> t) = s ∪ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("union", (OVar("s"), args[1]))
            results.append((rhs, "Mathlib: Set_orElse_def"))
        except Exception:
            pass
    return results


def _r0142_preimage_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_congr
    # f ⁻¹' s = g ⁻¹' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("g", (args[0], args[1],))
            results.append((rhs, "Mathlib: Set_preimage_congr"))
        except Exception:
            pass
    return results


def _r0143_preimage_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_union
    # f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("f", (args[0], OVar("s"),)), OOp("f", (args[0], OVar("t"),))))
            results.append((rhs, "Mathlib: Set_preimage_union"))
        except Exception:
            pass
    return results


def _r0144_preimage_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_compl
    # f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OVar("f_inv_prime_s")
            results.append((rhs, "Mathlib: Set_preimage_compl"))
        except Exception:
            pass
    return results


def _r0145_preimage_diff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_diff
    # f ⁻¹' (s \\ t) = f ⁻¹' s \\ f ⁻¹' t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[0], OVar("s"), OVar("bsl"), OVar("f"), args[0], OVar("t"),))
            results.append((rhs, "Mathlib: Set_preimage_diff"))
        except Exception:
            pass
    return results


def _r0146_preimage_ite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_ite
    # f ⁻¹' s.ite t₁ t₂ = (f ⁻¹' s).ite (f ⁻¹' t₁) (f ⁻¹' t₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 4)
    if args is not None:
        try:
            rhs = OOp("f_inv_prime_s_ite", (OOp("f", (args[0], args[2],)), OOp("f", (args[0], args[3],)),))
            results.append((rhs, "Mathlib: Set_preimage_ite"))
        except Exception:
            pass
    return results


def _r0147_preimage_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_id
    # id ⁻¹' s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "id", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_preimage_id"))
        except Exception:
            pass
    return results


def _r0148_preimage_const_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_const_of_mem
    # (fun _ : α => b) ⁻¹' s = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_colon_a_eq_gt_b", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Set_preimage_const_of_mem"))
        except Exception:
            pass
    return results


def _r0149_preimage_const_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_const_of_notMem
    # (fun _ : α => b) ⁻¹' s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_colon_a_eq_gt_b", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_preimage_const_of_notMem"))
        except Exception:
            pass
    return results


def _r0150_preimage_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_const
    # (fun _ : α => b) ⁻¹' s = if b ∈ s then univ else ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_colon_a_eq_gt_b", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("if", (OVar("b"),)), OOp("s", (OVar("then"), OVar("univ"), OVar("else"), OVar("empty"),))))
            results.append((rhs, "Mathlib: Set_preimage_const"))
        except Exception:
            pass
    return results


def _r0151_preimage_singleton_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_singleton_false
    # p ⁻¹' {False} = {a | ¬p a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p", 2)
    if args is not None:
        try:
            rhs = OVar("a_pipe_not_p_a")
            results.append((rhs, "Mathlib: Set_preimage_singleton_false"))
        except Exception:
            pass
    return results


def _r0152_inclusion_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inclusion_right
    # inclusion h ⟨x, m⟩ = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inclusion", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Set_inclusion_right"))
        except Exception:
            pass
    return results


def _r0153_val_comp_inclusion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.val_comp_inclusion
    # Subtype.val ∘ inclusion h = Subtype.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Set_val_comp_inclusion"))
        except Exception:
            pass
    return results


def _r0154_insert_eq_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.insert_eq_of_mem
    # insert a s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "insert", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_insert_eq_of_mem"))
        except Exception:
            pass
    return results


def _r0155_singleton_subset_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_subset_singleton
    # ({a} : Set α) ⊆ {b} ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Set_singleton_subset_singleton"))
        except Exception:
            pass
    return results


def _r0156_union_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.union_singleton
    # s ∪ {a} = insert a s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("insert", (args[1], args[0],))
            results.append((rhs, "Mathlib: Set_union_singleton"))
        except Exception:
            pass
    return results


def _r0157_singleton_inter_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_inter_eq_empty
    # {a} ∩ s = ∅ ↔ a ∉ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("empty"), OOp("not_in", (args[0], args[1]))))
            results.append((rhs, "Mathlib: Set_singleton_inter_eq_empty"))
        except Exception:
            pass
    return results


def _r0158_inter_singleton_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inter_singleton_eq_empty
    # s ∩ {a} = ∅ ↔ a ∉ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("empty"), OOp("not_in", (args[1], args[0]))))
            results.append((rhs, "Mathlib: Set_inter_singleton_eq_empty"))
        except Exception:
            pass
    return results


def _r0159_singleton_inter_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_inter_of_mem
    # {a} ∩ s = {a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Set_singleton_inter_of_mem"))
        except Exception:
            pass
    return results


def _r0160_inter_singleton_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inter_singleton_of_mem
    # s ∩ {a} = {a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_inter_singleton_of_mem"))
        except Exception:
            pass
    return results


def _r0161_subset_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.subset_singleton_iff
    # s ⊆ {x} ↔ ∀ y ∈ s, y = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Set_subset_singleton_iff"))
        except Exception:
            pass
    return results


def _r0162_subset_singleton_iff_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.subset_singleton_iff_eq
    # s ⊆ {x} ↔ s = ∅ ∨ s = {x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OVar("empty"), args[1])), OVar("x")))
            results.append((rhs, "Mathlib: Set_subset_singleton_iff_eq"))
        except Exception:
            pass
    return results


def _r0163_insert_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.insert_inj
    # insert a s = insert b s ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "insert", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("insert", (OVar("b"), args[1],)), args[0])), OVar("b")))
            results.append((rhs, "Mathlib: Set_insert_inj"))
        except Exception:
            pass
    return results


def _r0164_inter_insert_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inter_insert_of_mem
    # s ∩ insert a t = insert a (s ∩ t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("insert", (OVar("a"), OOp("inter", (args[0], OVar("t"))),))
            results.append((rhs, "Mathlib: Set_inter_insert_of_mem"))
        except Exception:
            pass
    return results


def _r0165_image_uncurry_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_uncurry_prod
    # uncurry f '' s ×ˢ t = image2 f s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uncurry", 5)
    if args is not None:
        try:
            rhs = OOp("image2", (args[0], args[2], args[4],))
            results.append((rhs, "Mathlib: Set_image_uncurry_prod"))
        except Exception:
            pass
    return results


def _r0166_image2_mk_eq_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image2_mk_eq_prod
    # image2 Prod.mk s t = s ×ˢ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image2", 3)
    if args is not None:
        try:
            rhs = OOp("s", (OVar("times"), args[2],))
            results.append((rhs, "Mathlib: Set_image2_mk_eq_prod"))
        except Exception:
            pass
    return results


def _r0167_image2_curry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image2_curry
    # image2 (fun a b ↦ f (a, b)) s t = f '' s ×ˢ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image2", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("prime_prime"), args[1], OVar("times"), args[2],))
            results.append((rhs, "Mathlib: Set_image2_curry"))
        except Exception:
            pass
    return results


def _r0168_image2_empty_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image2_empty_right
    # image2 f s ∅ = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image2", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Set_image2_empty_right"))
        except Exception:
            pass
    return results


def _r0169_image2_singleton_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image2_singleton_right
    # image2 f s {b} = (fun a => f a b) '' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image2", 3)
    if args is not None:
        try:
            rhs = OOp("fun_a_eq_gt_f_a_b", (OVar("prime_prime"), args[1],))
            results.append((rhs, "Mathlib: Set_image2_singleton_right"))
        except Exception:
            pass
    return results


def _r0170_image2_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image2_singleton
    # image2 f {a} {b} = {f a b}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image2", 3)
    if args is not None:
        try:
            rhs = OVar("f_a_b")
            results.append((rhs, "Mathlib: Set_image2_singleton"))
        except Exception:
            pass
    return results


def _r0171_image2_insert_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image2_insert_right
    # image2 f s (insert b t) = (fun a => f a b) '' s ∪ image2 f s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image2", 3)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("fun_a_eq_gt_f_a_b", (OVar("prime_prime"), args[1],)), OOp("image2", (args[0], args[1], OVar("t"),))))
            results.append((rhs, "Mathlib: Set_image2_insert_right"))
        except Exception:
            pass
    return results


def _r0172_image2_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image2_congr
    # image2 f s t = image2 f' s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image2", 3)
    if args is not None:
        try:
            rhs = OOp("image2", (OVar("f_prime"), args[1], args[2],))
            results.append((rhs, "Mathlib: Set_image2_congr"))
        except Exception:
            pass
    return results


def _r0173_image2_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image2_right
    # image2 (fun _ y => y) s t = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image2", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Set_image2_right"))
        except Exception:
            pass
    return results


def _r0174_image2_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image2_range
    # image2 f (range g) (range h) = range fun x : α × β ↦ f (g x.1) (h x.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image2", 3)
    if args is not None:
        try:
            rhs = OOp("product", (OOp("range", (OVar("fun"), OVar("x"), OVar("colon"), OVar("a"),)), OOp("b", (OVar("_unknown"), args[0], OOp("g", (OVar("x_1"),)), OOp("h", (OVar("x_2"),)),))))
            results.append((rhs, "Mathlib: Set_image2_range"))
        except Exception:
            pass
    return results


def _r0175_diff_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.diff_eq
    # s \\ t = s ∩ tᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (OVar("s"), args[1]))
            results.append((rhs, "Mathlib: Set_diff_eq"))
        except Exception:
            pass
    return results


def _r0176_rangeFactorization_eq_rangeFactorization(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.rangeFactorization_eq_rangeFactorization_iff
    # Set.rangeFactorization f a = Set.rangeFactorization f b ↔ f a = f b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_rangeFactorization", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("Set_rangeFactorization", (args[0], OVar("b"),)), OOp("f", (args[1],)))), OOp("f", (OVar("b"),))))
            results.append((rhs, "Mathlib: Set_rangeFactorization_eq_rangeFactorization_iff"))
        except Exception:
            pass
    return results


def _r0177_op_unop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.op_unop
    # s.op.unop = s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_op_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Set_op_unop"))
    except Exception:
        pass
    return results


def _r0178_unop_op(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.unop_op
    # s.unop.op = s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_unop_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Set_unop_op"))
    except Exception:
        pass
    return results


def _r0179_singleton_op(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_op
    # ({x} : Set α).op = {op x}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_colon_Set_a_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("op_x")
            results.append((rhs, "Mathlib: Set_singleton_op"))
    except Exception:
        pass
    return results


def _r0180_piecewise_eq_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.piecewise_eq_of_notMem
    # s.piecewise f g i = g i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_piecewise", 3)
    if args is not None:
        try:
            rhs = OOp("g", (args[2],))
            results.append((rhs, "Mathlib: Set_piecewise_eq_of_notMem"))
        except Exception:
            pass
    return results


def _r0181_piecewise_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.piecewise_singleton
    # piecewise {x} f g = Function.update g x (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "piecewise", 3)
    if args is not None:
        try:
            rhs = OOp("Function_update", (args[2], args[0], OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: Set_piecewise_singleton"))
        except Exception:
            pass
    return results


def _r0182_piecewise_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.piecewise_compl
    # sᶜ.piecewise f g = s.piecewise g f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_piecewise", 2)
    if args is not None:
        try:
            rhs = OOp("s_piecewise", (args[1], args[0],))
            results.append((rhs, "Mathlib: Set_piecewise_compl"))
        except Exception:
            pass
    return results


def _r0183_piecewise_range_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.piecewise_range_comp
    # (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OVar("g_1"), args[1]))
            results.append((rhs, "Mathlib: Set_piecewise_range_comp"))
        except Exception:
            pass
    return results


def _r0184_ncard_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.powersetCard.ncard_eq
    # (s : Set α).ncard = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_colon_Set_a_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Set_powersetCard_ncard_eq"))
    except Exception:
        pass
    return results


def _r0185_singleton_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_prod
    # ({a} : Set α) ×ˢ t = Prod.mk a '' t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_Set_a", 2)
    if args is not None:
        try:
            rhs = OOp("pair", (OVar("a"), OVar("prime_prime"), args[1],))
            results.append((rhs, "Mathlib: Set_singleton_prod"))
        except Exception:
            pass
    return results


def _r0186_union_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.union_prod
    # (s₁ ∪ s₂) ×ˢ t = s₁ ×ˢ t ∪ s₂ ×ˢ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_1_union_s_2", 2)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("s_1", (args[0], args[1],)), OOp("s_2", (args[0], args[1],))))
            results.append((rhs, "Mathlib: Set_union_prod"))
        except Exception:
            pass
    return results


def _r0187_mk_preimage_prod_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mk_preimage_prod_right
    # Prod.mk a ⁻¹' s ×ˢ t = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 5)
    if args is not None:
        try:
            rhs = args[4]
            results.append((rhs, "Mathlib: Set_mk_preimage_prod_right"))
        except Exception:
            pass
    return results


def _r0188_mk_preimage_prod_left_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mk_preimage_prod_left_eq_empty
    # (fun a => (a, b)) ⁻¹' s ×ˢ t = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_a_eq_gt_a_b", 4)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_mk_preimage_prod_left_eq_empty"))
        except Exception:
            pass
    return results


def _r0189_mk_preimage_prod_right_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mk_preimage_prod_right_eq_empty
    # Prod.mk a ⁻¹' s ×ˢ t = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 5)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_mk_preimage_prod_right_eq_empty"))
        except Exception:
            pass
    return results


def _r0190_mk_preimage_prod_left_eq_if(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mk_preimage_prod_left_eq_if
    # (fun a => (a, b)) ⁻¹' s ×ˢ t = if b ∈ t then s else ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_a_eq_gt_a_b", 4)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("if", (OVar("b"),)), OOp("t", (OVar("then"), args[1], OVar("else"), OVar("empty"),))))
            results.append((rhs, "Mathlib: Set_mk_preimage_prod_left_eq_if"))
        except Exception:
            pass
    return results


def _r0191_image_swap_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_swap_prod
    # Prod.swap '' s ×ˢ t = t ×ˢ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "swap", 4)
    if args is not None:
        try:
            rhs = OOp("t", (args[2], args[1],))
            results.append((rhs, "Mathlib: Set_image_swap_prod"))
        except Exception:
            pass
    return results


def _r0192_prod_range_univ_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.prod_range_univ_eq
    # range m₁ ×ˢ (univ : Set β) = range fun p : α × β => (m₁ p.1, p.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 3)
    if args is not None:
        try:
            rhs = OOp("product", (OOp("range", (OVar("fun"), OVar("p"), OVar("colon"), OVar("a"),)), OOp("b", (OVar("eq_gt"), OOp("m_1", (OVar("p_1"), OVar("p_2"),)),))))
            results.append((rhs, "Mathlib: Set_prod_range_univ_eq"))
        except Exception:
            pass
    return results


def _r0193_prod_eq_empty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.prod_eq_empty_iff
    # s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("s"))), OOp("==", (OOp("or", (OVar("empty"), args[1])), OVar("empty")))))
            results.append((rhs, "Mathlib: Set_prod_eq_empty_iff"))
        except Exception:
            pass
    return results


def _r0194_offDiag_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.offDiag_eq_empty
    # s.offDiag = ∅ ↔ s.Subsingleton
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_offDiag")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("empty"), OVar("s_Subsingleton")))
            results.append((rhs, "Mathlib: Set_offDiag_eq_empty"))
    except Exception:
        pass
    return results


def _r0195_offDiag_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.offDiag_singleton
    # ({a} : Set α).offDiag = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_Set_a_offDiag")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_offDiag_singleton"))
    except Exception:
        pass
    return results


def _r0196_offDiag_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.offDiag_univ
    # (univ : Set α).offDiag = (diagonal α)ᶜ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("univ_colon_Set_a_offDiag")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("diagonal_a")
            results.append((rhs, "Mathlib: Set_offDiag_univ"))
    except Exception:
        pass
    return results


def _r0197_prod_sdiff_diagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.prod_sdiff_diagonal
    # s ×ˢ s \\ diagonal α = s.offDiag
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 5)
    if args is not None:
        try:
            rhs = OVar("s_offDiag")
            results.append((rhs, "Mathlib: Set_prod_sdiff_diagonal"))
        except Exception:
            pass
    return results


def _r0198_offDiag_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.offDiag_inter
    # (s ∩ t).offDiag = s.offDiag ∩ t.offDiag
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_inter_t_offDiag")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OVar("s_offDiag"), OVar("t_offDiag")))
            results.append((rhs, "Mathlib: Set_offDiag_inter"))
    except Exception:
        pass
    return results


def _r0199_graphOn_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.graphOn_empty
    # graphOn f ∅ = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graphOn", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_graphOn_empty"))
        except Exception:
            pass
    return results


def _r0200_graphOn_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.graphOn_eq_empty
    # graphOn f s = ∅ ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graphOn", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("empty"), args[1])), OVar("empty")))
            results.append((rhs, "Mathlib: Set_graphOn_eq_empty"))
        except Exception:
            pass
    return results


def _r0201_graphOn_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.graphOn_union
    # graphOn f (s ∪ t) = graphOn f s ∪ graphOn f t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graphOn", 2)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("graphOn", (args[0], OVar("s"),)), OOp("graphOn", (args[0], OVar("t"),))))
            results.append((rhs, "Mathlib: Set_graphOn_union"))
        except Exception:
            pass
    return results


def _r0202_graphOn_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.graphOn_singleton
    # graphOn f {x} = {(x, f x)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graphOn", 2)
    if args is not None:
        try:
            rhs = OVar("x_f_x")
            results.append((rhs, "Mathlib: Set_graphOn_singleton"))
        except Exception:
            pass
    return results


def _r0203_graphOn_insert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.graphOn_insert
    # graphOn f (insert x s) = insert (x, f x) (graphOn f s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graphOn", 2)
    if args is not None:
        try:
            rhs = OOp("insert", (OOp("x", (args[0], OVar("x"),)), OOp("graphOn", (args[0], OVar("s"),)),))
            results.append((rhs, "Mathlib: Set_graphOn_insert"))
        except Exception:
            pass
    return results


def _r0204_image_snd_graphOn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_snd_graphOn
    # Prod.snd '' s.graphOn f = f '' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[0], OVar("s"),))
            results.append((rhs, "Mathlib: Set_image_snd_graphOn"))
        except Exception:
            pass
    return results


def _r0205_graphOn_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.graphOn_comp
    # s.graphOn (g ∘ f) = (fun x ↦ (x.1, g x.2)) '' s.graphOn f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_graphOn", 1)
    if args is not None:
        try:
            rhs = OOp("fun_x_x_1_g_x_2", (OVar("prime_prime"), OVar("s_graphOn"), OVar("f"),))
            results.append((rhs, "Mathlib: Set_graphOn_comp"))
        except Exception:
            pass
    return results


def _r0206_graphOn_prod_graphOn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.graphOn_prod_graphOn
    # s.graphOn f ×ˢ t.graphOn g = Equiv.prodProdProdComm .. ⁻¹' (s ×ˢ t).graphOn (Prod.map f g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_graphOn", 4)
    if args is not None:
        try:
            rhs = OOp("Equiv_prodProdProdComm", (OVar("_unknown"), OVar("inv_prime"), OVar("s_times_t_graphOn"), OOp("Prod_map", (args[0], args[3],)),))
            results.append((rhs, "Mathlib: Set_graphOn_prod_graphOn"))
        except Exception:
            pass
    return results


def _r0207_restrict_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.restrict_apply
    # s.restrict f x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_restrict", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: Set_restrict_apply"))
        except Exception:
            pass
    return results


def _r0208_restrict_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.restrict_eq_iff
    # restrict s f = g ↔ ∀ (a) (ha : a ∈ s), f a = g ⟨a, ha⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "restrict", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("g"), OOp("forall", (OVar("a"), OVar("ha_colon_a_in_s"), args[1], OVar("a"),)))), OOp("g", (OVar("a_ha"),))))
            results.append((rhs, "Mathlib: Set_restrict_eq_iff"))
        except Exception:
            pass
    return results


def _r0209_image_restrict(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_restrict
    # s.restrict f '' (Subtype.val ⁻¹' t) = f '' (t ∩ s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_restrict", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[1], OOp("inter", (OVar("t"), OVar("s"))),))
            results.append((rhs, "Mathlib: Set_image_restrict"))
        except Exception:
            pass
    return results


def _r0210_restrict_2_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.restrict₂_def
    # restrict₂ (π := π) hst = fun f x ↦ f ⟨x.1, hst x.2⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "restrict_2", 2)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("f"), OVar("x"), OVar("_unknown"), OVar("f"), OVar("x_1_hst_x_2"),))
            results.append((rhs, "Mathlib: Set_restrict_2_def"))
        except Exception:
            pass
    return results


def _r0211_surjective_codRestrict(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.surjective_codRestrict
    # (s.codRestrict f h).Surjective ↔ range f = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Set_surjective_codRestrict"))
        except Exception:
            pass
    return results


def _r0212_up_down(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetSemiring.up_down
    # s.down.up = s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_down_up")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s")
            results.append((rhs, "Mathlib: SetSemiring_up_down"))
    except Exception:
        pass
    return results


def _r0213_up_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.up_empty
    # (∅ : Set α).up = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("empty_colon_Set_a_up")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Set_up_empty"))
    except Exception:
        pass
    return results


def _r0214_add_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetSemiring.add_def
    # s + t = (s.down ∪ t.down).up
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("s_down_union_t_down_up")
            results.append((rhs, "Mathlib: SetSemiring_add_def"))
        except Exception:
            pass
    return results


def _r0215_up_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.up_union
    # (s ∪ t).up = s.up + t.up
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_union_t_up")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("s_up"), OVar("t_up")))
            results.append((rhs, "Mathlib: Set_up_union"))
    except Exception:
        pass
    return results


def _r0216_up_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.up_mul
    # (s * t).up = s.up * t.up
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_star_t_up")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("s_up"), OVar("t_up")))
            results.append((rhs, "Mathlib: Set_up_mul"))
    except Exception:
        pass
    return results


def _r0217_up_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.up_one
    # (1 : Set α).up = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Set_a_up")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Set_up_one"))
    except Exception:
        pass
    return results


def _r0218_preimage_image_sigmaMk_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_image_sigmaMk_of_ne
    # Sigma.mk i ⁻¹' (Sigma.mk j '' s) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_mk", 3)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_preimage_image_sigmaMk_of_ne"))
        except Exception:
            pass
    return results


def _r0219_empty_sigma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.empty_sigma
    # (∅ : Set ι).sigma t = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "empty_colon_Set_i_sigma", 1)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_empty_sigma"))
        except Exception:
            pass
    return results


def _r0220_univ_sigma_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.univ_sigma_univ
    # (@univ ι).sigma (fun _ ↦ @univ (α i)) = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_univ_i_sigma", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Set_univ_sigma_univ"))
        except Exception:
            pass
    return results


def _r0221_sigma_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sigma_univ
    # s.sigma (fun _ ↦ univ : ∀ i, Set (α i)) = Sigma.fst ⁻¹' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sigma", 1)
    if args is not None:
        try:
            rhs = OOp("Sigma_fst", (OVar("inv_prime"), OVar("s"),))
            results.append((rhs, "Mathlib: Set_sigma_univ"))
        except Exception:
            pass
    return results


def _r0222_univ_sigma_preimage_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.univ_sigma_preimage_mk
    # (univ : Set ι).sigma (fun i ↦ Sigma.mk i ⁻¹' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "univ_colon_Set_i_sigma", 1)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Set_univ_sigma_preimage_mk"))
        except Exception:
            pass
    return results


def _r0223_singleton_sigma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_sigma
    # ({i} : Set ι).sigma t = Sigma.mk i '' t i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_colon_Set_i_sigma", 1)
    if args is not None:
        try:
            rhs = OOp("Sigma_mk", (OVar("i"), OVar("prime_prime"), args[0], OVar("i"),))
            results.append((rhs, "Mathlib: Set_singleton_sigma"))
        except Exception:
            pass
    return results


def _r0224_sigma_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sigma_singleton
    # s.sigma (fun i ↦ ({a i} : Set (α i))) = (fun i ↦ Sigma.mk i <| a i) '' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sigma", 1)
    if args is not None:
        try:
            rhs = OOp("fun_i_Sigma_mk_i_lt_pipe_a_i", (OVar("prime_prime"), OVar("s"),))
            results.append((rhs, "Mathlib: Set_sigma_singleton"))
        except Exception:
            pass
    return results


def _r0225_singleton_sigma_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_sigma_singleton
    # (({i} : Set ι).sigma fun i ↦ ({a i} : Set (α i))) = {⟨i, a i⟩}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_colon_Set_i_sigma", 4)
    if args is not None:
        try:
            rhs = OVar("i_a_i")
            results.append((rhs, "Mathlib: Set_singleton_sigma_singleton"))
        except Exception:
            pass
    return results


def _r0226_sigma_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sigma_union
    # s.sigma (fun i ↦ t₁ i ∪ t₂ i) = s.sigma t₁ ∪ s.sigma t₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sigma", 1)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("s_sigma", (OVar("t_1"),)), OOp("s_sigma", (OVar("t_2"),))))
            results.append((rhs, "Mathlib: Set_sigma_union"))
        except Exception:
            pass
    return results


def _r0227_sigma_inter_sigma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sigma_inter_sigma
    # s₁.sigma t₁ ∩ s₂.sigma t₂ = (s₁ ∩ s₂).sigma fun i ↦ t₁ i ∩ t₂ i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("s_1_inter_s_2_sigma", (OVar("fun"), OVar("i"), OVar("_unknown"), OVar("t_1"), OVar("i"),)), OOp("t_2", (OVar("i"),))))
            results.append((rhs, "Mathlib: Set_sigma_inter_sigma"))
        except Exception:
            pass
    return results


def _r0228_mk_preimage_sigma_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mk_preimage_sigma_eq_empty
    # Sigma.mk i ⁻¹' s.sigma t = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_mk", 4)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_mk_preimage_sigma_eq_empty"))
        except Exception:
            pass
    return results


def _r0229_mk_preimage_sigma_eq_if(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.mk_preimage_sigma_eq_if
    # Sigma.mk i ⁻¹' s.sigma t = if i ∈ s then t i else ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_mk", 4)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("if", (args[0],)), OOp("s", (OVar("then"), args[3], args[0], OVar("else"), OVar("empty"),))))
            results.append((rhs, "Mathlib: Set_mk_preimage_sigma_eq_if"))
        except Exception:
            pass
    return results


def _r0230_preimage_val_sInter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_val_sInter
    # A ↓∩ (⋂₀ S) = ⋂₀ { (A ↓∩ B) | B ∈ S }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "A", 2)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("A_inter_B_pipe_B_in_S"),))
            results.append((rhs, "Mathlib: Set_preimage_val_sInter"))
        except Exception:
            pass
    return results


def _r0231_image_val_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_val_inter
    # (↑(D ∩ E) : Set α) = ↑D ∩ ↑E
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D_inter_E", 3)
    if args is not None:
        try:
            rhs = OOp("inter", (OVar("D"), OVar("E")))
            results.append((rhs, "Mathlib: Set_image_val_inter"))
        except Exception:
            pass
    return results


def _r0232_image_val_diff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_val_diff
    # (↑(D \\ E) : Set α) = ↑D \\ ↑E
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D_bsl_E", 3)
    if args is not None:
        try:
            rhs = OOp("D", (OVar("bsl"), OVar("E"),))
            results.append((rhs, "Mathlib: Set_image_val_diff"))
        except Exception:
            pass
    return results


def _r0233_image_val_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_val_compl
    # ↑(Dᶜ) = A \\ ↑D
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("D")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("A", (OVar("bsl"), OVar("D"),))
            results.append((rhs, "Mathlib: Set_image_val_compl"))
    except Exception:
        pass
    return results


def _r0234_image_val_sUnion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_val_sUnion
    # ↑(⋃₀ T) = ⋃₀ { (B : Set α) | B ∈ T}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_T")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_0", (OVar("B_colon_Set_a_pipe_B_in_T"),))
            results.append((rhs, "Mathlib: Set_image_val_sUnion"))
    except Exception:
        pass
    return results


def _r0235_image_val_iUnion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_val_iUnion
    # ↑(⋃ i, t i) = ⋃ i, (t i : Set α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_t_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OOp("t", (OVar("i"), OVar("colon"), OVar("Set"), OVar("a"),)),))
            results.append((rhs, "Mathlib: Set_image_val_iUnion"))
    except Exception:
        pass
    return results


def _r0236_image_val_sInter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_val_sInter
    # (↑(⋂₀ T) : Set α) = ⋂₀ { (↑B : Set α) | B ∈ T }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_T", 3)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("B_colon_Set_a_pipe_B_in_T"),))
            results.append((rhs, "Mathlib: Set_image_val_sInter"))
        except Exception:
            pass
    return results


def _r0237_image_val_union_self_right_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_val_union_self_right_eq
    # A ∪ ↑D = A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Set_image_val_union_self_right_eq"))
        except Exception:
            pass
    return results


def _r0238_image_val_union_self_left_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_val_union_self_left_eq
    # ↑D ∪ A = A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_image_val_union_self_left_eq"))
        except Exception:
            pass
    return results


def _r0239_image_val_inter_self_right_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_val_inter_self_right_eq_coe
    # A ∩ ↑D = ↑D
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_image_val_inter_self_right_eq_coe"))
        except Exception:
            pass
    return results


def _r0240_image_val_inter_self_left_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_val_inter_self_left_eq_coe
    # ↑D ∩ A = ↑D
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Set_image_val_inter_self_left_eq_coe"))
        except Exception:
            pass
    return results


def _r0241_sups_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sups_empty
    # s ⊻ ∅ = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_sups_empty"))
        except Exception:
            pass
    return results


def _r0242_sups_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sups_eq_empty
    # s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("s"))), OOp("==", (OOp("or", (OVar("empty"), args[1])), OVar("empty")))))
            results.append((rhs, "Mathlib: Set_sups_eq_empty"))
        except Exception:
            pass
    return results


def _r0243_singleton_sups(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_sups
    # {a} ⊻ t = t.image fun b => a ⊔ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("t_image", (OVar("fun"), OVar("b"), OVar("eq_gt"), OVar("a"), args[0], OVar("b"),))
            results.append((rhs, "Mathlib: Set_singleton_sups"))
        except Exception:
            pass
    return results


def _r0244_sups_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sups_singleton
    # s ⊻ {b} = s.image fun a => a ⊔ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("s_image", (OVar("fun"), OVar("a"), OVar("eq_gt"), OVar("a"), args[0], args[1],))
            results.append((rhs, "Mathlib: Set_sups_singleton"))
        except Exception:
            pass
    return results


def _r0245_singleton_sups_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.singleton_sups_singleton
    # ({a} ⊻ {b} : Set α) = {a ⊔ b}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 5)
    if args is not None:
        try:
            rhs = OVar("a_b")
            results.append((rhs, "Mathlib: Set_singleton_sups_singleton"))
        except Exception:
            pass
    return results


def _r0246_sep_sups_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sep_sups_le
    # {b ∈ s ⊻ t | b ≤ a} = {b ∈ s | b ≤ a} ⊻ {b ∈ t | b ≤ a}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b_in_s_t_pipe_b_le_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("b_in_s_pipe_b_le_a", (OVar("_unknown"), OVar("b_in_t_pipe_b_le_a"),))
            results.append((rhs, "Mathlib: Set_sep_sups_le"))
    except Exception:
        pass
    return results


def _r0247_sups_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sups_assoc
    # s ⊻ t ⊻ u = s ⊻ (t ⊻ u)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 4)
    if args is not None:
        try:
            rhs = OOp("s", (args[2], OOp("t", (args[2], args[3],)),))
            results.append((rhs, "Mathlib: Set_sups_assoc"))
        except Exception:
            pass
    return results


def _r0248_inter_symmDiff_distrib_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inter_symmDiff_distrib_left
    # s ∩ t ∆ u = (s ∩ t) ∆ (s ∩ u)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("s_inter_t", (OVar("_unknown"), OOp("inter", (args[0], OVar("u"))),))
            results.append((rhs, "Mathlib: Set_inter_symmDiff_distrib_left"))
        except Exception:
            pass
    return results


def _r0249_iUnionLift_inclusion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.iUnionLift_inclusion
    # iUnionLift S f hf T hT (Set.inclusion h x) = f i x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iUnionLift", 6)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("i"), OVar("x"),))
            results.append((rhs, "Mathlib: Set_iUnionLift_inclusion"))
        except Exception:
            pass
    return results


def _r0250_ker_apply_mk_out(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Setoid.ker_apply_mk_out
    # f (⟦a⟧ : Quotient (Setoid.ker f)).out = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"),))
            results.append((rhs, "Mathlib: Setoid_ker_apply_mk_out"))
        except Exception:
            pass
    return results


def _r0251_bot_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Setoid.bot_def
    # ⇑(⊥ : Setoid α) = (· = ·)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Setoid_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OVar("_unknown"), OVar("_unknown")))
            results.append((rhs, "Mathlib: Setoid_bot_def"))
    except Exception:
        pass
    return results


def _r0252_mk_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Setoid.mk_eq_top
    # mk r iseqv = ⊤ ↔ r = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OVar("top")))
            results.append((rhs, "Mathlib: Setoid_mk_eq_top"))
        except Exception:
            pass
    return results


def _r0253_mk_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Setoid.mk_eq_bot
    # mk r iseqv = ⊥ ↔ r = (· = ·)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("bot"), args[0])), OOp("==", (OVar("_unknown"), OVar("_unknown")))))
            results.append((rhs, "Mathlib: Setoid_mk_eq_bot"))
        except Exception:
            pass
    return results


def _r0254_eq_top_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Setoid.eq_top_iff
    # s = (⊤ : Setoid α) ↔ ∀ x y : α, s x y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("top", (OVar("colon"), OVar("Setoid"), OVar("a"),)), OOp("forall", (OVar("x"), OVar("y"), OVar("colon"), OVar("a"), OVar("s"), OVar("x"), OVar("y"),))))
            results.append((rhs, "Mathlib: Setoid_eq_top_iff"))
    except Exception:
        pass
    return results


def _r0255_sym2_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sym2_empty
    # (∅ : Set α).sym2 = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("empty_colon_Set_a_sym2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_sym2_empty"))
    except Exception:
        pass
    return results


def _r0256_sym2_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sym2_univ
    # (Set.univ : Set α).sym2 = Set.univ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Set_univ_colon_Set_a_sym2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: Set_sym2_univ"))
    except Exception:
        pass
    return results


def _r0257_sym2_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sym2_singleton
    # ({a} : Set α).sym2 = {s(a, a)}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_Set_a_sym2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_a_a")
            results.append((rhs, "Mathlib: Set_sym2_singleton"))
    except Exception:
        pass
    return results


def _r0258_sym2_insert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.sym2_insert
    # (insert a s).sym2 = (fun b ↦ s(a, b)) '' insert a s ∪ s.sym2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("insert_a_s_sym2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OOp("fun_b_s_a_b", (OVar("prime_prime"), OVar("insert"), OVar("a"), OVar("s"),)), OVar("s_sym2")))
            results.append((rhs, "Mathlib: Set_sym2_insert"))
    except Exception:
        pass
    return results


def _r0259_mk_smul_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetLike.mk_smul_mk
    # r • (⟨x, hx⟩ : s) = ⟨r • x, smul_mem r hx⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r", 2)
    if args is not None:
        try:
            rhs = OVar("r_x_smul_mem_r_hx")
            results.append((rhs, "Mathlib: SetLike_mk_smul_mk"))
        except Exception:
            pass
    return results


def _r0260_smul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SetLike.smul_def
    # r • x = ⟨r • x, smul_mem r x.2⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r", 2)
    if args is not None:
        try:
            rhs = OVar("r_x_smul_mem_r_x_2")
            results.append((rhs, "Mathlib: SetLike_smul_def"))
        except Exception:
            pass
    return results


def _r0261_image_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_symm_apply
    # (Set.image f s H).symm ⟨f x, h⟩ = ⟨x, H.mem_set_image.1 h⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_image_f_s_H_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x_H_mem_set_image_1_h")
            results.append((rhs, "Mathlib: Set_image_symm_apply"))
        except Exception:
            pass
    return results


def _r0262_preimage_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Definable.preimage_comp
    # A.Definable L ((fun g : β → M => g ∘ f) ⁻¹' s)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("M")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OOp("gt", (OVar("g"),)), OVar("f_inv_prime_s")))
            results.append((rhs, "Mathlib: Set_Definable_preimage_comp"))
    except Exception:
        pass
    return results


def _r0263_compl_inter_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_inter_self
    # sᶜ ∩ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_compl_inter_self"))
        except Exception:
            pass
    return results


def _r0264_compl_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_empty
    # (∅ : Set α)ᶜ = univ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("empty_colon_Set_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Set_compl_empty"))
    except Exception:
        pass
    return results


def _r0265_compl_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_union
    # (s ∪ t)ᶜ = sᶜ ∩ tᶜ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_union_t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: Set_compl_union"))
    except Exception:
        pass
    return results


def _r0266_compl_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_inter
    # (s ∩ t)ᶜ = sᶜ ∪ tᶜ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_inter_t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: Set_compl_inter"))
    except Exception:
        pass
    return results


def _r0267_compl_empty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_empty_iff
    # sᶜ = ∅ ↔ s = univ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("s"))), OVar("univ")))
            results.append((rhs, "Mathlib: Set_compl_empty_iff"))
    except Exception:
        pass
    return results


def _r0268_compl_univ_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_univ_iff
    # sᶜ = univ ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("univ"), OVar("s"))), OVar("empty")))
            results.append((rhs, "Mathlib: Set_compl_univ_iff"))
    except Exception:
        pass
    return results


def _r0269_compl_union_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_union_self
    # sᶜ ∪ s = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Set_compl_union_self"))
        except Exception:
            pass
    return results


def _r0270_compl_singleton_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_singleton_eq
    # {a}ᶜ = {x | x ≠ a}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_pipe_x_ne_a")
            results.append((rhs, "Mathlib: Set_compl_singleton_eq"))
    except Exception:
        pass
    return results


def _r0271_union_diff_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.union_diff_right
    # (s ∪ t) \\ t = s \\ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_union_t", 2)
    if args is not None:
        try:
            rhs = OOp("s", (args[0], args[1],))
            results.append((rhs, "Mathlib: Set_union_diff_right"))
        except Exception:
            pass
    return results


def _r0272_union_diff_distrib(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.union_diff_distrib
    # (s ∪ t) \\ u = s \\ u ∪ t \\ u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_union_t", 2)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("s", (args[0], args[1],)), OOp("t", (args[0], args[1],))))
            results.append((rhs, "Mathlib: Set_union_diff_distrib"))
        except Exception:
            pass
    return results


def _r0273_inter_union_diff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.inter_union_diff
    # s ∩ t ∪ s \\ t = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Set_inter_union_diff"))
        except Exception:
            pass
    return results


def _r0274_diff_union_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.diff_union_inter
    # s \\ t ∪ s ∩ t = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Set_diff_union_inter"))
        except Exception:
            pass
    return results


def _r0275_diff_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.diff_eq_empty
    # s \\ t = ∅ ↔ s ⊆ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("empty"), OOp("subset", (OVar("s"), args[1]))))
            results.append((rhs, "Mathlib: Set_diff_eq_empty"))
        except Exception:
            pass
    return results


def _r0276_diff_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.diff_univ
    # s \\ univ = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_diff_univ"))
        except Exception:
            pass
    return results


def _r0277_diff_diff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.diff_diff
    # (s \\ t) \\ u = s \\ (t ∪ u)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_bsl_t", 2)
    if args is not None:
        try:
            rhs = OOp("s", (args[0], OOp("union", (OVar("t"), args[1])),))
            results.append((rhs, "Mathlib: Set_diff_diff"))
        except Exception:
            pass
    return results


def _r0278_diff_union_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.diff_union_self
    # s \\ t ∪ t = s ∪ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("union", (OVar("s"), args[1]))
            results.append((rhs, "Mathlib: Set_diff_union_self"))
        except Exception:
            pass
    return results


def _r0279_diff_inter_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.diff_inter_self
    # b \\ a ∩ a = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_diff_inter_self"))
        except Exception:
            pass
    return results


def _r0280_diff_inter_self_eq_diff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.diff_inter_self_eq_diff
    # s \\ (t ∩ s) = s \\ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("s", (args[0], OVar("t"),))
            results.append((rhs, "Mathlib: Set_diff_inter_self_eq_diff"))
        except Exception:
            pass
    return results


def _r0281_diff_self_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.diff_self_inter
    # s \\ (s ∩ t) = s \\ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("s", (args[0], OVar("t"),))
            results.append((rhs, "Mathlib: Set_diff_self_inter"))
        except Exception:
            pass
    return results


def _r0282_diff_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.diff_self
    # s \\ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_diff_self"))
        except Exception:
            pass
    return results


def _r0283_insert_diff_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.insert_diff_of_notMem
    # insert a s \\ t = insert a (s \\ t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "insert", 4)
    if args is not None:
        try:
            rhs = OOp("insert", (args[0], OOp("s", (args[2], args[3],)),))
            results.append((rhs, "Mathlib: Set_insert_diff_of_notMem"))
        except Exception:
            pass
    return results


def _r0284_insert_diff_singleton_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.insert_diff_singleton_comm
    # insert a (s \\ {b}) = insert a s \\ {b}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "insert", 2)
    if args is not None:
        try:
            rhs = OOp("insert", (args[0], OVar("s"), OVar("bsl"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_insert_diff_singleton_comm"))
        except Exception:
            pass
    return results


def _r0285_ite_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ite_compl
    # tᶜ.ite s s' = t.ite s' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "t_ite", 2)
    if args is not None:
        try:
            rhs = OOp("t_ite", (args[1], args[0],))
            results.append((rhs, "Mathlib: Set_ite_compl"))
        except Exception:
            pass
    return results


def _r0286_ite_inter_compl_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ite_inter_compl_self
    # t.ite s s' ∩ tᶜ = s' ∩ tᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (OVar("s_prime"), args[1]))
            results.append((rhs, "Mathlib: Set_ite_inter_compl_self"))
        except Exception:
            pass
    return results


def _r0287_ite_diff_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ite_diff_self
    # t.ite s s' \\ t = s' \\ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "t_ite", 4)
    if args is not None:
        try:
            rhs = OOp("s_prime", (args[2], args[3],))
            results.append((rhs, "Mathlib: Set_ite_diff_self"))
        except Exception:
            pass
    return results


def _r0288_ite_same(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ite_same
    # t.ite s s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "t_ite", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_ite_same"))
        except Exception:
            pass
    return results


def _r0289_ite_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ite_left
    # s.ite s t = s ∪ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_ite", 2)
    if args is not None:
        try:
            rhs = OOp("union", (args[0], args[1]))
            results.append((rhs, "Mathlib: Set_ite_left"))
        except Exception:
            pass
    return results


def _r0290_ite_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ite_right
    # s.ite t s = t ∩ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_ite", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (args[0], args[1]))
            results.append((rhs, "Mathlib: Set_ite_right"))
        except Exception:
            pass
    return results


def _r0291_ite_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ite_empty
    # Set.ite ∅ s s' = s'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_ite", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Set_ite_empty"))
        except Exception:
            pass
    return results


def _r0292_ite_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ite_univ
    # Set.ite univ s s' = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_ite", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Set_ite_univ"))
        except Exception:
            pass
    return results


def _r0293_ite_empty_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ite_empty_left
    # t.ite ∅ s = s \\ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "t_ite", 2)
    if args is not None:
        try:
            rhs = OOp("s", (OVar("bsl"), OVar("t"),))
            results.append((rhs, "Mathlib: Set_ite_empty_left"))
        except Exception:
            pass
    return results


def _r0294_ite_empty_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ite_empty_right
    # t.ite s ∅ = s ∩ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "t_ite", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (args[0], OVar("t")))
            results.append((rhs, "Mathlib: Set_ite_empty_right"))
        except Exception:
            pass
    return results


def _r0295_coe_iSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iic.coe_iSup
    # (↑(⨆ i, f i) : α) = ⨆ i, (f i : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_f_i", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OOp("f", (OVar("i"), args[0], args[1],)),))
            results.append((rhs, "Mathlib: Set_Iic_coe_iSup"))
        except Exception:
            pass
    return results


def _r0296_coe_biSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iic.coe_biSup
    # (↑(⨆ i, ⨆ (_ : p i), f i) : α) = ⨆ i, ⨆ (_ : p i), (f i : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_colon_p_i_f_i", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("_unknown"), OVar("colon_p_i"), OOp("f", (OVar("i"), args[0], args[1],)),))
            results.append((rhs, "Mathlib: Set_Iic_coe_biSup"))
        except Exception:
            pass
    return results


def _r0297_coe_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iic.coe_iInf
    # (↑(⨅ i, f i) : α) = a ⊓ ⨅ i, (f i : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_f_i", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("_unknown"), OVar("i"), OOp("f", (OVar("i"), args[0], args[1],)),))
            results.append((rhs, "Mathlib: Set_Iic_coe_iInf"))
        except Exception:
            pass
    return results


def _r0298_coe_biInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iic.coe_biInf
    # (↑(⨅ i, ⨅ (_ : p i), f i) : α) = a ⊓ ⨅ i, ⨅ (_ : p i), (f i : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_colon_p_i_f_i", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("_unknown"), OVar("i"), OVar("_unknown"), OVar("colon_p_i"), OOp("f", (OVar("i"), args[0], args[1],)),))
            results.append((rhs, "Mathlib: Set_Iic_coe_biInf"))
        except Exception:
            pass
    return results


def _r0299_exists_set_insert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CovBy.exists_set_insert
    # ∃ a ∉ s, insert a s = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not_in", 2)
    if args is not None:
        try:
            rhs = OVar("t")
            results.append((rhs, "Mathlib: CovBy_exists_set_insert"))
        except Exception:
            pass
    return results


def _r0300_toFinset_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.toFinset_Ico
    # (Ico a b).toFinset = Finset.Ico a b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Ico_a_b_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Finset_Ico", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_toFinset_Ico"))
    except Exception:
        pass
    return results


def _r0301_toFinset_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.toFinset_Ioo
    # (Ioo a b).toFinset = Finset.Ioo a b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Ioo_a_b_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Finset_Ioo", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_toFinset_Ioo"))
    except Exception:
        pass
    return results


def _r0302_Iic_toDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iic_toDual
    # Iic (toDual a) = ofDual ⁻¹' Ici a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iic", 1)
    if args is not None:
        try:
            rhs = OOp("ofDual", (OVar("inv_prime"), OVar("Ici"), OVar("a"),))
            results.append((rhs, "Mathlib: Set_Iic_toDual"))
        except Exception:
            pass
    return results


def _r0303_Icc_toDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc_toDual
    # Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc b a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc", 2)
    if args is not None:
        try:
            rhs = OOp("ofDual", (OVar("inv_prime"), OVar("Icc"), OVar("b"), OVar("a"),))
            results.append((rhs, "Mathlib: Set_Icc_toDual"))
        except Exception:
            pass
    return results


def _r0304_Ico_toDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico_toDual
    # Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc b a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OOp("ofDual", (OVar("inv_prime"), OVar("Ioc"), OVar("b"), OVar("a"),))
            results.append((rhs, "Mathlib: Set_Ico_toDual"))
        except Exception:
            pass
    return results


def _r0305_Ioo_toDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioo_toDual
    # Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo b a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo", 2)
    if args is not None:
        try:
            rhs = OOp("ofDual", (OVar("inv_prime"), OVar("Ioo"), OVar("b"), OVar("a"),))
            results.append((rhs, "Mathlib: Set_Ioo_toDual"))
        except Exception:
            pass
    return results


def _r0306_Iio_ofDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iio_ofDual
    # Iio (ofDual x) = toDual ⁻¹' Ioi x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iio", 1)
    if args is not None:
        try:
            rhs = OOp("toDual", (OVar("inv_prime"), OVar("Ioi"), OVar("x"),))
            results.append((rhs, "Mathlib: Set_Iio_ofDual"))
        except Exception:
            pass
    return results


def _r0307_Iic_ofDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iic_ofDual
    # Iic (ofDual x) = toDual ⁻¹' Ici x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iic", 1)
    if args is not None:
        try:
            rhs = OOp("toDual", (OVar("inv_prime"), OVar("Ici"), OVar("x"),))
            results.append((rhs, "Mathlib: Set_Iic_ofDual"))
        except Exception:
            pass
    return results


def _r0308_Icc_ofDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc_ofDual
    # Icc (ofDual y) (ofDual x) = toDual ⁻¹' Icc x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc", 2)
    if args is not None:
        try:
            rhs = OOp("toDual", (OVar("inv_prime"), OVar("Icc"), OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: Set_Icc_ofDual"))
        except Exception:
            pass
    return results


def _r0309_Ico_ofDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico_ofDual
    # Ico (ofDual y) (ofDual x) = toDual ⁻¹' Ioc x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OOp("toDual", (OVar("inv_prime"), OVar("Ioc"), OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: Set_Ico_ofDual"))
        except Exception:
            pass
    return results


def _r0310_Ioo_ofDual(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioo_ofDual
    # Ioo (ofDual y) (ofDual x) = toDual ⁻¹' Ioo x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo", 2)
    if args is not None:
        try:
            rhs = OOp("toDual", (OVar("inv_prime"), OVar("Ioo"), OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: Set_Ioo_ofDual"))
        except Exception:
            pass
    return results


def _r0311_Ico_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico_eq_empty
    # Ico a b = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_Ico_eq_empty"))
        except Exception:
            pass
    return results


def _r0312_Ioo_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioo_eq_empty
    # Ioo a b = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_Ioo_eq_empty"))
        except Exception:
            pass
    return results


def _r0313_Icc_eq_empty_of_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc_eq_empty_of_lt
    # Icc a b = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_Icc_eq_empty_of_lt"))
        except Exception:
            pass
    return results


def _r0314_Ico_eq_empty_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico_eq_empty_of_le
    # Ico a b = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_Ico_eq_empty_of_le"))
        except Exception:
            pass
    return results


def _r0315_Ioo_eq_empty_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioo_eq_empty_of_le
    # Ioo a b = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_Ioo_eq_empty_of_le"))
        except Exception:
            pass
    return results


def _r0316_Ico_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico_self
    # Ico a a = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Set_Ico_self"))
        except Exception:
            pass
    return results


def _r0317_Iic_inter_Ioc_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iic_inter_Ioc_of_le
    # Iic a ∩ Ioc b c = Ioc b a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("b"), OVar("a"),))
            results.append((rhs, "Mathlib: Set_Iic_inter_Ioc_of_le"))
        except Exception:
            pass
    return results


def _r0318_Ioc_eq_Icc_same_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_eq_Icc_same_iff
    # Ioc a b = Icc a b ↔ ¬a ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OOp("Icc", (args[0], args[1],)), OOp("not", (args[0],)))), args[1]))
            results.append((rhs, "Mathlib: Set_Ioc_eq_Icc_same_iff"))
        except Exception:
            pass
    return results


def _r0319_Icc_eq_Ioo_same_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc_eq_Ioo_same_iff
    # Icc a b = Ioo a b ↔ ¬a ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OOp("Ioo", (args[0], args[1],)), OOp("not", (args[0],)))), args[1]))
            results.append((rhs, "Mathlib: Set_Icc_eq_Ioo_same_iff"))
        except Exception:
            pass
    return results


def _r0320_Ioo_eq_Icc_same_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioo_eq_Icc_same_iff
    # Ioo a b = Icc a b ↔ ¬a ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OOp("Icc", (args[0], args[1],)), OOp("not", (args[0],)))), args[1]))
            results.append((rhs, "Mathlib: Set_Ioo_eq_Icc_same_iff"))
        except Exception:
            pass
    return results


def _r0321_Ioc_eq_Ico_same_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_eq_Ico_same_iff
    # Ioc a b = Ico a b ↔ ¬a < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("iff", (OOp("Ico", (args[0], args[1],)), OOp("not", (args[0],)))), args[1]))
            results.append((rhs, "Mathlib: Set_Ioc_eq_Ico_same_iff"))
        except Exception:
            pass
    return results


def _r0322_Ioo_eq_Ioc_same_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioo_eq_Ioc_same_iff
    # Ioo a b = Ioc a b ↔ ¬a < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("iff", (OOp("Ioc", (args[0], args[1],)), OOp("not", (args[0],)))), args[1]))
            results.append((rhs, "Mathlib: Set_Ioo_eq_Ioc_same_iff"))
        except Exception:
            pass
    return results


def _r0323_Ioc_eq_Ioo_same_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_eq_Ioo_same_iff
    # Ioc a b = Ioo a b ↔ ¬a < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("iff", (OOp("Ioo", (args[0], args[1],)), OOp("not", (args[0],)))), args[1]))
            results.append((rhs, "Mathlib: Set_Ioc_eq_Ioo_same_iff"))
        except Exception:
            pass
    return results


def _r0324_Iio_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iio_def
    # { x | x < a } = Iio a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pipe_x_lt_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Iio", (OVar("a"),))
            results.append((rhs, "Mathlib: Set_Iio_def"))
    except Exception:
        pass
    return results


def _r0325_Iic_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iic_def
    # { x | x ≤ b } = Iic b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pipe_x_le_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Iic", (OVar("b"),))
            results.append((rhs, "Mathlib: Set_Iic_def"))
    except Exception:
        pass
    return results


def _r0326_Ioo_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioo_def
    # { x | a < x ∧ x < b } = Ioo a b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pipe_a_lt_x_and_x_lt_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ioo", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_Ioo_def"))
    except Exception:
        pass
    return results


def _r0327_Ico_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico_def
    # { x | a ≤ x ∧ x < b } = Ico a b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pipe_a_le_x_and_x_lt_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ico", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_Ico_def"))
    except Exception:
        pass
    return results


def _r0328_Ioc_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_def
    # { x | a < x ∧ x ≤ b } = Ioc a b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pipe_a_lt_x_and_x_le_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ioc", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_Ioc_def"))
    except Exception:
        pass
    return results


def _r0329_Icc_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc_def
    # { x | a ≤ x ∧ x ≤ b } = Icc a b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pipe_a_le_x_and_x_le_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Icc", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_Icc_def"))
    except Exception:
        pass
    return results


def _r0330_iUnion_Icc_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.iUnion_Icc_right
    # ⋃ b, Icc a b = Ici a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Ici", (args[2],))
            results.append((rhs, "Mathlib: Set_iUnion_Icc_right"))
        except Exception:
            pass
    return results


def _r0331_iUnion_Ioc_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.iUnion_Ioc_right
    # ⋃ b, Ioc a b = Ioi a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Ioi", (args[2],))
            results.append((rhs, "Mathlib: Set_iUnion_Ioc_right"))
        except Exception:
            pass
    return results


def _r0332_iUnion_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.iUnion_Iio
    # ⋃ a : α, Iio a = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 5)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Set_iUnion_Iio"))
        except Exception:
            pass
    return results


def _r0333_iUnion_Ico_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.iUnion_Ico_right
    # ⋃ b, Ico a b = Ici a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Ici", (args[2],))
            results.append((rhs, "Mathlib: Set_iUnion_Ico_right"))
        except Exception:
            pass
    return results


def _r0334_iUnion_Ioo_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.iUnion_Ioo_right
    # ⋃ b, Ioo a b = Ioi a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("Ioi", (args[2],))
            results.append((rhs, "Mathlib: Set_iUnion_Ioo_right"))
        except Exception:
            pass
    return results


def _r0335_preimage_subtype_val_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_subtype_val_Iic
    # (↑) ⁻¹' (Iic a.1) = Iic a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("a"),))
            results.append((rhs, "Mathlib: Set_preimage_subtype_val_Iic"))
        except Exception:
            pass
    return results


def _r0336_preimage_subtype_val_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_subtype_val_Ioi
    # (↑) ⁻¹' (Ioi a.1) = Ioi a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("a"),))
            results.append((rhs, "Mathlib: Set_preimage_subtype_val_Ioi"))
        except Exception:
            pass
    return results


def _r0337_preimage_subtype_val_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_subtype_val_Iio
    # (↑) ⁻¹' (Iio a.1) = Iio a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("a"),))
            results.append((rhs, "Mathlib: Set_preimage_subtype_val_Iio"))
        except Exception:
            pass
    return results


def _r0338_preimage_subtype_val_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_subtype_val_Icc
    # (↑) ⁻¹' (Icc a.1 b) = Icc a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_preimage_subtype_val_Icc"))
        except Exception:
            pass
    return results


def _r0339_preimage_subtype_val_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_subtype_val_Ico
    # (↑) ⁻¹' (Ico a.1 b) = Ico a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_preimage_subtype_val_Ico"))
        except Exception:
            pass
    return results


def _r0340_preimage_subtype_val_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_subtype_val_Ioc
    # (↑) ⁻¹' (Ioc a.1 b) = Ioc a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_preimage_subtype_val_Ioc"))
        except Exception:
            pass
    return results


def _r0341_preimage_subtype_val_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.preimage_subtype_val_Ioo
    # (↑) ⁻¹' (Ioo a.1 b) = Ioo a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_preimage_subtype_val_Ioo"))
        except Exception:
            pass
    return results


def _r0342_image_subtype_val_Ici_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ici_Iio
    # Subtype.val '' Iio b = Ico a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ici_Iio"))
        except Exception:
            pass
    return results


def _r0343_image_subtype_val_Ici_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ici_Ici
    # Subtype.val '' Ici b = Ici b.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ici", (OVar("b_1"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ici_Ici"))
        except Exception:
            pass
    return results


def _r0344_image_subtype_val_Ici_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ici_Ioi
    # Subtype.val '' Ioi b = Ioi b.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("b_1"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ici_Ioi"))
        except Exception:
            pass
    return results


def _r0345_image_subtype_val_Iic_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Iic_Ici
    # Subtype.val '' Ici b = Icc b.1 a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("b_1"), OVar("a"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Iic_Ici"))
        except Exception:
            pass
    return results


def _r0346_image_subtype_val_Iic_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Iic_Ioi
    # Subtype.val '' Ioi b = Ioc b.1 a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("b_1"), OVar("a"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Iic_Ioi"))
        except Exception:
            pass
    return results


def _r0347_image_subtype_val_Iic_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Iic_Iic
    # Subtype.val '' Iic b = Iic b.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("b_1"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Iic_Iic"))
        except Exception:
            pass
    return results


def _r0348_image_subtype_val_Iic_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Iic_Iio
    # Subtype.val '' Iio b = Iio b.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("b_1"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Iic_Iio"))
        except Exception:
            pass
    return results


def _r0349_image_subtype_val_Ioi_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioi_Ici
    # Subtype.val '' Ici b = Ici b.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ici", (OVar("b_1"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioi_Ici"))
        except Exception:
            pass
    return results


def _r0350_image_subtype_val_Ioi_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioi_Iic
    # Subtype.val '' Iic b = Ioc a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioi_Iic"))
        except Exception:
            pass
    return results


def _r0351_image_subtype_val_Ioi_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioi_Ioi
    # Subtype.val '' Ioi b = Ioi b.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OVar("b_1"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioi_Ioi"))
        except Exception:
            pass
    return results


def _r0352_image_subtype_val_Ioi_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioi_Iio
    # Subtype.val '' Iio b = Ioo a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioi_Iio"))
        except Exception:
            pass
    return results


def _r0353_image_subtype_val_Iio_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Iio_Ici
    # Subtype.val '' Ici b = Ico b.1 a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("b_1"), OVar("a"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Iio_Ici"))
        except Exception:
            pass
    return results


def _r0354_image_subtype_val_Iio_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Iio_Iic
    # Subtype.val '' Iic b = Iic b.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Iic", (OVar("b_1"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Iio_Iic"))
        except Exception:
            pass
    return results


def _r0355_image_subtype_val_Iio_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Iio_Ioi
    # Subtype.val '' Ioi b = Ioo b.1 a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("b_1"), OVar("a"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Iio_Ioi"))
        except Exception:
            pass
    return results


def _r0356_image_subtype_val_Iio_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Iio_Iio
    # Subtype.val '' Iio b = Iio b.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Iio", (OVar("b_1"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Iio_Iio"))
        except Exception:
            pass
    return results


def _r0357_image_subtype_val_Icc_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Icc_Ici
    # Subtype.val '' Ici c = Icc c.1 b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("c_1"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Icc_Ici"))
        except Exception:
            pass
    return results


def _r0358_image_subtype_val_Icc_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Icc_Iic
    # Subtype.val '' Iic c = Icc a c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Icc_Iic"))
        except Exception:
            pass
    return results


def _r0359_image_subtype_val_Icc_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Icc_Ioi
    # Subtype.val '' Ioi c = Ioc c.1 b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("c_1"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Icc_Ioi"))
        except Exception:
            pass
    return results


def _r0360_image_subtype_val_Icc_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Icc_Iio
    # Subtype.val '' Iio c = Ico a c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Icc_Iio"))
        except Exception:
            pass
    return results


def _r0361_image_subtype_val_Ico_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ico_Ici
    # Subtype.val '' Ici c = Ico c.1 b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("c_1"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ico_Ici"))
        except Exception:
            pass
    return results


def _r0362_image_subtype_val_Ico_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ico_Iic
    # Subtype.val '' Iic c = Icc a c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ico_Iic"))
        except Exception:
            pass
    return results


def _r0363_image_subtype_val_Ico_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ico_Ioi
    # Subtype.val '' Ioi c = Ioo c.1 b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("c_1"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ico_Ioi"))
        except Exception:
            pass
    return results


def _r0364_image_subtype_val_Ico_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ico_Iio
    # Subtype.val '' Iio c = Ico a c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ico_Iio"))
        except Exception:
            pass
    return results


def _r0365_image_subtype_val_Ioc_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioc_Ici
    # Subtype.val '' Ici c = Icc c.1 b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("c_1"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioc_Ici"))
        except Exception:
            pass
    return results


def _r0366_image_subtype_val_Ioc_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioc_Iic
    # Subtype.val '' Iic c = Ioc a c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioc_Iic"))
        except Exception:
            pass
    return results


def _r0367_image_subtype_val_Ioc_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioc_Ioi
    # Subtype.val '' Ioi c = Ioc c.1 b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("c_1"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioc_Ioi"))
        except Exception:
            pass
    return results


def _r0368_image_subtype_val_Ioc_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioc_Iio
    # Subtype.val '' Iio c = Ioo a c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioc_Iio"))
        except Exception:
            pass
    return results


def _r0369_image_subtype_val_Ioo_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioo_Ici
    # Subtype.val '' Ici c = Ico c.1 b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("c_1"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioo_Ici"))
        except Exception:
            pass
    return results


def _r0370_image_subtype_val_Ioo_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioo_Iic
    # Subtype.val '' Iic c = Ioc a c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioo_Iic"))
        except Exception:
            pass
    return results


def _r0371_image_subtype_val_Ioo_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioo_Ioi
    # Subtype.val '' Ioi c = Ioo c.1 b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("c_1"), OVar("b"),))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioo_Ioi"))
        except Exception:
            pass
    return results


def _r0372_image_subtype_val_Ioo_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.image_subtype_val_Ioo_Iio
    # Subtype.val '' Iio c = Ioo a c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subtype_val", 3)
    if args is not None:
        try:
            rhs = OOp("Ioo", (OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Set_image_subtype_val_Ioo_Iio"))
        except Exception:
            pass
    return results


def _r0373_compl_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_Iio
    # (Iio a)ᶜ = Ici a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Iio_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ici", (OVar("a"),))
            results.append((rhs, "Mathlib: Set_compl_Iio"))
    except Exception:
        pass
    return results


def _r0374_Ici_diff_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ici_diff_Ici
    # Ici a \\ Ici b = Ico a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ici", 4)
    if args is not None:
        try:
            rhs = OOp("Ico", (args[0], args[3],))
            results.append((rhs, "Mathlib: Set_Ici_diff_Ici"))
        except Exception:
            pass
    return results


def _r0375_Ici_diff_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ici_diff_Ioi
    # Ici a \\ Ioi b = Icc a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ici", 4)
    if args is not None:
        try:
            rhs = OOp("Icc", (args[0], args[3],))
            results.append((rhs, "Mathlib: Set_Ici_diff_Ioi"))
        except Exception:
            pass
    return results


def _r0376_Ioi_diff_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioi_diff_Ioi
    # Ioi a \\ Ioi b = Ioc a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioi", 4)
    if args is not None:
        try:
            rhs = OOp("Ioc", (args[0], args[3],))
            results.append((rhs, "Mathlib: Set_Ioi_diff_Ioi"))
        except Exception:
            pass
    return results


def _r0377_Ioi_diff_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioi_diff_Ici
    # Ioi a \\ Ici b = Ioo a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioi", 4)
    if args is not None:
        try:
            rhs = OOp("Ioo", (args[0], args[3],))
            results.append((rhs, "Mathlib: Set_Ioi_diff_Ici"))
        except Exception:
            pass
    return results


def _r0378_Iio_union_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iio_union_Ici
    # Iio a ∪ Ici a = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Set_Iio_union_Ici"))
        except Exception:
            pass
    return results


def _r0379_Iic_union_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iic_union_Ioi
    # Iic a ∪ Ioi a = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Set_Iic_union_Ioi"))
        except Exception:
            pass
    return results


def _r0380_Iio_union_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iio_union_Ioi
    # Iio a ∪ Ioi a = {a}ᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Set_Iio_union_Ioi"))
        except Exception:
            pass
    return results


def _r0381_Ico_union_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico_union_Ici
    # Ico a b ∪ Ici c = Ici (min a c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("Ici", (OOp("min", (OVar("a"), OVar("c"),)),))
            results.append((rhs, "Mathlib: Set_Ico_union_Ici"))
        except Exception:
            pass
    return results


def _r0382_Ioc_union_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_union_Ioi
    # Ioc a b ∪ Ioi c = Ioi (min a c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("Ioi", (OOp("min", (OVar("a"), OVar("c"),)),))
            results.append((rhs, "Mathlib: Set_Ioc_union_Ioi"))
        except Exception:
            pass
    return results


def _r0383_Icc_union_Ici(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Icc_union_Ici
    # Icc a b ∪ Ici c = Ici (min a c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("Ici", (OOp("min", (OVar("a"), OVar("c"),)),))
            results.append((rhs, "Mathlib: Set_Icc_union_Ici"))
        except Exception:
            pass
    return results


def _r0384_Ico_inter_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico_inter_Ico
    # Ico a₁ b₁ ∩ Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("a_1", (OVar("_unknown"), OVar("a_2"),)), OOp("b_1", (OVar("_unknown"), OVar("b_2"),)),))
            results.append((rhs, "Mathlib: Set_Ico_inter_Ico"))
        except Exception:
            pass
    return results


def _r0385_Ioc_diff_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_diff_Ioi
    # Ioc a b \\ Ioi c = Ioc a (min b c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc", 5)
    if args is not None:
        try:
            rhs = OOp("Ioc", (args[0], OOp("min", (args[1], args[4],)),))
            results.append((rhs, "Mathlib: Set_Ioc_diff_Ioi"))
        except Exception:
            pass
    return results


def _r0386_Ioc_inter_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_inter_Ioi
    # Ioc a b ∩ Ioi c = Ioc (a ⊔ c) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("a", (OVar("_unknown"), OVar("c"),)), OVar("b"),))
            results.append((rhs, "Mathlib: Set_Ioc_inter_Ioi"))
        except Exception:
            pass
    return results


def _r0387_Ico_inter_Iio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ico_inter_Iio
    # Ico a b ∩ Iio c = Ico a (min b c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("a"), OOp("min", (OVar("b"), OVar("c"),)),))
            results.append((rhs, "Mathlib: Set_Ico_inter_Iio"))
        except Exception:
            pass
    return results


def _r0388_Ioc_diff_Iic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_diff_Iic
    # Ioc a b \\ Iic c = Ioc (max a c) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc", 5)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("max", (args[0], args[4],)), args[1],))
            results.append((rhs, "Mathlib: Set_Ioc_diff_Iic"))
        except Exception:
            pass
    return results


def _r0389_compl_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.compl_Ioc
    # (Ioc a b)ᶜ = Iic a ∪ Ioi b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Ioc_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OOp("Iic", (OVar("a"),)), OOp("Ioi", (OVar("b"),))))
            results.append((rhs, "Mathlib: Set_compl_Ioc"))
    except Exception:
        pass
    return results


def _r0390_Iic_diff_Ioc_self_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Iic_diff_Ioc_self_of_le
    # Iic b \\ Ioc a b = Iic a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iic", 5)
    if args is not None:
        try:
            rhs = OOp("Iic", (args[3],))
            results.append((rhs, "Mathlib: Set_Iic_diff_Ioc_self_of_le"))
        except Exception:
            pass
    return results


def _r0391_Ioc_union_Ioc_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_union_Ioc_left
    # Ioc a c ∪ Ioc b c = Ioc (min a b) c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("min", (OVar("a"), OVar("b"),)), OVar("c"),))
            results.append((rhs, "Mathlib: Set_Ioc_union_Ioc_left"))
        except Exception:
            pass
    return results


def _r0392_Ioc_union_Ioc_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_union_Ioc_symm
    # Ioc a b ∪ Ioc b a = Ioc (min a b) (max a b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("min", (OVar("a"), OVar("b"),)), OOp("max", (OVar("a"), OVar("b"),)),))
            results.append((rhs, "Mathlib: Set_Ioc_union_Ioc_symm"))
        except Exception:
            pass
    return results


def _r0393_Ioc_union_Ioc_union_Ioc_cycle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.Ioc_union_Ioc_union_Ioc_cycle
    # Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc (min a (min b c)) (max a (max b c))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("Ioc", (OOp("min", (OVar("a"), OOp("min", (OVar("b"), OVar("c"),)),)), OOp("max", (OVar("a"), OOp("max", (OVar("b"), OVar("c"),)),)),))
            results.append((rhs, "Mathlib: Set_Ioc_union_Ioc_union_Ioc_cycle"))
        except Exception:
            pass
    return results


def _r0394_ncard_Ico_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ncard_Ico_nat
    # (Ico a b).ncard = b - a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Ico_a_b_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("b"), OVar("a")))
            results.append((rhs, "Mathlib: Set_ncard_Ico_nat"))
    except Exception:
        pass
    return results


def _r0395_ncard_Ioc_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ncard_Ioc_nat
    # (Ioc a b).ncard = b - a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Ioc_a_b_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("b"), OVar("a")))
            results.append((rhs, "Mathlib: Set_ncard_Ioc_nat"))
    except Exception:
        pass
    return results


def _r0396_ncard_Ioo_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ncard_Ioo_nat
    # (Ioo a b).ncard = b - a - 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Ioo_a_b_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("b"), OOp("-", (OVar("a"), OLit(1)))))
            results.append((rhs, "Mathlib: Set_ncard_Ioo_nat"))
    except Exception:
        pass
    return results


def _r0397_ncard_uIcc_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ncard_uIcc_nat
    # (uIcc a b).ncard = (b - a : ℤ).natAbs + 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("uIcc_a_b_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("b_minus_a_colon_natAbs"), OLit(1)))
            results.append((rhs, "Mathlib: Set_ncard_uIcc_nat"))
    except Exception:
        pass
    return results


def _r0398_ncard_Iic_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ncard_Iic_nat
    # (Iic b).ncard = b + 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Iic_b_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("b"), OLit(1)))
            results.append((rhs, "Mathlib: Set_ncard_Iic_nat"))
    except Exception:
        pass
    return results


def _r0399_ncard_Iio_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Set.ncard_Iio_nat
    # (Iio b).ncard = b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Iio_b_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b")
            results.append((rhs, "Mathlib: Set_ncard_Iio_nat"))
    except Exception:
        pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_set_basic rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("+", "<", "A", "D_bsl_E", "D_inter_E", "Disjoint", "ENat_card", "EqOn", "Icc", "Ici", "Ico", "Iic", "Iio", "Ioc", "Ioi", "Ioo", "IsCover", "IsEmpty", "R", "R_S", "R_image", "R_inv_preimage", "R_preimage", "Set_EqOn", "Set_image_f_s_H_symm", "Set_inclusion", "Set_ite", "Set_rangeFactorization", "Sigma_mk", "Star_star", "Subtype_val", "_0", "_0_T", "_0_h", "_1_colon_Set_a_image", "_1_h", "_unknown", "a", "a_colon_Set_a", "a_i", "accumulate", "at_univ_i_sigma", "b", "bot", "cod", "comp", "core", "dissipate", "dom", "empty",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_set_basic axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_set_basic rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_coe_ofNat(term, ctx))
    results.extend(_r0001_coe_mul(term, ctx))
    results.extend(_r0002_coe_pow(term, ctx))
    results.extend(_r0003_centralizer_prod(term, ctx))
    results.extend(_r0004_image_one(term, ctx))
    results.extend(_r0005_subset_one_iff_eq(term, ctx))
    results.extend(_r0006_image_op_one(term, ctx))
    results.extend(_r0007_sInter_inv(term, ctx))
    results.extend(_r0008_iUnion_inv(term, ctx))
    results.extend(_r0009_sUnion_inv(term, ctx))
    results.extend(_r0010_image_smul_prod(term, ctx))
    results.extend(_r0011_smul_empty(term, ctx))
    results.extend(_r0012_smul_eq_empty(term, ctx))
    results.extend(_r0013_singleton_smul(term, ctx))
    results.extend(_r0014_singleton_smul_singleton(term, ctx))
    results.extend(_r0015_mulIndicator_apply(term, ctx))
    results.extend(_r0016_mulIndicator_of_notMem(term, ctx))
    results.extend(_r0017_mulIndicator_eq_one_or_self(term, ctx))
    results.extend(_r0018_mulIndicator_range_comp(term, ctx))
    results.extend(_r0019_mulIndicator_empty(term, ctx))
    results.extend(_r0020_coe_one(term, ctx))
    results.extend(_r0021_mk_zero(term, ctx))
    results.extend(_r0022_mk_one(term, ctx))
    results.extend(_r0023_coe_eq_zero(term, ctx))
    results.extend(_r0024_coe_pow(term, ctx))
    results.extend(_r0025_mk_zero(term, ctx))
    results.extend(_r0026_coe_eq_zero(term, ctx))
    results.extend(_r0027_mk_one(term, ctx))
    results.extend(_r0028_coe_eq_one(term, ctx))
    results.extend(_r0029_coe_pow(term, ctx))
    results.extend(_r0030_image_add_const_Ioi(term, ctx))
    results.extend(_r0031_image_add_const_Icc(term, ctx))
    results.extend(_r0032_image_add_const_Ico(term, ctx))
    results.extend(_r0033_image_add_const_Ioc(term, ctx))
    results.extend(_r0034_image_add_const_Ioo(term, ctx))
    results.extend(_r0035_image_const_add_Ioi(term, ctx))
    results.extend(_r0036_image_const_add_Icc(term, ctx))
    results.extend(_r0037_image_const_add_Ico(term, ctx))
    results.extend(_r0038_image_const_add_Ioc(term, ctx))
    results.extend(_r0039_image_const_add_Ioo(term, ctx))
    results.extend(_r0040_smul_neg(term, ctx))
    results.extend(_r0041_star_univ(term, ctx))
    results.extend(_r0042_image_star(term, ctx))
    results.extend(_r0043_union_star(term, ctx))
    results.extend(_r0044_iInter_star(term, ctx))
    results.extend(_r0045_iUnion_star(term, ctx))
    results.extend(_r0046_compl_star(term, ctx))
    results.extend(_r0047_sized_singleton(term, ctx))
    results.extend(_r0048_inv_inv(term, ctx))
    results.extend(_r0049_inv_empty(term, ctx))
    results.extend(_r0050_inv_univ(term, ctx))
    results.extend(_r0051_cod_empty(term, ctx))
    results.extend(_r0052_dom_eq_empty_iff(term, ctx))
    results.extend(_r0053_cod_eq_empty_iff(term, ctx))
    results.extend(_r0054_dom_univ(term, ctx))
    results.extend(_r0055_cod_univ(term, ctx))
    results.extend(_r0056_cod_inv(term, ctx))
    results.extend(_r0057_dom_inv(term, ctx))
    results.extend(_r0058_inv_id(term, ctx))
    results.extend(_r0059_comp_assoc(term, ctx))
    results.extend(_r0060_id_comp(term, ctx))
    results.extend(_r0061_inv_comp(term, ctx))
    results.extend(_r0062_comp_empty(term, ctx))
    results.extend(_r0063_empty_comp(term, ctx))
    results.extend(_r0064_comp_univ(term, ctx))
    results.extend(_r0065_univ_comp(term, ctx))
    results.extend(_r0066_comp_iUnion(term, ctx))
    results.extend(_r0067_preimage_inv(term, ctx))
    results.extend(_r0068_preimage_empty_right(term, ctx))
    results.extend(_r0069_image_univ_right(term, ctx))
    results.extend(_r0070_preimage_univ_right(term, ctx))
    results.extend(_r0071_preimage_id(term, ctx))
    results.extend(_r0072_image_comp(term, ctx))
    results.extend(_r0073_preimage_empty_left(term, ctx))
    results.extend(_r0074_image_univ_left(term, ctx))
    results.extend(_r0075_preimage_univ_left(term, ctx))
    results.extend(_r0076_image_eq_cod_of_dom_subset(term, ctx))
    results.extend(_r0077_preimage_eq_dom_of_cod_subset(term, ctx))
    results.extend(_r0078_preimage_inter_cod(term, ctx))
    results.extend(_r0079_core_id(term, ctx))
    results.extend(_r0080_core_comp(term, ctx))
    results.extend(_r0081_inv_eq_self_iff(term, ctx))
    results.extend(_r0082_isCover_empty_right(term, ctx))
    results.extend(_r0083_accumulate_zero_nat(term, ctx))
    results.extend(_r0084_partialSups_eq_accumulate(term, ctx))
    results.extend(_r0085_bot_eq_empty(term, ctx))
    results.extend(_r0086_setOf_false(term, ctx))
    results.extend(_r0087_setOf_bot(term, ctx))
    results.extend(_r0088_subset_empty_iff(term, ctx))
    results.extend(_r0089_eq_empty_iff_forall_notMem(term, ctx))
    results.extend(_r0090_isEmpty_coe_sort(term, ctx))
    results.extend(_r0091_eq_empty_of_isEmpty(term, ctx))
    results.extend(_r0092_setOf_top(term, ctx))
    results.extend(_r0093_univ_eq_empty_iff(term, ctx))
    results.extend(_r0094_univ_subset_iff(term, ctx))
    results.extend(_r0095_union_self(term, ctx))
    results.extend(_r0096_union_empty(term, ctx))
    results.extend(_r0097_empty_union(term, ctx))
    results.extend(_r0098_union_comm(term, ctx))
    results.extend(_r0099_union_eq_right(term, ctx))
    results.extend(_r0100_union_eq_self_of_subset_left(term, ctx))
    results.extend(_r0101_univ_union(term, ctx))
    results.extend(_r0102_inter_empty(term, ctx))
    results.extend(_r0103_empty_inter(term, ctx))
    results.extend(_r0104_inter_comm(term, ctx))
    results.extend(_r0105_inter_eq_left(term, ctx))
    results.extend(_r0106_inter_eq_right(term, ctx))
    results.extend(_r0107_left_eq_inter(term, ctx))
    results.extend(_r0108_right_eq_inter(term, ctx))
    results.extend(_r0109_inter_eq_self_of_subset_left(term, ctx))
    results.extend(_r0110_univ_inter(term, ctx))
    results.extend(_r0111_sep_ext_iff(term, ctx))
    results.extend(_r0112_sep_eq_empty_iff_mem_false(term, ctx))
    results.extend(_r0113_sep_true(term, ctx))
    results.extend(_r0114_sep_inter(term, ctx))
    results.extend(_r0115_sep_and(term, ctx))
    results.extend(_r0116_sep_or(term, ctx))
    results.extend(_r0117_sep_setOf(term, ctx))
    results.extend(_r0118_card_coe_set_eq(term, ctx))
    results.extend(_r0119_encard_eq_coe_toFinset_card(term, ctx))
    results.extend(_r0120_toENat_cardinalMk_subtype(term, ctx))
    results.extend(_r0121_encard_coe_eq_coe_finsetCard(term, ctx))
    results.extend(_r0122_encard_eq(term, ctx))
    results.extend(_r0123_encard_eq_zero(term, ctx))
    results.extend(_r0124_encard_empty(term, ctx))
    results.extend(_r0125_encard_union_eq(term, ctx))
    results.extend(_r0126_encard_eq_top_iff(term, ctx))
    results.extend(_r0127_encard_lt_one(term, ctx))
    results.extend(_r0128_encard_diff_add_encard_inter(term, ctx))
    results.extend(_r0129_univ_disjoint(term, ctx))
    results.extend(_r0130_disjoint_univ(term, ctx))
    results.extend(_r0131_dissipate_zero_nat(term, ctx))
    results.extend(_r0132_coe_toFinset(term, ctx))
    results.extend(_r0133_toFinset_empty(term, ctx))
    results.extend(_r0134_eqOn_singleton(term, ctx))
    results.extend(_r0135_eqOn_univ(term, ctx))
    results.extend(_r0136_seq_eq_set_seq(term, ctx))
    results.extend(_r0137_seqLeft_def(term, ctx))
    results.extend(_r0138_seqRight_def(term, ctx))
    results.extend(_r0139_pure_def(term, ctx))
    results.extend(_r0140_failure_def(term, ctx))
    results.extend(_r0141_orElse_def(term, ctx))
    results.extend(_r0142_preimage_congr(term, ctx))
    results.extend(_r0143_preimage_union(term, ctx))
    results.extend(_r0144_preimage_compl(term, ctx))
    results.extend(_r0145_preimage_diff(term, ctx))
    results.extend(_r0146_preimage_ite(term, ctx))
    results.extend(_r0147_preimage_id(term, ctx))
    results.extend(_r0148_preimage_const_of_mem(term, ctx))
    results.extend(_r0149_preimage_const_of_notMem(term, ctx))
    results.extend(_r0150_preimage_const(term, ctx))
    results.extend(_r0151_preimage_singleton_false(term, ctx))
    results.extend(_r0152_inclusion_right(term, ctx))
    results.extend(_r0153_val_comp_inclusion(term, ctx))
    results.extend(_r0154_insert_eq_of_mem(term, ctx))
    results.extend(_r0155_singleton_subset_singleton(term, ctx))
    results.extend(_r0156_union_singleton(term, ctx))
    results.extend(_r0157_singleton_inter_eq_empty(term, ctx))
    results.extend(_r0158_inter_singleton_eq_empty(term, ctx))
    results.extend(_r0159_singleton_inter_of_mem(term, ctx))
    results.extend(_r0160_inter_singleton_of_mem(term, ctx))
    results.extend(_r0161_subset_singleton_iff(term, ctx))
    results.extend(_r0162_subset_singleton_iff_eq(term, ctx))
    results.extend(_r0163_insert_inj(term, ctx))
    results.extend(_r0164_inter_insert_of_mem(term, ctx))
    results.extend(_r0165_image_uncurry_prod(term, ctx))
    results.extend(_r0166_image2_mk_eq_prod(term, ctx))
    results.extend(_r0167_image2_curry(term, ctx))
    results.extend(_r0168_image2_empty_right(term, ctx))
    results.extend(_r0169_image2_singleton_right(term, ctx))
    results.extend(_r0170_image2_singleton(term, ctx))
    results.extend(_r0171_image2_insert_right(term, ctx))
    results.extend(_r0172_image2_congr(term, ctx))
    results.extend(_r0173_image2_right(term, ctx))
    results.extend(_r0174_image2_range(term, ctx))
    results.extend(_r0175_diff_eq(term, ctx))
    results.extend(_r0176_rangeFactorization_eq_rangeFactorization(term, ctx))
    results.extend(_r0177_op_unop(term, ctx))
    results.extend(_r0178_unop_op(term, ctx))
    results.extend(_r0179_singleton_op(term, ctx))
    results.extend(_r0180_piecewise_eq_of_notMem(term, ctx))
    results.extend(_r0181_piecewise_singleton(term, ctx))
    results.extend(_r0182_piecewise_compl(term, ctx))
    results.extend(_r0183_piecewise_range_comp(term, ctx))
    results.extend(_r0184_ncard_eq(term, ctx))
    results.extend(_r0185_singleton_prod(term, ctx))
    results.extend(_r0186_union_prod(term, ctx))
    results.extend(_r0187_mk_preimage_prod_right(term, ctx))
    results.extend(_r0188_mk_preimage_prod_left_eq_empty(term, ctx))
    results.extend(_r0189_mk_preimage_prod_right_eq_empty(term, ctx))
    results.extend(_r0190_mk_preimage_prod_left_eq_if(term, ctx))
    results.extend(_r0191_image_swap_prod(term, ctx))
    results.extend(_r0192_prod_range_univ_eq(term, ctx))
    results.extend(_r0193_prod_eq_empty_iff(term, ctx))
    results.extend(_r0194_offDiag_eq_empty(term, ctx))
    results.extend(_r0195_offDiag_singleton(term, ctx))
    results.extend(_r0196_offDiag_univ(term, ctx))
    results.extend(_r0197_prod_sdiff_diagonal(term, ctx))
    results.extend(_r0198_offDiag_inter(term, ctx))
    results.extend(_r0199_graphOn_empty(term, ctx))
    results.extend(_r0200_graphOn_eq_empty(term, ctx))
    results.extend(_r0201_graphOn_union(term, ctx))
    results.extend(_r0202_graphOn_singleton(term, ctx))
    results.extend(_r0203_graphOn_insert(term, ctx))
    results.extend(_r0204_image_snd_graphOn(term, ctx))
    results.extend(_r0205_graphOn_comp(term, ctx))
    results.extend(_r0206_graphOn_prod_graphOn(term, ctx))
    results.extend(_r0207_restrict_apply(term, ctx))
    results.extend(_r0208_restrict_eq_iff(term, ctx))
    results.extend(_r0209_image_restrict(term, ctx))
    results.extend(_r0210_restrict_2_def(term, ctx))
    results.extend(_r0211_surjective_codRestrict(term, ctx))
    results.extend(_r0212_up_down(term, ctx))
    results.extend(_r0213_up_empty(term, ctx))
    results.extend(_r0214_add_def(term, ctx))
    results.extend(_r0215_up_union(term, ctx))
    results.extend(_r0216_up_mul(term, ctx))
    results.extend(_r0217_up_one(term, ctx))
    results.extend(_r0218_preimage_image_sigmaMk_of_ne(term, ctx))
    results.extend(_r0219_empty_sigma(term, ctx))
    results.extend(_r0220_univ_sigma_univ(term, ctx))
    results.extend(_r0221_sigma_univ(term, ctx))
    results.extend(_r0222_univ_sigma_preimage_mk(term, ctx))
    results.extend(_r0223_singleton_sigma(term, ctx))
    results.extend(_r0224_sigma_singleton(term, ctx))
    results.extend(_r0225_singleton_sigma_singleton(term, ctx))
    results.extend(_r0226_sigma_union(term, ctx))
    results.extend(_r0227_sigma_inter_sigma(term, ctx))
    results.extend(_r0228_mk_preimage_sigma_eq_empty(term, ctx))
    results.extend(_r0229_mk_preimage_sigma_eq_if(term, ctx))
    results.extend(_r0230_preimage_val_sInter(term, ctx))
    results.extend(_r0231_image_val_inter(term, ctx))
    results.extend(_r0232_image_val_diff(term, ctx))
    results.extend(_r0233_image_val_compl(term, ctx))
    results.extend(_r0234_image_val_sUnion(term, ctx))
    results.extend(_r0235_image_val_iUnion(term, ctx))
    results.extend(_r0236_image_val_sInter(term, ctx))
    results.extend(_r0237_image_val_union_self_right_eq(term, ctx))
    results.extend(_r0238_image_val_union_self_left_eq(term, ctx))
    results.extend(_r0239_image_val_inter_self_right_eq_coe(term, ctx))
    results.extend(_r0240_image_val_inter_self_left_eq_coe(term, ctx))
    results.extend(_r0241_sups_empty(term, ctx))
    results.extend(_r0242_sups_eq_empty(term, ctx))
    results.extend(_r0243_singleton_sups(term, ctx))
    results.extend(_r0244_sups_singleton(term, ctx))
    results.extend(_r0245_singleton_sups_singleton(term, ctx))
    results.extend(_r0246_sep_sups_le(term, ctx))
    results.extend(_r0247_sups_assoc(term, ctx))
    results.extend(_r0248_inter_symmDiff_distrib_left(term, ctx))
    results.extend(_r0249_iUnionLift_inclusion(term, ctx))
    results.extend(_r0250_ker_apply_mk_out(term, ctx))
    results.extend(_r0251_bot_def(term, ctx))
    results.extend(_r0252_mk_eq_top(term, ctx))
    results.extend(_r0253_mk_eq_bot(term, ctx))
    results.extend(_r0254_eq_top_iff(term, ctx))
    results.extend(_r0255_sym2_empty(term, ctx))
    results.extend(_r0256_sym2_univ(term, ctx))
    results.extend(_r0257_sym2_singleton(term, ctx))
    results.extend(_r0258_sym2_insert(term, ctx))
    results.extend(_r0259_mk_smul_mk(term, ctx))
    results.extend(_r0260_smul_def(term, ctx))
    results.extend(_r0261_image_symm_apply(term, ctx))
    results.extend(_r0262_preimage_comp(term, ctx))
    results.extend(_r0263_compl_inter_self(term, ctx))
    results.extend(_r0264_compl_empty(term, ctx))
    results.extend(_r0265_compl_union(term, ctx))
    results.extend(_r0266_compl_inter(term, ctx))
    results.extend(_r0267_compl_empty_iff(term, ctx))
    results.extend(_r0268_compl_univ_iff(term, ctx))
    results.extend(_r0269_compl_union_self(term, ctx))
    results.extend(_r0270_compl_singleton_eq(term, ctx))
    results.extend(_r0271_union_diff_right(term, ctx))
    results.extend(_r0272_union_diff_distrib(term, ctx))
    results.extend(_r0273_inter_union_diff(term, ctx))
    results.extend(_r0274_diff_union_inter(term, ctx))
    results.extend(_r0275_diff_eq_empty(term, ctx))
    results.extend(_r0276_diff_univ(term, ctx))
    results.extend(_r0277_diff_diff(term, ctx))
    results.extend(_r0278_diff_union_self(term, ctx))
    results.extend(_r0279_diff_inter_self(term, ctx))
    results.extend(_r0280_diff_inter_self_eq_diff(term, ctx))
    results.extend(_r0281_diff_self_inter(term, ctx))
    results.extend(_r0282_diff_self(term, ctx))
    results.extend(_r0283_insert_diff_of_notMem(term, ctx))
    results.extend(_r0284_insert_diff_singleton_comm(term, ctx))
    results.extend(_r0285_ite_compl(term, ctx))
    results.extend(_r0286_ite_inter_compl_self(term, ctx))
    results.extend(_r0287_ite_diff_self(term, ctx))
    results.extend(_r0288_ite_same(term, ctx))
    results.extend(_r0289_ite_left(term, ctx))
    results.extend(_r0290_ite_right(term, ctx))
    results.extend(_r0291_ite_empty(term, ctx))
    results.extend(_r0292_ite_univ(term, ctx))
    results.extend(_r0293_ite_empty_left(term, ctx))
    results.extend(_r0294_ite_empty_right(term, ctx))
    results.extend(_r0295_coe_iSup(term, ctx))
    results.extend(_r0296_coe_biSup(term, ctx))
    results.extend(_r0297_coe_iInf(term, ctx))
    results.extend(_r0298_coe_biInf(term, ctx))
    results.extend(_r0299_exists_set_insert(term, ctx))
    results.extend(_r0300_toFinset_Ico(term, ctx))
    results.extend(_r0301_toFinset_Ioo(term, ctx))
    results.extend(_r0302_Iic_toDual(term, ctx))
    results.extend(_r0303_Icc_toDual(term, ctx))
    results.extend(_r0304_Ico_toDual(term, ctx))
    results.extend(_r0305_Ioo_toDual(term, ctx))
    results.extend(_r0306_Iio_ofDual(term, ctx))
    results.extend(_r0307_Iic_ofDual(term, ctx))
    results.extend(_r0308_Icc_ofDual(term, ctx))
    results.extend(_r0309_Ico_ofDual(term, ctx))
    results.extend(_r0310_Ioo_ofDual(term, ctx))
    results.extend(_r0311_Ico_eq_empty(term, ctx))
    results.extend(_r0312_Ioo_eq_empty(term, ctx))
    results.extend(_r0313_Icc_eq_empty_of_lt(term, ctx))
    results.extend(_r0314_Ico_eq_empty_of_le(term, ctx))
    results.extend(_r0315_Ioo_eq_empty_of_le(term, ctx))
    results.extend(_r0316_Ico_self(term, ctx))
    results.extend(_r0317_Iic_inter_Ioc_of_le(term, ctx))
    results.extend(_r0318_Ioc_eq_Icc_same_iff(term, ctx))
    results.extend(_r0319_Icc_eq_Ioo_same_iff(term, ctx))
    results.extend(_r0320_Ioo_eq_Icc_same_iff(term, ctx))
    results.extend(_r0321_Ioc_eq_Ico_same_iff(term, ctx))
    results.extend(_r0322_Ioo_eq_Ioc_same_iff(term, ctx))
    results.extend(_r0323_Ioc_eq_Ioo_same_iff(term, ctx))
    results.extend(_r0324_Iio_def(term, ctx))
    results.extend(_r0325_Iic_def(term, ctx))
    results.extend(_r0326_Ioo_def(term, ctx))
    results.extend(_r0327_Ico_def(term, ctx))
    results.extend(_r0328_Ioc_def(term, ctx))
    results.extend(_r0329_Icc_def(term, ctx))
    results.extend(_r0330_iUnion_Icc_right(term, ctx))
    results.extend(_r0331_iUnion_Ioc_right(term, ctx))
    results.extend(_r0332_iUnion_Iio(term, ctx))
    results.extend(_r0333_iUnion_Ico_right(term, ctx))
    results.extend(_r0334_iUnion_Ioo_right(term, ctx))
    results.extend(_r0335_preimage_subtype_val_Iic(term, ctx))
    results.extend(_r0336_preimage_subtype_val_Ioi(term, ctx))
    results.extend(_r0337_preimage_subtype_val_Iio(term, ctx))
    results.extend(_r0338_preimage_subtype_val_Icc(term, ctx))
    results.extend(_r0339_preimage_subtype_val_Ico(term, ctx))
    results.extend(_r0340_preimage_subtype_val_Ioc(term, ctx))
    results.extend(_r0341_preimage_subtype_val_Ioo(term, ctx))
    results.extend(_r0342_image_subtype_val_Ici_Iio(term, ctx))
    results.extend(_r0343_image_subtype_val_Ici_Ici(term, ctx))
    results.extend(_r0344_image_subtype_val_Ici_Ioi(term, ctx))
    results.extend(_r0345_image_subtype_val_Iic_Ici(term, ctx))
    results.extend(_r0346_image_subtype_val_Iic_Ioi(term, ctx))
    results.extend(_r0347_image_subtype_val_Iic_Iic(term, ctx))
    results.extend(_r0348_image_subtype_val_Iic_Iio(term, ctx))
    results.extend(_r0349_image_subtype_val_Ioi_Ici(term, ctx))
    results.extend(_r0350_image_subtype_val_Ioi_Iic(term, ctx))
    results.extend(_r0351_image_subtype_val_Ioi_Ioi(term, ctx))
    results.extend(_r0352_image_subtype_val_Ioi_Iio(term, ctx))
    results.extend(_r0353_image_subtype_val_Iio_Ici(term, ctx))
    results.extend(_r0354_image_subtype_val_Iio_Iic(term, ctx))
    results.extend(_r0355_image_subtype_val_Iio_Ioi(term, ctx))
    results.extend(_r0356_image_subtype_val_Iio_Iio(term, ctx))
    results.extend(_r0357_image_subtype_val_Icc_Ici(term, ctx))
    results.extend(_r0358_image_subtype_val_Icc_Iic(term, ctx))
    results.extend(_r0359_image_subtype_val_Icc_Ioi(term, ctx))
    results.extend(_r0360_image_subtype_val_Icc_Iio(term, ctx))
    results.extend(_r0361_image_subtype_val_Ico_Ici(term, ctx))
    results.extend(_r0362_image_subtype_val_Ico_Iic(term, ctx))
    results.extend(_r0363_image_subtype_val_Ico_Ioi(term, ctx))
    results.extend(_r0364_image_subtype_val_Ico_Iio(term, ctx))
    results.extend(_r0365_image_subtype_val_Ioc_Ici(term, ctx))
    results.extend(_r0366_image_subtype_val_Ioc_Iic(term, ctx))
    results.extend(_r0367_image_subtype_val_Ioc_Ioi(term, ctx))
    results.extend(_r0368_image_subtype_val_Ioc_Iio(term, ctx))
    results.extend(_r0369_image_subtype_val_Ioo_Ici(term, ctx))
    results.extend(_r0370_image_subtype_val_Ioo_Iic(term, ctx))
    results.extend(_r0371_image_subtype_val_Ioo_Ioi(term, ctx))
    results.extend(_r0372_image_subtype_val_Ioo_Iio(term, ctx))
    results.extend(_r0373_compl_Iio(term, ctx))
    results.extend(_r0374_Ici_diff_Ici(term, ctx))
    results.extend(_r0375_Ici_diff_Ioi(term, ctx))
    results.extend(_r0376_Ioi_diff_Ioi(term, ctx))
    results.extend(_r0377_Ioi_diff_Ici(term, ctx))
    results.extend(_r0378_Iio_union_Ici(term, ctx))
    results.extend(_r0379_Iic_union_Ioi(term, ctx))
    results.extend(_r0380_Iio_union_Ioi(term, ctx))
    results.extend(_r0381_Ico_union_Ici(term, ctx))
    results.extend(_r0382_Ioc_union_Ioi(term, ctx))
    results.extend(_r0383_Icc_union_Ici(term, ctx))
    results.extend(_r0384_Ico_inter_Ico(term, ctx))
    results.extend(_r0385_Ioc_diff_Ioi(term, ctx))
    results.extend(_r0386_Ioc_inter_Ioi(term, ctx))
    results.extend(_r0387_Ico_inter_Iio(term, ctx))
    results.extend(_r0388_Ioc_diff_Iic(term, ctx))
    results.extend(_r0389_compl_Ioc(term, ctx))
    results.extend(_r0390_Iic_diff_Ioc_self_of_le(term, ctx))
    results.extend(_r0391_Ioc_union_Ioc_left(term, ctx))
    results.extend(_r0392_Ioc_union_Ioc_symm(term, ctx))
    results.extend(_r0393_Ioc_union_Ioc_union_Ioc_cycle(term, ctx))
    results.extend(_r0394_ncard_Ico_nat(term, ctx))
    results.extend(_r0395_ncard_Ioc_nat(term, ctx))
    results.extend(_r0396_ncard_Ioo_nat(term, ctx))
    results.extend(_r0397_ncard_uIcc_nat(term, ctx))
    results.extend(_r0398_ncard_Iic_nat(term, ctx))
    results.extend(_r0399_ncard_Iio_nat(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_set_basic rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Set_smul_mem_center", "r_a_in_Set_center_A", "Not an equality or iff proposition"),
    ("Set_smul_mem_centralizer", "r_a_in_s_centralizer", "Not an equality or iff proposition"),
    ("Set_algebraMap_mem_center", "algebraMap_R_A_r_in_Set_center_A", "Not an equality or iff proposition"),
    ("Set_algebraMap_mem_centralizer", "algebraMap_R_A_r_in_s_centralizer", "Not an equality or iff proposition"),
    ("SetLike_algebraMap_mem_graded", "algebraMap_S_R_s_in_A_0", "Not an equality or iff proposition"),
    ("SetLike_natCast_mem_graded", "n_colon_R_in_A_0", "Not an equality or iff proposition"),
    ("SetLike_intCast_mem_graded", "z_colon_R_in_A_0", "Not an equality or iff proposition"),
    ("SetLike_homogeneous_zero_submodule", "SetLike_IsHomogeneousElem_A_0_colon_R", "Not an equality or iff proposition"),
    ("SetLike_Homogeneous_smul", "SetLike_IsHomogeneousElem_A_s_r", "Not an equality or iff proposition"),
    ("SetLike_one_mem_graded", "_1_colon_R_in_A_0", "Not an equality or iff proposition"),
    ("SetLike_mul_mem_graded", "_unknown", "Empty proposition"),
    ("SetLike_pow_mem_graded", "r_pow_n_in_A_n_i", "Not an equality or iff proposition"),
    ("SetLike_list_prod_map_mem_graded", "l_map_r_prod_in_A_l_map_i_sum", "Not an equality or iff proposition"),
    ("SetLike_list_prod_ofFn_mem_graded", "List_ofFn_r_prod_in_A_List_ofFn_i_sum", "Not an equality or iff proposition"),
    ("SetLike_isHomogeneousElem_coe", "SetLike_IsHomogeneousElem_A_x_colon_R", "Not an equality or iff proposition"),
    ("SetLike_isHomogeneousElem_one", "SetLike_IsHomogeneousElem_A_1_colon_R", "Not an equality or iff proposition"),
    ("SetLike_prod_mem_graded", "k_in_F_g_k_in_A_k_in_F_i_k", "Not an equality or iff proposition"),
    ("SetLike_prod_pow_mem_graded", "k_in_F_g_k_pow_n_k_in_A_k_in_F_n_k_i_k", "Not an equality or iff proposition"),
    ("Set_smul_set_subset_mul", "a_in_s_to_a_t_sub_s_star_t", "Not an equality or iff proposition"),
    ("Set_op_smul_set_subset_mul", "a_in_t_to_s_lt_a_sub_s_star_t", "Not an equality or iff proposition"),
    ("Set_mul_mem_center", "z_1_star_z_2_in_Set_center_M", "Not an equality or iff proposition"),
    ("Set_center_subset_centralizer", "Set_center_M_sub_S_centralizer", "Not an equality or iff proposition"),
    ("Set_centralizer_subset", "centralizer_T_sub_centralizer_S", "Not an equality or iff proposition"),
    ("Set_subset_centralizer_centralizer", "S_sub_S_centralizer_centralizer", "Not an equality or iff proposition"),
    ("Set_prod_centralizer_subset_centralizer_prod", "S_centralizer_times_T_centralizer_sub_S_times_T_centralizer", "Not an equality or iff proposition"),
    ("Set_mulIndicator_mul", "_unknown", "Empty proposition"),
    ("Set_range_one", "Set_range_1_colon_a_to_b_eq_1", "Not an equality or iff proposition"),
    ("Set_preimage_one", "_1_colon_a_to_b_inv_prime_s_eq_if_1_colon_b_in_s_then_Set_univ_else_empty", "Not an equality or iff proposition"),
    ("Set_one_mem_one", "_1_colon_a_in_1_colon_Set_a", "Not an equality or iff proposition"),
    ("Set_one_nonempty", "_1_colon_Set_a_Nonempty", "Not an equality or iff proposition"),
    ("Set_coe_singletonOneHom", "singletonOneHom_colon_a_to_Set_a_eq_singleton", "Not an equality or iff proposition"),
    ("Cardinal_mk_mul_le", "hash_s_star_t_le_hash_s_star_hash_t", "Not an equality or iff proposition"),
    ("Set_natCard_mul_le", "Nat_card_s_star_t_le_Nat_card_s_star_Nat_card_t", "Not an equality or iff proposition"),
    ("Set_finite_one", "_1_colon_Set_a_Finite", "Not an equality or iff proposition"),
    ("Set_smul_mem_smul", "a_in_s_to_b_in_t_to_a_b_in_s_t", "Not an equality or iff proposition"),
    ("Set_Nonempty_smul", "s_Nonempty_to_t_Nonempty_to_s_t_Nonempty", "Not an equality or iff proposition"),
    ("Set_Nonempty_of_smul_left", "s_t_Nonempty_to_s_Nonempty", "Not an equality or iff proposition"),
    ("Set_Nonempty_of_smul_right", "s_t_Nonempty_to_t_Nonempty", "Not an equality or iff proposition"),
    ("Set_smul_subset_smul", "s_1_sub_s_2_to_t_1_sub_t_2_to_s_1_t_1_sub_s_2_t_2", "Not an equality or iff proposition"),
    ("Set_smul_subset_smul_left", "t_1_sub_t_2_to_s_t_1_sub_s_t_2", "Not an equality or iff proposition"),
    ("Set_smul_subset_smul_right", "s_1_sub_s_2_to_s_1_t_sub_s_2_t", "Not an equality or iff proposition"),
    ("Set_inter_smul_subset", "s_1_inter_s_2_t_sub_s_1_t_inter_s_2_t", "Not an equality or iff proposition"),
    ("Set_smul_inter_subset", "s_t_1_inter_t_2_sub_s_t_1_inter_s_t_2", "Not an equality or iff proposition"),
    ("Set_inter_smul_union_subset_union", "s_1_inter_s_2_t_1_union_t_2_sub_s_1_t_1_union_s_2_t_2", "Not an equality or iff proposition"),
    ("Set_union_smul_inter_subset_union", "s_1_union_s_2_t_1_inter_t_2_sub_s_1_t_1_union_s_2_t_2", "Not an equality or iff proposition"),
    ("Set_smul_set_subset_smul", "a_in_s_to_a_t_sub_s_t", "Not an equality or iff proposition"),
    ("Set_IsPWO_submonoid_closure", "IsPWO_Submonoid_closure_s_colon_Set_a", "Not an equality or iff proposition"),
    ("Set_smul_set_pi_0", "_unknown", "Empty proposition"),
    ("Set_smul_zero_subset", "s_0_colon_Set_b_sub_0", "Not an equality or iff proposition"),
    ("Set_zero_mem_smul_set", "_0_colon_b_in_a_t", "Not an equality or iff proposition"),
    ("Set_zero_mem_center", "_0_colon_M_0_in_center_M_0", "Not an equality or iff proposition"),
    ("Set_zero_mem_centralizer", "_0_colon_M_0_in_centralizer_s", "Not an equality or iff proposition"),
    ("Set_mul_zero_subset", "s_star_0_sub_0", "Not an equality or iff proposition"),
    ("Set_zero_mul_subset", "_0_star_s_sub_0", "Not an equality or iff proposition"),
    ("Set_mulIndicator_eq_one", "_unknown", "Empty proposition"),
    ("Set_mem_of_mulIndicator_ne_one", "a_in_s", "Not an equality or iff proposition"),
    ("Set_eqOn_mulIndicator", "EqOn_mulIndicator_s_f_f_s", "Not an equality or iff proposition"),
    ("Set_eqOn_mulIndicator", "_unknown", "Empty proposition"),
    ("Set_mulSupport_mulIndicator_subset", "mulSupport_s_mulIndicator_f_sub_s", "Not an equality or iff proposition"),
    ("Set_mulIndicator_empty", "_unknown", "Empty proposition"),
    ("Set_mulIndicator_one", "_unknown", "Empty proposition"),
    ("Set_mulIndicator_one_preimage", "t_mulIndicator_1_inv_prime_s_in_Set_univ_empty_colon_Set_Set_a", "Not an equality or iff proposition"),
    ("Set_mulIndicator_const_preimage", "U_mulIndicator_fun_eq_gt_a_inv_prime_s_in_Set_univ_U_U_empty_colon_Set_Set_a", "Not an equality or iff proposition"),
    ("Set_mulIndicator_rel_mulIndicator", "r_mulIndicator_s_f_a_mulIndicator_s_g_a", "Not an equality or iff proposition"),
    ("Set_indicator_one_preimage", "U_indicator_1_inv_prime_s_in_Set_univ_U_U_empty_colon_Set_Set_a", "Not an equality or iff proposition"),
    ("Set_mulIndicator_apply_le", "_unknown", "Empty proposition"),
    ("Set_mulIndicator_le", "_unknown", "Empty proposition"),
    ("Set_le_mulIndicator_apply", "y_le_mulIndicator_s_g_a", "Not an equality or iff proposition"),
    ("Set_le_mulIndicator", "f_le_mulIndicator_s_g", "Not an equality or iff proposition"),
    ("Set_Icc_mul_Icc_subset", "_unknown", "Empty proposition"),
    ("Set_Iic_mul_Iic_subset", "_unknown", "Empty proposition"),
    ("Set_Ici_mul_Ici_subset", "_unknown", "Empty proposition"),
    ("Set_Icc_coe_nonneg", "_0_le_x_colon_R", "Not an equality or iff proposition"),
    ("Set_Icc_coe_le_one", "x_colon_R_le_1", "Not an equality or iff proposition"),
    ("Set_Icc_nonneg", "_0_le_t", "Not an equality or iff proposition"),
    ("Set_Icc_le_one", "t_le_1", "Not an equality or iff proposition"),
    ("Set_Icc_mul_le_left", "x_star_y_le_x", "Not an equality or iff proposition"),
    ("Set_Icc_mul_le_right", "x_star_y_le_y", "Not an equality or iff proposition"),
    ("Set_Icc_one_sub_mem", "_1_minus_t_in_Icc_0_colon_b_1", "Not an equality or iff proposition"),
    ("Set_Icc_one_sub_nonneg", "_0_le_1_minus_x_colon_b", "Not an equality or iff proposition"),
    ("Set_Icc_one_sub_le_one", "_1_minus_x_colon_b_le_1", "Not an equality or iff proposition"),
    ("Set_Ico_coe_nonneg", "_0_le_x_colon_R", "Not an equality or iff proposition"),
    ("Set_Ico_coe_lt_one", "x_colon_R_lt_1", "Not an equality or iff proposition"),
    ("Set_Ico_nonneg", "_0_le_t", "Not an equality or iff proposition"),
    ("Set_Ioc_coe_pos", "_0_lt_x_colon_R", "Not an equality or iff proposition"),
    ("Set_Ioc_coe_le_one", "x_colon_R_le_1", "Not an equality or iff proposition"),
    ("Set_Ioc_le_one", "t_le_1", "Not an equality or iff proposition"),
    ("Set_Ioo_pos", "_0_lt_x_colon_R", "Not an equality or iff proposition"),
    ("Set_Ioo_lt_one", "x_colon_R_lt_1", "Not an equality or iff proposition"),
    ("Set_Ioo_one_sub_mem", "_1_minus_t_in_Ioo_0_colon_b_1", "Not an equality or iff proposition"),
    ("Set_Ioo_one_minus_pos", "_0_lt_1_minus_x_colon_b", "Not an equality or iff proposition"),
    ("Set_Ioo_one_minus_lt_one", "_1_minus_x_colon_b_lt_1", "Not an equality or iff proposition"),
    ("Set_Ici_add_bij", "BijOn_plus_d_Ici_a_Ici_a_plus_d", "Not an equality or iff proposition"),
    ("Set_Ioi_add_bij", "BijOn_plus_d_Ioi_a_Ioi_a_plus_d", "Not an equality or iff proposition"),
    ("Set_Icc_add_bij", "BijOn_plus_d_Icc_a_b_Icc_a_plus_d_b_plus_d", "Not an equality or iff proposition"),
    ("Set_Ioo_add_bij", "BijOn_plus_d_Ioo_a_b_Ioo_a_plus_d_b_plus_d", "Not an equality or iff proposition"),
    ("Set_Ioc_add_bij", "BijOn_plus_d_Ioc_a_b_Ioc_a_plus_d_b_plus_d", "Not an equality or iff proposition"),
    ("Set_Ico_add_bij", "BijOn_plus_d_Ico_a_b_Ico_a_plus_d_b_plus_d", "Not an equality or iff proposition"),
    ("Set_OrdConnected_smul", "a_s_OrdConnected", "Not an equality or iff proposition"),
    ("Set_natCast_mem_center", "n_colon_M_in_Set_center_M", "Not an equality or iff proposition"),
    ("Set_ofNat_mem_center", "ofNat_n_in_Set_center_M", "Not an equality or iff proposition"),
    ("Set_intCast_mem_center", "n_colon_M_in_Set_center_M", "Not an equality or iff proposition"),
    ("Set_add_mem_center", "a_plus_b_in_Set_center_M", "Not an equality or iff proposition"),
    ("Set_neg_mem_center", "minus_a_in_Set_center_M", "Not an equality or iff proposition"),
    ("Set_add_mem_centralizer", "a_plus_b_in_centralizer_S", "Not an equality or iff proposition"),
    ("Set_neg_mem_centralizer", "minus_a_in_centralizer_S", "Not an equality or iff proposition"),
    ("Set_mul_add_subset", "s_star_t_plus_u_sub_s_star_t_plus_s_star_u", "Not an equality or iff proposition"),
    ("Set_add_mul_subset", "s_plus_t_star_u_sub_s_star_u_plus_t_star_u", "Not an equality or iff proposition"),
    ("Set_star_mem_center", "star_a_in_Set_center_R", "Not an equality or iff proposition"),
    ("Set_star_mem_centralizer", "_unknown", "Empty proposition"),
    ("Set_star_mem_centralizer", "star_a_in_Set_centralizer_s_union_star_s", "Not an equality or iff proposition"),
    ("Set_Nonempty_star", "s_Nonempty", "Not an equality or iff proposition"),
    ("Set_Finite_star", "s_Finite", "Not an equality or iff proposition"),
    ("Set_star_inv", "_unknown", "Empty proposition"),
    ("Set_InvOn_one_sub_one_add_inv", "Set_InvOn_fun_x_1_minus_1_plus_x_inv_fun_x_x_star_1_minus_x_inv_x_colon_ge_0_pipe_x_lt_1", "Not an equality or iff proposition"),
    ("Set_EqOn_iteratedFDerivWithin", "EqOn_iteratedFDerivWithin_n_f_1_s_iteratedFDerivWithin_n_f_s_s", "Not an equality or iff proposition"),
    ("Set_OrdConnected_image_hasDerivWithinAt", "OrdConnected_f_prime_prime_prime_s", "Not an equality or iff proposition"),
    ("Set_OrdConnected_image_derivWithin", "OrdConnected_derivWithin_f_s_prime_prime_s", "Not an equality or iff proposition"),
    ("Set_OrdConnected_image_deriv", "OrdConnected_deriv_f_prime_prime_s", "Not an equality or iff proposition"),
    ("Set_EqOn_deriv", "s_EqOn_deriv_f_deriv_g", "Not an equality or iff proposition"),
    ("Set_Subsingleton_differentiableOn", "DifferentiableOn_f_s", "Not an equality or iff proposition"),
    ("Set_EqOn_iteratedDeriv_of_isOpen", "Set_EqOn_iteratedDeriv_n_f_iteratedDeriv_n_g_s", "Not an equality or iff proposition"),
    ("Set_Subsingleton_convex", "Convex_s", "Not an equality or iff proposition"),
    ("Set_OrdConnected_convex_of_chain", "Convex_s", "Not an equality or iff proposition"),
    ("Set_OrdConnected_convex", "Convex_s", "Not an equality or iff proposition"),
    ("Set_MapsTo_egauge_le", "egauge_t_f_x_le_egauge_s_x", "Not an equality or iff proposition"),
    ("Set_Nonempty_intrinsicInterior", "intrinsicInterior_s_Nonempty", "Not an equality or iff proposition"),
    ("Set_OrdConnected_starConvex", "StarConvex_x_s", "Not an equality or iff proposition"),
    ("Set_Subsingleton_strictConvex", "StrictConvex_s", "Not an equality or iff proposition"),
    ("Set_OrdConnected_strictConvex", "StrictConvex_s", "Not an equality or iff proposition"),
    ("Set_Finite_isCompact_convexHull", "IsCompact_convexHull_s", "Not an equality or iff proposition"),
    ("Set_Finite_isClosed_convexHull", "IsClosed_convexHull_s", "Not an equality or iff proposition"),
    ("Set_Finite_isVonNBounded", "IsVonNBounded_s", "Not an equality or iff proposition"),
    ("Set_Countable_isPathConnected_compl_of_one_lt_rank", "IsPathConnected_s", "Not an equality or iff proposition"),
    ("Set_Countable_isConnected_compl_of_one_lt_rank", "IsConnected_s", "Not an equality or iff proposition"),
    ("Set_Countable_preimage_circleMap", "circleMap_c_R_inv_prime_s_Countable", "Not an equality or iff proposition"),
    ("Set_Countable_exists_pos_hasSum_le", "exists_e_prime_colon_i_to_forall_i_0_lt_e_prime_i_and_exists_c_HasSum_fun_i_colon_s_e_prime_i_c_and_c_le_e", "Not an equality or iff proposition"),
    ("Set_Countable_exists_pos_forall_sum_le", "exists_e_prime_colon_i_to_forall_i_0_lt_e_prime_i_and_forall_t_colon_Finset_i_t_sub_s_to_i_in_t_e_prime_i_le_e", "Not an equality or iff proposition"),
    ("HasCardinalLT_Set_isFiltered_of_aleph0_le", "IsFiltered_HasCardinalLT_Set_X_k", "Not an equality or iff proposition"),
    ("Set_Subsingleton_threeGPFree", "ThreeGPFree_s", "Not an equality or iff proposition"),
    ("Set_Subsingleton_isCornerFree", "IsCornerFree_A", "Not an equality or iff proposition"),
    ("Set_ruzsa_covering_mul", "exists_F_sub_A_Nat_card_F_le_K_and_A_sub_F_star_B_slash_B_and_F_Finite", "Not an equality or iff proposition"),
    ("Set_Sized_uvCompression", "u_v_colon_Set_Finset_a_Sized_r", "Not an equality or iff proposition"),
    ("Set_Intersecting_mono", "t_Intersecting", "Not an equality or iff proposition"),
    ("Set_Intersecting_bot_notMem", "bot_notin_s", "Not an equality or iff proposition"),
    ("Set_Intersecting_ne_bot", "a_ne_bot", "Not an equality or iff proposition"),
    ("Set_intersecting_empty", "empty_colon_Set_a_Intersecting", "Not an equality or iff proposition"),
    ("Set_Intersecting_insert", "insert_a_s_Intersecting", "Not an equality or iff proposition"),
    ("Set_Intersecting_isUpperSet", "IsUpperSet_s", "Not an equality or iff proposition"),
    ("Set_Intersecting_isUpperSet", "_unknown", "Empty proposition"),
    ("Set_Sized_upShadow", "pos_colon_Set_Finset_a_Sized_r_plus_1", "Not an equality or iff proposition"),
    ("Set_OrdConnected_preimage_coe_nnreal_ennreal", "inv_prime_u_colon_Set_ge_0_OrdConnected", "Not an equality or iff proposition"),
    ("Set_OrdConnected_image_coe_nnreal_ennreal", "prime_prime_t_colon_Set_ge_0inf_OrdConnected", "Not an equality or iff proposition"),
    ("Set_OrdConnected_preimage_ennreal_ofReal", "ENNReal_ofReal_inv_prime_u_OrdConnected", "Not an equality or iff proposition"),
    ("Set_OrdConnected_image_ennreal_ofReal", "ENNReal_ofReal_prime_prime_s_OrdConnected", "Not an equality or iff proposition"),
    ("Set_card_union_le", "Nat_card_s_union_t_le_Nat_card_s_plus_Nat_card_t", "Not an equality or iff proposition"),
    ("Set_Finite_card_lt_card", "Nat_card_s_lt_Nat_card_t", "Not an equality or iff proposition"),
    ("Set_ecard_le_ecard", "ENat_card_s_le_ENat_card_t", "Not an equality or iff proposition"),
    ("Set_Finite_ecard_lt_ecard", "ENat_card_s_lt_ENat_card_t", "Not an equality or iff proposition"),
    ("Set_Finite_card_strictMonoOn", "StrictMonoOn_a_colon_eq_Set_a_Nat_card_comp_setOf_Set_Finite", "Not an equality or iff proposition"),
    ("Set_Finite_ecard_strictMonoOn", "StrictMonoOn_a_colon_eq_Set_a_ENat_card_comp_setOf_Set_Finite", "Not an equality or iff proposition"),
    ("Set_card_strictMono", "StrictMono_a_colon_eq_Set_a_Nat_card_comp", "Not an equality or iff proposition"),
    ("Set_ecard_strictMono", "StrictMono_a_colon_eq_Set_a_ENat_card_comp", "Not an equality or iff proposition"),
    ("Set_toFinite", "s_Finite", "Not an equality or iff proposition"),
    ("Set_Finite_to_subtype", "Finite_s", "Not an equality or iff proposition"),
    ("Set_Infinite_not_finite", "not_s_Finite", "Not an equality or iff proposition"),
    ("Set_finite_or_infinite", "s_Finite_or_s_Infinite", "Not an equality or iff proposition"),
    ("Set_infinite_or_finite", "s_Infinite_or_s_Finite", "Not an equality or iff proposition"),
    ("Set_Finite_prod", "s_times_t_colon_Set_a_times_b_Finite", "Not an equality or iff proposition"),
    ("Set_Finite_of_prod_left", "t_Nonempty_to_s_Finite", "Not an equality or iff proposition"),
    ("Set_Finite_of_prod_right", "s_Nonempty_to_t_Finite", "Not an equality or iff proposition"),
    ("Set_Infinite_prod_left", "s_times_t_Infinite", "Not an equality or iff proposition"),
    ("Set_Infinite_prod_right", "s_times_t_Infinite", "Not an equality or iff proposition"),
    ("Set_Finite_offDiag", "s_offDiag_Finite", "Not an equality or iff proposition"),
    ("Set_Finite_image2", "image2_f_s_t_Finite", "Not an equality or iff proposition"),
    ("Set_Finite_exists_between", "exists_b_forall_x_in_s_x_lt_b_and_forall_y_in_t_b_lt_y", "Not an equality or iff proposition"),
    ("Set_Finite_exists_between", "_unknown", "Empty proposition"),
    ("Set_IsPWO_mul", "IsPWO_s_star_t", "Not an equality or iff proposition"),
    ("Set_IsWF_mul", "IsWF_s_star_t", "Not an equality or iff proposition"),
    ("Set_PairwiseDisjoint_image_finset_of_le", "s_image_g_colon_Set_i_PairwiseDisjoint_f", "Not an equality or iff proposition"),
    ("Set_PairwiseDisjoint_attach", "s_attach_colon_Set_x_slash_slash_x_in_s_PairwiseDisjoint_f_comp_Subtype_val", "Not an equality or iff proposition"),
    ("Set_IsPWO_smul", "IsPWO_s_t", "Not an equality or iff proposition"),
    ("Set_IsWF_smul", "IsWF_s_t", "Not an equality or iff proposition"),
    ("Set_Sized_mono", "A_Sized_r", "Not an equality or iff proposition"),
    ("Set_sized_empty", "empty_colon_Set_Finset_a_Sized_r", "Not an equality or iff proposition"),
    ("Set_Sized_isAntichain", "IsAntichain_sub_A", "Not an equality or iff proposition"),
    ("Set_Sized_subsingleton", "A_Subsingleton", "Not an equality or iff proposition"),
    ("Set_Sized_subsingleton", "_unknown", "Empty proposition"),
    ("Set_sized_powersetCard", "powersetCard_r_s_colon_Set_Finset_a_Sized_r", "Not an equality or iff proposition"),
    ("Set_Sized_compls", "colon_Set_Finset_a_Sized_Fintype_card_a_minus_n", "Not an equality or iff proposition"),
    ("Set_Finite_exists_le", "exists_M_forall_i_in_s_i_le_M", "Not an equality or iff proposition"),
    ("Set_Finite_exists_ge", "exists_M_forall_i_in_s_M_le_i", "Not an equality or iff proposition"),
    ("Set_Finite_pi", "pi_univ_t_Finite", "Not an equality or iff proposition"),
    ("Set_Finite_pi", "_unknown", "Empty proposition"),
    ("Set_biUnion_finsetSigma_univ", "_unknown", "Empty proposition"),
    ("Set_biInter_finsetSigma_univ", "_unknown", "Empty proposition"),
    ("Set_OrdConnected_preimage_coe_nnreal_real", "inv_prime_s_colon_Set_ge_0_OrdConnected", "Not an equality or iff proposition"),
    ("Set_OrdConnected_image_coe_nnreal_real", "prime_prime_t_colon_Set_OrdConnected", "Not an equality or iff proposition"),
    ("Set_OrdConnected_image_real_toNNReal", "Real_toNNReal_prime_prime_s_OrdConnected", "Not an equality or iff proposition"),
    ("Set_OrdConnected_preimage_real_toNNReal", "Real_toNNReal_inv_prime_t_OrdConnected", "Not an equality or iff proposition"),
]
