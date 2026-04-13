"""Mathlib: Prod — auto-generated from Mathlib4.

Contains 303 rewrite rules derived from Mathlib theorems.
Plus 166 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_prod"
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
# Rewrite rules (303 total)
# ════════════════════════════════════════════════════════════

def _r0000_snd_vadd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_vadd
    # (v +ᵥ p).2 = v.2 +ᵥ p.2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_plus_p_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("v_2", (OVar("plus"), OVar("p_2"),))
            results.append((rhs, "Mathlib: Prod_snd_vadd"))
    except Exception:
        pass
    return results


def _r0001_mk_vadd_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_vadd_mk
    # (v, v') +ᵥ (p, p') = (v +ᵥ p, v' +ᵥ p')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_v_prime", 2)
    if args is not None:
        try:
            rhs = OOp("v", (args[0], OVar("p"), OVar("v_prime"), args[0], OVar("p_prime"),))
            results.append((rhs, "Mathlib: Prod_mk_vadd_mk"))
        except Exception:
            pass
    return results


def _r0002_fst_vsub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_vsub
    # (p₁ -ᵥ p₂ : G × G').1 = p₁.1 -ᵥ p₂.1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_1_minus_p_2_colon_G_times_G_prime_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_1_1", (OVar("minus"), OVar("p_2_1"),))
            results.append((rhs, "Mathlib: Prod_fst_vsub"))
    except Exception:
        pass
    return results


def _r0003_snd_vsub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_vsub
    # (p₁ -ᵥ p₂ : G × G').2 = p₁.2 -ᵥ p₂.2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_1_minus_p_2_colon_G_times_G_prime_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_1_2", (OVar("minus"), OVar("p_2_2"),))
            results.append((rhs, "Mathlib: Prod_snd_vsub"))
    except Exception:
        pass
    return results


def _r0004_mk_vsub_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_vsub_mk
    # ((p₁, p₁') -ᵥ (p₂, p₂') : G × G') = (p₁ -ᵥ p₂, p₁' -ᵥ p₂')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "product", 2)
    if args is not None:
        try:
            rhs = OOp("p_1", (OVar("minus"), OVar("p_2"), OVar("p_1_prime"), OVar("minus"), OVar("p_2_prime"),))
            results.append((rhs, "Mathlib: Prod_mk_vsub_mk"))
        except Exception:
            pass
    return results


def _r0005_smul_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.smul_inr
    # a • (inr c : α ⊕ β) = inr (a • c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("inr", (OOp("a", (args[0], OVar("c"),)),))
            results.append((rhs, "Mathlib: Sum_smul_inr"))
        except Exception:
            pass
    return results


def _r0006_smul_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.smul_swap
    # (a • x).swap = a • x.swap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_x_swap")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a", (OVar("_unknown"), OVar("x_swap"),))
            results.append((rhs, "Mathlib: Sum_smul_swap"))
    except Exception:
        pass
    return results


def _r0007_uncurry_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.uncurry_one
    # Sigma.uncurry (1 : ∀ a b, γ a b) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_uncurry", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Sigma_uncurry_one"))
        except Exception:
            pass
    return results


def _r0008_curry_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.curry_mul
    # Sigma.curry (x * y) = Sigma.curry x * Sigma.curry y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_curry", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("Sigma_curry", (OVar("x"),)), OOp("Sigma_curry", (OVar("y"),))))
            results.append((rhs, "Mathlib: Sigma_curry_mul"))
        except Exception:
            pass
    return results


def _r0009_snd_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_one
    # (1 : M × N).2 = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_M_times_N_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Prod_snd_one"))
    except Exception:
        pass
    return results


def _r0010_one_eq_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.one_eq_mk
    # (1 : M × N) = (1, 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "product", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (OLit(1),))
            results.append((rhs, "Mathlib: Prod_one_eq_mk"))
        except Exception:
            pass
    return results


def _r0011_swap_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.swap_one
    # (1 : M × N).swap = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_M_times_N_swap")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Prod_swap_one"))
    except Exception:
        pass
    return results


def _r0012_snd_kstar(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_kstar
    # a∗.2 = a.2∗
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a_2")
            results.append((rhs, "Mathlib: Prod_snd_kstar"))
    except Exception:
        pass
    return results


def _r0013_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.map_id
    # Sigma.map (fun a => 𝟙 (f a)) = 𝟙 (∐ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_map", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("_unknown", (OVar("f"),)),))
            results.append((rhs, "Mathlib: Sigma_map_id"))
        except Exception:
            pass
    return results


def _r0014_map_comp_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.map_comp_map
    # Sigma.map q ≫ Sigma.map q' = Sigma.map (fun a => q a ≫ q' a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_map", 4)
    if args is not None:
        try:
            rhs = OOp("Sigma_map", (OOp("fun", (OVar("a"), OVar("eq_gt"), args[0], OVar("a"), args[1], args[3], OVar("a"),)),))
            results.append((rhs, "Mathlib: Sigma_map_comp_map"))
        except Exception:
            pass
    return results


def _r0015_swap_obj_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.swap_obj_inr
    # (swap C D).obj (inr X) = inl X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "swap_C_D_obj", 1)
    if args is not None:
        try:
            rhs = OOp("inl", (OVar("X"),))
            results.append((rhs, "Mathlib: Sum_swap_obj_inr"))
        except Exception:
            pass
    return results


def _r0016_swap_map_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.swap_map_inl
    # (swap C D).map f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "swap_C_D_map", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Sum_swap_map_inl"))
        except Exception:
            pass
    return results


def _r0017_swap_map_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.swap_map_inr
    # (swap C D).map f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "swap_C_D_map", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Sum_swap_map_inr"))
        except Exception:
            pass
    return results


def _r0018_snd_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_intCast
    # (n : α × β).snd = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_a_times_b_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Prod_snd_intCast"))
    except Exception:
        pass
    return results


def _r0019_fst_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_ofNat
    # (ofNat(n) : α × β).1 = (ofNat(n) : α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon_a_times_b_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ofNat_n", (OVar("colon"), OVar("a"),))
            results.append((rhs, "Mathlib: Prod_fst_ofNat"))
    except Exception:
        pass
    return results


def _r0020_snd_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_ofNat
    # (ofNat(n) : α × β).2 = (ofNat(n) : β)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon_a_times_b_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ofNat_n", (OVar("colon"), OVar("b"),))
            results.append((rhs, "Mathlib: Prod_snd_ofNat"))
    except Exception:
        pass
    return results


def _r0021_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.eq
    # ∀ {p₁ p₂ : Σ a, β a} (h₁ : p₁.1 = p₂.1),     (Eq.recOn h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂   | ⟨_, _⟩, _, rfl, rfl => rfl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("Sigma_mk", (OVar("b"),)), OVar("g_colon_a_eq_b_and_f_g")))
            results.append((rhs, "Mathlib: Sigma_eq"))
        except Exception:
            pass
    return results


def _r0022_fst_toSigma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_toSigma
    # (Prod.toSigma x).fst = x.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Prod_toSigma_x_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_fst")
            results.append((rhs, "Mathlib: Prod_fst_toSigma"))
    except Exception:
        pass
    return results


def _r0023_snd_toSigma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_toSigma
    # (Prod.toSigma x).snd = x.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Prod_toSigma_x_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_snd")
            results.append((rhs, "Mathlib: Prod_snd_toSigma"))
    except Exception:
        pass
    return results


def _r0024_toSigma_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.toSigma_mk
    # (x, y).toSigma = ⟨x, y⟩
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_y_toSigma")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_y")
            results.append((rhs, "Mathlib: Prod_toSigma_mk"))
    except Exception:
        pass
    return results


def _r0025_le_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.le_def
    # a ≤ b ↔ ∃ h : a.1 = b.1, h.rec a.2 ≤ b.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("b_1", (OVar("h_rec"), OVar("a_2"),)), OVar("b_2")))
            results.append((rhs, "Mathlib: Sigma_le_def"))
        except Exception:
            pass
    return results


def _r0026_Ico_inl_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ico_inl_inr
    # Ico (inl a₁) (inr b₂) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Sum_Ico_inl_inr"))
        except Exception:
            pass
    return results


def _r0027_Ioc_inl_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ioc_inl_inr
    # Ioc (inl a₁) (inr b₂) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Sum_Ioc_inl_inr"))
        except Exception:
            pass
    return results


def _r0028_Ioo_inl_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ioo_inl_inr
    # Ioo (inl a₁) (inr b₂) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Sum_Ioo_inl_inr"))
        except Exception:
            pass
    return results


def _r0029_Icc_inr_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Icc_inr_inl
    # Icc (inr b₁) (inl a₂) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Sum_Icc_inr_inl"))
        except Exception:
            pass
    return results


def _r0030_Ico_inr_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ico_inr_inl
    # Ico (inr b₁) (inl a₂) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Sum_Ico_inr_inl"))
        except Exception:
            pass
    return results


def _r0031_Ioc_inr_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ioc_inr_inl
    # Ioc (inr b₁) (inl a₂) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Sum_Ioc_inr_inl"))
        except Exception:
            pass
    return results


def _r0032_Ioo_inr_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ioo_inr_inl
    # Ioo (inr b₁) (inl a₂) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Sum_Ioo_inr_inl"))
        except Exception:
            pass
    return results


def _r0033_Icc_inr_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Icc_inr_inr
    # Icc (inr b₁ : α ⊕ β) (inr b₂) = (Icc b₁ b₂).map Embedding.inr
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc", 2)
    if args is not None:
        try:
            rhs = OOp("Icc_b_1_b_2_map", (OVar("Embedding_inr"),))
            results.append((rhs, "Mathlib: Sum_Icc_inr_inr"))
        except Exception:
            pass
    return results


def _r0034_inr_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Lex.inr_sup
    # (inrₗ (b₁ ⊔ b₂) : α ⊕ β) = inrₗ b₁ ⊔ inrₗ b₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inr", 5)
    if args is not None:
        try:
            rhs = OOp("inr", (OVar("b_1"), args[3], OVar("inr"), OVar("b_2"),))
            results.append((rhs, "Mathlib: Sum_Lex_inr_sup"))
        except Exception:
            pass
    return results


def _r0035_snd_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_top
    # (⊤ : α × β).snd = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_a_times_b_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Prod_snd_top"))
    except Exception:
        pass
    return results


def _r0036_fst_eq_or_snd_eq_of_wcovBy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_eq_or_snd_eq_of_wcovBy
    # x ⩿ y → x.1 = y.1 ∨ x.2 = y.2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("or", (OVar("y_1"), OVar("x_2"))), OVar("y_2")))
            results.append((rhs, "Mathlib: Prod_fst_eq_or_snd_eq_of_wcovBy"))
    except Exception:
        pass
    return results


def _r0037_snd_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_sup
    # (p ⊔ q).snd = p.snd ⊔ q.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_q_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_snd", (OVar("_unknown"), OVar("q_snd"),))
            results.append((rhs, "Mathlib: Prod_snd_sup"))
    except Exception:
        pass
    return results


def _r0038_swap_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.swap_sup
    # (p ⊔ q).swap = p.swap ⊔ q.swap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_q_swap")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_swap", (OVar("_unknown"), OVar("q_swap"),))
            results.append((rhs, "Mathlib: Prod_swap_sup"))
    except Exception:
        pass
    return results


def _r0039_sup_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.sup_def
    # p ⊔ q = (p.fst ⊔ q.fst, p.snd ⊔ q.snd)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p", 2)
    if args is not None:
        try:
            rhs = OOp("p_fst", (args[0], OVar("q_fst"), OVar("p_snd"), args[0], OVar("q_snd"),))
            results.append((rhs, "Mathlib: Prod_sup_def"))
        except Exception:
            pass
    return results


def _r0040_comul_comp_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.comul_comp_inl
    # comul ∘ₗ inl R A B = TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comul", 5)
    if args is not None:
        try:
            rhs = OOp("TensorProduct_map", (OOp("inl", (args[2], args[3], args[4],)), OOp("inl", (args[2], args[3], args[4],)), args[0], OVar("comul"),))
            results.append((rhs, "Mathlib: Prod_comul_comp_inl"))
        except Exception:
            pass
    return results


def _r0041_counit_comp_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.counit_comp_inl
    # counit ∘ₗ inl R A B = counit
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "counit", 5)
    if args is not None:
        try:
            rhs = OVar("counit")
            results.append((rhs, "Mathlib: Prod_counit_comp_inl"))
        except Exception:
            pass
    return results


def _r0042_add_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SummableFamily.add_apply
    # (s + t) a = s a + t a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_plus_t", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("s", (args[0],)), OOp("t", (args[0],))))
            results.append((rhs, "Mathlib: SummableFamily_add_apply"))
        except Exception:
            pass
    return results


def _r0043_zero_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SummableFamily.zero_apply
    # (0 : SummableFamily Γ R α) a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_SummableFamily_G_R_a", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: SummableFamily_zero_apply"))
        except Exception:
            pass
    return results


def _r0044_dist_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.dist_ne
    # dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ = dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨y⟩) y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dist", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("dist", (OVar("x"), OOp("Nonempty_some", (OVar("x"),)),)), OOp("+", (OLit(1), OOp("dist", (OOp("Nonempty_some", (OVar("y"),)), OVar("y"),))))))
            results.append((rhs, "Mathlib: Sigma_dist_ne"))
        except Exception:
            pass
    return results


def _r0045_mk_lt_mk_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.mk_lt_mk_iff
    # (⟨i, a⟩ : Sigma α) < ⟨i, b⟩ ↔ a < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("a"), OVar("b")))
            results.append((rhs, "Mathlib: Sigma_mk_lt_mk_iff"))
        except Exception:
            pass
    return results


def _r0046_swap_le_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.swap_le_mk
    # x.swap ≤ (b, a) ↔ x ≤ (a, b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("x"), OOp("a", (OVar("b"),))))
            results.append((rhs, "Mathlib: Prod_swap_le_mk"))
        except Exception:
            pass
    return results


def _r0047_swap_covBy_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.swap_covBy_swap
    # x.swap ⋖ y.swap ↔ x ⋖ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_swap", 2)
    if args is not None:
        try:
            rhs = OOp("x", (args[0], OVar("y"),))
            results.append((rhs, "Mathlib: Prod_swap_covBy_swap"))
        except Exception:
            pass
    return results


def _r0048_gameAdd_swap_swap_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.gameAdd_swap_swap_mk
    # GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ GameAdd rβ rα (b₁, a₁) (b₂, a₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "GameAdd", 4)
    if args is not None:
        try:
            rhs = OOp("GameAdd", (args[1], args[0], OOp("b_1", (OVar("a_1"),)), OOp("b_2", (OVar("a_2"),)),))
            results.append((rhs, "Mathlib: Prod_gameAdd_swap_swap_mk"))
        except Exception:
            pass
    return results


def _r0049_fst_vadd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_vadd
    # (v +ᵥ p).1 = v.1 +ᵥ p.1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_plus_p_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("v_1", (OVar("plus"), OVar("p_1"),))
            results.append((rhs, "Mathlib: Prod_fst_vadd"))
    except Exception:
        pass
    return results


def _r0050_algebraMap_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.algebraMap_apply
    # algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "algebraMap", 3)
    if args is not None:
        try:
            rhs = OOp("algebraMap", (args[0], OVar("A"), args[2], OVar("algebraMap"), args[0], OVar("B"), args[2],))
            results.append((rhs, "Mathlib: Prod_algebraMap_apply"))
        except Exception:
            pass
    return results


def _r0051_spectrum_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.spectrum_eq
    # spectrum R (⟨a, b⟩ : A × B) = spectrum R a ∪ spectrum R b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "spectrum", 2)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("spectrum", (args[0], OVar("a"),)), OOp("spectrum", (args[0], OVar("b"),))))
            results.append((rhs, "Mathlib: Prod_spectrum_eq"))
        except Exception:
            pass
    return results


def _r0052_quasispectrum_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.quasispectrum_eq
    # quasispectrum R (⟨a, b⟩ : A × B) = quasispectrum R a ∪ quasispectrum R b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "quasispectrum", 2)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("quasispectrum", (args[0], OVar("a"),)), OOp("quasispectrum", (args[0], OVar("b"),))))
            results.append((rhs, "Mathlib: Prod_quasispectrum_eq"))
        except Exception:
            pass
    return results


def _r0053_fst_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_prod
    # (∏ c ∈ s, f c).1 = ∏ c ∈ s, (f c).1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c_in_s_f_c_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("c"),)), OOp("s", (OVar("f_c_1"),))))
            results.append((rhs, "Mathlib: Prod_fst_prod"))
    except Exception:
        pass
    return results


def _r0054_snd_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_prod
    # (∏ c ∈ s, f c).2 = ∏ c ∈ s, (f c).2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c_in_s_f_c_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("c"),)), OOp("s", (OVar("f_c_2"),))))
            results.append((rhs, "Mathlib: Prod_snd_prod"))
    except Exception:
        pass
    return results


def _r0055_smul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.smul_def
    # a • x = x.map id fun _ => (a • ·)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("x_map", (OVar("id"), OVar("fun"), args[0], OVar("eq_gt"), OOp("a", (args[0], args[0],)),))
            results.append((rhs, "Mathlib: Sigma_smul_def"))
        except Exception:
            pass
    return results


def _r0056_smul_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.smul_mk
    # a • mk i b = ⟨i, a • b⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = OVar("i_a_b")
            results.append((rhs, "Mathlib: Sigma_smul_mk"))
        except Exception:
            pass
    return results


def _r0057_smul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.smul_def
    # a • x = x.map (a • ·) (a • ·)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("x_map", (OOp("a", (args[0], args[0],)), OOp("a", (args[0], args[0],)),))
            results.append((rhs, "Mathlib: Sum_smul_def"))
        except Exception:
            pass
    return results


def _r0058_smul_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.smul_inl
    # a • (inl b : α ⊕ β) = inl (a • b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("inl", (OOp("a", (args[0], OVar("b"),)),))
            results.append((rhs, "Mathlib: Sum_smul_inl"))
        except Exception:
            pass
    return results


def _r0059_elim_inv_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.elim_inv_inv
    # Sum.elim a⁻¹ b⁻¹ = (Sum.elim a b)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sum_elim", 2)
    if args is not None:
        try:
            rhs = OVar("Sum_elim_a_b_inv")
            results.append((rhs, "Mathlib: Sum_elim_inv_inv"))
        except Exception:
            pass
    return results


def _r0060_elim_mul_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.elim_mul_mul
    # Sum.elim (a * a') (b * b') = Sum.elim a b * Sum.elim a' b'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sum_elim", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("Sum_elim", (OVar("a"), OVar("b"),)), OOp("Sum_elim", (OVar("a_prime"), OVar("b_prime"),))))
            results.append((rhs, "Mathlib: Sum_elim_mul_mul"))
        except Exception:
            pass
    return results


def _r0061_elim_div_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.elim_div_div
    # Sum.elim (a / a') (b / b') = Sum.elim a b / Sum.elim a' b'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sum_elim", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("Sum_elim", (OVar("a"), OVar("b"),)), OOp("Sum_elim", (OVar("a_prime"), OVar("b_prime"),))))
            results.append((rhs, "Mathlib: Sum_elim_div_div"))
        except Exception:
            pass
    return results


def _r0062_uncurry_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.uncurry_mul
    # Sigma.uncurry (x * y) = Sigma.uncurry x * Sigma.uncurry y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_uncurry", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("Sigma_uncurry", (OVar("x"),)), OOp("Sigma_uncurry", (OVar("y"),))))
            results.append((rhs, "Mathlib: Sigma_uncurry_mul"))
        except Exception:
            pass
    return results


def _r0063_curry_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.curry_inv
    # Sigma.curry (x⁻¹) = (Sigma.curry x)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_curry", 1)
    if args is not None:
        try:
            rhs = OVar("Sigma_curry_x_inv")
            results.append((rhs, "Mathlib: Sigma_curry_inv"))
        except Exception:
            pass
    return results


def _r0064_uncurry_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.uncurry_inv
    # Sigma.uncurry (x⁻¹) = (Sigma.uncurry x)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_uncurry", 1)
    if args is not None:
        try:
            rhs = OVar("Sigma_uncurry_x_inv")
            results.append((rhs, "Mathlib: Sigma_uncurry_inv"))
        except Exception:
            pass
    return results


def _r0065_curry_mulSingle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.curry_mulSingle
    # Sigma.curry (Pi.mulSingle i x) = Pi.mulSingle i.1 (Pi.mulSingle i.2 x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_curry", 1)
    if args is not None:
        try:
            rhs = OOp("Pi_mulSingle", (OVar("i_1"), OOp("Pi_mulSingle", (OVar("i_2"), OVar("x"),)),))
            results.append((rhs, "Mathlib: Sigma_curry_mulSingle"))
        except Exception:
            pass
    return results


def _r0066_uncurry_mulSingle_mulSingle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.uncurry_mulSingle_mulSingle
    # Sigma.uncurry (Pi.mulSingle a (Pi.mulSingle b x)) = Pi.mulSingle (Sigma.mk a b) x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_uncurry", 1)
    if args is not None:
        try:
            rhs = OOp("Pi_mulSingle", (OOp("Sigma_mk", (OVar("a"), OVar("b"),)), OVar("x"),))
            results.append((rhs, "Mathlib: Sigma_uncurry_mulSingle_mulSingle"))
        except Exception:
            pass
    return results


def _r0067_one_mk_mul_one_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.one_mk_mul_one_mk
    # ((1 : M), b₁) * (1, b₂) = (1, b₁ * b₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("_1", (OVar("b_1"),)), OVar("b_2")))
            results.append((rhs, "Mathlib: Prod_one_mk_mul_one_mk"))
        except Exception:
            pass
    return results


def _r0068_mk_one_mul_mk_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_one_mul_mk_one
    # (a₁, (1 : N)) * (a₂, 1) = (a₁ * a₂, 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a_1"), OOp("a_2", (OLit(1),))))
            results.append((rhs, "Mathlib: Prod_mk_one_mul_mk_one"))
        except Exception:
            pass
    return results


def _r0069_fst_mul_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_mul_snd
    # (p.fst, 1) * (1, p.snd) = p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("p")
            results.append((rhs, "Mathlib: Prod_fst_mul_snd"))
        except Exception:
            pass
    return results


def _r0070_smul_zero_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.smul_zero_mk
    # a • ((0 : α), c) = (0, a • c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("a"), args[0], OVar("c"),))
            results.append((rhs, "Mathlib: Prod_smul_zero_mk"))
        except Exception:
            pass
    return results


def _r0071_smul_mk_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.smul_mk_zero
    # a • (b, (0 : β)) = (a • b, 0)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("a", (args[0], OVar("b"), OLit(0),))
            results.append((rhs, "Mathlib: Prod_smul_mk_zero"))
        except Exception:
            pass
    return results


def _r0072_bracket_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LieAlgebra.Prod.bracket_apply
    # ⁅x, y⁆ = ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 1)
    if args is not None:
        try:
            rhs = OVar("x_1_y_1_x_2_y_2")
            results.append((rhs, "Mathlib: LieAlgebra_Prod_bracket_apply"))
        except Exception:
            pass
    return results


def _r0073_fst_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_one
    # (1 : M × N).1 = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_M_times_N_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Prod_fst_one"))
    except Exception:
        pass
    return results


def _r0074_mk_one_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_one_one
    # ((1 : M), (1 : N)) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_M", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Prod_mk_one_one"))
        except Exception:
            pass
    return results


def _r0075_mk_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_eq_one
    # (x, y) = 1 ↔ x = 1 ∧ y = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("x"))), OOp("==", (OOp("and", (OLit(1), args[0])), OLit(1)))))
            results.append((rhs, "Mathlib: Prod_mk_eq_one"))
        except Exception:
            pass
    return results


def _r0076_kstar_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.kstar_def
    # a∗ = (a.1∗, a.2∗)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a_1", (OVar("a_2"),))
            results.append((rhs, "Mathlib: Prod_kstar_def"))
    except Exception:
        pass
    return results


def _r0077_fst_kstar(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_kstar
    # a∗.1 = a.1∗
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a_1")
            results.append((rhs, "Mathlib: Prod_fst_kstar"))
    except Exception:
        pass
    return results


def _r0078_image_mk_segment_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.image_mk_segment_left
    # (fun x => (x, y)) '' [x₁ -[𝕜] x₂] = [(x₁, y) -[𝕜] (x₂, y)]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_y", 2)
    if args is not None:
        try:
            rhs = OVar("x_1_y_minus_x_2_y")
            results.append((rhs, "Mathlib: Prod_image_mk_segment_left"))
        except Exception:
            pass
    return results


def _r0079_image_mk_segment_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.image_mk_segment_right
    # (fun y => (x, y)) '' [y₁ -[𝕜] y₂] = [(x, y₁) -[𝕜] (x, y₂)]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_y_eq_gt_x_y", 2)
    if args is not None:
        try:
            rhs = OVar("x_y_1_minus_x_y_2")
            results.append((rhs, "Mathlib: Prod_image_mk_segment_right"))
        except Exception:
            pass
    return results


def _r0080_image_mk_openSegment_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.image_mk_openSegment_left
    # (fun x => (x, y)) '' openSegment 𝕜 x₁ x₂ = openSegment 𝕜 (x₁, y) (x₂, y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_eq_gt_x_y", 5)
    if args is not None:
        try:
            rhs = OOp("openSegment", (args[2], OOp("x_1", (OVar("y"),)), OOp("x_2", (OVar("y"),)),))
            results.append((rhs, "Mathlib: Prod_image_mk_openSegment_left"))
        except Exception:
            pass
    return results


def _r0081_image_mk_openSegment_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.image_mk_openSegment_right
    # (fun y => (x, y)) '' openSegment 𝕜 y₁ y₂ = openSegment 𝕜 (x, y₁) (x, y₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_y_eq_gt_x_y", 5)
    if args is not None:
        try:
            rhs = OOp("openSegment", (args[2], OOp("x", (args[3],)), OOp("x", (args[4],)),))
            results.append((rhs, "Mathlib: Prod_image_mk_openSegment_right"))
        except Exception:
            pass
    return results


def _r0082_fst_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_exp
    # (exp x).fst = exp x.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("exp_x_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("exp", (OVar("x_fst"),))
            results.append((rhs, "Mathlib: Prod_fst_exp"))
    except Exception:
        pass
    return results


def _r0083_snd_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_exp
    # (exp x).snd = exp x.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("exp_x_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("exp", (OVar("x_snd"),))
            results.append((rhs, "Mathlib: Prod_snd_exp"))
    except Exception:
        pass
    return results


def _r0084_norm_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.norm_def
    # ‖x‖ = max ‖x.1‖ ‖x.2‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("max", (OVar("x_1"), OVar("x_2"),))
            results.append((rhs, "Mathlib: Prod_norm_def"))
    except Exception:
        pass
    return results


def _r0085_norm_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.norm_mk
    # ‖(x, y)‖ = max ‖x‖ ‖y‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_y")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("max", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: Prod_norm_mk"))
    except Exception:
        pass
    return results


def _r0086_mul_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.mul_of_nonneg
    # Summable fun x : ι × ι' => f x.1 * g x.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "product", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("gt", (OVar("f"), OVar("x_1"),)), OOp("g", (OVar("x_2"),))))
            results.append((rhs, "Mathlib: Summable_mul_of_nonneg"))
        except Exception:
            pass
    return results


def _r0087_mul_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.mul_norm
    # Summable fun x : ι × ι' => ‖f x.1 * g x.2‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "product", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("gt", (OVar("f"), OVar("x_1"),)), OOp("g", (OVar("x_2"),))))
            results.append((rhs, "Mathlib: Summable_mul_norm"))
        except Exception:
            pass
    return results


def _r0088_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.hom_ext
    # g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_2")
            results.append((rhs, "Mathlib: Sigma_hom_ext"))
    except Exception:
        pass
    return results


def _r0089_eqToHom_comp_i(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.eqToHom_comp_ι
    # eqToHom (by simp [w]) ≫ Sigma.ι f j' = Sigma.ι f j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eqToHom", 5)
    if args is not None:
        try:
            rhs = OOp("Sigma_i", (args[3], OVar("j"),))
            results.append((rhs, "Mathlib: Sigma_eqToHom_comp_i"))
        except Exception:
            pass
    return results


def _r0090_i_desc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.ι_desc
    # Sigma.ι f b ≫ Sigma.desc p = p b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_i", 5)
    if args is not None:
        try:
            rhs = OOp("p", (args[1],))
            results.append((rhs, "Mathlib: Sigma_i_desc"))
        except Exception:
            pass
    return results


def _r0091_i_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.ι_map
    # Sigma.ι f b ≫ Sigma.map p = p b ≫ Sigma.ι g b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_i", 5)
    if args is not None:
        try:
            rhs = OOp("p", (args[1], args[2], OVar("Sigma_i"), OVar("g"), args[1],))
            results.append((rhs, "Mathlib: Sigma_i_map"))
        except Exception:
            pass
    return results


def _r0092_i_isoColimit_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.ι_isoColimit_hom
    # Sigma.ι _ j ≫ (Sigma.isoColimit X).hom = colimit.ι _ (Discrete.mk j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_i", 4)
    if args is not None:
        try:
            rhs = OOp("colimit_i", (args[2], OOp("Discrete_mk", (args[1],)),))
            results.append((rhs, "Mathlib: Sigma_i_isoColimit_hom"))
        except Exception:
            pass
    return results


def _r0093_i_isoColimit_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.ι_isoColimit_inv
    # colimit.ι _ ⟨j⟩ ≫ (Sigma.isoColimit X).inv = Sigma.ι (fun j ↦ X.obj ⟨j⟩) _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "colimit_i", 4)
    if args is not None:
        try:
            rhs = OOp("Sigma_i", (OOp("fun", (args[1], args[2], OVar("X_obj"), args[1],)), args[2],))
            results.append((rhs, "Mathlib: Sigma_i_isoColimit_inv"))
        except Exception:
            pass
    return results


def _r0094_i_reindex_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.ι_reindex_hom
    # Sigma.ι (f ∘ ε) b ≫ (Sigma.reindex ε f).hom = Sigma.ι f (ε b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_i", 4)
    if args is not None:
        try:
            rhs = OOp("Sigma_i", (OVar("f"), OOp("e", (args[1],)),))
            results.append((rhs, "Mathlib: Sigma_i_reindex_hom"))
        except Exception:
            pass
    return results


def _r0095_i_reindex_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.ι_reindex_inv
    # Sigma.ι f (ε b) ≫ (Sigma.reindex ε f).inv = Sigma.ι (f ∘ ε) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_i", 4)
    if args is not None:
        try:
            rhs = OOp("Sigma_i", (OOp("comp", (args[0], OVar("e"))), OVar("b"),))
            results.append((rhs, "Mathlib: Sigma_i_reindex_inv"))
        except Exception:
            pass
    return results


def _r0096_i_pi_eq_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.ι_π_eq_id
    # Sigma.ι f b ≫ Sigma.π f b = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_i", 6)
    if args is not None:
        try:
            rhs = OOp("_1", (args[2],))
            results.append((rhs, "Mathlib: Sigma_i_pi_eq_id"))
        except Exception:
            pass
    return results


def _r0097_i_pi_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.ι_π_of_ne
    # Sigma.ι f b ≫ Sigma.π f c = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_i", 6)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Sigma_i_pi_of_ne"))
        except Exception:
            pass
    return results


def _r0098_i_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.ι_π
    # Sigma.ι f b ≫ Sigma.π f c = if h : b = c then eqToHom (congrArg f h) else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_i", 6)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (OVar("h"), OVar("colon"), args[1],)), OOp("c", (OVar("then"), OVar("eqToHom"), OOp("congrArg", (args[4], OVar("h"),)), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: Sigma_i_pi"))
        except Exception:
            pass
    return results


def _r0099_fac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fac
    # f = (𝟙 x.1 ×ₘ f.2) ≫ (f.1 ×ₘ (𝟙 y.2))
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1_x_1_times_f_2", (OVar("_unknown"), OOp("f_1", (OVar("times"), OOp("_1", (OVar("y_2"),)),)),))
            results.append((rhs, "Mathlib: Prod_fac"))
    except Exception:
        pass
    return results


def _r0100_homInduction_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.homInduction_left
    # homInduction inl inr ((inl_ C D).map f) = inl x y f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homInduction", 3)
    if args is not None:
        try:
            rhs = OOp("inl", (OVar("x"), OVar("y"), OVar("f"),))
            results.append((rhs, "Mathlib: Sum_homInduction_left"))
        except Exception:
            pass
    return results


def _r0101_homInduction_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.homInduction_right
    # homInduction inl inr ((inr_ C D).map f) = inr x y f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homInduction", 3)
    if args is not None:
        try:
            rhs = OOp("inr", (OVar("x"), OVar("y"), OVar("f"),))
            results.append((rhs, "Mathlib: Sum_homInduction_right"))
        except Exception:
            pass
    return results


def _r0102_swap_obj_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.swap_obj_inl
    # (swap C D).obj (inl X) = inr X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "swap_C_D_obj", 1)
    if args is not None:
        try:
            rhs = OOp("inr", (OVar("X"),))
            results.append((rhs, "Mathlib: Sum_swap_obj_inl"))
        except Exception:
            pass
    return results


def _r0103_traverse_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.traverse_map
    # Sum.traverse f (g <$> x) = Sum.traverse (f ∘ g) x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sum_traverse", 2)
    if args is not None:
        try:
            rhs = OOp("Sum_traverse", (OOp("comp", (args[0], OVar("g"))), OVar("x"),))
            results.append((rhs, "Mathlib: Sum_traverse_map"))
        except Exception:
            pass
    return results


def _r0104_comp_traverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.comp_traverse
    # Sum.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =     Comp.mk.{u} (Sum.traverse f <$> Sum.traverse g x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sum_traverse", 2)
    if args is not None:
        try:
            rhs = OOp("Comp_mk_u", (OOp("Sum_traverse", (OVar("f"), OVar("lt_gt"), OVar("Sum_traverse"), OVar("g"), args[1],)),))
            results.append((rhs, "Mathlib: Sum_comp_traverse"))
        except Exception:
            pass
    return results


def _r0105_map_traverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.map_traverse
    # (f <$> ·) <$> Sum.traverse g x = Sum.traverse (f <$> g ·) x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_lt_gt", 4)
    if args is not None:
        try:
            rhs = OOp("Sum_traverse", (OOp("f", (args[0], args[2], OVar("_unknown"),)), args[3],))
            results.append((rhs, "Mathlib: Sum_map_traverse"))
        except Exception:
            pass
    return results


def _r0106_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.naturality
    # η (Sum.traverse f x) = Sum.traverse (@η _ ∘ f) x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eta", 1)
    if args is not None:
        try:
            rhs = OOp("Sum_traverse", (OOp("comp", (OOp("at_eta", (OVar("_unknown"),)), OVar("f"))), OVar("x"),))
            results.append((rhs, "Mathlib: Sum_naturality"))
        except Exception:
            pass
    return results


def _r0107_fst_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_intCast
    # (n : α × β).fst = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_a_times_b_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Prod_fst_intCast"))
    except Exception:
        pass
    return results


def _r0108_fst_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_natCast
    # (n : α × β).fst = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_a_times_b_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Prod_fst_natCast"))
    except Exception:
        pass
    return results


def _r0109_snd_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_natCast
    # (n : α × β).snd = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_a_times_b_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Prod_snd_natCast"))
    except Exception:
        pass
    return results


def _r0110_swap_eq_iff_eq_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.swap_eq_iff_eq_swap
    # x.swap = y ↔ x = y.swap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_swap")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("y"), OVar("x"))), OVar("y_swap")))
            results.append((rhs, "Mathlib: Prod_swap_eq_iff_eq_swap"))
    except Exception:
        pass
    return results


def _r0111_eta(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk.eta
    # ∀ {p : α × β}, (p.1, p.2) = p   | (_, _) => rfl  theorem forall' {p : α → β → Prop} : (∀ x : α × β, p x.1 x.2) ↔ ∀ a b, 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_1", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("p", (OVar("pipe"), OOp("_unknown", (OVar("_unknown"),)), OVar("eq_gt"), OVar("rfl_theorem"), OVar("forall_prime"), OVar("p_colon_a_to_b_to_Prop"), OVar("colon"), OOp("product", (OOp("forall", (OVar("x"), OVar("colon"), OVar("a"),)), OOp("b", (OVar("p"), OVar("x_1"), OVar("x_2"),)))),)), OOp("forall", (OVar("a"), OVar("b"), OVar("p"), OVar("a"), OVar("b"),))))
            results.append((rhs, "Mathlib: Prod_mk_eta"))
        except Exception:
            pass
    return results


def _r0112_mk_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_inj
    # (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_1", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("a_2", (OVar("b_2"),)), OVar("a_1"))), OOp("==", (OOp("and", (OVar("a_2"), args[0])), OVar("b_2")))))
            results.append((rhs, "Mathlib: Prod_mk_inj"))
        except Exception:
            pass
    return results


def _r0113_mk_right_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_right_inj
    # (a, b₁) = (a, b₂) ↔ b₁ = b₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("a", (OVar("b_2"),)), args[0])), OVar("b_2")))
            results.append((rhs, "Mathlib: Prod_mk_right_inj"))
        except Exception:
            pass
    return results


def _r0114_mk_left_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_left_inj
    # (a₁, b) = (a₂, b) ↔ a₁ = a₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_1", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("a_2", (args[0],)), OVar("a_1"))), OVar("a_2")))
            results.append((rhs, "Mathlib: Prod_mk_left_inj"))
        except Exception:
            pass
    return results


def _r0115_map_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.map_def
    # Prod.map f g = fun p : α × β ↦ (f p.1, g p.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Prod_map", 2)
    if args is not None:
        try:
            rhs = OOp("product", (OOp("fun", (OVar("p"), OVar("colon"), OVar("a"),)), OOp("b", (OVar("_unknown"), OOp("f", (OVar("p_1"), args[1], OVar("p_2"),)),))))
            results.append((rhs, "Mathlib: Prod_map_def"))
        except Exception:
            pass
    return results


def _r0116_id_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.id_prod
    # (fun p : α × β ↦ (p.1, p.2)) = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "product", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Prod_id_prod"))
        except Exception:
            pass
    return results


def _r0117_map_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.map_iterate
    # (Prod.map f g)^[n] = Prod.map f^[n] g^[n]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Prod_map_f_g_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Prod_map", (OVar("fpow_n"), OVar("gpow_n"),))
            results.append((rhs, "Mathlib: Prod_map_iterate"))
    except Exception:
        pass
    return results


def _r0118_eq_iff_fst_eq_snd_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.eq_iff_fst_eq_snd_eq
    # ∀ {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q.2   | ⟨p₁, p₂⟩, ⟨q₁, q₂⟩ =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("q"), OVar("p_1"))), OOp("==", (OOp("and", (OVar("q_1"), OVar("p_2"))), OOp("q_2", (OVar("pipe"), OVar("p_1_p_2"), OVar("q_1_q_2"), OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: Prod_eq_iff_fst_eq_snd_eq"))
    except Exception:
        pass
    return results


def _r0119_fst_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_eq_iff
    # ∀ {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)   | ⟨a, b⟩, x =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("x"), OVar("p"))), OOp("x_p_2", (OVar("pipe"), OVar("a_b"), OVar("x"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Prod_fst_eq_iff"))
    except Exception:
        pass
    return results


def _r0120_snd_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_eq_iff
    # ∀ {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)   | ⟨a, b⟩, x =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("x"), OVar("p"))), OOp("p_1_x", (OVar("pipe"), OVar("a_b"), OVar("x"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Prod_snd_eq_iff"))
    except Exception:
        pass
    return results


def _r0121_lex_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.lex_iff
    # Prod.Lex r s x y ↔ r x.1 y.1 ∨ x.1 = y.1 ∧ s x.2 y.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OVar("y_1"), OOp("s", (OVar("x_2"), OVar("y_2"),))))
            results.append((rhs, "Mathlib: Prod_lex_iff"))
        except Exception:
            pass
    return results


def _r0122_refl_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.refl_left
    # ∀ x, Prod.Lex r s x x   | (_, _) => Lex.left _ _ (refl _)  instance {r : α → α → Prop} {s : β → β → Prop} [Std.Refl r] :
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Prod_Lex", 6)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("Lex_left"), OVar("_unknown"), OVar("_unknown"), OVar("refl_instance"), OVar("r_colon_a_to_a_to_Prop"), OVar("s_colon_b_to_b_to_Prop"), OSeq((OOp("Std_Refl", (args[0],)),)), OVar("colon"), OVar("Std_Refl"), OOp("Prod_Lex", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: Prod_Lex_refl_left"))
        except Exception:
            pass
    return results


def _r0123_refl_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.refl_right
    # ∀ x, Prod.Lex r s x x   | (_, _) => Lex.right _ (refl _)  instance {r : α → α → Prop} {s : β → β → Prop} [Std.Refl s] : 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Prod_Lex", 6)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("Lex_right"), OVar("_unknown"), OVar("refl_instance"), OVar("r_colon_a_to_a_to_Prop"), OVar("s_colon_b_to_b_to_Prop"), OSeq((OOp("Std_Refl", (args[1],)),)), OVar("colon"), OVar("Std_Refl"), OOp("Prod_Lex", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: Prod_Lex_refl_right"))
        except Exception:
            pass
    return results


def _r0124_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.trans
    # ∀ {x y z : α × β}, Prod.Lex r s x y → Prod.Lex r s y z → Prod.Lex r s x z   | (_, _), (_, _), (_, _), left  _ _ hxy₁, le
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Prod_Lex", 16)
    if args is not None:
        try:
            rhs = OOp("gt", (args[12], args[14], args[14], OOp("root_trans", (args[11], args[15],)), args[4], args[14], args[14], args[14], args[12], args[14], args[14], args[11], OVar("right"), args[14], args[14], OVar("eq_gt"), args[12], args[14], args[14], args[11], args[4], args[14], args[14], args[14], OVar("right"), args[14], args[14], args[12], args[14], args[14], args[15], OVar("eq_gt"), args[12], args[14], args[14], args[15], args[4], args[14], args[14], args[14], OVar("right"), args[14], OVar("hxy_2"), OVar("right"), args[14], OVar("hyz_2"), OVar("eq_gt"), OVar("right"), args[14], OVar("root_trans_hxy_2_hyz_2_instance"), OVar("r_colon_a_to_a_to_Prop"), OVar("s_colon_b_to_b_to_Prop"), OSeq((OOp("IsTrans", (OVar("a"), args[0],)),)), OSeq((OOp("IsTrans", (OVar("b"), args[1],)),)), OVar("colon"), OVar("IsTrans"), OOp("product", (OVar("a"), OVar("b"))), OOp("Prod_Lex", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: Prod_Lex_trans"))
        except Exception:
            pass
    return results


def _r0125_toLex_le_toLex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.toLex_le_toLex
    # toLex x ≤ toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 ≤ y.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("and", (OVar("y_1"), OVar("x_2"))), OVar("y_2")))
            results.append((rhs, "Mathlib: Prod_Lex_toLex_le_toLex"))
        except Exception:
            pass
    return results


def _r0126_toLex_lt_toLex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.toLex_lt_toLex
    # toLex x < toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("and", (OVar("y_1"), OVar("x_2"))), OVar("y_2")))
            results.append((rhs, "Mathlib: Prod_Lex_toLex_lt_toLex"))
        except Exception:
            pass
    return results


def _r0127_le_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.le_iff
    # x ≤ y ↔ (ofLex x).1 < (ofLex y).1 ∨ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 ≤ (ofLex y).2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("and", (OVar("ofLex_y_1"), OVar("ofLex_x_2"))), OVar("ofLex_y_2")))
            results.append((rhs, "Mathlib: Prod_Lex_le_iff"))
        except Exception:
            pass
    return results


def _r0128_lt_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.lt_iff
    # x < y ↔ (ofLex x).1 < (ofLex y).1 ∨ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("and", (OVar("ofLex_y_1"), OVar("ofLex_x_2"))), OVar("ofLex_y_2")))
            results.append((rhs, "Mathlib: Prod_Lex_lt_iff"))
        except Exception:
            pass
    return results


def _r0129_toLex_covBy_toLex_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.toLex_covBy_toLex_iff
    # toLex (a₁, b₁) ⋖ toLex (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ ⋖ b₂ ∨ a₁ ⋖ a₂ ∧ IsMax b₁ ∧ IsMin b₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OVar("a_2"), OOp("and", (OOp("or", (OOp("b_1", (OVar("_unknown"), OVar("b_2"),)), OOp("a_1", (OVar("_unknown"), OVar("a_2"),)))), OOp("and", (OOp("IsMax", (OVar("b_1"),)), OOp("IsMin", (OVar("b_2"),))))))))
            results.append((rhs, "Mathlib: Prod_Lex_toLex_covBy_toLex_iff"))
        except Exception:
            pass
    return results


def _r0130_covBy_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.covBy_iff
    # a ⋖ b ↔ (ofLex a).1 = (ofLex b).1 ∧ (ofLex a).2 ⋖ (ofLex b).2 ∨       (ofLex a).1 ⋖ (ofLex b).1 ∧ IsMax (ofLex a).2 ∧ Is
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OVar("ofLex_b_1"), OOp("and", (OOp("or", (OOp("ofLex_a_2", (OVar("_unknown"), OVar("ofLex_b_2"),)), OOp("ofLex_a_1", (OVar("_unknown"), OVar("ofLex_b_1"),)))), OOp("and", (OOp("IsMax", (OVar("ofLex_a_2"),)), OOp("IsMin", (OVar("ofLex_b_2"),))))))))
            results.append((rhs, "Mathlib: Prod_Lex_covBy_iff"))
        except Exception:
            pass
    return results


def _r0131_eta(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PProd.mk.eta
    # PProd.mk p.1 p.2 = p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OVar("p")
            results.append((rhs, "Mathlib: PProd_mk_eta"))
        except Exception:
            pass
    return results


def _r0132_range_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.range_eq
    # range f = range (f ∘ Sum.inl) ∪ range (f ∘ Sum.inr)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("range", (OOp("comp", (args[0], OVar("Sum_inl"))),)), OOp("range", (OOp("comp", (args[0], OVar("Sum_inr"))),))))
            results.append((rhs, "Mathlib: Sum_range_eq"))
        except Exception:
            pass
    return results


def _r0133_elim_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.elim_range
    # range (Sum.elim f g) = range f ∪ range g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("range", (OVar("f"),)), OOp("range", (OVar("g"),))))
            results.append((rhs, "Mathlib: Sum_elim_range"))
        except Exception:
            pass
    return results


def _r0134_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.univ
    # (Set.univ : Set (Σ a, X a)) = ⋃ a, range (Sigma.mk a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "univ_set", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("a"), OVar("range"), OOp("Sigma_mk", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Sigma_univ"))
        except Exception:
            pass
    return results


def _r0135_inj_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.mk.inj_iff
    # Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_mk", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("a_2_b_2"), args[0])), OOp("and", (OVar("a_2"), OOp("b_1", (OVar("_unknown"), OVar("b_2"),))))))
            results.append((rhs, "Mathlib: Sigma_mk_inj_iff"))
        except Exception:
            pass
    return results


def _r0136_eta(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.eta
    # ∀ x : Σ a, β a, Sigma.mk x.1 x.2 = x   | ⟨_, _⟩ => rfl  protected theorem eq {α : Type*} {β : α → Type*} : ∀ {p₁ p₂ : Σ 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("Sigma_mk", (OVar("b"),)), OVar("g_colon_a_eq_b_and_f_g")))
            results.append((rhs, "Mathlib: Sigma_eta"))
        except Exception:
            pass
    return results


def _r0137_eq_of_sigmaMk_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.eq_of_sigmaMk_comp
    # a = b ∧ f ≍ g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("and", (OVar("b"), OOp("f", (OVar("_unknown"), OVar("g"),))))
            results.append((rhs, "Mathlib: Function_eq_of_sigmaMk_comp"))
    except Exception:
        pass
    return results


def _r0138_subtype_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.subtype_ext
    # ∀ {x₀ x₁ : Σ a, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁   | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => 
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_0")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("x_1", (OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("rfl"), OVar("rfl"), OVar("eq_gt"), OVar("rfl_theorem"), OVar("forall"), OVar("p_colon_Sig_a_b_a_to_Prop"), OVar("colon"), OOp("forall", (OVar("x"), OVar("p"), OVar("x"),)),)), OOp("forall", (OVar("a"), OVar("b"), OVar("p"), OVar("a_b"),))))
            results.append((rhs, "Mathlib: Sigma_subtype_ext"))
    except Exception:
        pass
    return results


def _r0139_sigma_mk_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: sigma_mk_injective
    # Injective (@Sigma.mk α β i)   | _, _, rfl => rfl  theorem fst_surjective [h : ∀ a, Nonempty (β a)] : Surjective (fst : (
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("rfl_theorem"), OVar("fst_surjective"), OVar("h_colon_forall_a_Nonempty_b_a"), OVar("colon"), OVar("Surjective"), OOp("implies", (OOp("fst", (OVar("colon"), OOp("Sig", (OVar("a"), OVar("b"), OVar("a"),)),)), OVar("a"))),))
            results.append((rhs, "Mathlib: sigma_mk_injective"))
        except Exception:
            pass
    return results


def _r0140_map_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.map_mk
    # map f₁ f₂ ⟨x, y⟩ = ⟨f₁ x, f₂ x y⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 3)
    if args is not None:
        try:
            rhs = OVar("f_1_x_f_2_x_y")
            results.append((rhs, "Mathlib: Sigma_map_mk"))
        except Exception:
            pass
    return results


def _r0141_uncurry_curry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.uncurry_curry
    # Sigma.uncurry (Sigma.curry f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_uncurry", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Sigma_uncurry_curry"))
        except Exception:
            pass
    return results


def _r0142_curry_uncurry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.curry_uncurry
    # Sigma.curry (Sigma.uncurry f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_curry", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Sigma_curry_uncurry"))
        except Exception:
            pass
    return results


def _r0143_curry_update(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.curry_update
    # Sigma.curry (Function.update f i x) =       Function.update (Sigma.curry f) i.1 (Function.update (Sigma.curry f i.1) i.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_curry", 1)
    if args is not None:
        try:
            rhs = OOp("Function_update", (OOp("Sigma_curry", (OVar("f"),)), OVar("i_1"), OOp("Function_update", (OOp("Sigma_curry", (OVar("f"), OVar("i_1"),)), OVar("i_2"), OVar("x"),)),))
            results.append((rhs, "Mathlib: Sigma_curry_update"))
        except Exception:
            pass
    return results


def _r0144_fst_comp_toSigma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_comp_toSigma
    # Sigma.fst ∘ @Prod.toSigma α β = Prod.fst
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("Prod_fst")
            results.append((rhs, "Mathlib: Prod_fst_comp_toSigma"))
        except Exception:
            pass
    return results


def _r0145_toSigma_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.toSigma_inj
    # x.toSigma = y.toSigma ↔ x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_toSigma")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("y_toSigma"), OVar("x"))), OVar("y")))
            results.append((rhs, "Mathlib: Prod_toSigma_inj"))
    except Exception:
        pass
    return results


def _r0146_card_Icc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.card_Icc
    # #(Icc a b) = if h : a.1 = b.1 then #(Icc (h.rec a.2) b.2) else 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Icc_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("if", (OVar("h"), OVar("colon"), OVar("a_1"),)), OOp("b_1", (OVar("then"), OVar("hash_Icc_h_rec_a_2_b_2"), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: Sigma_card_Icc"))
    except Exception:
        pass
    return results


def _r0147_card_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.card_Ico
    # #(Ico a b) = if h : a.1 = b.1 then #(Ico (h.rec a.2) b.2) else 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Ico_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("if", (OVar("h"), OVar("colon"), OVar("a_1"),)), OOp("b_1", (OVar("then"), OVar("hash_Ico_h_rec_a_2_b_2"), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: Sigma_card_Ico"))
    except Exception:
        pass
    return results


def _r0148_card_Ioc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.card_Ioc
    # #(Ioc a b) = if h : a.1 = b.1 then #(Ioc (h.rec a.2) b.2) else 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Ioc_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("if", (OVar("h"), OVar("colon"), OVar("a_1"),)), OOp("b_1", (OVar("then"), OVar("hash_Ioc_h_rec_a_2_b_2"), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: Sigma_card_Ioc"))
    except Exception:
        pass
    return results


def _r0149_card_Ioo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.card_Ioo
    # #(Ioo a b) = if h : a.1 = b.1 then #(Ioo (h.rec a.2) b.2) else 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_Ioo_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("if", (OVar("h"), OVar("colon"), OVar("a_1"),)), OOp("b_1", (OVar("then"), OVar("hash_Ioo_h_rec_a_2_b_2"), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: Sigma_card_Ioo"))
    except Exception:
        pass
    return results


def _r0150_lex_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.lex_iff
    # Lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s b.1 (h.rec a.2) b.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 2)
    if args is not None:
        try:
            rhs = OOp("b_1", (OVar("s"), OVar("b_1"), OOp("h_rec", (OVar("a_2"),)), OVar("b_2"),))
            results.append((rhs, "Mathlib: Sigma_lex_iff"))
        except Exception:
            pass
    return results


def _r0151_lt_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.lt_def
    # a < b ↔ ∃ h : a.1 = b.1, h.rec a.2 < b.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("b_1", (OVar("h_rec"), OVar("a_2"),)), OVar("b_2")))
            results.append((rhs, "Mathlib: Sigma_lt_def"))
        except Exception:
            pass
    return results


def _r0152_le_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.Lex.le_def
    # a ≤ b ↔ a.1 < b.1 ∨ ∃ h : a.1 = b.1, h.rec a.2 ≤ b.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("b_1", (OVar("h_rec"), OVar("a_2"),)), OVar("b_2")))
            results.append((rhs, "Mathlib: Sigma_Lex_le_def"))
        except Exception:
            pass
    return results


def _r0153_lt_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.Lex.lt_def
    # a < b ↔ a.1 < b.1 ∨ ∃ h : a.1 = b.1, h.rec a.2 < b.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("b_1", (OVar("h_rec"), OVar("a_2"),)), OVar("b_2")))
            results.append((rhs, "Mathlib: Sigma_Lex_lt_def"))
        except Exception:
            pass
    return results


def _r0154_elim_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.elim_swap
    # Sum.elim f g ∘ Sum.swap = Sum.elim g f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("Sum_elim", (OVar("g"), OVar("f"),))
            results.append((rhs, "Mathlib: Sum_elim_swap"))
        except Exception:
            pass
    return results


def _r0155_sum_rec_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.sum_rec_congr
    # @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_Sum_rec", 6)
    if args is not None:
        try:
            rhs = OOp("cast", (OOp("congr_arg", (OVar("P"), OVar("h_symm"),)), OOp("at_Sum_rec", (args[2], args[2], args[2], args[3], args[4], OVar("y"),)),))
            results.append((rhs, "Mathlib: Sum_sum_rec_congr"))
        except Exception:
            pass
    return results


def _r0156_eq_left_iff_getLeft_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.eq_left_iff_getLeft_eq
    # x = inl a ↔ ∃ h, x.getLeft h = a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("inl", (OVar("a"),)), OOp("exists", (OVar("h"), OVar("x_getLeft"), OVar("h"),)))), OVar("a")))
            results.append((rhs, "Mathlib: Sum_eq_left_iff_getLeft_eq"))
    except Exception:
        pass
    return results


def _r0157_eq_right_iff_getRight_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.eq_right_iff_getRight_eq
    # x = inr b ↔ ∃ h, x.getRight h = b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("inr", (OVar("b"),)), OOp("exists", (OVar("h"), OVar("x_getRight"), OVar("h"),)))), OVar("b")))
            results.append((rhs, "Mathlib: Sum_eq_right_iff_getRight_eq"))
    except Exception:
        pass
    return results


def _r0158_Icc_inl_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Icc_inl_inl
    # Icc (inl a₁ : α ⊕ β) (inl a₂) = (Icc a₁ a₂).map Embedding.inl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc", 2)
    if args is not None:
        try:
            rhs = OOp("Icc_a_1_a_2_map", (OVar("Embedding_inl"),))
            results.append((rhs, "Mathlib: Sum_Icc_inl_inl"))
        except Exception:
            pass
    return results


def _r0159_Ico_inl_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ico_inl_inl
    # Ico (inl a₁ : α ⊕ β) (inl a₂) = (Ico a₁ a₂).map Embedding.inl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OOp("Ico_a_1_a_2_map", (OVar("Embedding_inl"),))
            results.append((rhs, "Mathlib: Sum_Ico_inl_inl"))
        except Exception:
            pass
    return results


def _r0160_Ioc_inl_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ioc_inl_inl
    # Ioc (inl a₁ : α ⊕ β) (inl a₂) = (Ioc a₁ a₂).map Embedding.inl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc", 2)
    if args is not None:
        try:
            rhs = OOp("Ioc_a_1_a_2_map", (OVar("Embedding_inl"),))
            results.append((rhs, "Mathlib: Sum_Ioc_inl_inl"))
        except Exception:
            pass
    return results


def _r0161_Ioo_inl_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ioo_inl_inl
    # Ioo (inl a₁ : α ⊕ β) (inl a₂) = (Ioo a₁ a₂).map Embedding.inl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo", 2)
    if args is not None:
        try:
            rhs = OOp("Ioo_a_1_a_2_map", (OVar("Embedding_inl"),))
            results.append((rhs, "Mathlib: Sum_Ioo_inl_inl"))
        except Exception:
            pass
    return results


def _r0162_Icc_inl_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Icc_inl_inr
    # Icc (inl a₁) (inr b₂) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Icc", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Sum_Icc_inl_inr"))
        except Exception:
            pass
    return results


def _r0163_Ico_inr_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ico_inr_inr
    # Ico (inr b₁ : α ⊕ β) (inr b₂) = (Ico b₁ b₂).map Embedding.inr
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OOp("Ico_b_1_b_2_map", (OVar("Embedding_inr"),))
            results.append((rhs, "Mathlib: Sum_Ico_inr_inr"))
        except Exception:
            pass
    return results


def _r0164_Ioc_inr_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ioc_inr_inr
    # Ioc (inr b₁ : α ⊕ β) (inr b₂) = (Ioc b₁ b₂).map Embedding.inr
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioc", 2)
    if args is not None:
        try:
            rhs = OOp("Ioc_b_1_b_2_map", (OVar("Embedding_inr"),))
            results.append((rhs, "Mathlib: Sum_Ioc_inr_inr"))
        except Exception:
            pass
    return results


def _r0165_Ioo_inr_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Ioo_inr_inr
    # Ioo (inr b₁ : α ⊕ β) (inr b₂) = (Ioo b₁ b₂).map Embedding.inr
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ioo", 2)
    if args is not None:
        try:
            rhs = OOp("Ioo_b_1_b_2_map", (OVar("Embedding_inr"),))
            results.append((rhs, "Mathlib: Sum_Ioo_inr_inr"))
        except Exception:
            pass
    return results


def _r0166_inl_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.Lex.inl_sup
    # (inlₗ (a₁ ⊔ a₂) : α ⊕ β) = inlₗ a₁ ⊔ inlₗ a₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 5)
    if args is not None:
        try:
            rhs = OOp("inl", (OVar("a_1"), args[3], OVar("inl"), OVar("a_2"),))
            results.append((rhs, "Mathlib: Sum_Lex_inl_sup"))
        except Exception:
            pass
    return results


def _r0167_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.LiftRel.refl
    # ∀ x, LiftRel r s x x   | inl a => LiftRel.inl (_root_.refl a)   | inr a => LiftRel.inr (_root_.refl a)  instance [Std.Re
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LiftRel", 7)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("LiftRel_inl"), OOp("root_refl", (args[6],)), args[4], OVar("inr"), args[6], OVar("eq_gt"), OVar("LiftRel_inr"), OVar("root_refl_a_instance"), OSeq((OOp("Std_Refl", (args[0],)),)), OSeq((OOp("Std_Refl", (args[1],)),)), OVar("colon"), OVar("Std_Refl"), OOp("LiftRel", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: Sum_LiftRel_refl"))
        except Exception:
            pass
    return results


def _r0168_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.LiftRel.trans
    # ∀ {a b c}, LiftRel r s a b → LiftRel r s b c → LiftRel r s a c   | _, _, _, LiftRel.inl hab, LiftRel.inl hbc => LiftRel.
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LiftRel", 12)
    if args is not None:
        try:
            rhs = OOp("gt", (args[10], OVar("lt_pipe"), OVar("root_trans"), args[9], args[11], args[4], args[7], args[7], args[7], OVar("LiftRel_inr"), args[9], OVar("LiftRel_inr"), args[11], OVar("eq_gt"), OVar("LiftRel_inr"), OVar("lt_pipe"), OVar("root_trans"), args[9], OVar("hbc_instance"), OSeq((OOp("IsTrans", (args[2], args[0],)),)), OSeq((OOp("IsTrans", (OVar("b"), args[1],)),)), OVar("colon"), OVar("IsTrans"), OOp("a", (args[7], OVar("b"),)), OOp("LiftRel", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: Sum_LiftRel_trans"))
        except Exception:
            pass
    return results


def _r0169_orderOf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.orderOf
    # orderOf x = (orderOf x.1).lcm (orderOf x.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "orderOf", 1)
    if args is not None:
        try:
            rhs = OOp("orderOf_x_1_lcm", (OOp("orderOf", (OVar("x_2"),)),))
            results.append((rhs, "Mathlib: Prod_orderOf"))
        except Exception:
            pass
    return results


def _r0170_orderOf_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.orderOf_mk
    # orderOf (a, b) = Nat.lcm (orderOf a) (orderOf b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "orderOf", 1)
    if args is not None:
        try:
            rhs = OOp("lcm", (OOp("orderOf", (OVar("a"),)), OOp("orderOf", (OVar("b"),)),))
            results.append((rhs, "Mathlib: Prod_orderOf_mk"))
        except Exception:
            pass
    return results


def _r0171_fst_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_top
    # (⊤ : α × β).fst = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_a_times_b_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Prod_fst_top"))
    except Exception:
        pass
    return results


def _r0172_fst_sSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_sSup
    # (sSup s).fst = sSup (Prod.fst '' s)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sSup_s_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sSup", (OOp("fst", (OVar("prime_prime"), OVar("s"),)),))
            results.append((rhs, "Mathlib: Prod_fst_sSup"))
    except Exception:
        pass
    return results


def _r0173_snd_sSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_sSup
    # (sSup s).snd = sSup (Prod.snd '' s)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sSup_s_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sSup", (OOp("snd", (OVar("prime_prime"), OVar("s"),)),))
            results.append((rhs, "Mathlib: Prod_snd_sSup"))
    except Exception:
        pass
    return results


def _r0174_swap_sSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.swap_sSup
    # (sSup s).swap = sSup (Prod.swap '' s)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sSup_s_swap")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sSup", (OOp("swap", (OVar("prime_prime"), OVar("s"),)),))
            results.append((rhs, "Mathlib: Prod_swap_sSup"))
    except Exception:
        pass
    return results


def _r0175_fst_iSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_iSup
    # (iSup f).fst = ⨆ i, (f i).fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("iSup_f_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("f_i_fst"),))
            results.append((rhs, "Mathlib: Prod_fst_iSup"))
    except Exception:
        pass
    return results


def _r0176_snd_iSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.snd_iSup
    # (iSup f).snd = ⨆ i, (f i).snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("iSup_f_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("f_i_snd"),))
            results.append((rhs, "Mathlib: Prod_snd_iSup"))
    except Exception:
        pass
    return results


def _r0177_swap_iSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.swap_iSup
    # (iSup f).swap = ⨆ i, (f i).swap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("iSup_f_swap")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("f_i_swap"),))
            results.append((rhs, "Mathlib: Prod_swap_iSup"))
    except Exception:
        pass
    return results


def _r0178_iSup_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.iSup_mk
    # ⨆ i, (f i, g i) = (⨆ i, f i, ⨆ i, g i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (args[0], OVar("f"), args[0], OVar("_unknown"), args[0], OVar("g"), args[0],))
            results.append((rhs, "Mathlib: Prod_iSup_mk"))
        except Exception:
            pass
    return results


def _r0179_mk_wcovBy_mk_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_wcovBy_mk_iff
    # (a₁, b₁) ⩿ (a₂, b₂) ↔ a₁ ⩿ a₂ ∧ b₁ = b₂ ∨ b₁ ⩿ b₂ ∧ a₁ = a₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("or", (OVar("b_2"), OOp("b_1", (OVar("_unknown"), OVar("b_2"),)))), OVar("a_1"))), OVar("a_2")))
            results.append((rhs, "Mathlib: Prod_mk_wcovBy_mk_iff"))
        except Exception:
            pass
    return results


def _r0180_mk_covBy_mk_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_covBy_mk_iff
    # (a₁, b₁) ⋖ (a₂, b₂) ↔ a₁ ⋖ a₂ ∧ b₁ = b₂ ∨ b₁ ⋖ b₂ ∧ a₁ = a₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("or", (OVar("b_2"), OOp("b_1", (OVar("_unknown"), OVar("b_2"),)))), OVar("a_1"))), OVar("a_2")))
            results.append((rhs, "Mathlib: Prod_mk_covBy_mk_iff"))
        except Exception:
            pass
    return results


def _r0181_wcovBy_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.wcovBy_iff
    # x ⩿ y ↔ x.1 ⩿ y.1 ∧ x.2 = y.2 ∨ x.2 ⩿ y.2 ∧ x.1 = y.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("or", (OVar("y_2"), OOp("x_2", (OVar("_unknown"), OVar("y_2"),)))), OVar("x_1"))), OVar("y_1")))
            results.append((rhs, "Mathlib: Prod_wcovBy_iff"))
        except Exception:
            pass
    return results


def _r0182_covBy_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.covBy_iff
    # x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("or", (OVar("y_2"), OOp("x_2", (OVar("_unknown"), OVar("y_2"),)))), OVar("x_1"))), OVar("y_1")))
            results.append((rhs, "Mathlib: Prod_covBy_iff"))
        except Exception:
            pass
    return results


def _r0183_gameAdd_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.gameAdd_iff
    # GameAdd rα rβ x y ↔ rα x.1 y.1 ∧ x.2 = y.2 ∨ rβ x.2 y.2 ∧ x.1 = y.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("or", (OVar("y_2"), OOp("rb", (args[1], OVar("y_2"),)))), OVar("x_1"))), OVar("y_1")))
            results.append((rhs, "Mathlib: Prod_gameAdd_iff"))
        except Exception:
            pass
    return results


def _r0184_gameAdd_mk_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.gameAdd_mk_iff
    # GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ rα a₁ a₂ ∧ b₁ = b₂ ∨ rβ b₁ b₂ ∧ a₁ = a₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("or", (OVar("b_2"), OOp("rb", (args[1], OVar("b_2"),)))), OVar("a_1"))), OVar("a_2")))
            results.append((rhs, "Mathlib: Prod_gameAdd_mk_iff"))
        except Exception:
            pass
    return results


def _r0185_rprod_le_transGen_gameAdd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.rprod_le_transGen_gameAdd
    # RProd rα rβ ≤ Relation.TransGen (GameAdd rα rβ)   | _, _, h => h.rec (by       intro _ _ _ _ hα hβ       exact Relation.
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("h_rec"), OVar("by_intro_ha_hb_exact_Relation_TransGen_tail_Relation_TransGen_single_lt_pipe_GameAdd_fst_ha_GameAdd_snd_hb_end"), OVar("Prod_theorem"), OVar("Acc_prod_gameAdd"), OOp("ha", (OVar("colon"), OVar("Acc"), OVar("ra"), OVar("a"),)), OOp("hb", (OVar("colon"), OVar("Acc"), OVar("rb"), OVar("b"),)), OVar("colon"), OVar("Acc"), OOp("Prod_GameAdd", (OVar("ra"), OVar("rb"),)), OOp("a", (OVar("b"),)),))
            results.append((rhs, "Mathlib: Prod_rprod_le_transGen_gameAdd"))
        except Exception:
            pass
    return results


def _r0186_recursion_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.GameAdd.recursion_eq
    # GameAdd.recursion hα hβ IH a b = IH a b fun a' b' _ => GameAdd.recursion hα hβ IH a' b'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "GameAdd_recursion", 5)
    if args is not None:
        try:
            rhs = OOp("IH", (args[3], args[4], OVar("fun"), OVar("a_prime"), OVar("b_prime"), OVar("_unknown"), OVar("eq_gt"), OVar("GameAdd_recursion"), args[0], args[1], args[2], OVar("a_prime"), OVar("b_prime"),))
            results.append((rhs, "Mathlib: Prod_GameAdd_recursion_eq"))
        except Exception:
            pass
    return results


def _r0187_prodUnique_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.prodUnique_apply
    # prodUnique α β x = (ofLex x).1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prodUnique", 3)
    if args is not None:
        try:
            rhs = OVar("ofLex_x_1")
            results.append((rhs, "Mathlib: Prod_Lex_prodUnique_apply"))
        except Exception:
            pass
    return results


def _r0188_uniqueProd_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.Lex.uniqueProd_apply
    # uniqueProd α β x = (ofLex x).2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uniqueProd", 3)
    if args is not None:
        try:
            rhs = OVar("ofLex_x_2")
            results.append((rhs, "Mathlib: Prod_Lex_uniqueProd_apply"))
        except Exception:
            pass
    return results


def _r0189_card_box_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.card_box_succ
    # #(box (n + 1) : Finset (α × β)) =       #(Icc (-n.succ : α) n.succ) * #(Icc (-n.succ : β) n.succ) -         #(Icc (-n : 
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_box_n_plus_1_colon_Finset_a_times_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("hash_Icc_minus_n_succ_colon_a_n_succ"), OOp("*", (OOp("-", (OVar("hash_Icc_minus_n_succ_colon_b_n_succ"), OVar("hash_Icc_minus_n_colon_a_n"))), OVar("hash_Icc_minus_n_colon_b_n")))))
            results.append((rhs, "Mathlib: Prod_card_box_succ"))
    except Exception:
        pass
    return results


def _r0190_mk_sup_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_sup_mk
    # (a₁, b₁) ⊔ (a₂, b₂) = (a₁ ⊔ a₂, b₁ ⊔ b₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_1_b_1", 2)
    if args is not None:
        try:
            rhs = OOp("a_1", (args[0], OVar("a_2"), OVar("b_1"), args[0], OVar("b_2"),))
            results.append((rhs, "Mathlib: Prod_mk_sup_mk"))
        except Exception:
            pass
    return results


def _r0191_fst_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.fst_sup
    # (p ⊔ q).fst = p.fst ⊔ q.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_q_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_fst", (OVar("_unknown"), OVar("q_fst"),))
            results.append((rhs, "Mathlib: Prod_fst_sup"))
    except Exception:
        pass
    return results


def _r0192_omegaSup_zip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.ωSup_zip
    # ωSup (c₀.zip c₁) = (ωSup c₀, ωSup c₁)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "omegaSup", 1)
    if args is not None:
        try:
            rhs = OOp("omegaSup", (OVar("c_0"), OVar("omegaSup"), OVar("c_1"),))
            results.append((rhs, "Mathlib: Prod_omegaSup_zip"))
        except Exception:
            pass
    return results


def _r0193_comul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.comul_apply
    # comul r =       TensorProduct.map (.inl R A B) (.inl R A B) (comul r.1) +       TensorProduct.map (.inr R A B) (.inr R A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comul", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("TensorProduct_map", (OOp("inl", (OVar("R"), OVar("A"), OVar("B"),)), OOp("inl", (OVar("R"), OVar("A"), OVar("B"),)), OOp("comul", (OVar("r_1"),)),)), OOp("TensorProduct_map", (OOp("inr", (OVar("R"), OVar("A"), OVar("B"),)), OOp("inr", (OVar("R"), OVar("A"), OVar("B"),)), OOp("comul", (OVar("r_2"),)),))))
            results.append((rhs, "Mathlib: Prod_comul_apply"))
        except Exception:
            pass
    return results


def _r0194_counit_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.counit_apply
    # (counit r : R) = counit r.1 + counit r.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "counit", 3)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("counit", (OVar("r_1"),)), OOp("counit", (OVar("r_2"),))))
            results.append((rhs, "Mathlib: Prod_counit_apply"))
        except Exception:
            pass
    return results


def _r0195_comul_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.comul_comp_inr
    # comul ∘ₗ inr R A B = TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comul", 5)
    if args is not None:
        try:
            rhs = OOp("TensorProduct_map", (OOp("inr", (args[2], args[3], args[4],)), OOp("inr", (args[2], args[3], args[4],)), args[0], OVar("comul"),))
            results.append((rhs, "Mathlib: Prod_comul_comp_inr"))
        except Exception:
            pass
    return results


def _r0196_comul_comp_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.comul_comp_fst
    # comul ∘ₗ .fst R A B = TensorProduct.map (.fst R A B) (.fst R A B) ∘ₗ comul
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comul", 5)
    if args is not None:
        try:
            rhs = OOp("TensorProduct_map", (OOp("fst", (args[2], args[3], args[4],)), OOp("fst", (args[2], args[3], args[4],)), args[0], OVar("comul"),))
            results.append((rhs, "Mathlib: Prod_comul_comp_fst"))
        except Exception:
            pass
    return results


def _r0197_comul_comp_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.comul_comp_snd
    # comul ∘ₗ .snd R A B = TensorProduct.map (.snd R A B) (.snd R A B) ∘ₗ comul
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comul", 5)
    if args is not None:
        try:
            rhs = OOp("TensorProduct_map", (OOp("snd", (args[2], args[3], args[4],)), OOp("snd", (args[2], args[3], args[4],)), args[0], OVar("comul"),))
            results.append((rhs, "Mathlib: Prod_comul_comp_snd"))
        except Exception:
            pass
    return results


def _r0198_counit_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.counit_comp_inr
    # counit ∘ₗ inr R A B = counit
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "counit", 5)
    if args is not None:
        try:
            rhs = OVar("counit")
            results.append((rhs, "Mathlib: Prod_counit_comp_inr"))
        except Exception:
            pass
    return results


def _r0199_binomialFamily_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HahnSeries.SummableFamily.binomialFamily_apply
    # binomialFamily x r n = Ring.choose r n • (x - 1) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "binomialFamily", 3)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("Ring_choose", (args[1], args[2], OVar("_unknown"), OOp("-", (args[0], OLit(1))),)), args[2]))
            results.append((rhs, "Mathlib: HahnSeries_SummableFamily_binomialFamily_apply"))
        except Exception:
            pass
    return results


def _r0200_binomialFamily_apply_of_orderTop_nonpos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HahnSeries.SummableFamily.binomialFamily_apply_of_orderTop_nonpos
    # binomialFamily x r n = 0 ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "binomialFamily", 3)
    if args is not None:
        try:
            rhs = OOp("**", (OLit(0), args[2]))
            results.append((rhs, "Mathlib: HahnSeries_SummableFamily_binomialFamily_apply_of_orderTop_nonpos"))
        except Exception:
            pass
    return results


def _r0201_powerSeriesFamily_of_not_orderTop_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HahnSeries.SummableFamily.powerSeriesFamily_of_not_orderTop_pos
    # powerSeriesFamily x f = powerSeriesFamily 0 f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "powerSeriesFamily", 2)
    if args is not None:
        try:
            rhs = OOp("powerSeriesFamily", (OLit(0), args[1],))
            results.append((rhs, "Mathlib: HahnSeries_SummableFamily_powerSeriesFamily_of_not_orderTop_pos"))
        except Exception:
            pass
    return results


def _r0202_powerSeriesFamily_of_orderTop_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HahnSeries.SummableFamily.powerSeriesFamily_of_orderTop_pos
    # powerSeriesFamily x f n = f.coeff n • x ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "powerSeriesFamily", 3)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("f_coeff", (args[2], OVar("_unknown"), args[0],)), args[2]))
            results.append((rhs, "Mathlib: HahnSeries_SummableFamily_powerSeriesFamily_of_orderTop_pos"))
        except Exception:
            pass
    return results


def _r0203_powerSeriesFamily_hsum_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HahnSeries.SummableFamily.powerSeriesFamily_hsum_zero
    # (powerSeriesFamily 0 f).hsum = f.constantCoeff • (1 : V⟦Γ⟧)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("powerSeriesFamily_0_f_hsum")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_constantCoeff", (OVar("_unknown"), OOp("_1", (OVar("colon"), OVar("V_G"),)),))
            results.append((rhs, "Mathlib: HahnSeries_SummableFamily_powerSeriesFamily_hsum_zero"))
    except Exception:
        pass
    return results


def _r0204_powerSeriesFamily_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HahnSeries.SummableFamily.powerSeriesFamily_add
    # powerSeriesFamily x (f + g) = powerSeriesFamily x f + powerSeriesFamily x g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "powerSeriesFamily", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("powerSeriesFamily", (args[0], OVar("f"),)), OOp("powerSeriesFamily", (args[0], OVar("g"),))))
            results.append((rhs, "Mathlib: HahnSeries_SummableFamily_powerSeriesFamily_add"))
        except Exception:
            pass
    return results


def _r0205_powerSeriesFamily_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HahnSeries.SummableFamily.powerSeriesFamily_smul
    # powerSeriesFamily x (r • f) = HahnSeries.single (0 : Γ) r • powerSeriesFamily x f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "powerSeriesFamily", 2)
    if args is not None:
        try:
            rhs = OOp("HahnSeries_single", (OOp("_0", (OVar("colon"), OVar("G"),)), OVar("r"), OVar("_unknown"), OVar("powerSeriesFamily"), args[0], OVar("f"),))
            results.append((rhs, "Mathlib: HahnSeries_SummableFamily_powerSeriesFamily_smul"))
        except Exception:
            pass
    return results


def _r0206_support_powerSeriesFamily_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HahnSeries.SummableFamily.support_powerSeriesFamily_subset
    # ((powerSeriesFamily x (a * b)).coeff g).support ⊆     (((powerSeriesFamily x a).mul (powerSeriesFamily x b)).coeff g).su
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("gt", (OVar("i_1"),)), OVar("i_2")))
            results.append((rhs, "Mathlib: HahnSeries_SummableFamily_support_powerSeriesFamily_subset"))
        except Exception:
            pass
    return results


def _r0207_hsum_powerSeriesFamily_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HahnSeries.SummableFamily.hsum_powerSeriesFamily_mul
    # (powerSeriesFamily x (a * b)).hsum =     ((powerSeriesFamily x a).mul (powerSeriesFamily x b)).hsum
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("powerSeriesFamily_x_a_star_b_hsum")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("powerSeriesFamily_x_a_mul_powerSeriesFamily_x_b_hsum")
            results.append((rhs, "Mathlib: HahnSeries_SummableFamily_hsum_powerSeriesFamily_mul"))
    except Exception:
        pass
    return results


def _r0208_coe_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SummableFamily.coe_mk
    # (⟨toFun, h1, h2⟩ : SummableFamily Γ R α) = toFun
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFun_h1_h2", 5)
    if args is not None:
        try:
            rhs = OVar("toFun")
            results.append((rhs, "Mathlib: SummableFamily_coe_mk"))
        except Exception:
            pass
    return results


def _r0209_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SummableFamily.ext
    # s = t
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("t")
            results.append((rhs, "Mathlib: SummableFamily_ext"))
    except Exception:
        pass
    return results


def _r0210_coe_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SummableFamily.coe_add
    # ⇑(s + t) = s + t
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_plus_t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: SummableFamily_coe_add"))
    except Exception:
        pass
    return results


def _r0211_toNNReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.toNNReal
    # Summable fun n => (f n).toNNReal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Summable", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("f_n_toNNReal"),))
            results.append((rhs, "Mathlib: Summable_toNNReal"))
        except Exception:
            pass
    return results


def _r0212_toCompl_tsum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.toCompl_tsum
    # ∑'[L] i, toCompl (f i) = ∑'[L] i, f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime_L", 3)
    if args is not None:
        try:
            rhs = OOp("prime_L", (args[0], OVar("f"), args[0],))
            results.append((rhs, "Mathlib: Summable_toCompl_tsum"))
        except Exception:
            pass
    return results


def _r0213_tsum_const_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.tsum_const_smul
    # ∑'[L] i, b • f i = b • ∑'[L] i, f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime_L", 5)
    if args is not None:
        try:
            rhs = OOp("b", (args[2], OVar("prime_L"), args[4], args[3], args[4],))
            results.append((rhs, "Mathlib: Summable_tsum_const_smul"))
        except Exception:
            pass
    return results


def _r0214_tsum_smul_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.tsum_smul_const
    # ∑'[L] z, f z • a = (∑'[L] z, f z) • a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime_L", 5)
    if args is not None:
        try:
            rhs = OOp("prime_L_z_f_z", (args[3], args[4],))
            results.append((rhs, "Mathlib: Summable_tsum_smul_const"))
        except Exception:
            pass
    return results


def _r0215_tsum_mul_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.tsum_mul_left
    # ∑'[L] i, a * f i = a * ∑'[L] i, f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), OOp("prime_L", (OVar("i"), OVar("f"), OVar("i"),))))
            results.append((rhs, "Mathlib: Summable_tsum_mul_left"))
        except Exception:
            pass
    return results


def _r0216_tsum_mul_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.tsum_mul_right
    # ∑'[L] i, f i * a = (∑'[L] i, f i) * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("prime_L", (OVar("i"), OVar("f"), OVar("i"),)), args[1]))
            results.append((rhs, "Mathlib: Summable_tsum_mul_right"))
        except Exception:
            pass
    return results


def _r0217_tsum_mul_tsum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.tsum_mul_tsum
    # ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × κ, f z.1 * g z.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("product", (OOp("prime", (OVar("z"), OVar("colon"), OVar("i"),)), OOp("k", (OVar("f"), OVar("z_1"),)))), OOp("g", (OVar("z_2"),))))
            results.append((rhs, "Mathlib: Summable_tsum_mul_tsum"))
        except Exception:
            pass
    return results


def _r0218_tsum_mul_tsum_eq_tsum_sum_antidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
    # ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("in", (OOp("prime", (OVar("n"), OVar("_unknown"), OVar("kl"),)), OOp("antidiagonal", (OVar("n"), OVar("f"), OVar("kl_1"),)))), OOp("g", (OVar("kl_2"),))))
            results.append((rhs, "Mathlib: Summable_tsum_mul_tsum_eq_tsum_sum_antidiagonal"))
        except Exception:
            pass
    return results


def _r0219_tsum_mul_tsum_eq_tsum_sum_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.tsum_mul_tsum_eq_tsum_sum_range
    # ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k ∈ range (n + 1), f k * g (n - k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("in", (OOp("prime", (OVar("n"), OVar("_unknown"), OVar("k"),)), OOp("range", (OVar("n_plus_1"), OVar("f"), OVar("k"),)))), OOp("g", (OOp("-", (OVar("n"), OVar("k"))),))))
            results.append((rhs, "Mathlib: Summable_tsum_mul_tsum_eq_tsum_sum_range"))
        except Exception:
            pass
    return results


def _r0220_tsum_pow_mul_one_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.tsum_pow_mul_one_sub
    # (∑' (i : ℕ), x ^ i) * (1 - x) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Summable_tsum_pow_mul_one_sub"))
        except Exception:
            pass
    return results


def _r0221_one_sub_mul_tsum_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Summable.one_sub_mul_tsum_pow
    # (1 - x) * ∑' (i : ℕ), x ^ i = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Summable_one_sub_mul_tsum_pow"))
        except Exception:
            pass
    return results


def _r0222_neBot_or_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SummationFilter.neBot_or_eq_bot
    # L.NeBot ∨ L.filter = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 2)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: SummationFilter_neBot_or_eq_bot"))
        except Exception:
            pass
    return results


def _r0223_support_eq_limsInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SummationFilter.support_eq_limsInf
    # support L = limsInf (L.filter.map (↑))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "support", 1)
    if args is not None:
        try:
            rhs = OOp("limsInf", (OOp("L_filter_map", (OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: SummationFilter_support_eq_limsInf"))
        except Exception:
            pass
    return results


def _r0224_support_eq_univ_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SummationFilter.support_eq_univ_iff
    # L.support = univ ↔ L.filter ≤ atTop
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("iff", (OVar("univ"), OVar("L_filter"))), OVar("atTop")))
            results.append((rhs, "Mathlib: SummationFilter_support_eq_univ_iff"))
    except Exception:
        pass
    return results


def _r0225_support_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SummationFilter.support_eq_univ
    # L.support = univ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: SummationFilter_support_eq_univ"))
    except Exception:
        pass
    return results


def _r0226_evalFacProp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Products.evalFacProp
    # l.eval (π C J) ∘ ProjRestrict C J = l.eval C
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("l_eval", (OVar("C"),))
            results.append((rhs, "Mathlib: Products_evalFacProp"))
        except Exception:
            pass
    return results


def _r0227_evalFacProps(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Products.evalFacProps
    # l.eval (π C J) ∘ ProjRestricts C hJK = l.eval (π C K)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("l_eval", (OOp("pi", (OVar("C"), OVar("K"),)),))
            results.append((rhs, "Mathlib: Products_evalFacProps"))
        except Exception:
            pass
    return results


def _r0228_eval_pis(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Products.eval_πs
    # πs C o (l.eval (π C (ord I · < o))) = l.eval C
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pis", 3)
    if args is not None:
        try:
            rhs = OOp("l_eval", (args[0],))
            results.append((rhs, "Mathlib: Products_eval_pis"))
        except Exception:
            pass
    return results


def _r0229_eval_pis_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Products.eval_πs_image
    # eval C '' { m | m < l } =     (πs C o) '' (eval (π C (ord I · < o)) '' { m | m < l })
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eval", 3)
    if args is not None:
        try:
            rhs = OOp("pis_C_o", (args[1], OOp("eval", (OOp("pi", (args[0], OOp("<", (OOp("ord", (OVar("I"), OVar("_unknown"),)), OVar("o"))),)), args[1], args[2],)),))
            results.append((rhs, "Mathlib: Products_eval_pis_image"))
        except Exception:
            pass
    return results


def _r0230_max_eq_o_cons_tail(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Products.max_eq_o_cons_tail
    # l.val = term I ho :: l.Tail.val
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("term", (OVar("I"), OVar("ho"), OVar("colon_colon"), OVar("l_Tail_val"),))
            results.append((rhs, "Mathlib: Products_max_eq_o_cons_tail"))
    except Exception:
        pass
    return results


def _r0231_evalCons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Products.evalCons
    # Products.eval C ⟨a::l,hla⟩ =     (e C a) * Products.eval C ⟨l,List.IsChain.sublist hla (List.tail_sublist (a::l))⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Products_eval", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("e", (args[0], OVar("a"),)), OOp("Products_eval", (args[0], OVar("l_List_IsChain_sublist_hla_List_tail_sublist_acolon_colon_l"),))))
            results.append((rhs, "Mathlib: Products_evalCons"))
        except Exception:
            pass
    return results


def _r0232_max_eq_eval(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Products.max_eq_eval
    # Linear_CC' C hsC ho (l.eval C) = l.Tail.eval (C' C ho)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Linear_CC_prime", 4)
    if args is not None:
        try:
            rhs = OOp("l_Tail_eval", (OOp("C_prime", (args[0], args[2],)),))
            results.append((rhs, "Mathlib: Products_max_eq_eval"))
        except Exception:
            pass
    return results


def _r0233_lt_nil_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Profinite.NobelingProof.Products.lt_nil_empty
    # { m : Products I | m < Products.nil } = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_colon_Products_I_pipe_m_lt_Products_nil")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Profinite_NobelingProof_Products_lt_nil_empty"))
    except Exception:
        pass
    return results


def _r0234_SigmaCompactSpace_iff_exists_compact_cov(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SigmaCompactSpace_iff_exists_compact_covering
    # SigmaCompactSpace X ↔ ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: SigmaCompactSpace_iff_exists_compact_covering"))
        except Exception:
            pass
    return results


def _r0235_exists_compact_covering(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SigmaCompactSpace.exists_compact_covering
    # ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: SigmaCompactSpace_exists_compact_covering"))
        except Exception:
            pass
    return results


def _r0236_isConnected_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.isConnected_iff
    # IsConnected s ↔ ∃ i t, IsConnected t ∧ s = Sigma.mk i '' t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("Sigma_mk", (OVar("i"), OVar("prime_prime"), OVar("t"),))
            results.append((rhs, "Mathlib: Sigma_isConnected_iff"))
        except Exception:
            pass
    return results


def _r0237_isPreconnected_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.isPreconnected_iff
    # IsPreconnected s ↔ ∃ i t, IsPreconnected t ∧ s = Sigma.mk i '' t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("Sigma_mk", (OVar("i"), OVar("prime_prime"), OVar("t"),))
            results.append((rhs, "Mathlib: Sigma_isPreconnected_iff"))
        except Exception:
            pass
    return results


def _r0238_isConnected_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.isConnected_iff
    # IsConnected s ↔       (∃ t, IsConnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsConnected t ∧ s = Sum.inr '' t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("Sum_inr", (OVar("prime_prime"), OVar("t"),))
            results.append((rhs, "Mathlib: Sum_isConnected_iff"))
        except Exception:
            pass
    return results


def _r0239_isPreconnected_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.isPreconnected_iff
    # IsPreconnected s ↔       (∃ t, IsPreconnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsPreconnected t ∧ s = Sum.inr '' t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("Sum_inr", (OVar("prime_prime"), OVar("t"),))
            results.append((rhs, "Mathlib: Sum_isPreconnected_iff"))
        except Exception:
            pass
    return results


def _r0240_nhds_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.nhds_mk
    # 𝓝 (⟨i, x⟩ : Sigma σ) = Filter.map (Sigma.mk i) (𝓝 x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("Filter_map", (OOp("Sigma_mk", (OVar("i"),)), OOp("_unknown", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Sigma_nhds_mk"))
        except Exception:
            pass
    return results


def _r0241_nhds_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.nhds_eq
    # 𝓝 x = Filter.map (Sigma.mk x.1) (𝓝 x.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("Filter_map", (OOp("Sigma_mk", (OVar("x_1"),)), OOp("_unknown", (OVar("x_2"),)),))
            results.append((rhs, "Mathlib: Sigma_nhds_eq"))
        except Exception:
            pass
    return results


def _r0242_edist_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.edist_eq
    # edist x y = max (edist x.1 y.1) (edist x.2 y.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "edist", 2)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("edist", (OVar("x_1"), OVar("y_1"),)), OOp("edist", (OVar("x_2"), OVar("y_2"),)),))
            results.append((rhs, "Mathlib: Prod_edist_eq"))
        except Exception:
            pass
    return results


def _r0243_left_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bundle.Trivialization.Prod.left_inv
    # Prod.invFun' e₁ e₂ (Prod.toFun' e₁ e₂ x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Prod_invFun_prime", 3)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Bundle_Trivialization_Prod_left_inv"))
        except Exception:
            pass
    return results


def _r0244_right_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bundle.Trivialization.Prod.right_inv
    # Prod.toFun' e₁ e₂ (Prod.invFun' e₁ e₂ x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Prod_toFun_prime", 3)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Bundle_Trivialization_Prod_right_inv"))
        except Exception:
            pass
    return results


def _r0245_dist_eq_glueDist(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.dist_eq_glueDist
    # Sum.dist p q =       glueDist (fun _ : Unit => Nonempty.some ⟨x⟩) (fun _ : Unit => Nonempty.some ⟨y⟩) 1 p q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sum_dist", 2)
    if args is not None:
        try:
            rhs = OOp("glueDist", (OOp("fun", (OVar("_unknown"), OVar("colon"), OVar("Unit"), OVar("eq_gt"), OVar("Nonempty_some"), OVar("x"),)), OOp("fun", (OVar("_unknown"), OVar("colon"), OVar("Unit"), OVar("eq_gt"), OVar("Nonempty_some"), OVar("y"),)), OLit(1), args[0], args[1],))
            results.append((rhs, "Mathlib: Sum_dist_eq_glueDist"))
        except Exception:
            pass
    return results


def _r0246_dist_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.dist_comm
    # Sum.dist x y = Sum.dist y x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sum_dist", 2)
    if args is not None:
        try:
            rhs = OOp("Sum_dist", (args[1], args[0],))
            results.append((rhs, "Mathlib: Sum_dist_comm"))
        except Exception:
            pass
    return results


def _r0247_dist_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.dist_eq
    # dist x y = Sum.dist x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dist", 2)
    if args is not None:
        try:
            rhs = OOp("Sum_dist", (args[0], args[1],))
            results.append((rhs, "Mathlib: Sum_dist_eq"))
        except Exception:
            pass
    return results


def _r0248_dist_same(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.dist_same
    # dist (Sigma.mk i x) ⟨i, y⟩ = dist x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dist", 2)
    if args is not None:
        try:
            rhs = OOp("dist", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: Sigma_dist_same"))
        except Exception:
            pass
    return results


def _r0249_fst_eq_of_dist_lt_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.fst_eq_of_dist_lt_one
    # x.1 = y.1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y_1")
            results.append((rhs, "Mathlib: Sigma_fst_eq_of_dist_lt_one"))
    except Exception:
        pass
    return results


def _r0250_dist_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.dist_eq
    # dist x y = max (dist x.1 y.1) (dist x.2 y.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dist", 2)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("dist", (OVar("x_1"), OVar("y_1"),)), OOp("dist", (OVar("x_2"), OVar("y_2"),)),))
            results.append((rhs, "Mathlib: Prod_dist_eq"))
        except Exception:
            pass
    return results


def _r0251_uniformity(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.uniformity
    # 𝓤 (α ⊕ β) = map (Prod.map inl inl) (𝓤 α) ⊔ map (Prod.map inr inr) (𝓤 β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("map", (OOp("Prod_map", (OVar("inl"), OVar("inl"),)), OOp("_unknown", (OVar("a"),)), OVar("_unknown"), OVar("map"), OOp("Prod_map", (OVar("inr"), OVar("inr"),)), OOp("_unknown", (OVar("b"),)),))
            results.append((rhs, "Mathlib: Sum_uniformity"))
        except Exception:
            pass
    return results


def _r0252_associated_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.associated_iff
    # x ~ᵤ z ↔ x.1 ~ᵤ z.1 ∧ x.2 ~ᵤ z.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("x_1", (args[0], OVar("z_1"),)), OOp("x_2", (args[0], OVar("z_2"),))))
            results.append((rhs, "Mathlib: Prod_associated_iff"))
        except Exception:
            pass
    return results


def _r0253_mk_dvd_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_dvd_mk
    # (x₁, x₂) ∣ (y₁, y₂) ↔ x₁ ∣ y₁ ∧ x₂ ∣ y₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_1_x_2", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("x_1", (args[0], OVar("y_1"),)), OOp("x_2", (args[0], OVar("y_2"),))))
            results.append((rhs, "Mathlib: Prod_mk_dvd_mk"))
        except Exception:
            pass
    return results


def _r0254_semiconjBy_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.semiconjBy_iff
    # SemiconjBy x y z ↔ SemiconjBy x.1 y.1 z.1 ∧ SemiconjBy x.2 y.2 z.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "SemiconjBy", 3)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("SemiconjBy", (OVar("x_1"), OVar("y_1"), OVar("z_1"),)), OOp("SemiconjBy", (OVar("x_2"), OVar("y_2"), OVar("z_2"),))))
            results.append((rhs, "Mathlib: Prod_semiconjBy_iff"))
        except Exception:
            pass
    return results


def _r0255_commute_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.commute_iff
    # Commute x y ↔ Commute x.1 y.1 ∧ Commute x.2 y.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Commute", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("Commute", (OVar("x_1"), OVar("y_1"),)), OOp("Commute", (OVar("x_2"), OVar("y_2"),))))
            results.append((rhs, "Mathlib: Prod_commute_iff"))
        except Exception:
            pass
    return results


def _r0256_isUnit_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.isUnit_iff
    # IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsUnit", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsUnit", (OVar("x_1"),)), OOp("IsUnit", (OVar("x_2"),))))
            results.append((rhs, "Mathlib: Prod_isUnit_iff"))
        except Exception:
            pass
    return results


def _r0257_one_le_elim_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.one_le_elim_iff
    # 1 ≤ Sum.elim v₁ v₂ ↔ 1 ≤ v₁ ∧ 1 ≤ v₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(1), OOp("<=", (OOp("and", (OVar("v_1"), OLit(1))), OVar("v_2")))))
            results.append((rhs, "Mathlib: Sum_one_le_elim_iff"))
        except Exception:
            pass
    return results


def _r0258_elim_le_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.elim_le_one_iff
    # Sum.elim v₁ v₂ ≤ 1 ↔ v₁ ≤ 1 ∧ v₂ ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("v_1"), OOp("<=", (OOp("and", (OLit(1), OVar("v_2"))), OLit(1)))))
            results.append((rhs, "Mathlib: Sum_elim_le_one_iff"))
        except Exception:
            pass
    return results


def _r0259_isLeftRegular_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.isLeftRegular_mk
    # IsLeftRegular (a, b) ↔ IsLeftRegular a ∧ IsLeftRegular b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsLeftRegular", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsLeftRegular", (OVar("a"),)), OOp("IsLeftRegular", (OVar("b"),))))
            results.append((rhs, "Mathlib: Prod_isLeftRegular_mk"))
        except Exception:
            pass
    return results


def _r0260_isRightRegular_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.isRightRegular_mk
    # IsRightRegular (a, b) ↔ IsRightRegular a ∧ IsRightRegular b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsRightRegular", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsRightRegular", (OVar("a"),)), OOp("IsRightRegular", (OVar("b"),))))
            results.append((rhs, "Mathlib: Prod_isRightRegular_mk"))
        except Exception:
            pass
    return results


def _r0261_isRegular_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.isRegular_mk
    # IsRegular (a, b) ↔ IsRegular a ∧ IsRegular b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsRegular", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsRegular", (OVar("a"),)), OOp("IsRegular", (OVar("b"),))))
            results.append((rhs, "Mathlib: Prod_isRegular_mk"))
        except Exception:
            pass
    return results


def _r0262_isSMulRegular_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.isSMulRegular_iff
    # IsSMulRegular (R × S) r ↔ IsSMulRegular R r ∧ IsSMulRegular S r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsSMulRegular", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsSMulRegular", (OVar("R"), args[1],)), OOp("IsSMulRegular", (OVar("S"), args[1],))))
            results.append((rhs, "Mathlib: Prod_isSMulRegular_iff"))
        except Exception:
            pass
    return results


def _r0263_finite_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.finite_iff
    # Finite (α × β) ↔ Finite α ∧ Finite β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Finite", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("Finite", (OVar("a"),)), OOp("Finite", (OVar("b"),))))
            results.append((rhs, "Mathlib: Prod_finite_iff"))
        except Exception:
            pass
    return results


def _r0264_map_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.map_injective
    # Injective (map f g) ↔ Injective f ∧ Injective g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("injective", (OVar("f"),)), OOp("injective", (OVar("g"),))))
            results.append((rhs, "Mathlib: Prod_map_injective"))
        except Exception:
            pass
    return results


def _r0265_map_surjective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.map_surjective
    # Surjective (map f g) ↔ Surjective f ∧ Surjective g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "surjective", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("surjective", (OVar("f"),)), OOp("surjective", (OVar("g"),))))
            results.append((rhs, "Mathlib: Prod_map_surjective"))
        except Exception:
            pass
    return results


def _r0266_map_bijective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.map_bijective
    # Bijective (map f g) ↔ Bijective f ∧ Bijective g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bijective", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("bijective", (OVar("f"),)), OOp("bijective", (OVar("g"),))))
            results.append((rhs, "Mathlib: Prod_map_bijective"))
        except Exception:
            pass
    return results


def _r0267_map_leftInverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.map_leftInverse
    # LeftInverse (map f₁ g₁) (map f₂ g₂) ↔ LeftInverse f₁ f₂ ∧ LeftInverse g₁ g₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LeftInverse", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("LeftInverse", (OVar("f_1"), OVar("f_2"),)), OOp("LeftInverse", (OVar("g_1"), OVar("g_2"),))))
            results.append((rhs, "Mathlib: Prod_map_leftInverse"))
        except Exception:
            pass
    return results


def _r0268_map_rightInverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.map_rightInverse
    # RightInverse (map f₁ g₁) (map f₂ g₂) ↔ RightInverse f₁ f₂ ∧ RightInverse g₁ g₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "RightInverse", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("RightInverse", (OVar("f_1"), OVar("f_2"),)), OOp("RightInverse", (OVar("g_1"), OVar("g_2"),))))
            results.append((rhs, "Mathlib: Prod_map_rightInverse"))
        except Exception:
            pass
    return results


def _r0269_map_involutive(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.map_involutive
    # Involutive (map f g) ↔ Involutive f ∧ Involutive g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Involutive", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("Involutive", (OVar("f"),)), OOp("Involutive", (OVar("g"),))))
            results.append((rhs, "Mathlib: Prod_map_involutive"))
        except Exception:
            pass
    return results


def _r0270_fst_surjective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.fst_surjective_iff
    # Surjective (fst : (Σ a, β a) → α) ↔ ∀ a, Nonempty (β a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "surjective", 1)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("a"), OVar("Nonempty"), OOp("b", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Sigma_fst_surjective_iff"))
        except Exception:
            pass
    return results


def _r0271_fst_injective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.fst_injective_iff
    # Injective (fst : (Σ a, β a) → α) ↔ ∀ a, Subsingleton (β a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 1)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("a"), OVar("Subsingleton"), OOp("b", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Sigma_fst_injective_iff"))
        except Exception:
            pass
    return results


def _r0272_lex_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.lex_swap
    # Lex (Function.swap r) s a b ↔ Lex r (fun i => Function.swap (s i)) b a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Lex", 4)
    if args is not None:
        try:
            rhs = OOp("Lex", (OVar("r"), OOp("fun", (OVar("i"), OVar("eq_gt"), OVar("Function_swap"), OOp("s", (OVar("i"),)),)), args[3], args[2],))
            results.append((rhs, "Mathlib: Sigma_lex_swap"))
        except Exception:
            pass
    return results


def _r0273_mk_le_mk_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.mk_le_mk_iff
    # (⟨i, a⟩ : Sigma α) ≤ ⟨i, b⟩ ↔ a ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("a"), OVar("b")))
            results.append((rhs, "Mathlib: Sigma_mk_le_mk_iff"))
        except Exception:
            pass
    return results


def _r0274_exists_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.exists_sum
    # (∃ fab, p fab) ↔ (∃ fa fb, p (Sum.rec fa fb))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = OOp("exists", (OVar("fa"), OVar("fb"), args[1], OOp("Sum_rec", (OVar("fa"), OVar("fb"),)),))
            results.append((rhs, "Mathlib: Sum_exists_sum"))
        except Exception:
            pass
    return results


def _r0275_elim_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.elim_injective
    # Injective (Sum.elim f g) ↔ Injective f ∧ Injective g ∧ ∀ a b, f a ≠ g b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 1)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OOp("injective", (OVar("f"),)), OOp("and", (OOp("injective", (OVar("g"),)), OOp("forall", (OVar("a"), OVar("b"), OVar("f"), OVar("a"),)))))), OOp("g", (OVar("b"),))))
            results.append((rhs, "Mathlib: Sum_elim_injective"))
        except Exception:
            pass
    return results


def _r0276_map_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.map_injective
    # Injective (Sum.map f g) ↔ Injective f ∧ Injective g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("injective", (OVar("f"),)), OOp("injective", (OVar("g"),))))
            results.append((rhs, "Mathlib: Sum_map_injective"))
        except Exception:
            pass
    return results


def _r0277_map_surjective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.map_surjective
    # Surjective (Sum.map f g) ↔ Surjective f ∧ Surjective g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "surjective", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("surjective", (OVar("f"),)), OOp("surjective", (OVar("g"),))))
            results.append((rhs, "Mathlib: Sum_map_surjective"))
        except Exception:
            pass
    return results


def _r0278_map_bijective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.map_bijective
    # Bijective (Sum.map f g) ↔ Bijective f ∧ Bijective g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bijective", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("bijective", (OVar("f"),)), OOp("bijective", (OVar("g"),))))
            results.append((rhs, "Mathlib: Sum_map_bijective"))
        except Exception:
            pass
    return results


def _r0279_elim_le_elim_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.elim_le_elim_iff
    # Sum.elim u₁ u₂ ≤ Sum.elim v₁ v₂ ↔ u₁ ≤ v₁ ∧ u₂ ≤ v₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("u_1"), OOp("<=", (OOp("and", (OVar("v_1"), OVar("u_2"))), OVar("v_2")))))
            results.append((rhs, "Mathlib: Sum_elim_le_elim_iff"))
        except Exception:
            pass
    return results


def _r0280_const_le_elim_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.const_le_elim_iff
    # Function.const _ b ≤ Sum.elim v₁ v₂ ↔ Function.const _ b ≤ v₁ ∧ Function.const _ b ≤ v₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("const", (OVar("_unknown"), OVar("b"),)), OOp("<=", (OOp("and", (OVar("v_1"), OOp("const", (OVar("_unknown"), OVar("b"),)))), OVar("v_2")))))
            results.append((rhs, "Mathlib: Sum_const_le_elim_iff"))
        except Exception:
            pass
    return results


def _r0281_elim_le_const_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.elim_le_const_iff
    # Sum.elim u₁ u₂ ≤ Function.const _ b ↔ u₁ ≤ Function.const _ b ∧ u₂ ≤ Function.const _ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("u_1"), OOp("<=", (OOp("and", (OOp("const", (OVar("_unknown"), OVar("b"),)), OVar("u_2"))), OOp("const", (OVar("_unknown"), OVar("b"),))))))
            results.append((rhs, "Mathlib: Sum_elim_le_const_iff"))
        except Exception:
            pass
    return results


def _r0282_le_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.le_def
    # x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("x_1"), OOp("<=", (OOp("and", (OVar("y_1"), OVar("x_2"))), OVar("y_2")))))
            results.append((rhs, "Mathlib: Prod_le_def"))
        except Exception:
            pass
    return results


def _r0283_mk_le_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_le_mk
    # (a₁, b₁) ≤ (a₂, b₂) ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("a_1"), OOp("<=", (OOp("and", (OVar("a_2"), OVar("b_1"))), OVar("b_2")))))
            results.append((rhs, "Mathlib: Prod_mk_le_mk"))
        except Exception:
            pass
    return results


def _r0284_swap_le_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.swap_le_swap
    # x.swap ≤ y.swap ↔ x ≤ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Prod_swap_le_swap"))
        except Exception:
            pass
    return results


def _r0285_swap_wcovBy_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.swap_wcovBy_swap
    # x.swap ⩿ y.swap ↔ x ⩿ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_swap", 2)
    if args is not None:
        try:
            rhs = OOp("x", (args[0], OVar("y"),))
            results.append((rhs, "Mathlib: Prod_swap_wcovBy_swap"))
        except Exception:
            pass
    return results


def _r0286_mk_wcovBy_mk_iff_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_wcovBy_mk_iff_left
    # (a₁, b) ⩿ (a₂, b) ↔ a₁ ⩿ a₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_1_b", 2)
    if args is not None:
        try:
            rhs = OOp("a_1", (args[0], OVar("a_2"),))
            results.append((rhs, "Mathlib: Prod_mk_wcovBy_mk_iff_left"))
        except Exception:
            pass
    return results


def _r0287_mk_wcovBy_mk_iff_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_wcovBy_mk_iff_right
    # (a, b₁) ⩿ (a, b₂) ↔ b₁ ⩿ b₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_b_1", 2)
    if args is not None:
        try:
            rhs = OOp("b_1", (args[0], OVar("b_2"),))
            results.append((rhs, "Mathlib: Prod_mk_wcovBy_mk_iff_right"))
        except Exception:
            pass
    return results


def _r0288_mk_covBy_mk_iff_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_covBy_mk_iff_left
    # (a₁, b) ⋖ (a₂, b) ↔ a₁ ⋖ a₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_1_b", 2)
    if args is not None:
        try:
            rhs = OOp("a_1", (args[0], OVar("a_2"),))
            results.append((rhs, "Mathlib: Prod_mk_covBy_mk_iff_left"))
        except Exception:
            pass
    return results


def _r0289_mk_covBy_mk_iff_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.mk_covBy_mk_iff_right
    # (a, b₁) ⋖ (a, b₂) ↔ b₁ ⋖ b₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_b_1", 2)
    if args is not None:
        try:
            rhs = OOp("b_1", (args[0], OVar("b_2"),))
            results.append((rhs, "Mathlib: Prod_mk_covBy_mk_iff_right"))
        except Exception:
            pass
    return results


def _r0290_disjoint_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.disjoint_iff
    # Disjoint x y ↔ Disjoint x.1 y.1 ∧ Disjoint x.2 y.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Disjoint", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("Disjoint", (OVar("x_1"), OVar("y_1"),)), OOp("Disjoint", (OVar("x_2"), OVar("y_2"),))))
            results.append((rhs, "Mathlib: Prod_disjoint_iff"))
        except Exception:
            pass
    return results


def _r0291_codisjoint_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.codisjoint_iff
    # Codisjoint x y ↔ Codisjoint x.1 y.1 ∧ Codisjoint x.2 y.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Codisjoint", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("Codisjoint", (OVar("x_1"), OVar("y_1"),)), OOp("Codisjoint", (OVar("x_2"), OVar("y_2"),))))
            results.append((rhs, "Mathlib: Prod_codisjoint_iff"))
        except Exception:
            pass
    return results


def _r0292_isCompl_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.isCompl_iff
    # IsCompl x y ↔ IsCompl x.1 y.1 ∧ IsCompl x.2 y.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsCompl", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsCompl", (OVar("x_1"), OVar("y_1"),)), OOp("IsCompl", (OVar("x_2"), OVar("y_2"),))))
            results.append((rhs, "Mathlib: Prod_isCompl_iff"))
        except Exception:
            pass
    return results


def _r0293_gameAdd_swap_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.gameAdd_swap_swap
    # ∀ a b : α × β, GameAdd rβ rα a.swap b.swap ↔ GameAdd rα rβ a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "GameAdd", 4)
    if args is not None:
        try:
            rhs = OOp("GameAdd", (args[1], args[0], OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Prod_gameAdd_swap_swap"))
        except Exception:
            pass
    return results


def _r0294_isBot_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.isBot_iff
    # IsBot x ↔ IsBot x.1 ∧ IsBot x.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsBot", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsBot", (OVar("x_1"),)), OOp("IsBot", (OVar("x_2"),))))
            results.append((rhs, "Mathlib: Prod_isBot_iff"))
        except Exception:
            pass
    return results


def _r0295_isMin_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.isMin_iff
    # IsMin x ↔ IsMin x.1 ∧ IsMin x.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsMin", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsMin", (OVar("x_1"),)), OOp("IsMin", (OVar("x_2"),))))
            results.append((rhs, "Mathlib: Prod_isMin_iff"))
        except Exception:
            pass
    return results


def _r0296_lt_iff_lex_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Products.lt_iff_lex_lt
    # l < m ↔ List.Lex (· < ·) l.val m.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("List_Lex", (OOp("<", (OVar("_unknown"), OVar("_unknown"))), OVar("l_val"), OVar("m_val"),))
            results.append((rhs, "Mathlib: Products_lt_iff_lex_lt"))
        except Exception:
            pass
    return results


def _r0297_limitOrdinal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Products.limitOrdinal
    # l.isGood (π C (ord I · < o)) ↔     ∃ (o' : Ordinal), o' < o ∧ l.isGood (π C (ord I · < o'))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_isGood", 1)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("exists", (OVar("o_prime_colon_Ordinal"), OVar("o_prime"),)), OOp("and", (OVar("o"), OOp("l_isGood", (OOp("pi", (OVar("C"), OOp("<", (OOp("ord", (OVar("I"), OVar("_unknown"),)), OVar("o_prime"))),)),))))))
            results.append((rhs, "Mathlib: Products_limitOrdinal"))
        except Exception:
            pass
    return results


def _r0298_noncompactSpace_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.noncompactSpace_iff
    # NoncompactSpace (X × Y) ↔ NoncompactSpace X ∧ Nonempty Y ∨ Nonempty X ∧ NoncompactSpace Y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NoncompactSpace", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("NoncompactSpace", (OVar("X"),)), OOp("and", (OOp("or", (OOp("Nonempty", (OVar("Y"),)), OOp("Nonempty", (OVar("X"),)))), OOp("NoncompactSpace", (OVar("Y"),))))))
            results.append((rhs, "Mathlib: Prod_noncompactSpace_iff"))
        except Exception:
            pass
    return results


def _r0299_tendsto_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Prod.tendsto_iff
    # Tendsto seq f (𝓝 p) ↔       Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) ∧ Tendsto (fun n => (seq n).snd) f (𝓝 p.snd)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Tendsto", 3)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("Tendsto", (OOp("fun", (OVar("n"), OVar("eq_gt"), OVar("seq_n_fst"),)), args[1], OOp("_unknown", (OVar("p_fst"),)),)), OOp("Tendsto", (OOp("fun", (OVar("n"), OVar("eq_gt"), OVar("seq_n_snd"),)), args[1], OOp("_unknown", (OVar("p_snd"),)),))))
            results.append((rhs, "Mathlib: Prod_tendsto_iff"))
        except Exception:
            pass
    return results


def _r0300_mem_uniformity_iff_glueDist(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.mem_uniformity_iff_glueDist
    # s ∈ 𝓤 (X ⊕ Y) ↔ ∃ δ > 0, ∀ a b, glueDist Φ Ψ ε a b < δ → (a, b) ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp(">", (OOp("exists", (OVar("d"),)), OOp("_0", (OVar("forall"), OVar("a"), OVar("b"), OVar("glueDist"), OVar("_unknown"), OVar("_unknown"), OVar("e"), OVar("a"), OVar("b"),)))), OOp("implies", (OVar("d"), OOp("in", (OOp("a", (OVar("b"),)), args[0]))))))
            results.append((rhs, "Mathlib: Sum_mem_uniformity_iff_glueDist"))
        except Exception:
            pass
    return results


def _r0301_mem_uniformity(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sum.mem_uniformity
    # s ∈ 𝓤 (X ⊕ Y) ↔ ∃ ε > 0, ∀ a b, Sum.dist a b < ε → (a, b) ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp(">", (OOp("exists", (OVar("e"),)), OOp("_0", (OVar("forall"), OVar("a"), OVar("b"), OVar("Sum_dist"), OVar("a"), OVar("b"),)))), OOp("implies", (OVar("e"), OOp("in", (OOp("a", (OVar("b"),)), args[0]))))))
            results.append((rhs, "Mathlib: Sum_mem_uniformity"))
        except Exception:
            pass
    return results


def _r0302_isOpen_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Sigma.isOpen_iff
    # IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsOpen", 1)
    if args is not None:
        try:
            rhs = OOp("<", (OOp(">", (OOp("in", (OOp("forall", (OVar("x"),)), OOp("s", (OVar("exists"), OVar("e"),)))), OOp("_0", (OVar("forall"), OVar("y"), OVar("dist"), OVar("x"), OVar("y"),)))), OOp("implies", (OVar("e"), OOp("in", (OVar("y"), args[0]))))))
            results.append((rhs, "Mathlib: Sigma_isOpen_iff"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_prod rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "**", "+", "-", "//", "<", "<=", "==", "Codisjoint", "Commute", "Disjoint", "Finite", "Function_swap", "Function_update", "GameAdd", "GameAdd_recursion", "Icc", "Ico", "Involutive", "Ioc", "Ioo", "IsBot", "IsCompl", "IsConnected", "IsLeftRegular", "IsMin", "IsOpen", "IsPreconnected", "IsRegular", "IsRightRegular", "IsSMulRegular", "IsUnit", "K", "LeftInverse", "Lex", "LiftRel", "Linear_CC_prime", "NoncompactSpace", "Pi_mulSingle", "Prod_Lex", "Prod_invFun_prime", "Prod_map", "Prod_toFun_prime", "Products_eval", "ProjRestrict", "ProjRestricts", "RProd", "Relation_TransGen", "RightInverse", "SemiconjBy",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_prod axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_prod rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_snd_vadd(term, ctx))
    results.extend(_r0001_mk_vadd_mk(term, ctx))
    results.extend(_r0002_fst_vsub(term, ctx))
    results.extend(_r0003_snd_vsub(term, ctx))
    results.extend(_r0004_mk_vsub_mk(term, ctx))
    results.extend(_r0005_smul_inr(term, ctx))
    results.extend(_r0006_smul_swap(term, ctx))
    results.extend(_r0007_uncurry_one(term, ctx))
    results.extend(_r0008_curry_mul(term, ctx))
    results.extend(_r0009_snd_one(term, ctx))
    results.extend(_r0010_one_eq_mk(term, ctx))
    results.extend(_r0011_swap_one(term, ctx))
    results.extend(_r0012_snd_kstar(term, ctx))
    results.extend(_r0013_map_id(term, ctx))
    results.extend(_r0014_map_comp_map(term, ctx))
    results.extend(_r0015_swap_obj_inr(term, ctx))
    results.extend(_r0016_swap_map_inl(term, ctx))
    results.extend(_r0017_swap_map_inr(term, ctx))
    results.extend(_r0018_snd_intCast(term, ctx))
    results.extend(_r0019_fst_ofNat(term, ctx))
    results.extend(_r0020_snd_ofNat(term, ctx))
    results.extend(_r0021_eq(term, ctx))
    results.extend(_r0022_fst_toSigma(term, ctx))
    results.extend(_r0023_snd_toSigma(term, ctx))
    results.extend(_r0024_toSigma_mk(term, ctx))
    results.extend(_r0025_le_def(term, ctx))
    results.extend(_r0026_Ico_inl_inr(term, ctx))
    results.extend(_r0027_Ioc_inl_inr(term, ctx))
    results.extend(_r0028_Ioo_inl_inr(term, ctx))
    results.extend(_r0029_Icc_inr_inl(term, ctx))
    results.extend(_r0030_Ico_inr_inl(term, ctx))
    results.extend(_r0031_Ioc_inr_inl(term, ctx))
    results.extend(_r0032_Ioo_inr_inl(term, ctx))
    results.extend(_r0033_Icc_inr_inr(term, ctx))
    results.extend(_r0034_inr_sup(term, ctx))
    results.extend(_r0035_snd_top(term, ctx))
    results.extend(_r0036_fst_eq_or_snd_eq_of_wcovBy(term, ctx))
    results.extend(_r0037_snd_sup(term, ctx))
    results.extend(_r0038_swap_sup(term, ctx))
    results.extend(_r0039_sup_def(term, ctx))
    results.extend(_r0040_comul_comp_inl(term, ctx))
    results.extend(_r0041_counit_comp_inl(term, ctx))
    results.extend(_r0042_add_apply(term, ctx))
    results.extend(_r0043_zero_apply(term, ctx))
    results.extend(_r0044_dist_ne(term, ctx))
    results.extend(_r0045_mk_lt_mk_iff(term, ctx))
    results.extend(_r0046_swap_le_mk(term, ctx))
    results.extend(_r0047_swap_covBy_swap(term, ctx))
    results.extend(_r0048_gameAdd_swap_swap_mk(term, ctx))
    results.extend(_r0049_fst_vadd(term, ctx))
    results.extend(_r0050_algebraMap_apply(term, ctx))
    results.extend(_r0051_spectrum_eq(term, ctx))
    results.extend(_r0052_quasispectrum_eq(term, ctx))
    results.extend(_r0053_fst_prod(term, ctx))
    results.extend(_r0054_snd_prod(term, ctx))
    results.extend(_r0055_smul_def(term, ctx))
    results.extend(_r0056_smul_mk(term, ctx))
    results.extend(_r0057_smul_def(term, ctx))
    results.extend(_r0058_smul_inl(term, ctx))
    results.extend(_r0059_elim_inv_inv(term, ctx))
    results.extend(_r0060_elim_mul_mul(term, ctx))
    results.extend(_r0061_elim_div_div(term, ctx))
    results.extend(_r0062_uncurry_mul(term, ctx))
    results.extend(_r0063_curry_inv(term, ctx))
    results.extend(_r0064_uncurry_inv(term, ctx))
    results.extend(_r0065_curry_mulSingle(term, ctx))
    results.extend(_r0066_uncurry_mulSingle_mulSingle(term, ctx))
    results.extend(_r0067_one_mk_mul_one_mk(term, ctx))
    results.extend(_r0068_mk_one_mul_mk_one(term, ctx))
    results.extend(_r0069_fst_mul_snd(term, ctx))
    results.extend(_r0070_smul_zero_mk(term, ctx))
    results.extend(_r0071_smul_mk_zero(term, ctx))
    results.extend(_r0072_bracket_apply(term, ctx))
    results.extend(_r0073_fst_one(term, ctx))
    results.extend(_r0074_mk_one_one(term, ctx))
    results.extend(_r0075_mk_eq_one(term, ctx))
    results.extend(_r0076_kstar_def(term, ctx))
    results.extend(_r0077_fst_kstar(term, ctx))
    results.extend(_r0078_image_mk_segment_left(term, ctx))
    results.extend(_r0079_image_mk_segment_right(term, ctx))
    results.extend(_r0080_image_mk_openSegment_left(term, ctx))
    results.extend(_r0081_image_mk_openSegment_right(term, ctx))
    results.extend(_r0082_fst_exp(term, ctx))
    results.extend(_r0083_snd_exp(term, ctx))
    results.extend(_r0084_norm_def(term, ctx))
    results.extend(_r0085_norm_mk(term, ctx))
    results.extend(_r0086_mul_of_nonneg(term, ctx))
    results.extend(_r0087_mul_norm(term, ctx))
    results.extend(_r0088_hom_ext(term, ctx))
    results.extend(_r0089_eqToHom_comp_i(term, ctx))
    results.extend(_r0090_i_desc(term, ctx))
    results.extend(_r0091_i_map(term, ctx))
    results.extend(_r0092_i_isoColimit_hom(term, ctx))
    results.extend(_r0093_i_isoColimit_inv(term, ctx))
    results.extend(_r0094_i_reindex_hom(term, ctx))
    results.extend(_r0095_i_reindex_inv(term, ctx))
    results.extend(_r0096_i_pi_eq_id(term, ctx))
    results.extend(_r0097_i_pi_of_ne(term, ctx))
    results.extend(_r0098_i_pi(term, ctx))
    results.extend(_r0099_fac(term, ctx))
    results.extend(_r0100_homInduction_left(term, ctx))
    results.extend(_r0101_homInduction_right(term, ctx))
    results.extend(_r0102_swap_obj_inl(term, ctx))
    results.extend(_r0103_traverse_map(term, ctx))
    results.extend(_r0104_comp_traverse(term, ctx))
    results.extend(_r0105_map_traverse(term, ctx))
    results.extend(_r0106_naturality(term, ctx))
    results.extend(_r0107_fst_intCast(term, ctx))
    results.extend(_r0108_fst_natCast(term, ctx))
    results.extend(_r0109_snd_natCast(term, ctx))
    results.extend(_r0110_swap_eq_iff_eq_swap(term, ctx))
    results.extend(_r0111_eta(term, ctx))
    results.extend(_r0112_mk_inj(term, ctx))
    results.extend(_r0113_mk_right_inj(term, ctx))
    results.extend(_r0114_mk_left_inj(term, ctx))
    results.extend(_r0115_map_def(term, ctx))
    results.extend(_r0116_id_prod(term, ctx))
    results.extend(_r0117_map_iterate(term, ctx))
    results.extend(_r0118_eq_iff_fst_eq_snd_eq(term, ctx))
    results.extend(_r0119_fst_eq_iff(term, ctx))
    results.extend(_r0120_snd_eq_iff(term, ctx))
    results.extend(_r0121_lex_iff(term, ctx))
    results.extend(_r0122_refl_left(term, ctx))
    results.extend(_r0123_refl_right(term, ctx))
    results.extend(_r0124_trans(term, ctx))
    results.extend(_r0125_toLex_le_toLex(term, ctx))
    results.extend(_r0126_toLex_lt_toLex(term, ctx))
    results.extend(_r0127_le_iff(term, ctx))
    results.extend(_r0128_lt_iff(term, ctx))
    results.extend(_r0129_toLex_covBy_toLex_iff(term, ctx))
    results.extend(_r0130_covBy_iff(term, ctx))
    results.extend(_r0131_eta(term, ctx))
    results.extend(_r0132_range_eq(term, ctx))
    results.extend(_r0133_elim_range(term, ctx))
    results.extend(_r0134_univ(term, ctx))
    results.extend(_r0135_inj_iff(term, ctx))
    results.extend(_r0136_eta(term, ctx))
    results.extend(_r0137_eq_of_sigmaMk_comp(term, ctx))
    results.extend(_r0138_subtype_ext(term, ctx))
    results.extend(_r0139_sigma_mk_injective(term, ctx))
    results.extend(_r0140_map_mk(term, ctx))
    results.extend(_r0141_uncurry_curry(term, ctx))
    results.extend(_r0142_curry_uncurry(term, ctx))
    results.extend(_r0143_curry_update(term, ctx))
    results.extend(_r0144_fst_comp_toSigma(term, ctx))
    results.extend(_r0145_toSigma_inj(term, ctx))
    results.extend(_r0146_card_Icc(term, ctx))
    results.extend(_r0147_card_Ico(term, ctx))
    results.extend(_r0148_card_Ioc(term, ctx))
    results.extend(_r0149_card_Ioo(term, ctx))
    results.extend(_r0150_lex_iff(term, ctx))
    results.extend(_r0151_lt_def(term, ctx))
    results.extend(_r0152_le_def(term, ctx))
    results.extend(_r0153_lt_def(term, ctx))
    results.extend(_r0154_elim_swap(term, ctx))
    results.extend(_r0155_sum_rec_congr(term, ctx))
    results.extend(_r0156_eq_left_iff_getLeft_eq(term, ctx))
    results.extend(_r0157_eq_right_iff_getRight_eq(term, ctx))
    results.extend(_r0158_Icc_inl_inl(term, ctx))
    results.extend(_r0159_Ico_inl_inl(term, ctx))
    results.extend(_r0160_Ioc_inl_inl(term, ctx))
    results.extend(_r0161_Ioo_inl_inl(term, ctx))
    results.extend(_r0162_Icc_inl_inr(term, ctx))
    results.extend(_r0163_Ico_inr_inr(term, ctx))
    results.extend(_r0164_Ioc_inr_inr(term, ctx))
    results.extend(_r0165_Ioo_inr_inr(term, ctx))
    results.extend(_r0166_inl_sup(term, ctx))
    results.extend(_r0167_refl(term, ctx))
    results.extend(_r0168_trans(term, ctx))
    results.extend(_r0169_orderOf(term, ctx))
    results.extend(_r0170_orderOf_mk(term, ctx))
    results.extend(_r0171_fst_top(term, ctx))
    results.extend(_r0172_fst_sSup(term, ctx))
    results.extend(_r0173_snd_sSup(term, ctx))
    results.extend(_r0174_swap_sSup(term, ctx))
    results.extend(_r0175_fst_iSup(term, ctx))
    results.extend(_r0176_snd_iSup(term, ctx))
    results.extend(_r0177_swap_iSup(term, ctx))
    results.extend(_r0178_iSup_mk(term, ctx))
    results.extend(_r0179_mk_wcovBy_mk_iff(term, ctx))
    results.extend(_r0180_mk_covBy_mk_iff(term, ctx))
    results.extend(_r0181_wcovBy_iff(term, ctx))
    results.extend(_r0182_covBy_iff(term, ctx))
    results.extend(_r0183_gameAdd_iff(term, ctx))
    results.extend(_r0184_gameAdd_mk_iff(term, ctx))
    results.extend(_r0185_rprod_le_transGen_gameAdd(term, ctx))
    results.extend(_r0186_recursion_eq(term, ctx))
    results.extend(_r0187_prodUnique_apply(term, ctx))
    results.extend(_r0188_uniqueProd_apply(term, ctx))
    results.extend(_r0189_card_box_succ(term, ctx))
    results.extend(_r0190_mk_sup_mk(term, ctx))
    results.extend(_r0191_fst_sup(term, ctx))
    results.extend(_r0192_omegaSup_zip(term, ctx))
    results.extend(_r0193_comul_apply(term, ctx))
    results.extend(_r0194_counit_apply(term, ctx))
    results.extend(_r0195_comul_comp_inr(term, ctx))
    results.extend(_r0196_comul_comp_fst(term, ctx))
    results.extend(_r0197_comul_comp_snd(term, ctx))
    results.extend(_r0198_counit_comp_inr(term, ctx))
    results.extend(_r0199_binomialFamily_apply(term, ctx))
    results.extend(_r0200_binomialFamily_apply_of_orderTop_nonpos(term, ctx))
    results.extend(_r0201_powerSeriesFamily_of_not_orderTop_pos(term, ctx))
    results.extend(_r0202_powerSeriesFamily_of_orderTop_pos(term, ctx))
    results.extend(_r0203_powerSeriesFamily_hsum_zero(term, ctx))
    results.extend(_r0204_powerSeriesFamily_add(term, ctx))
    results.extend(_r0205_powerSeriesFamily_smul(term, ctx))
    results.extend(_r0206_support_powerSeriesFamily_subset(term, ctx))
    results.extend(_r0207_hsum_powerSeriesFamily_mul(term, ctx))
    results.extend(_r0208_coe_mk(term, ctx))
    results.extend(_r0209_ext(term, ctx))
    results.extend(_r0210_coe_add(term, ctx))
    results.extend(_r0211_toNNReal(term, ctx))
    results.extend(_r0212_toCompl_tsum(term, ctx))
    results.extend(_r0213_tsum_const_smul(term, ctx))
    results.extend(_r0214_tsum_smul_const(term, ctx))
    results.extend(_r0215_tsum_mul_left(term, ctx))
    results.extend(_r0216_tsum_mul_right(term, ctx))
    results.extend(_r0217_tsum_mul_tsum(term, ctx))
    results.extend(_r0218_tsum_mul_tsum_eq_tsum_sum_antidiagonal(term, ctx))
    results.extend(_r0219_tsum_mul_tsum_eq_tsum_sum_range(term, ctx))
    results.extend(_r0220_tsum_pow_mul_one_sub(term, ctx))
    results.extend(_r0221_one_sub_mul_tsum_pow(term, ctx))
    results.extend(_r0222_neBot_or_eq_bot(term, ctx))
    results.extend(_r0223_support_eq_limsInf(term, ctx))
    results.extend(_r0224_support_eq_univ_iff(term, ctx))
    results.extend(_r0225_support_eq_univ(term, ctx))
    results.extend(_r0226_evalFacProp(term, ctx))
    results.extend(_r0227_evalFacProps(term, ctx))
    results.extend(_r0228_eval_pis(term, ctx))
    results.extend(_r0229_eval_pis_image(term, ctx))
    results.extend(_r0230_max_eq_o_cons_tail(term, ctx))
    results.extend(_r0231_evalCons(term, ctx))
    results.extend(_r0232_max_eq_eval(term, ctx))
    results.extend(_r0233_lt_nil_empty(term, ctx))
    results.extend(_r0234_SigmaCompactSpace_iff_exists_compact_cov(term, ctx))
    results.extend(_r0235_exists_compact_covering(term, ctx))
    results.extend(_r0236_isConnected_iff(term, ctx))
    results.extend(_r0237_isPreconnected_iff(term, ctx))
    results.extend(_r0238_isConnected_iff(term, ctx))
    results.extend(_r0239_isPreconnected_iff(term, ctx))
    results.extend(_r0240_nhds_mk(term, ctx))
    results.extend(_r0241_nhds_eq(term, ctx))
    results.extend(_r0242_edist_eq(term, ctx))
    results.extend(_r0243_left_inv(term, ctx))
    results.extend(_r0244_right_inv(term, ctx))
    results.extend(_r0245_dist_eq_glueDist(term, ctx))
    results.extend(_r0246_dist_comm(term, ctx))
    results.extend(_r0247_dist_eq(term, ctx))
    results.extend(_r0248_dist_same(term, ctx))
    results.extend(_r0249_fst_eq_of_dist_lt_one(term, ctx))
    results.extend(_r0250_dist_eq(term, ctx))
    results.extend(_r0251_uniformity(term, ctx))
    results.extend(_r0252_associated_iff(term, ctx))
    results.extend(_r0253_mk_dvd_mk(term, ctx))
    results.extend(_r0254_semiconjBy_iff(term, ctx))
    results.extend(_r0255_commute_iff(term, ctx))
    results.extend(_r0256_isUnit_iff(term, ctx))
    results.extend(_r0257_one_le_elim_iff(term, ctx))
    results.extend(_r0258_elim_le_one_iff(term, ctx))
    results.extend(_r0259_isLeftRegular_mk(term, ctx))
    results.extend(_r0260_isRightRegular_mk(term, ctx))
    results.extend(_r0261_isRegular_mk(term, ctx))
    results.extend(_r0262_isSMulRegular_iff(term, ctx))
    results.extend(_r0263_finite_iff(term, ctx))
    results.extend(_r0264_map_injective(term, ctx))
    results.extend(_r0265_map_surjective(term, ctx))
    results.extend(_r0266_map_bijective(term, ctx))
    results.extend(_r0267_map_leftInverse(term, ctx))
    results.extend(_r0268_map_rightInverse(term, ctx))
    results.extend(_r0269_map_involutive(term, ctx))
    results.extend(_r0270_fst_surjective_iff(term, ctx))
    results.extend(_r0271_fst_injective_iff(term, ctx))
    results.extend(_r0272_lex_swap(term, ctx))
    results.extend(_r0273_mk_le_mk_iff(term, ctx))
    results.extend(_r0274_exists_sum(term, ctx))
    results.extend(_r0275_elim_injective(term, ctx))
    results.extend(_r0276_map_injective(term, ctx))
    results.extend(_r0277_map_surjective(term, ctx))
    results.extend(_r0278_map_bijective(term, ctx))
    results.extend(_r0279_elim_le_elim_iff(term, ctx))
    results.extend(_r0280_const_le_elim_iff(term, ctx))
    results.extend(_r0281_elim_le_const_iff(term, ctx))
    results.extend(_r0282_le_def(term, ctx))
    results.extend(_r0283_mk_le_mk(term, ctx))
    results.extend(_r0284_swap_le_swap(term, ctx))
    results.extend(_r0285_swap_wcovBy_swap(term, ctx))
    results.extend(_r0286_mk_wcovBy_mk_iff_left(term, ctx))
    results.extend(_r0287_mk_wcovBy_mk_iff_right(term, ctx))
    results.extend(_r0288_mk_covBy_mk_iff_left(term, ctx))
    results.extend(_r0289_mk_covBy_mk_iff_right(term, ctx))
    results.extend(_r0290_disjoint_iff(term, ctx))
    results.extend(_r0291_codisjoint_iff(term, ctx))
    results.extend(_r0292_isCompl_iff(term, ctx))
    results.extend(_r0293_gameAdd_swap_swap(term, ctx))
    results.extend(_r0294_isBot_iff(term, ctx))
    results.extend(_r0295_isMin_iff(term, ctx))
    results.extend(_r0296_lt_iff_lex_lt(term, ctx))
    results.extend(_r0297_limitOrdinal(term, ctx))
    results.extend(_r0298_noncompactSpace_iff(term, ctx))
    results.extend(_r0299_tendsto_iff(term, ctx))
    results.extend(_r0300_mem_uniformity_iff_glueDist(term, ctx))
    results.extend(_r0301_mem_uniformity(term, ctx))
    results.extend(_r0302_isOpen_iff(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_prod rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Sigma_FaithfulSMul", "_unknown", "Empty proposition"),
    ("Sum_elim_one_one", "Sum_elim_1_colon_a_to_g_1_colon_b_to_g_eq_1", "Not an equality or iff proposition"),
    ("Sum_elim_mulSingle_one", "Sum_elim_Pi_mulSingle_i_c_1_colon_b_to_g_eq_Pi_mulSingle_Sum_inl_i_c", "Not an equality or iff proposition"),
    ("Sum_elim_one_mulSingle", "Sum_elim_1_colon_a_to_g_Pi_mulSingle_i_c_eq_Pi_mulSingle_Sum_inr_i_c", "Not an equality or iff proposition"),
    ("Sigma_curry_one", "Sigma_curry_1_colon_i_colon_Sig_a_b_a_to_g_i_1_i_2_eq_1", "Not an equality or iff proposition"),
    ("Summable_mul_tendsto_const", "Summable_fun_n_f_n_star_g_n", "Not an equality or iff proposition"),
    ("SummableLocallyUniformlyOn_differentiableOn", "DifferentiableOn_fun_z_prime_n_f_n_z_s", "Not an equality or iff proposition"),
    ("Prod_segment_subset", "segment_x_y_sub_segment_x_1_y_1_times_segment_x_2_y_2", "Not an equality or iff proposition"),
    ("Prod_openSegment_subset", "openSegment_x_y_sub_openSegment_x_1_y_1_times_openSegment_x_2_y_2", "Not an equality or iff proposition"),
    ("Prod_nnnorm_def", "_unknown", "Empty proposition"),
    ("Prod_nnnorm_mk", "_unknown", "Empty proposition"),
    ("Summable_of_norm_bounded", "Summable_f", "Not an equality or iff proposition"),
    ("Summable_of_norm_bounded_eventually", "Summable_f", "Not an equality or iff proposition"),
    ("Summable_of_norm_bounded_eventually_nat", "Summable_f", "Not an equality or iff proposition"),
    ("Summable_of_nnnorm_bounded", "Summable_f", "Not an equality or iff proposition"),
    ("Summable_of_norm", "Summable_f", "Not an equality or iff proposition"),
    ("Summable_of_nnnorm", "Summable_f", "Not an equality or iff proposition"),
    ("Summable_hasSumUniformlyOn_log_one_add", "HasSumUniformlyOn_fun_i_x_log_1_plus_f_i_x_fun_x_prime_i_log_1_plus_f_i_x_K", "Not an equality or iff proposition"),
    ("Summable_tendstoUniformlyOn_tsum_nat_log_one_add", "TendstoUniformlyOn_fun_n_x_m_in_Finset_range_n_log_1_plus_f_m_x_fun_x", "Not an equality or iff proposition"),
    ("Summable_hasProdUniformlyOn_one_add", "HasProdUniformlyOn_fun_i_x_1_plus_f_i_x_fun_x_prime_i_1_plus_f_i_x_K", "Not an equality or iff proposition"),
    ("Summable_multipliableUniformlyOn_one_add", "MultipliableUniformlyOn_fun_i_x_1_plus_f_i_x_K", "Not an equality or iff proposition"),
    ("Summable_hasProdUniformlyOn_nat_one_add", "HasProdUniformlyOn_fun_n_x_1_plus_f_n_x_fun_x_prime_i_1_plus_f_i_x_K", "Not an equality or iff proposition"),
    ("Summable_multipliableUniformlyOn_nat_one_add", "MultipliableUniformlyOn_fun_n_x_1_plus_f_n_x_K", "Not an equality or iff proposition"),
    ("Summable_hasProdLocallyUniformlyOn_one_add", "HasProdLocallyUniformlyOn_fun_i_x_1_plus_f_i_x_fun_x_prime_i_1_plus_f_i_x_K", "Not an equality or iff proposition"),
    ("Summable_multipliableLocallyUniformlyOn_one_add", "MultipliableLocallyUniformlyOn_fun_i_x_1_plus_f_i_x_K", "Not an equality or iff proposition"),
    ("Summable_hasProdLocallyUniformlyOn_nat_one_add", "HasProdLocallyUniformlyOn_fun_n_x_1_plus_f_n_x_fun_x_prime_i_1_plus_f_i_x_K", "Not an equality or iff proposition"),
    ("Summable_multipliableLocallyUniformlyOn_nat_one_add", "MultipliableLocallyUniformlyOn_fun_n_x_1_plus_f_n_x_K", "Not an equality or iff proposition"),
    ("Summable_summable_log_norm_one_add", "Summable_fun_i_Real_log_1_plus_f_i", "Not an equality or iff proposition"),
    ("Summable_tendsto_alternating_series_tsum", "Tendsto_fun_n_eq_gt_i_in_range_n_minus_1_pow_i_star_f_i_atTop_prime_i_colon_minus_1_pow_i", "Not an equality or iff proposition"),
    ("Sigma_i_comp_map", "_unknown", "Empty proposition"),
    ("Sigma_map", "_unknown", "Empty proposition"),
    ("Sigma_map", "_unknown", "Empty proposition"),
    ("Sigma_map", "_unknown", "Empty proposition"),
    ("Sigma_map", "_unknown", "Empty proposition"),
    ("Sigma_map_comp_map", "_unknown", "Empty proposition"),
    ("Sigma_map", "_unknown", "Empty proposition"),
    ("Prod_fac", "_unknown", "Empty proposition"),
    ("ContextFreeGrammar_Produces_single", "g_Derives_v_w", "Not an equality or iff proposition"),
    ("ContextFreeGrammar_Produces_trans_derives", "g_Derives_u_w", "Not an equality or iff proposition"),
    ("ContextFreeGrammar_Produces_append_left", "g_Produces_p_plus_plus_v_p_plus_plus_w", "Not an equality or iff proposition"),
    ("ContextFreeGrammar_Produces_append_right", "g_Produces_v_plus_plus_p_w_plus_plus_p", "Not an equality or iff proposition"),
    ("ContextFreeGrammar_Produces_exists_nonterminal_input_mem", "exists_r_in_g_rules_nonterminal_r_input_in_u", "Not an equality or iff proposition"),
    ("Sum_id_traverse", "Sum_traverse_pure_colon_a_to_Id_a_x_eq_x", "Not an equality or iff proposition"),
    ("Sum_traverse_eq_map_id", "Sum_traverse_pure_colon_to_Id_comp_f_x_eq_pure_colon_to_Id_f_lt_gt_x", "Not an equality or iff proposition"),
    ("Sigma_uncountable", "Uncountable_Sigma_pi", "Not an equality or iff proposition"),
    ("Sum_elim_intCast_intCast", "Sum_elim_n_colon_a_to_g_n_colon_b_to_g_eq_n", "Not an equality or iff proposition"),
    ("Sum_elim_natCast_natCast", "Sum_elim_n_colon_a_to_g_n_colon_b_to_g_eq_n", "Not an equality or iff proposition"),
    ("Prod_forall", "_unknown", "Empty proposition"),
    ("Prod_exists", "_unknown", "Empty proposition"),
    ("Prod_snd_comp_mk", "Prod_snd_comp_Prod_mk_x_colon_b_to_a_times_b_eq_id", "Not an equality or iff proposition"),
    ("Prod_fst_comp_mk", "Prod_fst_comp_Prod_mk_x_colon_b_to_a_times_b_eq_Function_const_b_x", "Not an equality or iff proposition"),
    ("Prod_map_apply", "_unknown", "Empty proposition"),
    ("Prod_map_fst", "_unknown", "Empty proposition"),
    ("Prod_map_snd", "_unknown", "Empty proposition"),
    ("Prod_mk_right_injective", "mk_a_colon_b_to_a_times_b_Injective", "Not an equality or iff proposition"),
    ("Prod_mk_left_injective", "fun_a_mk_a_b_colon_a_to_a_times_b_Injective", "Not an equality or iff proposition"),
    ("Prod_fst_surjective", "Function_Surjective_at_fst_a_b", "Not an equality or iff proposition"),
    ("Prod_snd_surjective", "Function_Surjective_at_snd_a_b", "Not an equality or iff proposition"),
    ("Prod_fst_injective", "Function_Injective_at_fst_a_b", "Not an equality or iff proposition"),
    ("Prod_snd_injective", "Function_Injective_at_snd_a_b", "Not an equality or iff proposition"),
    ("Prod_swap_leftInverse", "Function_LeftInverse_at_swap_a_b_swap", "Not an equality or iff proposition"),
    ("Prod_swap_rightInverse", "Function_RightInverse_at_swap_a_b_swap", "Not an equality or iff proposition"),
    ("Prod_swap_injective", "Function_Injective_at_swap_a_b", "Not an equality or iff proposition"),
    ("Prod_swap_surjective", "Function_Surjective_at_swap_a_b", "Not an equality or iff proposition"),
    ("Prod_swap_bijective", "Function_Bijective_at_swap_a_b", "Not an equality or iff proposition"),
    ("Function_Semiconj_swap_map", "Function_Semiconj_swap_map_f_g_map_g_f", "Not an equality or iff proposition"),
    ("Prod_Lex_monotone_fst", "ofLex_t_1_le_ofLex_c_1", "Not an equality or iff proposition"),
    ("Prod_Lex_monotone_fst_ofLex", "Monotone_fun_x_colon_a_times_b_ofLex_x_1", "Not an equality or iff proposition"),
    ("WCovBy_fst_ofLex", "ofLex_a_1_ofLex_b_1", "Not an equality or iff proposition"),
    ("PProd_forall", "_unknown", "Empty proposition"),
    ("PProd_exists", "_unknown", "Empty proposition"),
    ("Prod_range_fst", "range_Prod_fst_colon_a_times_b_to_a_eq_univ", "Not an equality or iff proposition"),
    ("Prod_range_snd", "range_Prod_snd_colon_a_times_b_to_b_eq_univ", "Not an equality or iff proposition"),
    ("Sigma_exists", "_unknown", "Empty proposition"),
    ("Sigma_forall", "_unknown", "Empty proposition"),
    ("Sigma_fst_surjective", "Surjective_fst_colon_Sig_a_b_a_to_a", "Not an equality or iff proposition"),
    ("Sigma_fst_injective", "Injective_fst_colon_Sig_a_b_a_to_a", "Not an equality or iff proposition"),
    ("Prod_toSigma_injective", "Function_Injective_a_colon_eq_a_times_b_Prod_toSigma", "Not an equality or iff proposition"),
    ("Sigma_Lex_mono", "Lex_r_2_s_2_a_b", "Not an equality or iff proposition"),
    ("Sigma_Lex_mono_left", "Lex_r_2_s_a_b", "Not an equality or iff proposition"),
    ("Sigma_Lex_mono_right", "Lex_r_s_2_a_b", "Not an equality or iff proposition"),
    ("Sum_inl_injective", "Function_Injective_inl_colon_a_to_a_b", "Not an equality or iff proposition"),
    ("Sum_inr_injective", "Function_Injective_inr_colon_b_to_a_b", "Not an equality or iff proposition"),
    ("Sum_getLeft_eq_getLeft", "_unknown", "Empty proposition"),
    ("Sum_getRight_eq_getRight", "_unknown", "Empty proposition"),
    ("Sum_isSome_getLeft", "_unknown", "Empty proposition"),
    ("Sum_isSome_getRight", "_unknown", "Empty proposition"),
    ("Sum_elim_injective", "_unknown", "Empty proposition"),
    ("SigmaFinite_out", "Nonempty_mu_FiniteSpanningSetsIn_univ", "Not an equality or iff proposition"),
    ("SigmaFinite_of_map", "SigmaFinite_mu", "Not an equality or iff proposition"),
    ("Summable_norm_lt_one", "f_p_lt_1", "Not an equality or iff proposition"),
    ("Summable_clog_one_sub", "Summable_fun_n_log_1_minus_f_n", "Not an equality or iff proposition"),
    ("Prod_GCongr_mk_le_mk", "a_1_b_1_le_a_2_b_2", "Not an equality or iff proposition"),
    ("WCovBy_fst", "x_1_y_1", "Not an equality or iff proposition"),
    ("WCovBy_snd", "x_2_y_2", "Not an equality or iff proposition"),
    ("Prod_gameAdd_le_lex", "GameAdd_ra_rb_le_Prod_Lex_ra_rb", "Not an equality or iff proposition"),
    ("Prod_GameAdd_induction", "WellFounded_ra_to_WellFounded_rb_to_forall_a_1_b_1_forall_a_2_b_2_GameAdd_ra_r", "Not an equality or iff proposition"),
    ("Prod_GameAdd_to_sym2", "Sym2_GameAdd_ra_s_a_1_b_1_s_a_2_b_2", "Not an equality or iff proposition"),
    ("Prod_omegaScottContinuous_prodMk", "omegaScottContinuous_fun_x_f_x_g_x", "Not an equality or iff proposition"),
    ("Prod_omegaScottContinuous_fst", "omegaScottContinuous_Prod_fst_colon_a_times_b_to_a", "Not an equality or iff proposition"),
    ("Prod_omegaScottContinuous_snd", "omegaScottContinuous_Prod_snd_colon_a_times_b_to_b", "Not an equality or iff proposition"),
    ("HahnSeries_SummableFamily_binomialFamily_orderTop_pos", "_0_lt_binomialFamily_x_r_n_orderTop", "Not an equality or iff proposition"),
    ("HahnSeries_SummableFamily_binomialFamily_mem_support", "_0_le_g", "Not an equality or iff proposition"),
    ("HahnSeries_SummableFamily_orderTop_hsum_binomialFamily_pos", "_0_colon_WithTop_G_lt_SummableFamily_hsum_binomialFamily_x_r_minus_1_orderTop", "Not an equality or iff proposition"),
    ("SummableFamily_isPWO_iUnion_support", "Set_IsPWO_a_colon_a_s_a_support", "Not an equality or iff proposition"),
    ("SummableFamily_finite_co_support", "fun_a_eq_gt_s_a_coeff_g_HasFiniteSupport", "Not an equality or iff proposition"),
    ("SummableFamily_coe_injective", "at_Function_Injective_SummableFamily_G_R_a_a_to_R_G", "Not an equality or iff proposition"),
    ("SummableFamily_coe_zero", "_0_colon_SummableFamily_G_R_a_colon_a_to_R_G_eq_0", "Not an equality or iff proposition"),
    ("SummableFamily_coe_smul", "_unknown", "Empty proposition"),
    ("SummableFamily_smul_apply", "_unknown", "Empty proposition"),
    ("SummationFilter_symmetricIcc_le_Conditional", "symmetricIcc_G_filter_le_conditional_G_filter", "Not an equality or iff proposition"),
    ("Summable_tendsto_zero_of_even_summable_symmetricIcc", "Tendsto_f_atTop_0", "Not an equality or iff proposition"),
    ("Summable_op", "Summable_op_comp_f_L", "Not an equality or iff proposition"),
    ("Summable_unop", "Summable_unop_comp_f_L", "Not an equality or iff proposition"),
    ("Summable_star", "Summable_fun_b_star_f_b_L", "Not an equality or iff proposition"),
    ("Summable_ofStar", "Summable_f_L", "Not an equality or iff proposition"),
    ("Summable_of_nonneg_of_le", "Summable_g", "Not an equality or iff proposition"),
    ("Summable_tsum_ofReal_lt_top", "prime_i_ofReal_f_i_lt_inf", "Not an equality or iff proposition"),
    ("Summable_tsum_ofReal_ne_top", "prime_i_ofReal_f_i_ne_inf", "Not an equality or iff proposition"),
    ("Summable_countable_support_ennreal", "f_support_Countable", "Not an equality or iff proposition"),
    ("Summable_const_smul", "Summable_fun_i_b_f_i_L", "Not an equality or iff proposition"),
    ("Summable_smul_const", "Summable_fun_z_f_z_a_L", "Not an equality or iff proposition"),
    ("Summable_alternating", "Summable_fun_n_eq_gt_minus_1_pow_n_star_f_n", "Not an equality or iff proposition"),
    ("Summable_mul_of_complete_nonarchimedean", "Summable_fun_i_colon_a_times_b_f_i_1_star_g_i_2", "Not an equality or iff proposition"),
    ("Summable_mul_of_nonarchimedean", "Summable_fun_i_colon_a_times_b_f_i_1_star_g_i_2", "Not an equality or iff proposition"),
    ("Summable_tendsto_atTop_of_pos", "Tendsto_f_atTop_atTop", "Not an equality or iff proposition"),
    ("Summable_tsum_lt_tsum_of_nonneg", "prime_n_f_n_lt_prime_n_g_n", "Not an equality or iff proposition"),
    ("Summable_mul_left", "Summable_fun_i_a_star_f_i_L", "Not an equality or iff proposition"),
    ("Summable_mul_right", "Summable_fun_i_f_i_star_a_L", "Not an equality or iff proposition"),
    ("Summable_div_const", "Summable_fun_i_f_i_slash_b_L", "Not an equality or iff proposition"),
    ("Summable_const_div", "Summable_fun_i_b_slash_f_i_L", "Not an equality or iff proposition"),
    ("SummationFilter_leAtTop_of_not_NeBot", "L_LeAtTop", "Not an equality or iff proposition"),
    ("SummableLocallyUniformlyOn_of_locally_bounded_eventually", "SummableLocallyUniformlyOn_f_s", "Not an equality or iff proposition"),
    ("SummableLocallyUniformlyOn_of_locally_bounded", "SummableLocallyUniformlyOn_f_s", "Not an equality or iff proposition"),
    ("CompHausLike_Sigma_isOpenEmbedding_i", "IsOpenEmbedding_Sigma_i_X_a", "Not an equality or iff proposition"),
    ("Products_rel_head", "_unknown", "Empty proposition"),
    ("Products_head", "_unknown", "Empty proposition"),
    ("Products_eval_eq", "l_eval_C_x_eq_if_forall_i_i_in_l_val_to_x_val_i_eq_true_then_1_else_0", "Not an equality or iff proposition"),
    ("Products_prop_of_isGood", "forall_a_a_in_l_val_to_J_a", "Not an equality or iff proposition"),
    ("Products_prop_of_isGood_of_contained", "ord_I_i_lt_o", "Not an equality or iff proposition"),
    ("Products_lt_ord_of_lt", "forall_i_in_m_val_ord_I_i_lt_o", "Not an equality or iff proposition"),
    ("Products_eval_pis", "_unknown", "Empty proposition"),
    ("Products_eval_pis_image", "_unknown", "Empty proposition"),
    ("Products_head_lt_ord_of_isGood", "ord_I_l_val_head_bang_lt_o", "Not an equality or iff proposition"),
    ("Products_isGood_mono", "l_isGood_pi_C_ord_I_lt_o_2", "Not an equality or iff proposition"),
    ("Products_max_eq_o_cons_tail", "_unknown", "Empty proposition"),
    ("Profinite_NobelingProof_Products_isGood_nil", "Products_isGood_fun_false_colon_Set_I_to_Bool_Products_nil", "Not an equality or iff proposition"),
    ("Profinite_NobelingProof_Products_span_nil_eq_top", "Submodule_span_eval_fun_false_colon_Set_I_to_Bool_prime_prime_nil_eq_top", "Not an equality or iff proposition"),
    ("SigmaCompactSpace_of_countable", "SigmaCompactSpace_X", "Not an equality or iff proposition"),
    ("FiberBundle_Prod_isInducing_diag", "IsInducing_fun_p_p_1_p_2_1_p_1_p_2_2_colon_TotalSpace_F_1_times_F_2_E", "Not an equality or iff proposition"),
    ("Bundle_Trivialization_Prod_continuous_to_fun", "ContinuousOn_Prod_toFun_prime_e_1_e_2_pi_F_1_times_F_2_E_1_times_E_2_inv_prime_e_1_baseSet_inter_e", "Not an equality or iff proposition"),
    ("Bundle_Trivialization_Prod_continuous_inv_fun", "ContinuousOn_Prod_invFun_prime_e_1_e_2_e_1_baseSet_inter_e_2_baseSet_times_univ", "Not an equality or iff proposition"),
    ("Summable_matrix_transpose", "Summable_fun_x_eq_gt_f_x_L", "Not an equality or iff proposition"),
    ("Summable_matrix_conjTranspose", "Summable_fun_x_eq_gt_f_x_L", "Not an equality or iff proposition"),
    ("Summable_matrix_diagonal", "Summable_fun_x_eq_gt_diagonal_f_x_L", "Not an equality or iff proposition"),
    ("Summable_matrix_diag", "Summable_fun_x_eq_gt_diag_f_x_L", "Not an equality or iff proposition"),
    ("Summable_matrix_blockDiagonal", "Summable_fun_x_eq_gt_blockDiagonal_f_x_L", "Not an equality or iff proposition"),
    ("Summable_matrix_blockDiag", "Summable_fun_x_eq_gt_blockDiag_f_x_L", "Not an equality or iff proposition"),
    ("Summable_matrix_blockDiagonal", "_unknown", "Empty proposition"),
    ("Summable_matrix_blockDiag", "_unknown", "Empty proposition"),
    ("Sum_one_le_dist_inl_inr", "_1_le_Sum_dist_inl_x_inr_y", "Not an equality or iff proposition"),
    ("Sum_one_le_dist_inr_inl", "_1_le_Sum_dist_inr_y_inl_x", "Not an equality or iff proposition"),
    ("Sigma_one_le_dist_of_ne", "_1_le_dist_i_x_colon_Sig_k_E_k_j_y", "Not an equality or iff proposition"),
    ("Sigma_dist_triangle", "dist_x_z_le_dist_x_y_plus_dist_y_z", "Not an equality or iff proposition"),
    ("Sigma_isometry_mk", "Isometry_Sigma_mk_i_colon_E_i_to_Sig_k_E_k", "Not an equality or iff proposition"),
    ("Sigma_completeSpace", "CompleteSpace_Sig_i_E_i", "Not an equality or iff proposition"),
]
