"""Mathlib: Other — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 39293 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_other"
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

def _r0000_vadd_vsub_vadd_cancel_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: vadd_vsub_vadd_cancel_left
    # (v +ᵥ p₁) -ᵥ (v +ᵥ p₂) = p₁ -ᵥ p₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_plus_p_1", 2)
    if args is not None:
        try:
            rhs = OOp("p_1", (args[0], OVar("p_2"),))
            results.append((rhs, "Mathlib: vadd_vsub_vadd_cancel_left"))
        except Exception:
            pass
    return results


def _r0001_vadd_vsub_vadd_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: vadd_vsub_vadd_comm
    # (v₁ +ᵥ p₁) -ᵥ (v₂ +ᵥ p₂) = (v₁ - v₂) + (p₁ -ᵥ p₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_1_plus_p_1", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("-", (OVar("v_1"), OVar("v_2"))), OOp("p_1", (args[0], OVar("p_2"),))))
            results.append((rhs, "Mathlib: vadd_vsub_vadd_comm"))
        except Exception:
            pass
    return results


def _r0002_vsub_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Pi.vsub_def
    # p -ᵥ q = fun i => p i -ᵥ q i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p", 2)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("i"), OVar("eq_gt"), OVar("p"), OVar("i"), args[0], args[1], OVar("i"),))
            results.append((rhs, "Mathlib: Pi_vsub_def"))
        except Exception:
            pass
    return results


def _r0003_expect_neg_index(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: expect_neg_index
    # 𝔼 i ∈ -s, f i = 𝔼 i ∈ s, f (-i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f"), OVar("minus_i"),))))
            results.append((rhs, "Mathlib: expect_neg_index"))
        except Exception:
            pass
    return results


def _r0004_map_expect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_expect
    # g (𝔼 i ∈ s, f i) = 𝔼 i ∈ s, g (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("g"), OOp("f", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: map_expect"))
        except Exception:
            pass
    return results


def _r0005_expect_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: expect_const
    # 𝔼 _i ∈ s, a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: expect_const"))
        except Exception:
            pass
    return results


def _r0006_smul_expect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_expect
    # a • 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a • f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("a"), OVar("_unknown"), OVar("f"), OVar("i"),))))
            results.append((rhs, "Mathlib: smul_expect"))
        except Exception:
            pass
    return results


def _r0007_expect_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: expect_mul
    # (𝔼 i ∈ s, f i) * a = 𝔼 i ∈ s, f i * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f"), OVar("i"),)))), args[1]))
            results.append((rhs, "Mathlib: expect_mul"))
        except Exception:
            pass
    return results


def _r0008_partialProd_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: partialProd_succ
    # partialProd f j.succ = partialProd f (Fin.castSucc j) * f j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "partialProd", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("partialProd", (args[0], OOp("Fin_castSucc", (OVar("j"),)),)), OOp("f", (OVar("j"),))))
            results.append((rhs, "Mathlib: partialProd_succ"))
        except Exception:
            pass
    return results


def _r0009_finprod_eq_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: finprod_eq_single
    # ∏ᶠ x, f x = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"),))
            results.append((rhs, "Mathlib: finprod_eq_single"))
        except Exception:
            pass
    return results


def _r0010_finprod_eq_dif(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: finprod_eq_dif
    # ∏ᶠ i, f i = if h : p then f h else 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("if", (OVar("h"), OVar("colon"), OVar("p"), OVar("then"), args[1], OVar("h"), OVar("else"), OLit(1),))
            results.append((rhs, "Mathlib: finprod_eq_dif"))
        except Exception:
            pass
    return results


def _r0011_finprod_mem_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: finprod_mem_def
    # ∏ᶠ a ∈ s, f a = ∏ᶠ a, mulIndicator s f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("a"), OVar("mulIndicator"), OVar("s"), OVar("f"), OVar("a"),))
            results.append((rhs, "Mathlib: finprod_mem_def"))
        except Exception:
            pass
    return results


def _r0012_finprod_cond_eq_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: finprod_cond_eq_right
    # (∏ᶠ (i) (_ : a = i), f i) = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"),))
            results.append((rhs, "Mathlib: finprod_cond_eq_right"))
        except Exception:
            pass
    return results


def _r0013_prod_subtype_eq_prod_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_subtype_eq_prod_filter
    # ∏ x ∈ s.subtype p, f x = ∏ x ∈ s with p x, f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (OVar("with"), OVar("p"), OVar("x"), OVar("f"), OVar("x"),))))
            results.append((rhs, "Mathlib: prod_subtype_eq_prod_filter"))
        except Exception:
            pass
    return results


def _r0014_prod_eq_pow_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_eq_pow_card
    # ∏ a ∈ s, f a = b ^ #s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("b"), OVar("hash_s")))
            results.append((rhs, "Mathlib: prod_eq_pow_card"))
        except Exception:
            pass
    return results


def _r0015_prod_image_of_pairwise_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_image_of_pairwise_eq_one
    # ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("I", (OVar("g"), OOp("f", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: prod_image_of_pairwise_eq_one"))
        except Exception:
            pass
    return results


def _r0016_prod_image_of_disjoint(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_image_of_disjoint
    # ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("I", (OVar("g"), OOp("f", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: prod_image_of_disjoint"))
        except Exception:
            pass
    return results


def _r0017_prod_sdiff_div_prod_sdiff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_sdiff_div_prod_sdiff
    # (∏ x ∈ s₂ \\ s₁, f x) / ∏ x ∈ s₁ \\ s₂, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s_2", (OVar("f"), OVar("x"),)))), OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s_1", (OVar("f"), OVar("x"),))))))
            results.append((rhs, "Mathlib: prod_sdiff_div_prod_sdiff"))
        except Exception:
            pass
    return results


def _r0018_unop_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: unop_sum
    # unop (∑ x ∈ s, f x) = ∑ x ∈ s, unop (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (OVar("unop"), OOp("f", (OVar("x"),)),))))
            results.append((rhs, "Mathlib: unop_sum"))
        except Exception:
            pass
    return results


def _r0019_unop_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: unop_prod
    # unop (∏ i ∈ s, f i) = ∏ i ∈ s, unop (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("unop"), OOp("f", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: unop_prod"))
        except Exception:
            pass
    return results


def _r0020_prod_div_distrib(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_div_distrib
    # ∏ x ∈ s, f x / g x = (∏ x ∈ s, f x) / ∏ x ∈ s, g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (OVar("f"), OVar("x"),)))), OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (OVar("g"), OVar("x"),))))))
            results.append((rhs, "Mathlib: prod_div_distrib"))
        except Exception:
            pass
    return results


def _r0021_prod_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_zpow
    # ∏ a ∈ s, f a ^ n = (∏ a ∈ s, f a) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("in", (OOp("_unknown", (OVar("a"),)), OOp("s", (OVar("f"), OVar("a"),)))), OVar("n")))
            results.append((rhs, "Mathlib: prod_zpow"))
        except Exception:
            pass
    return results


def _r0022_toMul_list_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toMul_list_sum
    # s.sum.toMul = (s.map toMul).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_sum_toMul")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_map_toMul_prod")
            results.append((rhs, "Mathlib: toMul_list_sum"))
    except Exception:
        pass
    return results


def _r0023_toAdd_list_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toAdd_list_sum
    # s.prod.toAdd = (s.map toAdd).sum
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_prod_toAdd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_map_toAdd_sum")
            results.append((rhs, "Mathlib: toAdd_list_sum"))
    except Exception:
        pass
    return results


def _r0024_ofMul_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofMul_prod
    # ofMul (∏ i ∈ s, f i) = ∑ i ∈ s, ofMul (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofMul", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("ofMul"), OOp("f", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: ofMul_prod"))
        except Exception:
            pass
    return results


def _r0025_toMul_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toMul_sum
    # (∑ i ∈ s, f i).toMul = ∏ i ∈ s, (f i).toMul
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_in_s_f_i_toMul")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f_i_toMul"),))))
            results.append((rhs, "Mathlib: toMul_sum"))
    except Exception:
        pass
    return results


def _r0026_toAdd_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toAdd_prod
    # (∏ i ∈ s, f i).toAdd = ∑ i ∈ s, (f i).toAdd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_in_s_f_i_toAdd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f_i_toAdd"),))))
            results.append((rhs, "Mathlib: toAdd_prod"))
    except Exception:
        pass
    return results


def _r0027_prod_erase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_erase
    # a * (l.erase a).prod = l.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("l_prod")
            results.append((rhs, "Mathlib: prod_erase"))
        except Exception:
            pass
    return results


def _r0028_prod_map_erase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_map_erase
    # ∀ {l : List α}, a ∈ l → f a * ((l.erase a).map f).prod = (l.map f).prod   | b :: l, h =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("l_map_f_prod", (OVar("pipe"), OVar("b"), OVar("colon_colon"), OVar("l"), OVar("h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: prod_map_erase"))
        except Exception:
            pass
    return results


def _r0029_prod_drop_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_drop_succ
    # ∀ (L : List G) (i : ℕ) (p : i < L.length), (L.drop (i + 1)).prod = L[i]⁻¹ * (L.drop i).prod   | [], _, p => False.elim (
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L_drop_i_plus_1_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("L_i_inv"), OOp("L_drop_i_prod", (OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("p"), OVar("eq_gt"), OVar("False_elim"), OOp("Nat_not_lt_zero", (OVar("_unknown"), OVar("p"),)), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), OVar("_unknown"), OVar("_0"), OVar("_unknown"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: prod_drop_succ"))
    except Exception:
        pass
    return results


def _r0030_alternatingProd_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: alternatingProd_singleton
    # alternatingProd [a] = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "alternatingProd", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: alternatingProd_singleton"))
        except Exception:
            pass
    return results


def _r0031_prod_map_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_map_div
    # (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_map_fun_i_eq_gt_f_i_slash_g_i_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("m_map_f_prod"), OVar("m_map_g_prod")))
            results.append((rhs, "Mathlib: prod_map_div"))
    except Exception:
        pass
    return results


def _r0032_prod_map_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_map_zpow
    # (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_map_fun_i_eq_gt_f_i_pow_n_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("m_map_f_prod"), OVar("n")))
            results.append((rhs, "Mathlib: prod_map_zpow"))
    except Exception:
        pass
    return results


def _r0033_sum_nat_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: sum_nat_mod
    # s.sum % n = (s.map (· % n)).sum % n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sum", 2)
    if args is not None:
        try:
            rhs = OOp("s_map_n_sum", (args[0], args[1],))
            results.append((rhs, "Mathlib: sum_nat_mod"))
        except Exception:
            pass
    return results


def _r0034_sum_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithTop.sum_eq_top
    # ∑ i ∈ s, f i = ⊤ ↔ ∃ i ∈ s, f i = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), OOp("in", (OOp("exists", (OVar("i"),)), OOp("s", (OVar("f"), OVar("i"),)))))), OVar("top")))
            results.append((rhs, "Mathlib: WithTop_sum_eq_top"))
        except Exception:
            pass
    return results


def _r0035_sum_eq_bot_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithBot.sum_eq_bot_iff
    # ∑ i ∈ s, f i = ⊥ ↔ ∃ i ∈ s, f i = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("bot"), OOp("in", (OOp("exists", (OVar("i"),)), OOp("s", (OVar("f"), OVar("i"),)))))), OVar("bot")))
            results.append((rhs, "Mathlib: WithBot_sum_eq_bot_iff"))
        except Exception:
            pass
    return results


def _r0036_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgCat.id_apply
    # (𝟙 A : A ⟶ A) a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_A_colon_A_A", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: AlgCat_id_apply"))
        except Exception:
            pass
    return results


def _r0037_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: AlgCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0038_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgCat.ofHom_id
    # ofHom (AlgHom.id R X) = 𝟙 (of R X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("R"), OVar("X"),)),))
            results.append((rhs, "Mathlib: AlgCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0039_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: AlgCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0040_toBialgHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BialgCat.toBialgHom_id
    # Hom.toBialgHom (𝟙 M) = BialgHom.id _ _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_toBialgHom", 1)
    if args is not None:
        try:
            rhs = OOp("BialgHom_id", (OVar("_unknown"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: BialgCat_toBialgHom_id"))
        except Exception:
            pass
    return results


def _r0041_toBialgIso_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BialgEquiv.toBialgIso_symm
    # toBialgIso e.symm = (toBialgIso e).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toBialgIso", 1)
    if args is not None:
        try:
            rhs = OVar("toBialgIso_e_symm")
            results.append((rhs, "Mathlib: BialgEquiv_toBialgIso_symm"))
        except Exception:
            pass
    return results


def _r0042_toBialgIso_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BialgEquiv.toBialgIso_trans
    # toBialgIso (e.trans f) = toBialgIso e ≪≫ toBialgIso f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toBialgIso", 1)
    if args is not None:
        try:
            rhs = OOp("toBialgIso", (OVar("e"), OVar("_unknown"), OVar("toBialgIso"), OVar("f"),))
            results.append((rhs, "Mathlib: BialgEquiv_toBialgIso_trans"))
        except Exception:
            pass
    return results


def _r0043_of_counit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CoalgCat.of_counit
    # Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Coalgebra_counit", 1)
    if args is not None:
        try:
            rhs = OOp("Coalgebra_counit", (OOp("R", (OVar("colon_eq"), OVar("R"),)), OOp("A", (OVar("colon_eq"), OVar("X"),)),))
            results.append((rhs, "Mathlib: CoalgCat_of_counit"))
        except Exception:
            pass
    return results


def _r0044_toCoalgHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CoalgCat.toCoalgHom_id
    # Hom.toCoalgHom (𝟙 M) = CoalgHom.id _ _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_toCoalgHom", 1)
    if args is not None:
        try:
            rhs = OOp("CoalgHom_id", (OVar("_unknown"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: CoalgCat_toCoalgHom_id"))
        except Exception:
            pass
    return results


def _r0045_toCoalgIso_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CoalgEquiv.toCoalgIso_symm
    # toCoalgIso e.symm = (toCoalgIso e).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCoalgIso", 1)
    if args is not None:
        try:
            rhs = OVar("toCoalgIso_e_symm")
            results.append((rhs, "Mathlib: CoalgEquiv_toCoalgIso_symm"))
        except Exception:
            pass
    return results


def _r0046_toCoalgIso_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CoalgEquiv.toCoalgIso_trans
    # toCoalgIso (e.trans f) = toCoalgIso e ≪≫ toCoalgIso f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCoalgIso", 1)
    if args is not None:
        try:
            rhs = OOp("toCoalgIso", (OVar("e"), OVar("_unknown"), OVar("toCoalgIso"), OVar("f"),))
            results.append((rhs, "Mathlib: CoalgEquiv_toCoalgIso_trans"))
        except Exception:
            pass
    return results


def _r0047_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.id_apply
    # (𝟙 A : A ⟶ A) a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_A_colon_A_A", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CommAlgCat_id_apply"))
        except Exception:
            pass
    return results


def _r0048_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.comp_apply
    # (f ≫ g) a = g (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: CommAlgCat_comp_apply"))
        except Exception:
            pass
    return results


def _r0049_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.ofHom_hom
    # ofHom f.hom = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CommAlgCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0050_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.ofHom_id
    # ofHom (.id R X) = 𝟙 (of R X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("R"), OVar("X"),)),))
            results.append((rhs, "Mathlib: CommAlgCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0051_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: CommAlgCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0052_ofHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.ofHom_apply
    # ofHom f x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: CommAlgCat_ofHom_apply"))
        except Exception:
            pass
    return results


def _r0053_forget_2_commRingCat_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.forget₂_commRingCat_map
    # (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).map f = CommRingCat.ofHom f.hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_2_CommAlgCat_v_R_CommRingCat_v_map", 1)
    if args is not None:
        try:
            rhs = OOp("CommRingCat_ofHom", (OVar("f_hom"),))
            results.append((rhs, "Mathlib: CommAlgCat_forget_2_commRingCat_map"))
        except Exception:
            pass
    return results


def _r0054_forget_2_algCat_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.forget₂_algCat_obj
    # (forget₂ (CommAlgCat.{v} R) (AlgCat.{v} R)).obj A = .of R A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_2_CommAlgCat_v_R_AlgCat_v_R_obj", 1)
    if args is not None:
        try:
            rhs = OOp("of", (OVar("R"), args[0],))
            results.append((rhs, "Mathlib: CommAlgCat_forget_2_algCat_obj"))
        except Exception:
            pass
    return results


def _r0055_forget_2_algCat_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.forget₂_algCat_map
    # (forget₂ (CommAlgCat.{v} R) (AlgCat.{v} R)).map f = AlgCat.ofHom f.hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_2_CommAlgCat_v_R_AlgCat_v_R_map", 1)
    if args is not None:
        try:
            rhs = OOp("AlgCat_ofHom", (OVar("f_hom"),))
            results.append((rhs, "Mathlib: CommAlgCat_forget_2_algCat_map"))
        except Exception:
            pass
    return results


def _r0056_binaryCofan_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.binaryCofan_inr
    # (binaryCofan A B).inr = ofHom includeRight
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("binaryCofan_A_B_inr")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ofHom", (OVar("includeRight"),))
            results.append((rhs, "Mathlib: CommAlgCat_binaryCofan_inr"))
    except Exception:
        pass
    return results


def _r0057_binaryCofan_pt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.binaryCofan_pt
    # (binaryCofan A B).pt = .of R (A ⊗[R] B)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("binaryCofan_A_B_pt")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("of", (OVar("R"), OOp("A", (OVar("R"), OVar("B"),)),))
            results.append((rhs, "Mathlib: CommAlgCat_binaryCofan_pt"))
    except Exception:
        pass
    return results


def _r0058_coe_tensorObj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.coe_tensorObj
    # A ⊗ B = A ⊗[R] B
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "A", 2)
    if args is not None:
        try:
            rhs = OOp("A", (OVar("R"), args[1],))
            results.append((rhs, "Mathlib: CommAlgCat_coe_tensorObj"))
        except Exception:
            pass
    return results


def _r0059_tensorHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.tensorHom_hom
    # (f ⊗ₘ g).hom = map f.hom g.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("map", (OVar("f_hom"), OVar("g_hom"),))
            results.append((rhs, "Mathlib: CommAlgCat_tensorHom_hom"))
    except Exception:
        pass
    return results


def _r0060_whiskerRight_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.whiskerRight_hom
    # (f ▷ C).hom = map f.hom (.id _ _)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_C_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("map", (OVar("f_hom"), OOp("id", (OVar("_unknown"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: CommAlgCat_whiskerRight_hom"))
    except Exception:
        pass
    return results


def _r0061_whiskerLeft_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.whiskerLeft_hom
    # (C ◁ f).hom = map (.id _ _) f.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("C_f_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("map", (OOp("id", (OVar("_unknown"), OVar("_unknown"),)), OVar("f_hom"),))
            results.append((rhs, "Mathlib: CommAlgCat_whiskerLeft_hom"))
    except Exception:
        pass
    return results


def _r0062_associator_hom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.associator_hom_hom
    # (α_ A B C).hom.hom = (assoc R R R A B C).toAlgHom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_A_B_C_hom_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("assoc_R_R_R_A_B_C_toAlgHom")
            results.append((rhs, "Mathlib: CommAlgCat_associator_hom_hom"))
    except Exception:
        pass
    return results


def _r0063_associator_inv_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.associator_inv_hom
    # (α_ A B C).inv.hom = (assoc R R R A B C).symm.toAlgHom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_A_B_C_inv_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("assoc_R_R_R_A_B_C_symm_toAlgHom")
            results.append((rhs, "Mathlib: CommAlgCat_associator_inv_hom"))
    except Exception:
        pass
    return results


def _r0064_braiding_inv_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.braiding_inv_hom
    # (β_ A B).inv.hom = (comm R B A).toAlgHom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b_A_B_inv_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("comm_R_B_A_toAlgHom")
            results.append((rhs, "Mathlib: CommAlgCat_braiding_inv_hom"))
    except Exception:
        pass
    return results


def _r0065_snd_unop_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.snd_unop_hom
    # (snd A B).unop.hom = includeRight
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("snd_A_B_unop_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("includeRight")
            results.append((rhs, "Mathlib: CommAlgCat_snd_unop_hom"))
    except Exception:
        pass
    return results


def _r0066_toUnit_unop_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.toUnit_unop_hom
    # (toUnit A).unop.hom = Algebra.ofId R A.unop
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toUnit_A_unop_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Algebra_ofId", (OVar("R"), OVar("A_unop"),))
            results.append((rhs, "Mathlib: CommAlgCat_toUnit_unop_hom"))
    except Exception:
        pass
    return results


def _r0067_lift_unop_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.lift_unop_hom
    # (lift f g).unop.hom = lift f.unop.hom g.unop.hom fun _ _ ↦ .all _ _
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("lift_f_g_unop_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("lift", (OVar("f_unop_hom"), OVar("g_unop_hom"), OVar("fun"), OVar("_unknown"), OVar("_unknown"), OVar("_unknown"), OVar("all"), OVar("_unknown"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: CommAlgCat_lift_unop_hom"))
    except Exception:
        pass
    return results


def _r0068_hom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommBialgCat.hom_comp
    # (f ≫ g).hom = g.hom.comp f.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g_hom_comp", (OVar("f_hom"),))
            results.append((rhs, "Mathlib: CommBialgCat_hom_comp"))
    except Exception:
        pass
    return results


def _r0069_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommBialgCat.id_apply
    # (𝟙 A : A ⟶ A) a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_A_colon_A_A", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CommBialgCat_id_apply"))
        except Exception:
            pass
    return results


def _r0070_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommBialgCat.comp_apply
    # (f ≫ g) a = g (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: CommBialgCat_comp_apply"))
        except Exception:
            pass
    return results


def _r0071_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommBialgCat.ofHom_hom
    # ofHom f.hom = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CommBialgCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0072_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommBialgCat.ofHom_id
    # ofHom (.id R X) = 𝟙 (of R X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("R"), OVar("X"),)),))
            results.append((rhs, "Mathlib: CommBialgCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0073_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommBialgCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: CommBialgCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0074_ofHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommBialgCat.ofHom_apply
    # ofHom f x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: CommBialgCat_ofHom_apply"))
        except Exception:
            pass
    return results


def _r0075_forget_2_commAlgCat_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommBialgCat.forget₂_commAlgCat_map
    # (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).map f = CommAlgCat.ofHom f.hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_2_CommBialgCat_v_R_CommAlgCat_v_R_map", 1)
    if args is not None:
        try:
            rhs = OOp("CommAlgCat_ofHom", (OVar("f_hom"),))
            results.append((rhs, "Mathlib: CommBialgCat_forget_2_commAlgCat_map"))
        except Exception:
            pass
    return results


def _r0076_mul_op_of_unop_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommAlgCat.mul_op_of_unop_hom
    # μ[op <| CommAlgCat.of R A].unop.hom = comulAlgHom R A
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mu_op_lt_pipe_CommAlgCat_of_R_A_unop_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comulAlgHom", (OVar("R"), OVar("A"),))
            results.append((rhs, "Mathlib: CommAlgCat_mul_op_of_unop_hom"))
    except Exception:
        pass
    return results


def _r0077_hom_hom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FGModuleCat.hom_hom_id
    # (𝟙 A : A ⟶ A).hom.hom = LinearMap.id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_A_colon_A_A_hom_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("LinearMap_id")
            results.append((rhs, "Mathlib: FGModuleCat_hom_hom_id"))
    except Exception:
        pass
    return results


def _r0078_tensorObj_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: tensorObj_obj
    # (M ⊗ N).obj = (M.obj ⊗ N.obj)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("M_N_obj")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("M_obj", (OVar("_unknown"), OVar("N_obj"),))
            results.append((rhs, "Mathlib: tensorObj_obj"))
    except Exception:
        pass
    return results


def _r0079_FGModuleCatDual_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FGModuleCatDual_coe
    # (FGModuleCatDual K V : Type u) = Module.Dual K V
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FGModuleCatDual", 5)
    if args is not None:
        try:
            rhs = OOp("Module_Dual", (args[0], args[1],))
            results.append((rhs, "Mathlib: FGModuleCatDual_coe"))
        except Exception:
            pass
    return results


def _r0080_forget_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.forget_map
    # (forget GrpCat).map f = (f : X → Y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_GrpCat_map", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("f", (OVar("colon"), OVar("X"),)), OVar("Y")))
            results.append((rhs, "Mathlib: GrpCat_forget_map"))
        except Exception:
            pass
    return results


def _r0081_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: GrpCat_ext"))
    except Exception:
        pass
    return results


def _r0082_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.id_apply
    # (𝟙 X : X ⟶ X) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_X_colon_X_X", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: GrpCat_id_apply"))
        except Exception:
            pass
    return results


def _r0083_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: GrpCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0084_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.ofHom_id
    # ofHom (MonoidHom.id X) = 𝟙 (of X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("X"),)),))
            results.append((rhs, "Mathlib: GrpCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0085_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: GrpCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0086_forget_2_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpCat.forget₂_map
    # (forget₂ GrpCat MonCat).map f x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_2_GrpCat_MonCat_map", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: GrpCat_forget_2_map"))
        except Exception:
            pass
    return results


def _r0087_forget_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommGrpCat.forget_map
    # (forget CommGrpCat).map f = (f : X → Y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_CommGrpCat_map", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("f", (OVar("colon"), OVar("X"),)), OVar("Y")))
            results.append((rhs, "Mathlib: CommGrpCat_forget_map"))
        except Exception:
            pass
    return results


def _r0088_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommGrpCat.id_apply
    # (𝟙 X : X ⟶ X) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_X_colon_X_X", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CommGrpCat_id_apply"))
        except Exception:
            pass
    return results


def _r0089_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommGrpCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CommGrpCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0090_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommGrpCat.ofHom_id
    # ofHom (MonoidHom.id X) = 𝟙 (of X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("X"),)),))
            results.append((rhs, "Mathlib: CommGrpCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0091_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommGrpCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: CommGrpCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0092_forget_2_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommGrpCat.forget₂_map
    # (forget₂ CommGrpCat GrpCat).map f x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_2_CommGrpCat_GrpCat_map", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: CommGrpCat_forget_2_map"))
        except Exception:
            pass
    return results


def _r0093_hom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GrpWithZero.hom_comp
    # ConcreteCategory.hom (f ≫ g) = g.comp f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ConcreteCategory_hom", 1)
    if args is not None:
        try:
            rhs = OOp("g_comp", (OVar("f"),))
            results.append((rhs, "Mathlib: GrpWithZero_hom_comp"))
        except Exception:
            pass
    return results


def _r0094_of_counit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HopfAlgCat.of_counit
    # Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Coalgebra_counit", 1)
    if args is not None:
        try:
            rhs = OOp("Coalgebra_counit", (OOp("R", (OVar("colon_eq"), OVar("R"),)), OOp("A", (OVar("colon_eq"), OVar("X"),)),))
            results.append((rhs, "Mathlib: HopfAlgCat_of_counit"))
        except Exception:
            pass
    return results


def _r0095_toBialgHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: HopfAlgCat.toBialgHom_id
    # Hom.toBialgHom (𝟙 M) = BialgHom.id _ _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_toBialgHom", 1)
    if args is not None:
        try:
            rhs = OOp("BialgHom_id", (OVar("_unknown"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: HopfAlgCat_toBialgHom_id"))
        except Exception:
            pass
    return results


def _r0096_toHopfAlgIso_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BialgEquiv.toHopfAlgIso_symm
    # toHopfAlgIso e.symm = (toHopfAlgIso e).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toHopfAlgIso", 1)
    if args is not None:
        try:
            rhs = OVar("toHopfAlgIso_e_symm")
            results.append((rhs, "Mathlib: BialgEquiv_toHopfAlgIso_symm"))
        except Exception:
            pass
    return results


def _r0097_toHopfAlgIso_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BialgEquiv.toHopfAlgIso_trans
    # toHopfAlgIso (e.trans f) = toHopfAlgIso e ≪≫ toHopfAlgIso f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toHopfAlgIso", 1)
    if args is not None:
        try:
            rhs = OOp("toHopfAlgIso", (OVar("e"), OVar("_unknown"), OVar("toHopfAlgIso"), OVar("f"),))
            results.append((rhs, "Mathlib: BialgEquiv_toHopfAlgIso_trans"))
        except Exception:
            pass
    return results


def _r0098_eIso_inv_freeMk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoidal.εIso_inv_freeMk
    # (εIso R).inv (freeMk x) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eIso_R_inv", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: FreeMonoidal_eIso_inv_freeMk"))
        except Exception:
            pass
    return results


def _r0099_free_eta_freeMk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: free_η_freeMk
    # η (free R) (freeMk x) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eta", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: free_eta_freeMk"))
        except Exception:
            pass
    return results


def _r0100_free_mu_freeMk_tmul_freeMk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: free_μ_freeMk_tmul_freeMk
    # μ (free R) _ _ (freeMk x ⊗ₜ freeMk y) = freeMk ⟨x, y⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu", 4)
    if args is not None:
        try:
            rhs = OOp("freeMk", (OVar("x_y"),))
            results.append((rhs, "Mathlib: free_mu_freeMk_tmul_freeMk"))
        except Exception:
            pass
    return results


def _r0101_comp_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.comp_app
    # (f ≫ g).app X = f.app X ≫ g.app X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g_app", 1)
    if args is not None:
        try:
            rhs = OOp("f_app", (args[0], OVar("_unknown"), OVar("g_app"), args[0],))
            results.append((rhs, "Mathlib: PresheafOfModules_comp_app"))
        except Exception:
            pass
    return results


def _r0102_presheaf_map_apply_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.presheaf_map_apply_coe
    # DFunLike.coe (α := M.obj X) (β := fun _ ↦ M.obj Y) (M.presheaf.map f).hom x = M.map f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "DFunLike_coe", 4)
    if args is not None:
        try:
            rhs = OOp("M_map", (OVar("f"), args[3],))
            results.append((rhs, "Mathlib: PresheafOfModules_presheaf_map_apply_coe"))
        except Exception:
            pass
    return results


def _r0103_toPresheaf_map_app_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.toPresheaf_map_app_apply
    # DFunLike.coe (α := M₁.obj X) (β := fun _ ↦ M₂.obj X)       (((toPresheaf R).map f).app X).hom x = f.app X x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "DFunLike_coe", 4)
    if args is not None:
        try:
            rhs = OOp("f_app", (OVar("X"), args[3],))
            results.append((rhs, "Mathlib: PresheafOfModules_toPresheaf_map_app_apply"))
        except Exception:
            pass
    return results


def _r0104_add_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.add_app
    # (f + g).app X = f.app X + g.app X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_plus_g_app", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f_app", (args[0],)), OOp("g_app", (args[0],))))
            results.append((rhs, "Mathlib: PresheafOfModules_add_app"))
        except Exception:
            pass
    return results


def _r0105_sub_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.sub_app
    # (f - g).app X = f.app X - g.app X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_minus_g_app", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("f_app", (args[0],)), OOp("g_app", (args[0],))))
            results.append((rhs, "Mathlib: PresheafOfModules_sub_app"))
        except Exception:
            pass
    return results


def _r0106_sectionsMap_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PresheafOfModules.sectionsMap_id
    # sectionsMap (𝟙 M) s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sectionsMap", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: PresheafOfModules_sectionsMap_id"))
        except Exception:
            pass
    return results


def _r0107_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemimoduleCat.id_apply
    # (𝟙 M : M ⟶ M) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_M_colon_M_M", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: SemimoduleCat_id_apply"))
        except Exception:
            pass
    return results


def _r0108_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemimoduleCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: SemimoduleCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0109_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemimoduleCat.ofHom_id
    # ofHom LinearMap.id = 𝟙 (of R M)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("R"), OVar("M"),)),))
            results.append((rhs, "Mathlib: SemimoduleCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0110_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemimoduleCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: SemimoduleCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0111_hom_2_ofHom_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemimoduleCat.Hom.hom₂_ofHom₂
    # (ofHom₂ f).hom₂ = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofHom_2_f_hom_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: SemimoduleCat_Hom_hom_2_ofHom_2"))
    except Exception:
        pass
    return results


def _r0112_ofHom_2_hom_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemimoduleCat.ofHom₂_hom₂
    # ofHom₂ f.hom₂ = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom_2", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: SemimoduleCat_ofHom_2_hom_2"))
        except Exception:
            pass
    return results


def _r0113_comp_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SheafOfModules.comp_val
    # (f ≫ g).val = f.val ≫ g.val
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_val", (OVar("_unknown"), OVar("g_val"),))
            results.append((rhs, "Mathlib: SheafOfModules_comp_val"))
    except Exception:
        pass
    return results


def _r0114_sectionsMap_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SheafOfModules.sectionsMap_id
    # sectionsMap (𝟙 M) s = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sectionsMap", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: SheafOfModules_sectionsMap_id"))
        except Exception:
            pass
    return results


def _r0115_unitHomEquiv_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SheafOfModules.unitHomEquiv_comp_apply
    # N.unitHomEquiv (f ≫ p) = sectionsMap p (M.unitHomEquiv f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "N_unitHomEquiv", 1)
    if args is not None:
        try:
            rhs = OOp("sectionsMap", (OVar("p"), OOp("M_unitHomEquiv", (OVar("f"),)),))
            results.append((rhs, "Mathlib: SheafOfModules_unitHomEquiv_comp_apply"))
        except Exception:
            pass
    return results


def _r0116_pushforwardCongr_hom_app_val_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SheafOfModules.pushforwardCongr_hom_app_val_app
    # ((pushforwardCongr e).hom.app M).val.app U x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pushforwardCongr_e_hom_app_M_val_app", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: SheafOfModules_pushforwardCongr_hom_app_val_app"))
        except Exception:
            pass
    return results


def _r0117_pushforwardCongr_inv_app_val_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SheafOfModules.pushforwardCongr_inv_app_val_app
    # ((pushforwardCongr e).inv.app M).val.app U x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pushforwardCongr_e_inv_app_M_val_app", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: SheafOfModules_pushforwardCongr_inv_app_val_app"))
        except Exception:
            pass
    return results


def _r0118_pushforwardNatTrans_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pushforwardNatTrans_id
    # pushforwardNatTrans φ (𝟙 G) = (pushforwardCongr (by cat_disch)).hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pushforwardNatTrans", 2)
    if args is not None:
        try:
            rhs = OVar("pushforwardCongr_by_cat_disch_hom")
            results.append((rhs, "Mathlib: pushforwardNatTrans_id"))
        except Exception:
            pass
    return results


def _r0119_pushforwardNatTrans_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pushforwardNatTrans_comp
    # pushforwardNatTrans φ (α ≫ β) = pushforwardNatTrans φ β ≫ pushforwardNatTrans _ α ≫       (pushforwardCongr (by cat_disc
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pushforwardNatTrans", 2)
    if args is not None:
        try:
            rhs = OOp("pushforwardNatTrans", (args[0], OVar("b"), OVar("_unknown"), OVar("pushforwardNatTrans"), OVar("_unknown"), OVar("a"), OVar("_unknown"), OVar("pushforwardCongr_by_cat_disch_hom"),))
            results.append((rhs, "Mathlib: pushforwardNatTrans_comp"))
        except Exception:
            pass
    return results


def _r0120_forget_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonCat.forget_map
    # (forget MonCat).map f = (f : _ → _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_MonCat_map", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("f", (OVar("colon"), OVar("_unknown"),)), OVar("_unknown")))
            results.append((rhs, "Mathlib: MonCat_forget_map"))
        except Exception:
            pass
    return results


def _r0121_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonCat.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: MonCat_ext"))
    except Exception:
        pass
    return results


def _r0122_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonCat.id_apply
    # (𝟙 M : M ⟶ M) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_M_colon_M_M", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MonCat_id_apply"))
        except Exception:
            pass
    return results


def _r0123_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MonCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0124_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonCat.ofHom_id
    # ofHom (MonoidHom.id M) = 𝟙 (of M)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("M"),)),))
            results.append((rhs, "Mathlib: MonCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0125_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: MonCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0126_oneHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonCat.oneHom_apply
    # (1 : X ⟶ Y).hom x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_X_Y_hom", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MonCat_oneHom_apply"))
        except Exception:
            pass
    return results


def _r0127_mul_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonCat.mul_of
    # @HMul.hMul (MonCat.of A) (MonCat.of A) (MonCat.of A) _ a b = a * b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 6)
    if args is not None:
        try:
            rhs = OOp("*", (args[4], args[5]))
            results.append((rhs, "Mathlib: MonCat_mul_of"))
        except Exception:
            pass
    return results


def _r0128_forget_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommMonCat.forget_map
    # (forget CommMonCat).map f = (f : X → Y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_CommMonCat_map", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("f", (OVar("colon"), OVar("X"),)), OVar("Y")))
            results.append((rhs, "Mathlib: CommMonCat_forget_map"))
        except Exception:
            pass
    return results


def _r0129_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommMonCat.id_apply
    # (𝟙 M : M ⟶ M) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_M_colon_M_M", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CommMonCat_id_apply"))
        except Exception:
            pass
    return results


def _r0130_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommMonCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CommMonCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0131_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommMonCat.ofHom_id
    # ofHom (MonoidHom.id M) = 𝟙 (of M)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("M"),)),))
            results.append((rhs, "Mathlib: CommMonCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0132_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommMonCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: CommMonCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0133_hom_forget_2_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommMonCat.hom_forget₂_map
    # ((forget₂ CommMonCat MonCat).map f).hom = f.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("forget_2_CommMonCat_MonCat_map_f_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_hom")
            results.append((rhs, "Mathlib: CommMonCat_hom_forget_2_map"))
    except Exception:
        pass
    return results


def _r0134_forget_2_map_ofHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommMonCat.forget₂_map_ofHom
    # (forget₂ CommMonCat MonCat).map (ofHom f) = MonCat.ofHom f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_2_CommMonCat_MonCat_map", 1)
    if args is not None:
        try:
            rhs = OOp("MonCat_ofHom", (OVar("f"),))
            results.append((rhs, "Mathlib: CommMonCat_forget_2_map_ofHom"))
        except Exception:
            pass
    return results


def _r0135_quot_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonCat.Colimits.quot_mul
    # Quot.mk Setoid.r (mul x y) =     @HMul.hMul (ColimitType F) (ColimitType F) (ColimitType F) _       (Quot.mk Setoid.r x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("ColimitType", (OVar("F"),)), OOp("ColimitType", (OVar("F"),)), OOp("ColimitType", (OVar("F"),)), OVar("_unknown"), OOp("Quot_mk", (args[0], OVar("x"),)), OOp("Quot_mk", (args[0], OVar("y"),)),))
            results.append((rhs, "Mathlib: MonCat_Colimits_quot_mul"))
        except Exception:
            pass
    return results


def _r0136_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemiRingCat.id_apply
    # (𝟙 R : R ⟶ R) r = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_R_colon_R_R", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: SemiRingCat_id_apply"))
        except Exception:
            pass
    return results


def _r0137_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemiRingCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: SemiRingCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0138_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemiRingCat.ofHom_id
    # ofHom (RingHom.id R) = 𝟙 (of R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("R"),)),))
            results.append((rhs, "Mathlib: SemiRingCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0139_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemiRingCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: SemiRingCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0140_forget_2_addCommMonCat_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SemiRingCat.forget₂_addCommMonCat_map
    # (forget₂ SemiRingCat AddCommMonCat).map f x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_2_SemiRingCat_AddCommMonCat_map", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: SemiRingCat_forget_2_addCommMonCat_map"))
        except Exception:
            pass
    return results


def _r0141_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommSemiRingCat.id_apply
    # (𝟙 R : R ⟶ R) r = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_R_colon_R_R", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CommSemiRingCat_id_apply"))
        except Exception:
            pass
    return results


def _r0142_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommSemiRingCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CommSemiRingCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0143_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommSemiRingCat.ofHom_id
    # ofHom (RingHom.id R) = 𝟙 (of R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("R"),)),))
            results.append((rhs, "Mathlib: CommSemiRingCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0144_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommSemiRingCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: CommSemiRingCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0145_coproductCocone_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coproductCocone_inr
    # (coproductCocone A B).inr = ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("coproductCocone_A_B_inr")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ofHom", (OVar("Algebra_TensorProduct_includeRight_R_colon_eq_toRingHom"),))
            results.append((rhs, "Mathlib: coproductCocone_inr"))
    except Exception:
        pass
    return results


def _r0146_forget_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MagmaCat.forget_map
    # (forget MagmaCat).map f = (f : _ → _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_MagmaCat_map", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("f", (OVar("colon"), OVar("_unknown"),)), OVar("_unknown")))
            results.append((rhs, "Mathlib: MagmaCat_forget_map"))
        except Exception:
            pass
    return results


def _r0147_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MagmaCat.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: MagmaCat_ext"))
    except Exception:
        pass
    return results


def _r0148_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MagmaCat.id_apply
    # (𝟙 M : M ⟶ M) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_M_colon_M_M", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MagmaCat_id_apply"))
        except Exception:
            pass
    return results


def _r0149_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MagmaCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MagmaCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0150_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MagmaCat.ofHom_id
    # ofHom (MulHom.id M) = 𝟙 (of M)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("M"),)),))
            results.append((rhs, "Mathlib: MagmaCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0151_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MagmaCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: MagmaCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0152_forget_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Semigrp.forget_map
    # (forget Semigrp).map f = (f : X → Y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_Semigrp_map", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("f", (OVar("colon"), OVar("X"),)), OVar("Y")))
            results.append((rhs, "Mathlib: Semigrp_forget_map"))
        except Exception:
            pass
    return results


def _r0153_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Semigrp.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: Semigrp_ext"))
    except Exception:
        pass
    return results


def _r0154_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Semigrp.id_apply
    # (𝟙 X : X ⟶ X) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_X_colon_X_X", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Semigrp_id_apply"))
        except Exception:
            pass
    return results


def _r0155_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Semigrp.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Semigrp_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0156_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Semigrp.ofHom_id
    # ofHom (MulHom.id X) = 𝟙 (of X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("X"),)),))
            results.append((rhs, "Mathlib: Semigrp_ofHom_id"))
        except Exception:
            pass
    return results


def _r0157_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Semigrp.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: Semigrp_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0158_ringChar_subsingleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ringChar.ringChar_subsingleton
    # ringChar R = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ringChar", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ringChar_ringChar_subsingleton"))
        except Exception:
            pass
    return results


def _r0159_iterateFrobenius_zero_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: iterateFrobenius_zero_apply
    # iterateFrobenius R p 0 x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iterateFrobenius", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: iterateFrobenius_zero_apply"))
        except Exception:
            pass
    return results


def _r0160_iterateFrobenius_add_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: iterateFrobenius_add_apply
    # iterateFrobenius R p (m + n) x = iterateFrobenius R p m (iterateFrobenius R p n x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iterateFrobenius", 4)
    if args is not None:
        try:
            rhs = OOp("iterateFrobenius", (args[0], args[1], OVar("m"), OOp("iterateFrobenius", (args[0], args[1], OVar("n"), args[3],)),))
            results.append((rhs, "Mathlib: iterateFrobenius_add_apply"))
        except Exception:
            pass
    return results


def _r0161_two_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: two_nsmul
    # 2 • x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_2", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: two_nsmul"))
        except Exception:
            pass
    return results


def _r0162_add_cancel_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_cancel_left
    # a + (a + b) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: add_cancel_left"))
        except Exception:
            pass
    return results


def _r0163_add_cancel_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_cancel_right
    # a + b + b = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: add_cancel_right"))
        except Exception:
            pass
    return results


def _r0164_add_eq_iff_eq_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_eq_iff_eq_add
    # a + b = c ↔ a = c + b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("c"), args[0])), OOp("+", (OVar("c"), args[1]))))
            results.append((rhs, "Mathlib: add_eq_iff_eq_add"))
        except Exception:
            pass
    return results


def _r0165_add_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_eq_zero
    # a + b = 0 ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), args[1]))
            results.append((rhs, "Mathlib: add_eq_zero"))
        except Exception:
            pass
    return results


def _r0166_ofNat_eq_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OfNat.ofNat_eq_ofNat
    # (ofNat(m) : R) = ofNat(n) ↔ (ofNat m : ℕ) = ofNat n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNat_m", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("ofNat_n"), OOp("ofNat", (OVar("m"), args[0], OVar("_unknown"),)))), OOp("ofNat", (OVar("n"),))))
            results.append((rhs, "Mathlib: OfNat_ofNat_eq_ofNat"))
        except Exception:
            pass
    return results


def _r0167_of_h_eq_intFractPair_seq1_fst_b(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GenContFract.of_h_eq_intFractPair_seq1_fst_b
    # (of v).h = (IntFractPair.seq1 v).fst.b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("of_v_h")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("IntFractPair_seq1_v_fst_b")
            results.append((rhs, "Mathlib: GenContFract_of_h_eq_intFractPair_seq1_fst_b"))
    except Exception:
        pass
    return results


def _r0168_first_contAux_eq_h_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: first_contAux_eq_h_one
    # g.contsAux 1 = ⟨g.h, 1⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_contsAux", 1)
    if args is not None:
        try:
            rhs = OVar("g_h_1")
            results.append((rhs, "Mathlib: first_contAux_eq_h_one"))
        except Exception:
            pass
    return results


def _r0169_zeroth_cont_eq_h_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zeroth_cont_eq_h_one
    # g.conts 0 = ⟨g.h, 1⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_conts", 1)
    if args is not None:
        try:
            rhs = OVar("g_h_1")
            results.append((rhs, "Mathlib: zeroth_cont_eq_h_one"))
        except Exception:
            pass
    return results


def _r0170_zeroth_num_eq_h(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zeroth_num_eq_h
    # g.nums 0 = g.h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_nums", 1)
    if args is not None:
        try:
            rhs = OVar("g_h")
            results.append((rhs, "Mathlib: zeroth_num_eq_h"))
        except Exception:
            pass
    return results


def _r0171_zeroth_den_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zeroth_den_eq_one
    # g.dens 0 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_dens", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: zeroth_den_eq_one"))
        except Exception:
            pass
    return results


def _r0172_zeroth_conv_eq_h(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zeroth_conv_eq_h
    # g.convs 0 = g.h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_convs", 1)
    if args is not None:
        try:
            rhs = OVar("g_h")
            results.append((rhs, "Mathlib: zeroth_conv_eq_h"))
        except Exception:
            pass
    return results


def _r0173_second_contAux_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: second_contAux_eq
    # g.contsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_contsAux", 1)
    if args is not None:
        try:
            rhs = OVar("gp_b_star_g_h_plus_gp_a_gp_b")
            results.append((rhs, "Mathlib: second_contAux_eq"))
        except Exception:
            pass
    return results


def _r0174_coeff_eq_a(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cubic.coeff_eq_a
    # P.toPoly.coeff 3 = P.a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "P_toPoly_coeff", 1)
    if args is not None:
        try:
            rhs = OVar("P_a")
            results.append((rhs, "Mathlib: Cubic_coeff_eq_a"))
        except Exception:
            pass
    return results


def _r0175_coeff_eq_b(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cubic.coeff_eq_b
    # P.toPoly.coeff 2 = P.b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "P_toPoly_coeff", 1)
    if args is not None:
        try:
            rhs = OVar("P_b")
            results.append((rhs, "Mathlib: Cubic_coeff_eq_b"))
        except Exception:
            pass
    return results


def _r0176_coeff_eq_c(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cubic.coeff_eq_c
    # P.toPoly.coeff 1 = P.c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "P_toPoly_coeff", 1)
    if args is not None:
        try:
            rhs = OVar("P_c")
            results.append((rhs, "Mathlib: Cubic_coeff_eq_c"))
        except Exception:
            pass
    return results


def _r0177_coeff_eq_d(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cubic.coeff_eq_d
    # P.toPoly.coeff 0 = P.d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "P_toPoly_coeff", 1)
    if args is not None:
        try:
            rhs = OVar("P_d")
            results.append((rhs, "Mathlib: Cubic_coeff_eq_d"))
        except Exception:
            pass
    return results


def _r0178_a_of_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Cubic.a_of_eq
    # P.a = Q.a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("P_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Q_a")
            results.append((rhs, "Mathlib: Cubic_a_of_eq"))
    except Exception:
        pass
    return results


def _r0179_natDegree_of_a_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: natDegree_of_a_ne_zero
    # P.toPoly.natDegree = 3
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("P_toPoly_natDegree")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(3)
            results.append((rhs, "Mathlib: natDegree_of_a_ne_zero"))
    except Exception:
        pass
    return results


def _r0180_sum_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: sum_apply
    # (∑ a ∈ s, g a) i = ∑ a ∈ s, g a i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_in_s_g_a", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("a"),)), OOp("s", (OVar("g"), OVar("a"), args[0],))))
            results.append((rhs, "Mathlib: sum_apply"))
        except Exception:
            pass
    return results


def _r0181_of_eq_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: of_eq_of_ne
    # (of _ i x) j = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "of_i_x", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: of_eq_of_ne"))
        except Exception:
            pass
    return results


def _r0182_support_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: support_of
    # (of _ i x).support = {i}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("of_i_x_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("i")
            results.append((rhs, "Mathlib: support_of"))
    except Exception:
        pass
    return results


def _r0183_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toAddMonoid.unique
    # ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi", 1)
    if args is not None:
        try:
            rhs = OOp("toAddMonoid", (OOp("fun", (OVar("i"), OVar("eq_gt"), OVar("psi_comp"), OOp("of", (OVar("b"), OVar("i"),)),)), args[0],))
            results.append((rhs, "Mathlib: toAddMonoid_unique"))
        except Exception:
            pass
    return results


def _r0184_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: id_apply
    # DirectSum.id M ι x = x default
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "DirectSum_id", 3)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("default"),))
            results.append((rhs, "Mathlib: id_apply"))
        except Exception:
            pass
    return results


def _r0185_map_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_apply
    # map f x i = f i (x i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[2], OOp("x", (args[2],)),))
            results.append((rhs, "Mathlib: map_apply"))
        except Exception:
            pass
    return results


def _r0186_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_id
    # (map (fun i ↦ AddMonoidHom.id (α i))) = AddMonoidHom.id (⨁ i, α i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 1)
    if args is not None:
        try:
            rhs = OOp("AddMonoidHom_id", (OOp("_unknown", (OVar("i"), OVar("a"), OVar("i"),)),))
            results.append((rhs, "Mathlib: map_id"))
        except Exception:
            pass
    return results


def _r0187_map_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_comp
    # (map (fun i ↦ (g i).comp (f i))) = (map g).comp (map f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 1)
    if args is not None:
        try:
            rhs = OOp("map_g_comp", (OOp("map", (OVar("f"),)),))
            results.append((rhs, "Mathlib: map_comp"))
        except Exception:
            pass
    return results


def _r0188_decompose_symm_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DirectSum.decompose_symm_of
    # (decompose ℳ).symm (DirectSum.of _ i x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decompose_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: DirectSum_decompose_symm_of"))
        except Exception:
            pass
    return results


def _r0189_decompose_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DirectSum.decompose_coe
    # decompose ℳ (x : M) = DirectSum.of _ i x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decompose", 2)
    if args is not None:
        try:
            rhs = OOp("DirectSum_of", (args[0], OVar("i"), OVar("x"),))
            results.append((rhs, "Mathlib: DirectSum_decompose_coe"))
        except Exception:
            pass
    return results


def _r0190_decompose_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DirectSum.decompose_of_mem
    # decompose ℳ x = DirectSum.of (fun i ↦ ℳ i) i ⟨x, hx⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decompose", 2)
    if args is not None:
        try:
            rhs = OOp("DirectSum_of", (OOp("fun", (OVar("i"), args[0], args[0], OVar("i"),)), OVar("i"), OVar("x_hx"),))
            results.append((rhs, "Mathlib: DirectSum_decompose_of_mem"))
        except Exception:
            pass
    return results


def _r0191_decompose_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DirectSum.decompose_zero
    # decompose ℳ (0 : M) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decompose", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DirectSum_decompose_zero"))
        except Exception:
            pass
    return results


def _r0192_decompose_symm_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DirectSum.decompose_symm_zero
    # (decompose ℳ).symm 0 = (0 : M)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decompose_symm", 1)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("colon"), OVar("M"),))
            results.append((rhs, "Mathlib: DirectSum_decompose_symm_zero"))
        except Exception:
            pass
    return results


def _r0193_decompose_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DirectSum.decompose_add
    # decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decompose", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("decompose", (args[0], OVar("x"),)), OOp("decompose", (args[0], OVar("y"),))))
            results.append((rhs, "Mathlib: DirectSum_decompose_add"))
        except Exception:
            pass
    return results


def _r0194_decompose_symm_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DirectSum.decompose_symm_add
    # (decompose ℳ).symm (x + y) = (decompose ℳ).symm x + (decompose ℳ).symm y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decompose_symm", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("decompose_symm", (OVar("x"),)), OOp("decompose_symm", (OVar("y"),))))
            results.append((rhs, "Mathlib: DirectSum_decompose_symm_add"))
        except Exception:
            pass
    return results


def _r0195_decompose_symm_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: decompose_symm_neg
    # (decompose ℳ).symm (-x) = -(decompose ℳ).symm x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decompose_symm", 1)
    if args is not None:
        try:
            rhs = OOp("minus_decompose_symm", (OVar("x"),))
            results.append((rhs, "Mathlib: decompose_symm_neg"))
        except Exception:
            pass
    return results


def _r0196_decompose_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: decompose_sub
    # decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decompose", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("decompose", (args[0], OVar("x"),)), OOp("decompose", (args[0], OVar("y"),))))
            results.append((rhs, "Mathlib: decompose_sub"))
        except Exception:
            pass
    return results


def _r0197_decompose_symm_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: decompose_symm_sub
    # (decompose ℳ).symm (x - y) = (decompose ℳ).symm x - (decompose ℳ).symm y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decompose_symm", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("decompose_symm", (OVar("x"),)), OOp("decompose_symm", (OVar("y"),))))
            results.append((rhs, "Mathlib: decompose_symm_sub"))
        except Exception:
            pass
    return results


def _r0198_decomposeLinearEquiv_symm_comp_lof(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: decomposeLinearEquiv_symm_comp_lof
    # (decomposeLinearEquiv ℳ).symm ∘ₗ lof R ι (ℳ ·) i = (ℳ i).subtype
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decomposeLinearEquiv_symm", 6)
    if args is not None:
        try:
            rhs = OVar("i_subtype")
            results.append((rhs, "Mathlib: decomposeLinearEquiv_symm_comp_lof"))
        except Exception:
            pass
    return results


def _r0199_decomposeLinearEquiv_symm_lof(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: decomposeLinearEquiv_symm_lof
    # (decomposeLinearEquiv ℳ).symm (lof R _ _ i x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decomposeLinearEquiv_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: decomposeLinearEquiv_symm_lof"))
        except Exception:
            pass
    return results


def _r0200_decomposeLinearEquiv_apply_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: decomposeLinearEquiv_apply_coe
    # decomposeLinearEquiv ℳ x = lof R _ _ i x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decomposeLinearEquiv", 2)
    if args is not None:
        try:
            rhs = OOp("lof", (OVar("R"), args[0], args[0], OVar("i"), args[1],))
            results.append((rhs, "Mathlib: decomposeLinearEquiv_apply_coe"))
        except Exception:
            pass
    return results


def _r0201_lid_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lid_symm_apply
    # (DirectSum.lid R M ι).symm x = lof R _ _ default x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "DirectSum_lid_R_M_i_symm", 1)
    if args is not None:
        try:
            rhs = OOp("lof", (OVar("R"), OVar("_unknown"), OVar("_unknown"), OVar("default"), args[0],))
            results.append((rhs, "Mathlib: lid_symm_apply"))
        except Exception:
            pass
    return results


def _r0202_lof_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: component.lof_self
    # component R ι M i ((lof R ι M i) b) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "component", 5)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: component_lof_self"))
        except Exception:
            pass
    return results


def _r0203_lmap_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lmap_of
    # lmap f (of M i x) = of N i (f i x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lmap", 2)
    if args is not None:
        try:
            rhs = OOp("of", (OVar("N"), OVar("i"), OOp("f", (OVar("i"), OVar("x"),)),))
            results.append((rhs, "Mathlib: lmap_of"))
        except Exception:
            pass
    return results


def _r0204_lmap_lof(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lmap_lof
    # lmap f (lof R _ _ _ x) = lof R _ _ _ (f i x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lmap", 2)
    if args is not None:
        try:
            rhs = OOp("lof", (OVar("R"), OVar("_unknown"), OVar("_unknown"), OVar("_unknown"), OOp("f", (OVar("i"), OVar("x"),)),))
            results.append((rhs, "Mathlib: lmap_lof"))
        except Exception:
            pass
    return results


def _r0205_lmap_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lmap_id
    # (lmap (fun i ↦ LinearMap.id (R := R) (M := M i))) = LinearMap.id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lmap", 1)
    if args is not None:
        try:
            rhs = OVar("LinearMap_id")
            results.append((rhs, "Mathlib: lmap_id"))
        except Exception:
            pass
    return results


def _r0206_lmap_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lmap_comp
    # (lmap (fun i ↦ (g i) ∘ₗ (f i))) = (lmap g) ∘ₗ (lmap f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lmap", 1)
    if args is not None:
        try:
            rhs = OOp("lmap_g", (OVar("comp"), OOp("lmap", (OVar("f"),)),))
            results.append((rhs, "Mathlib: lmap_comp"))
        except Exception:
            pass
    return results


def _r0207_of_zero_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: of_zero_mul
    # of _ 0 (a * b) = of _ 0 a * of _ 0 b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "of", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("of", (args[0], OLit(0), OVar("a"),)), OOp("of", (args[0], OLit(0), OVar("b"),))))
            results.append((rhs, "Mathlib: of_zero_mul"))
        except Exception:
            pass
    return results


def _r0208_of_zero_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: of_zero_ofNat
    # of A 0 ofNat(n) = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "of", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: of_zero_ofNat"))
        except Exception:
            pass
    return results


def _r0209_snd_eps(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DualNumber.snd_eps
    # snd ε = (1 : R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("colon"), OVar("R"),))
            results.append((rhs, "Mathlib: DualNumber_snd_eps"))
        except Exception:
            pass
    return results


def _r0210_eps_mul_eps(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DualNumber.eps_mul_eps
    # (ε * ε : R[ε]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DualNumber_eps_mul_eps"))
        except Exception:
            pass
    return results


def _r0211_eps_pow_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DualNumber.eps_pow_two
    # (ε : R[ε]) ^ 2 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DualNumber_eps_pow_two"))
        except Exception:
            pass
    return results


def _r0212_inv_eps(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DualNumber.inv_eps
    # (ε : R[ε])⁻¹ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_colon_R_e_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: DualNumber_inv_eps"))
    except Exception:
        pass
    return results


def _r0213_inr_eq_smul_eps(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DualNumber.inr_eq_smul_eps
    # inr r = (r • ε : R[ε])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inr", 1)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("_unknown"), OVar("e"), OVar("colon"), OVar("R_e"),))
            results.append((rhs, "Mathlib: DualNumber_inr_eq_smul_eps"))
        except Exception:
            pass
    return results


def _r0214_lift_apply_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DualNumber.lift_apply_inl
    # lift fe (inl a : A[ε]) = fe.val.1 a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 2)
    if args is not None:
        try:
            rhs = OOp("fe_val_1", (OVar("a"),))
            results.append((rhs, "Mathlib: DualNumber_lift_apply_inl"))
        except Exception:
            pass
    return results


def _r0215_lift_comp_inlHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DualNumber.lift_comp_inlHom
    # (lift fe).comp (inlAlgHom R A A) = fe.val.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_fe_comp", 1)
    if args is not None:
        try:
            rhs = OVar("fe_val_1")
            results.append((rhs, "Mathlib: DualNumber_lift_comp_inlHom"))
        except Exception:
            pass
    return results


def _r0216_zero_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EuclideanDomain.zero_mod
    # 0 % b = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: EuclideanDomain_zero_mod"))
        except Exception:
            pass
    return results


def _r0217_zero_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EuclideanDomain.zero_div
    # 0 / a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: EuclideanDomain_zero_div"))
        except Exception:
            pass
    return results


def _r0218_eq_div_of_mul_eq_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EuclideanDomain.eq_div_of_mul_eq_left
    # a = c / b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("c"), OVar("b")))
            results.append((rhs, "Mathlib: EuclideanDomain_eq_div_of_mul_eq_left"))
    except Exception:
        pass
    return results


def _r0219_gcd_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EuclideanDomain.gcd_self
    # gcd a a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "gcd", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: EuclideanDomain_gcd_self"))
        except Exception:
            pass
    return results


def _r0220_xgcdAux_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EuclideanDomain.xgcdAux_fst
    # ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("xgcdAux_x_s_t_y_s_prime_t_prime_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("gcd", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: EuclideanDomain_xgcdAux_fst"))
    except Exception:
        pass
    return results


def _r0221_lcm_zero_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lcm_zero_right
    # lcm x 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lcm", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: lcm_zero_right"))
        except Exception:
            pass
    return results


def _r0222_lcm_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lcm_eq_zero_iff
    # lcm x y = 0 ↔ x = 0 ∨ y = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lcm", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OOp("==", (OOp("or", (OLit(0), args[1])), OLit(0)))))
            results.append((rhs, "Mathlib: lcm_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0223_lt_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: EuclideanDomain.lt_one
    # a ≺ (1 : R) → a = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: EuclideanDomain_lt_one"))
    except Exception:
        pass
    return results


def _r0224_add_halves(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_halves
    # a / 2 + a / 2 = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: add_halves"))
        except Exception:
            pass
    return results


def _r0225_neg_div_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: neg_div_self
    # -a / a = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: neg_div_self"))
        except Exception:
            pass
    return results


def _r0226_div_sub_div_same(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_sub_div_same
    # a / c - b / c = (a - b) / c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("-", (OVar("a"), OVar("b"))), OVar("c")))
            results.append((rhs, "Mathlib: div_sub_div_same"))
        except Exception:
            pass
    return results


def _r0227_ofDual_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofDual_ratCast
    # (ofDual n : K) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofDual", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ofDual_ratCast"))
        except Exception:
            pass
    return results


def _r0228_ofLex_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofLex_ratCast
    # (ofLex n : K) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLex", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ofLex_ratCast"))
        except Exception:
            pass
    return results


def _r0229_coe_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNRat.coe_div
    # ((p / q : ℚ≥0) : ℚ) = p / q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_slash_q_colon_ge_0", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("p"), OVar("q")))
            results.append((rhs, "Mathlib: NNRat_coe_div"))
        except Exception:
            pass
    return results


def _r0230_coe_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNRat.coe_zpow
    # ((p ^ n : ℚ≥0) : ℚ) = p ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_pow_n_colon_ge_0", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("p"), OVar("n")))
            results.append((rhs, "Mathlib: NNRat_coe_zpow"))
        except Exception:
            pass
    return results


def _r0231_inv_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNRat.inv_def
    # q⁻¹ = divNat q.den q.num
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("qinv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("divNat", (OVar("q_den"), OVar("q_num"),))
            results.append((rhs, "Mathlib: NNRat_inv_def"))
    except Exception:
        pass
    return results


def _r0232_div_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NNRat.div_def
    # p / q = divNat (p.num * q.den) (p.den * q.num)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("divNat", (OOp("*", (OVar("p_num"), OVar("q_den"))), OOp("*", (OVar("p_den"), OVar("q_num"))),))
            results.append((rhs, "Mathlib: NNRat_div_def"))
        except Exception:
            pass
    return results


def _r0233_coe_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_top
    # ((⊤ : Subfield K) : Set K) = Set.univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Subfield_K", 3)
    if args is not None:
        try:
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: coe_top"))
        except Exception:
            pass
    return results


def _r0234_comap_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: comap_comap
    # (s.comap g).comap f = s.comap (g.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_comap_g_comap", 1)
    if args is not None:
        try:
            rhs = OOp("s_comap", (OOp("g_comp", (args[0],)),))
            results.append((rhs, "Mathlib: comap_comap"))
        except Exception:
            pass
    return results


def _r0235_mem_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mem_map
    # y ∈ s.map f ↔ ∃ x ∈ s, f x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: mem_map"))
        except Exception:
            pass
    return results


def _r0236_lift_comp_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMagma.lift_comp_of
    # lift f ∘ of = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: FreeMagma_lift_comp_of"))
        except Exception:
            pass
    return results


def _r0237_pure_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pure_bind
    # pure x >>= f = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pure", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: pure_bind"))
        except Exception:
            pass
    return results


def _r0238_mul_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_bind
    # x * y >>= f = (x >>= f) * (y >>= f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("x", (OVar("gt_gt_eq"), OVar("f"),)), OOp("y", (OVar("gt_gt_eq"), OVar("f"),))))
            results.append((rhs, "Mathlib: mul_bind"))
        except Exception:
            pass
    return results


def _r0239_pure_seq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pure_seq
    # pure f <*> x = f <$> x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pure", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("lt_gt"), args[2],))
            results.append((rhs, "Mathlib: pure_seq"))
        except Exception:
            pass
    return results


def _r0240_mul_seq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_seq
    # f * g <*> x = (f <*> x) * (g <*> x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OVar("lt_star_gt"), OVar("x"),)), OOp("g", (OVar("lt_star_gt"), OVar("x"),))))
            results.append((rhs, "Mathlib: mul_seq"))
        except Exception:
            pass
    return results


def _r0241_traverse_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMagma.traverse_mul
    # traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "traverse", 2)
    if args is not None:
        try:
            rhs = OOp("star", (OVar("lt_gt"), OVar("traverse"), args[0], OVar("x"), OVar("lt_star_gt"), OVar("traverse"), args[0], OVar("y"),))
            results.append((rhs, "Mathlib: FreeMagma_traverse_mul"))
        except Exception:
            pass
    return results


def _r0242_lift_comp_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Magma.AssocQuotient.lift_comp_of
    # (lift f).comp of = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_f_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Magma_AssocQuotient_lift_comp_of"))
        except Exception:
            pass
    return results


def _r0243_tail_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeSemigroup.tail_mul
    # (x * y).2 = x.2 ++ y.1 :: y.2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_star_y_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OVar("x_2"), OOp("y_1", (OVar("colon_colon"), OVar("y_2"),))))
            results.append((rhs, "Mathlib: FreeSemigroup_tail_mul"))
    except Exception:
        pass
    return results


def _r0244_mk_mul_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeSemigroup.mk_mul_mk
    # mk x L1 * mk y L2 = mk x (L1 ++ y :: L2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("pair", (OVar("x"), OOp("concat", (OVar("L1"), OOp("y", (OVar("colon_colon"), OVar("L2"),)))),))
            results.append((rhs, "Mathlib: FreeSemigroup_mk_mul_mk"))
        except Exception:
            pass
    return results


def _r0245_length_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeSemigroup.length_of
    # (of x).length = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("of_x_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: FreeSemigroup_length_of"))
    except Exception:
        pass
    return results


def _r0246_lift_comp_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeSemigroup.lift_comp_of
    # lift f ∘ of = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: FreeSemigroup_lift_comp_of"))
        except Exception:
            pass
    return results


def _r0247_lift_of_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeSemigroup.lift_of_mul
    # lift f (of x * y) = f x * lift f y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OVar("x"),)), OOp("lift", (args[0], OVar("y"),))))
            results.append((rhs, "Mathlib: FreeSemigroup_lift_of_mul"))
        except Exception:
            pass
    return results


def _r0248_length_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: length_map
    # (map f x).length = x.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("map_f_x_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_length")
            results.append((rhs, "Mathlib: length_map"))
    except Exception:
        pass
    return results


def _r0249_pure_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pure_bind
    # pure x >>= f = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pure", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: pure_bind"))
        except Exception:
            pass
    return results


def _r0250_mul_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_bind
    # x * y >>= f = (x >>= f) * (y >>= f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("x", (OVar("gt_gt_eq"), OVar("f"),)), OOp("y", (OVar("gt_gt_eq"), OVar("f"),))))
            results.append((rhs, "Mathlib: mul_bind"))
        except Exception:
            pass
    return results


def _r0251_pure_seq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pure_seq
    # pure f <*> x = f <$> x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pure", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("lt_gt"), args[2],))
            results.append((rhs, "Mathlib: pure_seq"))
        except Exception:
            pass
    return results


def _r0252_mul_seq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_seq
    # f * g <*> x = (f <*> x) * (g <*> x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OVar("lt_star_gt"), OVar("x"),)), OOp("g", (OVar("lt_star_gt"), OVar("x"),))))
            results.append((rhs, "Mathlib: mul_seq"))
        except Exception:
            pass
    return results


def _r0253_toFreeSemigroup_comp_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMagma.toFreeSemigroup_comp_of
    # @toFreeSemigroup α ∘ of = FreeSemigroup.of
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("FreeSemigroup_of")
            results.append((rhs, "Mathlib: FreeMagma_toFreeSemigroup_comp_of"))
        except Exception:
            pass
    return results


def _r0254_toFreeSemigroup_comp_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMagma.toFreeSemigroup_comp_map
    # toFreeSemigroup.comp (map f) = (FreeSemigroup.map f).comp toFreeSemigroup
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFreeSemigroup_comp", 1)
    if args is not None:
        try:
            rhs = OOp("FreeSemigroup_map_f_comp", (OVar("toFreeSemigroup"),))
            results.append((rhs, "Mathlib: FreeMagma_toFreeSemigroup_comp_map"))
        except Exception:
            pass
    return results


def _r0255_support_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeAbelianGroup.support_of
    # support (of x) = {x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "support", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: FreeAbelianGroup_support_of"))
        except Exception:
            pass
    return results


def _r0256_support_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeAbelianGroup.support_neg
    # support (-a) = support a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "support", 1)
    if args is not None:
        try:
            rhs = OOp("support", (OVar("a"),))
            results.append((rhs, "Mathlib: FreeAbelianGroup_support_neg"))
        except Exception:
            pass
    return results


def _r0257_support_zsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeAbelianGroup.support_zsmul
    # support (k • a) = support a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "support", 1)
    if args is not None:
        try:
            rhs = OOp("support", (OVar("a"),))
            results.append((rhs, "Mathlib: FreeAbelianGroup_support_zsmul"))
        except Exception:
            pass
    return results


def _r0258_ofList_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.ofList_symm
    # (@ofList α).symm = toList
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("at_ofList_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("toList")
            results.append((rhs, "Mathlib: FreeMonoid_ofList_symm"))
    except Exception:
        pass
    return results


def _r0259_toList_ofList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.toList_ofList
    # toList (ofList l) = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: FreeMonoid_toList_ofList"))
        except Exception:
            pass
    return results


def _r0260_ofList_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.ofList_toList
    # ofList (toList xs) = xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OVar("xs")
            results.append((rhs, "Mathlib: FreeMonoid_ofList_toList"))
        except Exception:
            pass
    return results


def _r0261_toList_comp_ofList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.toList_comp_ofList
    # @toList α ∘ ofList = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: FreeMonoid_toList_comp_ofList"))
        except Exception:
            pass
    return results


def _r0262_ofList_comp_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.ofList_comp_toList
    # @ofList α ∘ toList = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: FreeMonoid_ofList_comp_toList"))
        except Exception:
            pass
    return results


def _r0263_ofList_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.ofList_nil
    # ofList ([] : List α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: FreeMonoid_ofList_nil"))
        except Exception:
            pass
    return results


def _r0264_toList_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.toList_nil
    # toList ([] : FreeMonoid α) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 1)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: FreeMonoid_toList_nil"))
        except Exception:
            pass
    return results


def _r0265_toList_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.toList_cons
    # toList (x :: xs) = x :: toList xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 1)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("colon_colon"), OVar("toList"), OVar("xs"),))
            results.append((rhs, "Mathlib: FreeMonoid_toList_cons"))
        except Exception:
            pass
    return results


def _r0266_toList_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.toList_prod
    # toList xs.prod = (xs.map toList).flatten
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 1)
    if args is not None:
        try:
            rhs = OVar("xs_map_toList_flatten")
            results.append((rhs, "Mathlib: FreeMonoid_toList_prod"))
        except Exception:
            pass
    return results


def _r0267_ofList_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.ofList_flatten
    # ofList xs.flatten = (xs.map ofList).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OVar("xs_map_ofList_prod")
            results.append((rhs, "Mathlib: FreeMonoid_ofList_flatten"))
        except Exception:
            pass
    return results


def _r0268_ofList_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.ofList_singleton
    # ofList [x] = of x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OOp("of", (OVar("x"),))
            results.append((rhs, "Mathlib: FreeMonoid_ofList_singleton"))
        except Exception:
            pass
    return results


def _r0269_toList_of_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.toList_of_mul
    # toList (of x * xs) = x :: toList xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 1)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("colon_colon"), OVar("toList"), OVar("xs"),))
            results.append((rhs, "Mathlib: FreeMonoid_toList_of_mul"))
        except Exception:
            pass
    return results


def _r0270_length_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.length_eq_zero
    # length a = 0 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: FreeMonoid_length_eq_zero"))
        except Exception:
            pass
    return results


def _r0271_length_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.length_of
    # length (of m) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: FreeMonoid_length_of"))
        except Exception:
            pass
    return results


def _r0272_length_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.length_eq_one
    # length a = 1 ↔ ∃ m, a = FreeMonoid.of m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OOp("exists", (OVar("m"), args[0],)))), OOp("FreeMonoid_of", (OVar("m"),))))
            results.append((rhs, "Mathlib: FreeMonoid_length_eq_one"))
        except Exception:
            pass
    return results


def _r0273_recOn_of_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: recOn_of_mul
    # @recOn α C (of x * xs) h0 ih = ih x xs (recOn xs h0 ih)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_recOn", 5)
    if args is not None:
        try:
            rhs = OOp("ih", (OVar("x"), OVar("xs"), OOp("recOn", (OVar("xs"), args[3], args[4],)),))
            results.append((rhs, "Mathlib: recOn_of_mul"))
        except Exception:
            pass
    return results


def _r0274_casesOn_of_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: casesOn_of_mul
    # @casesOn α C (of x * xs) h0 ih = ih x xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_casesOn", 5)
    if args is not None:
        try:
            rhs = OOp("ih", (OVar("x"), OVar("xs"),))
            results.append((rhs, "Mathlib: casesOn_of_mul"))
        except Exception:
            pass
    return results


def _r0275_lift_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lift_symm_apply
    # lift.symm f = f ∘ of
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_symm", 1)
    if args is not None:
        try:
            rhs = OOp("comp", (args[0], OVar("of")))
            results.append((rhs, "Mathlib: lift_symm_apply"))
        except Exception:
            pass
    return results


def _r0276_lift_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lift_apply
    # lift f l = ((toList l).map f).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 2)
    if args is not None:
        try:
            rhs = OVar("toList_l_map_f_prod")
            results.append((rhs, "Mathlib: lift_apply"))
        except Exception:
            pass
    return results


def _r0277_lift_restrict(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lift_restrict
    # lift (f ∘ of) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: lift_restrict"))
        except Exception:
            pass
    return results


def _r0278_comp_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: comp_lift
    # g.comp (lift f) = lift (g ∘ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("lift", (OOp("comp", (OVar("g"), OVar("f"))),))
            results.append((rhs, "Mathlib: comp_lift"))
        except Exception:
            pass
    return results


def _r0279_mem_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mem_map
    # m ∈ map f a ↔ ∃ n ∈ a, f n = m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("m")
            results.append((rhs, "Mathlib: mem_map"))
        except Exception:
            pass
    return results


def _r0280_ofList_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofList_map
    # ofList (xs.map f) = map f (ofList xs)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OOp("map", (OVar("f"), OOp("ofList", (OVar("xs"),)),))
            results.append((rhs, "Mathlib: ofList_map"))
        except Exception:
            pass
    return results


def _r0281_map_symm_apply_map_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_symm_apply_map_eq
    # (map ⇑e.symm) ((map ⇑e) x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_e_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: map_symm_apply_map_eq"))
        except Exception:
            pass
    return results


def _r0282_map_apply_map_symm_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_apply_map_symm_eq
    # (map ⇑e) ((map ⇑e.symm) x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_e", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: map_apply_map_symm_eq"))
        except Exception:
            pass
    return results


def _r0283_reverse_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: reverse_mul
    # reverse (a * b) = reverse b * reverse a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reverse", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("reverse", (OVar("b"),)), OOp("reverse", (OVar("a"),))))
            results.append((rhs, "Mathlib: reverse_mul"))
        except Exception:
            pass
    return results


def _r0284_length_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: length_reverse
    # a.reverse.length = a.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_reverse_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a_length")
            results.append((rhs, "Mathlib: length_reverse"))
    except Exception:
        pass
    return results


def _r0285_freeMonoidCongr_symm_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: freeMonoidCongr_symm_of
    # freeMonoidCongr e.symm (of b) = of (e.symm b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "freeMonoidCongr", 2)
    if args is not None:
        try:
            rhs = OOp("of", (OOp("e_symm", (OVar("b"),)),))
            results.append((rhs, "Mathlib: freeMonoidCongr_symm_of"))
        except Exception:
            pass
    return results


def _r0286_symbols_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.symbols_of
    # symbols (of m) = {m}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "symbols", 1)
    if args is not None:
        try:
            rhs = OVar("m")
            results.append((rhs, "Mathlib: FreeMonoid_symbols_of"))
        except Exception:
            pass
    return results


def _r0287_symbols_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeMonoid.symbols_mul
    # symbols (a * b) = symbols a ∪ symbols b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "symbols", 1)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("symbols", (OVar("a"),)), OOp("symbols", (OVar("b"),))))
            results.append((rhs, "Mathlib: FreeMonoid_symbols_mul"))
        except Exception:
            pass
    return results


def _r0288_of_comp_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeNonUnitalNonAssocAlgebra.of_comp_lift
    # lift R f ∘ of R = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: FreeNonUnitalNonAssocAlgebra_of_comp_lift"))
        except Exception:
            pass
    return results


def _r0289_lift_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeNonUnitalNonAssocAlgebra.lift_unique
    # F ∘ of R = f ↔ F = lift R f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("f"), args[0])), OOp("lift", (OVar("R"), OVar("f"),))))
            results.append((rhs, "Mathlib: FreeNonUnitalNonAssocAlgebra_lift_unique"))
        except Exception:
            pass
    return results


def _r0290_lift_comp_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeNonUnitalNonAssocAlgebra.lift_comp_of
    # lift R (F ∘ of R) = F
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 2)
    if args is not None:
        try:
            rhs = OVar("F")
            results.append((rhs, "Mathlib: FreeNonUnitalNonAssocAlgebra_lift_comp_of"))
        except Exception:
            pass
    return results


def _r0291_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeNonUnitalNonAssocAlgebra.hom_ext
    # F₁ = F₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("F_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("F_2")
            results.append((rhs, "Mathlib: FreeNonUnitalNonAssocAlgebra_hom_ext"))
    except Exception:
        pass
    return results


def _r0292_normalize_eq_normalize(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: normalize_eq_normalize
    # normalize a = normalize b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = OOp("normalize", (OVar("b"),))
            results.append((rhs, "Mathlib: normalize_eq_normalize"))
        except Exception:
            pass
    return results


def _r0293_out_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Associates.out_one
    # (1 : Associates α).out = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Associates_a_out")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Associates_out_one"))
    except Exception:
        pass
    return results


def _r0294_out_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Associates.out_mul
    # (a * b).out = a.out * b.out
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_star_b_out")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("a_out"), OVar("b_out")))
            results.append((rhs, "Mathlib: Associates_out_mul"))
    except Exception:
        pass
    return results


def _r0295_normalize_out(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Associates.normalize_out
    # normalize a.out = a.out
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Associates_normalize_out"))
        except Exception:
            pass
    return results


def _r0296_mk_out(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Associates.mk_out
    # Associates.mk a.out = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Associates_mk", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Associates_mk_out"))
        except Exception:
            pass
    return results


def _r0297_out_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Associates.out_zero
    # (0 : Associates α).out = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Associates_a_out")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Associates_out_zero"))
    except Exception:
        pass
    return results


def _r0298_gcd_mul_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: gcd_mul_left
    # gcd (a * b) (a * c) = normalize a * gcd b c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "gcd", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("normalize", (OVar("a"),)), OOp("gcd", (OVar("b"), OVar("c"),))))
            results.append((rhs, "Mathlib: gcd_mul_left"))
        except Exception:
            pass
    return results


def _r0299_lcm_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lcm_comm
    # lcm a b = lcm b a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lcm", 2)
    if args is not None:
        try:
            rhs = OOp("lcm", (args[1], args[0],))
            results.append((rhs, "Mathlib: lcm_comm"))
        except Exception:
            pass
    return results


def _r0300_lcm_units_coe_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lcm_units_coe_right
    # lcm a ↑u = normalize a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lcm", 2)
    if args is not None:
        try:
            rhs = OOp("normalize", (args[0],))
            results.append((rhs, "Mathlib: lcm_units_coe_right"))
        except Exception:
            pass
    return results


def _r0301_lcm_one_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lcm_one_left
    # lcm 1 a = normalize a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lcm", 2)
    if args is not None:
        try:
            rhs = OOp("normalize", (args[1],))
            results.append((rhs, "Mathlib: lcm_one_left"))
        except Exception:
            pass
    return results


def _r0302_lcm_one_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lcm_one_right
    # lcm a 1 = normalize a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lcm", 2)
    if args is not None:
        try:
            rhs = OOp("normalize", (args[0],))
            results.append((rhs, "Mathlib: lcm_one_right"))
        except Exception:
            pass
    return results


def _r0303_lcm_same(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lcm_same
    # lcm a a = normalize a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lcm", 2)
    if args is not None:
        try:
            rhs = OOp("normalize", (args[1],))
            results.append((rhs, "Mathlib: lcm_same"))
        except Exception:
            pass
    return results


def _r0304_lcm_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lcm_eq_one_iff
    # lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lcm", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("iff", (OLit(1), OOp("a", (OVar("_unknown"), OLit(1),)))), OOp("b", (OVar("_unknown"), OLit(1),))))
            results.append((rhs, "Mathlib: lcm_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0305_lcm_eq_left_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: lcm_eq_left_iff
    # lcm a b = a ↔ b ∣ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lcm", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (args[0], OOp("b", (OVar("_unknown"), args[0],))))
            results.append((rhs, "Mathlib: lcm_eq_left_iff"))
        except Exception:
            pass
    return results


def _r0306_normalize_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: normalize_eq
    # normalize x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: normalize_eq"))
        except Exception:
            pass
    return results


def _r0307_normalize_gcd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: normalize_gcd
    # normalize (s.gcd f) = s.gcd f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = OOp("s_gcd", (OVar("f"),))
            results.append((rhs, "Mathlib: normalize_gcd"))
        except Exception:
            pass
    return results


def _r0308_gcd_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: gcd_union
    # (s₁ ∪ s₂).gcd f = GCDMonoid.gcd (s₁.gcd f) (s₂.gcd f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_1_union_s_2_gcd", 1)
    if args is not None:
        try:
            rhs = OOp("GCDMonoid_gcd", (OOp("s_1_gcd", (args[0],)), OOp("s_2_gcd", (args[0],)),))
            results.append((rhs, "Mathlib: gcd_union"))
        except Exception:
            pass
    return results


def _r0309_gcd_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: gcd_cons
    # (a ::ₘ s).gcd = GCDMonoid.gcd a s.gcd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_colon_s_gcd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("GCDMonoid_gcd", (OVar("a"), OVar("s_gcd"),))
            results.append((rhs, "Mathlib: gcd_cons"))
    except Exception:
        pass
    return results


def _r0310_gcd_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: gcd_singleton
    # ({a} : Multiset α).gcd = normalize a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_Multiset_a_gcd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("normalize", (OVar("a"),))
            results.append((rhs, "Mathlib: gcd_singleton"))
    except Exception:
        pass
    return results


def _r0311_gcd_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: gcd_add
    # (s₁ + s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_1_plus_s_2_gcd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("GCDMonoid_gcd", (OVar("s_1_gcd"), OVar("s_2_gcd"),))
            results.append((rhs, "Mathlib: gcd_add"))
    except Exception:
        pass
    return results


def _r0312_gcd_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: gcd_eq_zero_iff
    # s.gcd = 0 ↔ ∀ x ∈ s, x = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_gcd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("in", (OOp("forall", (OVar("x"),)), OOp("s", (OVar("x"),)))))), OLit(0)))
            results.append((rhs, "Mathlib: gcd_eq_zero_iff"))
    except Exception:
        pass
    return results


def _r0313_lcm_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PUnit.lcm_eq
    # lcm x y = unit
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lcm", 2)
    if args is not None:
        try:
            rhs = OVar("unit")
            results.append((rhs, "Mathlib: PUnit_lcm_eq"))
        except Exception:
            pass
    return results


def _r0314_norm_unit_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PUnit.norm_unit_eq
    # normUnit x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normUnit", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PUnit_norm_unit_eq"))
        except Exception:
            pass
    return results


def _r0315_snd_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GradedMonoid.snd_smul
    # (a • x).snd = a • x.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_x_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a", (OVar("_unknown"), OVar("x_snd"),))
            results.append((rhs, "Mathlib: GradedMonoid_snd_smul"))
    except Exception:
        pass
    return results


def _r0316_smul_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GradedMonoid.smul_mk
    # c • mk i a = mk i (c • a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c", 4)
    if args is not None:
        try:
            rhs = OOp("pair", (args[2], OOp("c", (args[0], args[3],)),))
            results.append((rhs, "Mathlib: GradedMonoid_smul_mk"))
        except Exception:
            pass
    return results


def _r0317_snd_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: snd_one
    # (1 : GradedMonoid A).snd = GOne.one
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_GradedMonoid_A_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("GOne_one")
            results.append((rhs, "Mathlib: snd_one"))
    except Exception:
        pass
    return results


def _r0318_snd_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: snd_mul
    # (x * y).snd = GMul.mul x.snd y.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_star_y_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("x_snd"), OVar("y_snd"),))
            results.append((rhs, "Mathlib: snd_mul"))
    except Exception:
        pass
    return results


def _r0319_mk_mul_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mk_mul_mk
    # mk i a * mk j b = mk (i + j) (GMul.mul a b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("pair", (OOp("+", (OVar("i"), OVar("j"))), OOp("*", (OVar("a"), OVar("b"),)),))
            results.append((rhs, "Mathlib: mk_mul_mk"))
        except Exception:
            pass
    return results


def _r0320_gnpowRec_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GMonoid.gnpowRec_succ
    # (GradedMonoid.mk _ <| gnpowRec n.succ a.snd) = ⟨_, gnpowRec n a.snd⟩ * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "GradedMonoid_mk", 5)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("gnpowRec_n_a_snd"), OVar("a")))
            results.append((rhs, "Mathlib: GMonoid_gnpowRec_succ"))
        except Exception:
            pass
    return results


def _r0321_snd_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: snd_pow
    # (x ^ n).snd = GMonoid.gnpow n x.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pow_n_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("GMonoid_gnpow", (OVar("n"), OVar("x_snd"),))
            results.append((rhs, "Mathlib: snd_pow"))
    except Exception:
        pass
    return results


def _r0322_mk_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mk_pow
    # mk i a ^ n = mk (n • i) (GMonoid.gnpow _ a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("pair", (OOp("n", (OVar("_unknown"), OVar("i"),)), OOp("GMonoid_gnpow", (OVar("_unknown"), OVar("a"),)),))
            results.append((rhs, "Mathlib: mk_pow"))
        except Exception:
            pass
    return results


def _r0323_smul_eq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GradeZero.smul_eq_mul
    # a • b = a * b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), args[1]))
            results.append((rhs, "Mathlib: GradeZero_smul_eq_mul"))
        except Exception:
            pass
    return results


def _r0324_smul_eq_iff_eq_inv_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_eq_iff_eq_inv_smul
    # g • x = y ↔ x = g⁻¹ • y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("y"), args[1])), OOp("ginv", (args[0], OVar("y"),))))
            results.append((rhs, "Mathlib: smul_eq_iff_eq_inv_smul"))
        except Exception:
            pass
    return results


def _r0325_smul_invOf_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_invOf_smul
    # c • (⅟c • x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: smul_invOf_smul"))
        except Exception:
            pass
    return results


def _r0326_invOf_smul_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: invOf_smul_eq_iff
    # ⅟c • x = y ↔ x = c • y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("y"), args[1])), OOp("c", (args[0], OVar("y"),))))
            results.append((rhs, "Mathlib: invOf_smul_eq_iff"))
        except Exception:
            pass
    return results


def _r0327_op_smul_eq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: op_smul_eq_mul
    # MulOpposite.op a • b = b * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MulOpposite_op", 3)
    if args is not None:
        try:
            rhs = OOp("*", (args[2], args[0]))
            results.append((rhs, "Mathlib: op_smul_eq_mul"))
        except Exception:
            pass
    return results


def _r0328_smul_inv_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_inv_smul
    # g • g⁻¹ • a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: smul_inv_smul"))
        except Exception:
            pass
    return results


def _r0329_inv_smul_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_smul_eq_iff
    # g⁻¹ • a = b ↔ a = g • b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ginv", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("b"), args[1])), OOp("g", (args[0], OVar("b"),))))
            results.append((rhs, "Mathlib: inv_smul_eq_iff"))
        except Exception:
            pass
    return results


def _r0330_mul_smul_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_smul_one
    # y * x • (1 : N) = x • y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("_unknown"), args[0],))
            results.append((rhs, "Mathlib: mul_smul_one"))
        except Exception:
            pass
    return results


def _r0331_restr_refl_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: restr_refl_symm
    # ((Equidecomp.refl X G).restr A).symm = (Equidecomp.refl X G).restr A
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Equidecomp_refl_X_G_restr_A_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Equidecomp_refl_X_G_restr", (OVar("A"),))
            results.append((rhs, "Mathlib: restr_refl_symm"))
    except Exception:
        pass
    return results


def _r0332_smul_finset_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_finset_eq_univ
    # a • s = univ ↔ s = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("univ"), args[1])), OVar("univ")))
            results.append((rhs, "Mathlib: smul_finset_eq_univ"))
        except Exception:
            pass
    return results


def _r0333_smul_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_univ
    # s • (univ : Finset β) = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: smul_univ"))
        except Exception:
            pass
    return results


def _r0334_inv_op_smul_finset_distrib(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_op_smul_finset_distrib
    # (op a • s)⁻¹ = a⁻¹ • s⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("op_a_s_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ainv", (OVar("_unknown"), OVar("sinv"),))
            results.append((rhs, "Mathlib: inv_op_smul_finset_distrib"))
    except Exception:
        pass
    return results


def _r0335_preimage_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: preimage_smul
    # (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_x_a_x", 2)
    if args is not None:
        try:
            rhs = OOp("ainv", (OVar("_unknown"), args[1],))
            results.append((rhs, "Mathlib: preimage_smul"))
        except Exception:
            pass
    return results


def _r0336_smul_set_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_set_eq_univ
    # a • s = univ ↔ s = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("univ"), args[1])), OVar("univ")))
            results.append((rhs, "Mathlib: smul_set_eq_univ"))
        except Exception:
            pass
    return results


def _r0337_smul_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_univ
    # s • (univ : Set β) = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: smul_univ"))
        except Exception:
            pass
    return results


def _r0338_iUnion_smul_eq_setOf_exists(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: iUnion_smul_eq_setOf_exists
    # ⋃ g : α, g • s = { a | ∃ g : α, g • a ∈ s }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 6)
    if args is not None:
        try:
            rhs = OVar("a_pipe_exists_g_colon_a_g_a_in_s")
            results.append((rhs, "Mathlib: iUnion_smul_eq_setOf_exists"))
        except Exception:
            pass
    return results


def _r0339_inv_op_smul_set_distrib(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_op_smul_set_distrib
    # (op a • s)⁻¹ = a⁻¹ • s⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("op_a_s_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ainv", (OVar("_unknown"), OVar("sinv"),))
            results.append((rhs, "Mathlib: inv_op_smul_set_distrib"))
    except Exception:
        pass
    return results


def _r0340_ofMul_vadd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofMul_vadd
    # ofMul a +ᵥ b = a • b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofMul", 3)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), args[2],))
            results.append((rhs, "Mathlib: ofMul_vadd"))
        except Exception:
            pass
    return results


def _r0341_toAdd_vadd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toAdd_vadd
    # (a.toAdd : α) +ᵥ b = a • b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_toAdd_colon_a", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), args[1],))
            results.append((rhs, "Mathlib: toAdd_vadd"))
        except Exception:
            pass
    return results


def _r0342_ofAdd_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofAdd_smul
    # ofAdd a • b = a +ᵥ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofAdd", 3)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("plus"), args[2],))
            results.append((rhs, "Mathlib: ofAdd_smul"))
        except Exception:
            pass
    return results


def _r0343_smul_isUnit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Units.smul_isUnit
    # hm.unit • a = m • a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hm_unit", 2)
    if args is not None:
        try:
            rhs = OOp("m", (args[0], args[1],))
            results.append((rhs, "Mathlib: Units_smul_isUnit"))
        except Exception:
            pass
    return results


def _r0344_inv_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsUnit.inv_smul
    # h.unit⁻¹ • a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_unitinv", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: IsUnit_inv_smul"))
        except Exception:
            pass
    return results


def _r0345_coe_inv_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Units.coe_inv_smul
    # (m • u)⁻¹.val = m • u⁻¹.val
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_u_inv_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("m", (OVar("_unknown"), OVar("uinv_val"),))
            results.append((rhs, "Mathlib: Units_coe_inv_smul"))
    except Exception:
        pass
    return results


def _r0346_coe_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_add
    # ⇑(ψ + χ) = ψ * χ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("psi_plus_chi")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("psi"), OVar("chi")))
            results.append((rhs, "Mathlib: coe_add"))
    except Exception:
        pass
    return results


def _r0347_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_pow
    # ⇑(ψ ^ n) = ψ ^ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("psi_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("psi"), OVar("n")))
            results.append((rhs, "Mathlib: coe_pow"))
    except Exception:
        pass
    return results


def _r0348_coe_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_nsmul
    # ⇑(n • ψ) = ψ ^ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_psi")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("psi"), OVar("n")))
            results.append((rhs, "Mathlib: coe_nsmul"))
    except Exception:
        pass
    return results


def _r0349_coe_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_prod
    # ∏ i ∈ s, ψ i = ∏ i ∈ s, ⇑(ψ i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("psi_i"),))))
            results.append((rhs, "Mathlib: coe_prod"))
        except Exception:
            pass
    return results


def _r0350_coe_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_sum
    # ∑ i ∈ s, ψ i = ∏ i ∈ s, ⇑(ψ i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("psi_i"),))))
            results.append((rhs, "Mathlib: coe_sum"))
        except Exception:
            pass
    return results


def _r0351_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_apply
    # (ψ * φ) a = ψ a * φ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi_star_phi", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("psi", (args[0],)), OOp("phi", (args[0],))))
            results.append((rhs, "Mathlib: mul_apply"))
        except Exception:
            pass
    return results


def _r0352_add_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: add_apply
    # (ψ + φ) a = ψ a * φ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi_plus_phi", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("psi", (args[0],)), OOp("phi", (args[0],))))
            results.append((rhs, "Mathlib: add_apply"))
        except Exception:
            pass
    return results


def _r0353_pow_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_apply
    # (ψ ^ n) a = (ψ a) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi_pow_n", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("psi", (args[0],)), OVar("n")))
            results.append((rhs, "Mathlib: pow_apply"))
        except Exception:
            pass
    return results


def _r0354_nsmul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: nsmul_apply
    # (n • ψ) a = (ψ a) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_psi", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("psi", (args[0],)), OVar("n")))
            results.append((rhs, "Mathlib: nsmul_apply"))
        except Exception:
            pass
    return results


def _r0355_prod_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: prod_apply
    # (∏ i ∈ s, ψ i) a = ∏ i ∈ s, ψ i a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_in_s_psi_i", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("psi"), OVar("i"), args[0],))))
            results.append((rhs, "Mathlib: prod_apply"))
        except Exception:
            pass
    return results


def _r0356_toMonoidHomEquiv_symm_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toMonoidHomEquiv_symm_mul
    # toMonoidHomEquiv.symm (ψ * φ) = toMonoidHomEquiv.symm ψ + toMonoidHomEquiv.symm φ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toMonoidHomEquiv_symm", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("toMonoidHomEquiv_symm", (OVar("psi"),)), OOp("toMonoidHomEquiv_symm", (OVar("phi"),))))
            results.append((rhs, "Mathlib: toMonoidHomEquiv_symm_mul"))
        except Exception:
            pass
    return results


def _r0357_neg_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: neg_apply
    # (-ψ) a = ψ (-a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_psi", 1)
    if args is not None:
        try:
            rhs = OOp("psi", (OVar("minus_a"),))
            results.append((rhs, "Mathlib: neg_apply"))
        except Exception:
            pass
    return results


def _r0358_div_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_apply
    # (ψ / χ) a = ψ a * χ (-a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi_slash_chi", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("psi", (args[0],)), OOp("chi", (OVar("minus_a"),))))
            results.append((rhs, "Mathlib: div_apply"))
        except Exception:
            pass
    return results


def _r0359_sub_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: sub_apply
    # (ψ - χ) a = ψ a * χ (-a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi_minus_chi", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("psi", (args[0],)), OOp("chi", (OVar("minus_a"),))))
            results.append((rhs, "Mathlib: sub_apply"))
        except Exception:
            pass
    return results


def _r0360_zpow_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zpow_apply
    # (ψ ^ n) a = ψ a ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi_pow_n", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("psi", (args[0],)), OVar("n")))
            results.append((rhs, "Mathlib: zpow_apply"))
        except Exception:
            pass
    return results


def _r0361_map_sub_eq_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_sub_eq_div
    # ψ (a - b) = ψ a / ψ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("psi", (OVar("a"),)), OOp("psi", (OVar("b"),))))
            results.append((rhs, "Mathlib: map_sub_eq_div"))
        except Exception:
            pass
    return results


def _r0362_inv_mulShift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_mulShift
    # ψ⁻¹ = mulShift ψ (-1)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("psiinv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("mulShift", (OVar("psi"), OVar("minus_1"),))
            results.append((rhs, "Mathlib: inv_mulShift"))
    except Exception:
        pass
    return results


def _r0363_mulShift_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mulShift_one
    # mulShift ψ 1 = ψ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulShift", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: mulShift_one"))
        except Exception:
            pass
    return results


def _r0364_mulShift_unit_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mulShift_unit_eq_one_iff
    # ψ.mulShift u = 1 ↔ ψ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi_mulShift", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("psi"))), OLit(1)))
            results.append((rhs, "Mathlib: mulShift_unit_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0365_ite_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ite_pow
    # (if p then a else b) ^ c = if p then a ^ c else b ^ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("if", (OVar("p"), OVar("then"), OVar("a"),)), OOp("**", (OOp("c", (OVar("else"), OVar("b"),)), args[1]))))
            results.append((rhs, "Mathlib: ite_pow"))
        except Exception:
            pass
    return results


def _r0366_inv_eq_iff_eq_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_eq_iff_eq_inv
    # a⁻¹ = b ↔ a = b⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ainv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("b"), OVar("a"))), OVar("binv")))
            results.append((rhs, "Mathlib: inv_eq_iff_eq_inv"))
    except Exception:
        pass
    return results


def _r0367_one_div_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: one_div_one
    # (1 : G) / 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: one_div_one"))
        except Exception:
            pass
    return results


def _r0368_one_div_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: one_div_div
    # 1 / (a / b) = b / a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("b"), OVar("a")))
            results.append((rhs, "Mathlib: one_div_div"))
        except Exception:
            pass
    return results


def _r0369_one_div_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: one_div_pow
    # (1 / a) ^ n = 1 / a ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OLit(1), OOp("**", (OVar("a"), args[1]))))
            results.append((rhs, "Mathlib: one_div_pow"))
        except Exception:
            pass
    return results


def _r0370_one_eq_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: one_eq_inv
    # 1 = a⁻¹ ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    if _is_lit(term, 1):
        try:
            rhs = OOp("==", (OOp("iff", (OVar("ainv"), OVar("a"))), OLit(1)))
            results.append((rhs, "Mathlib: one_eq_inv"))
        except Exception:
            pass
    return results


def _r0371_div_mul_eq_div_div_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_mul_eq_div_div_swap
    # a / (b * c) = a / c / b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (args[0], OOp("//", (OVar("c"), OVar("b")))))
            results.append((rhs, "Mathlib: div_mul_eq_div_div_swap"))
        except Exception:
            pass
    return results


def _r0372_mul_div_mul_right_eq_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_div_mul_right_eq_div
    # a * c / (b * c) = a / b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("//", (args[0], OVar("b")))
            results.append((rhs, "Mathlib: mul_div_mul_right_eq_div"))
        except Exception:
            pass
    return results


def _r0373_div_left_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_left_inj
    # b / a = c / a ↔ b = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("//", (OVar("c"), args[1])), args[0])), OVar("c")))
            results.append((rhs, "Mathlib: div_left_inj"))
        except Exception:
            pass
    return results


def _r0374_mul_mul_inv_mul_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_mul_inv_mul_cancel
    # a * b * (b⁻¹ * c) = a * c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (args[0], OVar("c")))
            results.append((rhs, "Mathlib: mul_mul_inv_mul_cancel"))
        except Exception:
            pass
    return results


def _r0375_mul_inv_mul_mul_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_inv_mul_mul_cancel
    # a * b⁻¹ * (b * c) = a * c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (args[0], OVar("c")))
            results.append((rhs, "Mathlib: mul_inv_mul_mul_cancel"))
        except Exception:
            pass
    return results


def _r0376_div_div_div_cancel_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_div_div_cancel_right
    # a / c / (b / c) = a / b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (args[0], OVar("b")))
            results.append((rhs, "Mathlib: div_div_div_cancel_right"))
        except Exception:
            pass
    return results


def _r0377_div_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_eq_one
    # a / b = 1 ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), args[1]))
            results.append((rhs, "Mathlib: div_eq_one"))
        except Exception:
            pass
    return results


def _r0378_pow_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_sub
    # a ^ (m - n) = a ^ m * (a ^ n)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (args[0], OVar("m"))), OVar("a_pow_n_inv")))
            results.append((rhs, "Mathlib: pow_sub"))
        except Exception:
            pass
    return results


def _r0379_div_div_cancel_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_div_cancel_left
    # a / b / a = b⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OVar("binv")
            results.append((rhs, "Mathlib: div_div_cancel_left"))
        except Exception:
            pass
    return results


def _r0380_mul_div_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_div_cancel
    # a * (b / a) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: mul_div_cancel"))
        except Exception:
            pass
    return results


def _r0381_div_mul_cancel_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_mul_cancel_left
    # a / (a * b) = b⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OVar("binv")
            results.append((rhs, "Mathlib: div_mul_cancel_left"))
        except Exception:
            pass
    return results


def _r0382_div_mul_mul_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_mul_mul_cancel
    # a / c * (b * c) = a * b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), OVar("b")))
            results.append((rhs, "Mathlib: div_mul_mul_cancel"))
        except Exception:
            pass
    return results


def _r0383_mul_div_div_cancel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_div_div_cancel
    # a * b / (a / c) = b * c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("b"), OVar("c")))
            results.append((rhs, "Mathlib: mul_div_div_cancel"))
        except Exception:
            pass
    return results


def _r0384_div_div_div_cancel_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_div_div_cancel_left
    # c / a / (c / b) = b / a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("b"), OVar("a")))
            results.append((rhs, "Mathlib: div_div_div_cancel_left"))
        except Exception:
            pass
    return results


def _r0385_div_eq_div_iff_mul_eq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: div_eq_div_iff_mul_eq_mul
    # a / b = c / d ↔ a * d = c * b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "//", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("//", (OVar("c"), OVar("d"))), OOp("*", (args[0], OVar("d"))))), OOp("*", (OVar("c"), args[1]))))
            results.append((rhs, "Mathlib: div_eq_div_iff_mul_eq_mul"))
        except Exception:
            pass
    return results


def _r0386_centralizer_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: centralizer_eq_univ
    # centralizer S = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "centralizer", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: centralizer_eq_univ"))
        except Exception:
            pass
    return results


def _r0387_div_mul_div_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Commute.div_mul_div_comm
    # a / b * (c / d) = a * c / (b * d)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), OOp("//", (OVar("c"), OOp("*", (OVar("b"), OVar("d")))))))
            results.append((rhs, "Mathlib: Commute_div_mul_div_comm"))
        except Exception:
            pass
    return results


def _r0388_pow_ofPowEqOne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Units.pow_ofPowEqOne
    # Units.ofPowEqOne _ n ha hn ^ n = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Units_pow_ofPowEqOne"))
        except Exception:
            pass
    return results


def _r0389_conj_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: conj_pow
    # (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("a"), OOp("*", (OOp("**", (OVar("b"), args[1])), OVar("ainv")))))
            results.append((rhs, "Mathlib: conj_pow"))
        except Exception:
            pass
    return results


def _r0390_mul_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_one
    # ∀ a : M, a * 1 = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: mul_one"))
        except Exception:
            pass
    return results


def _r0391_left_inv_eq_right_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: left_inv_eq_right_inv
    # b = c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("c")
            results.append((rhs, "Mathlib: left_inv_eq_right_inv"))
    except Exception:
        pass
    return results


def _r0392_pow_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_succ
    # a ^ (n + 1) = a ^ n * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (args[0], OVar("n"))), args[0]))
            results.append((rhs, "Mathlib: pow_succ"))
        except Exception:
            pass
    return results


def _r0393_pow_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_add
    # ∀ n, a ^ (m + n) = a ^ m * a ^ n   | 0 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (args[0], OVar("m"))), OOp("**", (args[0], OOp("n", (OVar("pipe"), OLit(0), OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: pow_add"))
        except Exception:
            pass
    return results


def _r0394_zpow_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zpow_zero
    # a ^ (0 : ℤ) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: zpow_zero"))
        except Exception:
            pass
    return results


def _r0395_zpow_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zpow_natCast
    # ∀ n : ℕ, a ^ (n : ℤ) = a ^ n   | 0 => (zpow_zero _).trans (pow_zero _).symm   | n + 1 => calc     a ^ (↑(n + 1) : ℤ) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("+", (OOp("**", (args[0], OOp("n", (OVar("pipe"), OLit(0), OVar("eq_gt"), OVar("zpow_zero_trans"), OVar("pow_zero_symm"), OVar("pipe"), OVar("n"),)))), OOp("**", (OOp("_1", (OVar("eq_gt"), OVar("calc"), args[0],)), OOp("n_plus_1", (OVar("colon"), OVar("_unknown"),)))))), OOp("*", (OOp("**", (args[0], OOp("n", (OVar("colon"), OVar("_unknown"),)))), args[0]))))
            results.append((rhs, "Mathlib: zpow_natCast"))
        except Exception:
            pass
    return results


def _r0396_zpow_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zpow_one
    # a ^ (1 : ℤ) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: zpow_one"))
        except Exception:
            pass
    return results


def _r0397_zpow_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zpow_two
    # a ^ (2 : ℤ) = a * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (args[0], args[0]))
            results.append((rhs, "Mathlib: zpow_two"))
        except Exception:
            pass
    return results


def _r0398_inv_eq_of_mul_eq_one_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_eq_of_mul_eq_one_right
    # a * b = 1 → a⁻¹ = b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ainv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b")
            results.append((rhs, "Mathlib: inv_eq_of_mul_eq_one_right"))
    except Exception:
        pass
    return results


def _r0399_inv_mul_cancel_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inv_mul_cancel_left
    # a⁻¹ * (a * b) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: inv_mul_cancel_left"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_other rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "**", "+", "-", "//", "A", "AlgHom_id", "Associates_mk", "Coalgebra_counit", "ConcreteCategory_hom", "DFunLike_coe", "DirectSum_id", "DirectSum_lid_R_M_i_symm", "DirectSum_of", "FGModuleCatDual", "GradedMonoid_mk", "Hom_hom", "Hom_toBialgHom", "Hom_toCoalgHom", "I_image", "M", "MonCat_of", "MonoidHom_id", "MulHom_id", "MulOpposite_op", "N_unitHomEquiv", "P_toPoly_coeff", "Quot_mk", "R", "RingHom_id", "Units_ofPowEqOne", "_0", "_1", "_1_A_colon_A_A", "_1_M_colon_M_M", "_1_R_colon_R_R", "_1_X_colon_X_X", "_1_colon_X_Y_hom", "_2", "_unknown", "a", "a_in_s_g_a", "a_toAdd_colon_a", "alternatingProd", "at_casesOn", "at_ofList", "at_recOn", "at_toFreeSemigroup", "at_toList", "b",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_other axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_other rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_vadd_vsub_vadd_cancel_left(term, ctx))
    results.extend(_r0001_vadd_vsub_vadd_comm(term, ctx))
    results.extend(_r0002_vsub_def(term, ctx))
    results.extend(_r0003_expect_neg_index(term, ctx))
    results.extend(_r0004_map_expect(term, ctx))
    results.extend(_r0005_expect_const(term, ctx))
    results.extend(_r0006_smul_expect(term, ctx))
    results.extend(_r0007_expect_mul(term, ctx))
    results.extend(_r0008_partialProd_succ(term, ctx))
    results.extend(_r0009_finprod_eq_single(term, ctx))
    results.extend(_r0010_finprod_eq_dif(term, ctx))
    results.extend(_r0011_finprod_mem_def(term, ctx))
    results.extend(_r0012_finprod_cond_eq_right(term, ctx))
    results.extend(_r0013_prod_subtype_eq_prod_filter(term, ctx))
    results.extend(_r0014_prod_eq_pow_card(term, ctx))
    results.extend(_r0015_prod_image_of_pairwise_eq_one(term, ctx))
    results.extend(_r0016_prod_image_of_disjoint(term, ctx))
    results.extend(_r0017_prod_sdiff_div_prod_sdiff(term, ctx))
    results.extend(_r0018_unop_sum(term, ctx))
    results.extend(_r0019_unop_prod(term, ctx))
    results.extend(_r0020_prod_div_distrib(term, ctx))
    results.extend(_r0021_prod_zpow(term, ctx))
    results.extend(_r0022_toMul_list_sum(term, ctx))
    results.extend(_r0023_toAdd_list_sum(term, ctx))
    results.extend(_r0024_ofMul_prod(term, ctx))
    results.extend(_r0025_toMul_sum(term, ctx))
    results.extend(_r0026_toAdd_prod(term, ctx))
    results.extend(_r0027_prod_erase(term, ctx))
    results.extend(_r0028_prod_map_erase(term, ctx))
    results.extend(_r0029_prod_drop_succ(term, ctx))
    results.extend(_r0030_alternatingProd_singleton(term, ctx))
    results.extend(_r0031_prod_map_div(term, ctx))
    results.extend(_r0032_prod_map_zpow(term, ctx))
    results.extend(_r0033_sum_nat_mod(term, ctx))
    results.extend(_r0034_sum_eq_top(term, ctx))
    results.extend(_r0035_sum_eq_bot_iff(term, ctx))
    results.extend(_r0036_id_apply(term, ctx))
    results.extend(_r0037_ofHom_hom(term, ctx))
    results.extend(_r0038_ofHom_id(term, ctx))
    results.extend(_r0039_ofHom_comp(term, ctx))
    results.extend(_r0040_toBialgHom_id(term, ctx))
    results.extend(_r0041_toBialgIso_symm(term, ctx))
    results.extend(_r0042_toBialgIso_trans(term, ctx))
    results.extend(_r0043_of_counit(term, ctx))
    results.extend(_r0044_toCoalgHom_id(term, ctx))
    results.extend(_r0045_toCoalgIso_symm(term, ctx))
    results.extend(_r0046_toCoalgIso_trans(term, ctx))
    results.extend(_r0047_id_apply(term, ctx))
    results.extend(_r0048_comp_apply(term, ctx))
    results.extend(_r0049_ofHom_hom(term, ctx))
    results.extend(_r0050_ofHom_id(term, ctx))
    results.extend(_r0051_ofHom_comp(term, ctx))
    results.extend(_r0052_ofHom_apply(term, ctx))
    results.extend(_r0053_forget_2_commRingCat_map(term, ctx))
    results.extend(_r0054_forget_2_algCat_obj(term, ctx))
    results.extend(_r0055_forget_2_algCat_map(term, ctx))
    results.extend(_r0056_binaryCofan_inr(term, ctx))
    results.extend(_r0057_binaryCofan_pt(term, ctx))
    results.extend(_r0058_coe_tensorObj(term, ctx))
    results.extend(_r0059_tensorHom_hom(term, ctx))
    results.extend(_r0060_whiskerRight_hom(term, ctx))
    results.extend(_r0061_whiskerLeft_hom(term, ctx))
    results.extend(_r0062_associator_hom_hom(term, ctx))
    results.extend(_r0063_associator_inv_hom(term, ctx))
    results.extend(_r0064_braiding_inv_hom(term, ctx))
    results.extend(_r0065_snd_unop_hom(term, ctx))
    results.extend(_r0066_toUnit_unop_hom(term, ctx))
    results.extend(_r0067_lift_unop_hom(term, ctx))
    results.extend(_r0068_hom_comp(term, ctx))
    results.extend(_r0069_id_apply(term, ctx))
    results.extend(_r0070_comp_apply(term, ctx))
    results.extend(_r0071_ofHom_hom(term, ctx))
    results.extend(_r0072_ofHom_id(term, ctx))
    results.extend(_r0073_ofHom_comp(term, ctx))
    results.extend(_r0074_ofHom_apply(term, ctx))
    results.extend(_r0075_forget_2_commAlgCat_map(term, ctx))
    results.extend(_r0076_mul_op_of_unop_hom(term, ctx))
    results.extend(_r0077_hom_hom_id(term, ctx))
    results.extend(_r0078_tensorObj_obj(term, ctx))
    results.extend(_r0079_FGModuleCatDual_coe(term, ctx))
    results.extend(_r0080_forget_map(term, ctx))
    results.extend(_r0081_ext(term, ctx))
    results.extend(_r0082_id_apply(term, ctx))
    results.extend(_r0083_ofHom_hom(term, ctx))
    results.extend(_r0084_ofHom_id(term, ctx))
    results.extend(_r0085_ofHom_comp(term, ctx))
    results.extend(_r0086_forget_2_map(term, ctx))
    results.extend(_r0087_forget_map(term, ctx))
    results.extend(_r0088_id_apply(term, ctx))
    results.extend(_r0089_ofHom_hom(term, ctx))
    results.extend(_r0090_ofHom_id(term, ctx))
    results.extend(_r0091_ofHom_comp(term, ctx))
    results.extend(_r0092_forget_2_map(term, ctx))
    results.extend(_r0093_hom_comp(term, ctx))
    results.extend(_r0094_of_counit(term, ctx))
    results.extend(_r0095_toBialgHom_id(term, ctx))
    results.extend(_r0096_toHopfAlgIso_symm(term, ctx))
    results.extend(_r0097_toHopfAlgIso_trans(term, ctx))
    results.extend(_r0098_eIso_inv_freeMk(term, ctx))
    results.extend(_r0099_free_eta_freeMk(term, ctx))
    results.extend(_r0100_free_mu_freeMk_tmul_freeMk(term, ctx))
    results.extend(_r0101_comp_app(term, ctx))
    results.extend(_r0102_presheaf_map_apply_coe(term, ctx))
    results.extend(_r0103_toPresheaf_map_app_apply(term, ctx))
    results.extend(_r0104_add_app(term, ctx))
    results.extend(_r0105_sub_app(term, ctx))
    results.extend(_r0106_sectionsMap_id(term, ctx))
    results.extend(_r0107_id_apply(term, ctx))
    results.extend(_r0108_ofHom_hom(term, ctx))
    results.extend(_r0109_ofHom_id(term, ctx))
    results.extend(_r0110_ofHom_comp(term, ctx))
    results.extend(_r0111_hom_2_ofHom_2(term, ctx))
    results.extend(_r0112_ofHom_2_hom_2(term, ctx))
    results.extend(_r0113_comp_val(term, ctx))
    results.extend(_r0114_sectionsMap_id(term, ctx))
    results.extend(_r0115_unitHomEquiv_comp_apply(term, ctx))
    results.extend(_r0116_pushforwardCongr_hom_app_val_app(term, ctx))
    results.extend(_r0117_pushforwardCongr_inv_app_val_app(term, ctx))
    results.extend(_r0118_pushforwardNatTrans_id(term, ctx))
    results.extend(_r0119_pushforwardNatTrans_comp(term, ctx))
    results.extend(_r0120_forget_map(term, ctx))
    results.extend(_r0121_ext(term, ctx))
    results.extend(_r0122_id_apply(term, ctx))
    results.extend(_r0123_ofHom_hom(term, ctx))
    results.extend(_r0124_ofHom_id(term, ctx))
    results.extend(_r0125_ofHom_comp(term, ctx))
    results.extend(_r0126_oneHom_apply(term, ctx))
    results.extend(_r0127_mul_of(term, ctx))
    results.extend(_r0128_forget_map(term, ctx))
    results.extend(_r0129_id_apply(term, ctx))
    results.extend(_r0130_ofHom_hom(term, ctx))
    results.extend(_r0131_ofHom_id(term, ctx))
    results.extend(_r0132_ofHom_comp(term, ctx))
    results.extend(_r0133_hom_forget_2_map(term, ctx))
    results.extend(_r0134_forget_2_map_ofHom(term, ctx))
    results.extend(_r0135_quot_mul(term, ctx))
    results.extend(_r0136_id_apply(term, ctx))
    results.extend(_r0137_ofHom_hom(term, ctx))
    results.extend(_r0138_ofHom_id(term, ctx))
    results.extend(_r0139_ofHom_comp(term, ctx))
    results.extend(_r0140_forget_2_addCommMonCat_map(term, ctx))
    results.extend(_r0141_id_apply(term, ctx))
    results.extend(_r0142_ofHom_hom(term, ctx))
    results.extend(_r0143_ofHom_id(term, ctx))
    results.extend(_r0144_ofHom_comp(term, ctx))
    results.extend(_r0145_coproductCocone_inr(term, ctx))
    results.extend(_r0146_forget_map(term, ctx))
    results.extend(_r0147_ext(term, ctx))
    results.extend(_r0148_id_apply(term, ctx))
    results.extend(_r0149_ofHom_hom(term, ctx))
    results.extend(_r0150_ofHom_id(term, ctx))
    results.extend(_r0151_ofHom_comp(term, ctx))
    results.extend(_r0152_forget_map(term, ctx))
    results.extend(_r0153_ext(term, ctx))
    results.extend(_r0154_id_apply(term, ctx))
    results.extend(_r0155_ofHom_hom(term, ctx))
    results.extend(_r0156_ofHom_id(term, ctx))
    results.extend(_r0157_ofHom_comp(term, ctx))
    results.extend(_r0158_ringChar_subsingleton(term, ctx))
    results.extend(_r0159_iterateFrobenius_zero_apply(term, ctx))
    results.extend(_r0160_iterateFrobenius_add_apply(term, ctx))
    results.extend(_r0161_two_nsmul(term, ctx))
    results.extend(_r0162_add_cancel_left(term, ctx))
    results.extend(_r0163_add_cancel_right(term, ctx))
    results.extend(_r0164_add_eq_iff_eq_add(term, ctx))
    results.extend(_r0165_add_eq_zero(term, ctx))
    results.extend(_r0166_ofNat_eq_ofNat(term, ctx))
    results.extend(_r0167_of_h_eq_intFractPair_seq1_fst_b(term, ctx))
    results.extend(_r0168_first_contAux_eq_h_one(term, ctx))
    results.extend(_r0169_zeroth_cont_eq_h_one(term, ctx))
    results.extend(_r0170_zeroth_num_eq_h(term, ctx))
    results.extend(_r0171_zeroth_den_eq_one(term, ctx))
    results.extend(_r0172_zeroth_conv_eq_h(term, ctx))
    results.extend(_r0173_second_contAux_eq(term, ctx))
    results.extend(_r0174_coeff_eq_a(term, ctx))
    results.extend(_r0175_coeff_eq_b(term, ctx))
    results.extend(_r0176_coeff_eq_c(term, ctx))
    results.extend(_r0177_coeff_eq_d(term, ctx))
    results.extend(_r0178_a_of_eq(term, ctx))
    results.extend(_r0179_natDegree_of_a_ne_zero(term, ctx))
    results.extend(_r0180_sum_apply(term, ctx))
    results.extend(_r0181_of_eq_of_ne(term, ctx))
    results.extend(_r0182_support_of(term, ctx))
    results.extend(_r0183_unique(term, ctx))
    results.extend(_r0184_id_apply(term, ctx))
    results.extend(_r0185_map_apply(term, ctx))
    results.extend(_r0186_map_id(term, ctx))
    results.extend(_r0187_map_comp(term, ctx))
    results.extend(_r0188_decompose_symm_of(term, ctx))
    results.extend(_r0189_decompose_coe(term, ctx))
    results.extend(_r0190_decompose_of_mem(term, ctx))
    results.extend(_r0191_decompose_zero(term, ctx))
    results.extend(_r0192_decompose_symm_zero(term, ctx))
    results.extend(_r0193_decompose_add(term, ctx))
    results.extend(_r0194_decompose_symm_add(term, ctx))
    results.extend(_r0195_decompose_symm_neg(term, ctx))
    results.extend(_r0196_decompose_sub(term, ctx))
    results.extend(_r0197_decompose_symm_sub(term, ctx))
    results.extend(_r0198_decomposeLinearEquiv_symm_comp_lof(term, ctx))
    results.extend(_r0199_decomposeLinearEquiv_symm_lof(term, ctx))
    results.extend(_r0200_decomposeLinearEquiv_apply_coe(term, ctx))
    results.extend(_r0201_lid_symm_apply(term, ctx))
    results.extend(_r0202_lof_self(term, ctx))
    results.extend(_r0203_lmap_of(term, ctx))
    results.extend(_r0204_lmap_lof(term, ctx))
    results.extend(_r0205_lmap_id(term, ctx))
    results.extend(_r0206_lmap_comp(term, ctx))
    results.extend(_r0207_of_zero_mul(term, ctx))
    results.extend(_r0208_of_zero_ofNat(term, ctx))
    results.extend(_r0209_snd_eps(term, ctx))
    results.extend(_r0210_eps_mul_eps(term, ctx))
    results.extend(_r0211_eps_pow_two(term, ctx))
    results.extend(_r0212_inv_eps(term, ctx))
    results.extend(_r0213_inr_eq_smul_eps(term, ctx))
    results.extend(_r0214_lift_apply_inl(term, ctx))
    results.extend(_r0215_lift_comp_inlHom(term, ctx))
    results.extend(_r0216_zero_mod(term, ctx))
    results.extend(_r0217_zero_div(term, ctx))
    results.extend(_r0218_eq_div_of_mul_eq_left(term, ctx))
    results.extend(_r0219_gcd_self(term, ctx))
    results.extend(_r0220_xgcdAux_fst(term, ctx))
    results.extend(_r0221_lcm_zero_right(term, ctx))
    results.extend(_r0222_lcm_eq_zero_iff(term, ctx))
    results.extend(_r0223_lt_one(term, ctx))
    results.extend(_r0224_add_halves(term, ctx))
    results.extend(_r0225_neg_div_self(term, ctx))
    results.extend(_r0226_div_sub_div_same(term, ctx))
    results.extend(_r0227_ofDual_ratCast(term, ctx))
    results.extend(_r0228_ofLex_ratCast(term, ctx))
    results.extend(_r0229_coe_div(term, ctx))
    results.extend(_r0230_coe_zpow(term, ctx))
    results.extend(_r0231_inv_def(term, ctx))
    results.extend(_r0232_div_def(term, ctx))
    results.extend(_r0233_coe_top(term, ctx))
    results.extend(_r0234_comap_comap(term, ctx))
    results.extend(_r0235_mem_map(term, ctx))
    results.extend(_r0236_lift_comp_of(term, ctx))
    results.extend(_r0237_pure_bind(term, ctx))
    results.extend(_r0238_mul_bind(term, ctx))
    results.extend(_r0239_pure_seq(term, ctx))
    results.extend(_r0240_mul_seq(term, ctx))
    results.extend(_r0241_traverse_mul(term, ctx))
    results.extend(_r0242_lift_comp_of(term, ctx))
    results.extend(_r0243_tail_mul(term, ctx))
    results.extend(_r0244_mk_mul_mk(term, ctx))
    results.extend(_r0245_length_of(term, ctx))
    results.extend(_r0246_lift_comp_of(term, ctx))
    results.extend(_r0247_lift_of_mul(term, ctx))
    results.extend(_r0248_length_map(term, ctx))
    results.extend(_r0249_pure_bind(term, ctx))
    results.extend(_r0250_mul_bind(term, ctx))
    results.extend(_r0251_pure_seq(term, ctx))
    results.extend(_r0252_mul_seq(term, ctx))
    results.extend(_r0253_toFreeSemigroup_comp_of(term, ctx))
    results.extend(_r0254_toFreeSemigroup_comp_map(term, ctx))
    results.extend(_r0255_support_of(term, ctx))
    results.extend(_r0256_support_neg(term, ctx))
    results.extend(_r0257_support_zsmul(term, ctx))
    results.extend(_r0258_ofList_symm(term, ctx))
    results.extend(_r0259_toList_ofList(term, ctx))
    results.extend(_r0260_ofList_toList(term, ctx))
    results.extend(_r0261_toList_comp_ofList(term, ctx))
    results.extend(_r0262_ofList_comp_toList(term, ctx))
    results.extend(_r0263_ofList_nil(term, ctx))
    results.extend(_r0264_toList_nil(term, ctx))
    results.extend(_r0265_toList_cons(term, ctx))
    results.extend(_r0266_toList_prod(term, ctx))
    results.extend(_r0267_ofList_flatten(term, ctx))
    results.extend(_r0268_ofList_singleton(term, ctx))
    results.extend(_r0269_toList_of_mul(term, ctx))
    results.extend(_r0270_length_eq_zero(term, ctx))
    results.extend(_r0271_length_of(term, ctx))
    results.extend(_r0272_length_eq_one(term, ctx))
    results.extend(_r0273_recOn_of_mul(term, ctx))
    results.extend(_r0274_casesOn_of_mul(term, ctx))
    results.extend(_r0275_lift_symm_apply(term, ctx))
    results.extend(_r0276_lift_apply(term, ctx))
    results.extend(_r0277_lift_restrict(term, ctx))
    results.extend(_r0278_comp_lift(term, ctx))
    results.extend(_r0279_mem_map(term, ctx))
    results.extend(_r0280_ofList_map(term, ctx))
    results.extend(_r0281_map_symm_apply_map_eq(term, ctx))
    results.extend(_r0282_map_apply_map_symm_eq(term, ctx))
    results.extend(_r0283_reverse_mul(term, ctx))
    results.extend(_r0284_length_reverse(term, ctx))
    results.extend(_r0285_freeMonoidCongr_symm_of(term, ctx))
    results.extend(_r0286_symbols_of(term, ctx))
    results.extend(_r0287_symbols_mul(term, ctx))
    results.extend(_r0288_of_comp_lift(term, ctx))
    results.extend(_r0289_lift_unique(term, ctx))
    results.extend(_r0290_lift_comp_of(term, ctx))
    results.extend(_r0291_hom_ext(term, ctx))
    results.extend(_r0292_normalize_eq_normalize(term, ctx))
    results.extend(_r0293_out_one(term, ctx))
    results.extend(_r0294_out_mul(term, ctx))
    results.extend(_r0295_normalize_out(term, ctx))
    results.extend(_r0296_mk_out(term, ctx))
    results.extend(_r0297_out_zero(term, ctx))
    results.extend(_r0298_gcd_mul_left(term, ctx))
    results.extend(_r0299_lcm_comm(term, ctx))
    results.extend(_r0300_lcm_units_coe_right(term, ctx))
    results.extend(_r0301_lcm_one_left(term, ctx))
    results.extend(_r0302_lcm_one_right(term, ctx))
    results.extend(_r0303_lcm_same(term, ctx))
    results.extend(_r0304_lcm_eq_one_iff(term, ctx))
    results.extend(_r0305_lcm_eq_left_iff(term, ctx))
    results.extend(_r0306_normalize_eq(term, ctx))
    results.extend(_r0307_normalize_gcd(term, ctx))
    results.extend(_r0308_gcd_union(term, ctx))
    results.extend(_r0309_gcd_cons(term, ctx))
    results.extend(_r0310_gcd_singleton(term, ctx))
    results.extend(_r0311_gcd_add(term, ctx))
    results.extend(_r0312_gcd_eq_zero_iff(term, ctx))
    results.extend(_r0313_lcm_eq(term, ctx))
    results.extend(_r0314_norm_unit_eq(term, ctx))
    results.extend(_r0315_snd_smul(term, ctx))
    results.extend(_r0316_smul_mk(term, ctx))
    results.extend(_r0317_snd_one(term, ctx))
    results.extend(_r0318_snd_mul(term, ctx))
    results.extend(_r0319_mk_mul_mk(term, ctx))
    results.extend(_r0320_gnpowRec_succ(term, ctx))
    results.extend(_r0321_snd_pow(term, ctx))
    results.extend(_r0322_mk_pow(term, ctx))
    results.extend(_r0323_smul_eq_mul(term, ctx))
    results.extend(_r0324_smul_eq_iff_eq_inv_smul(term, ctx))
    results.extend(_r0325_smul_invOf_smul(term, ctx))
    results.extend(_r0326_invOf_smul_eq_iff(term, ctx))
    results.extend(_r0327_op_smul_eq_mul(term, ctx))
    results.extend(_r0328_smul_inv_smul(term, ctx))
    results.extend(_r0329_inv_smul_eq_iff(term, ctx))
    results.extend(_r0330_mul_smul_one(term, ctx))
    results.extend(_r0331_restr_refl_symm(term, ctx))
    results.extend(_r0332_smul_finset_eq_univ(term, ctx))
    results.extend(_r0333_smul_univ(term, ctx))
    results.extend(_r0334_inv_op_smul_finset_distrib(term, ctx))
    results.extend(_r0335_preimage_smul(term, ctx))
    results.extend(_r0336_smul_set_eq_univ(term, ctx))
    results.extend(_r0337_smul_univ(term, ctx))
    results.extend(_r0338_iUnion_smul_eq_setOf_exists(term, ctx))
    results.extend(_r0339_inv_op_smul_set_distrib(term, ctx))
    results.extend(_r0340_ofMul_vadd(term, ctx))
    results.extend(_r0341_toAdd_vadd(term, ctx))
    results.extend(_r0342_ofAdd_smul(term, ctx))
    results.extend(_r0343_smul_isUnit(term, ctx))
    results.extend(_r0344_inv_smul(term, ctx))
    results.extend(_r0345_coe_inv_smul(term, ctx))
    results.extend(_r0346_coe_add(term, ctx))
    results.extend(_r0347_coe_pow(term, ctx))
    results.extend(_r0348_coe_nsmul(term, ctx))
    results.extend(_r0349_coe_prod(term, ctx))
    results.extend(_r0350_coe_sum(term, ctx))
    results.extend(_r0351_mul_apply(term, ctx))
    results.extend(_r0352_add_apply(term, ctx))
    results.extend(_r0353_pow_apply(term, ctx))
    results.extend(_r0354_nsmul_apply(term, ctx))
    results.extend(_r0355_prod_apply(term, ctx))
    results.extend(_r0356_toMonoidHomEquiv_symm_mul(term, ctx))
    results.extend(_r0357_neg_apply(term, ctx))
    results.extend(_r0358_div_apply(term, ctx))
    results.extend(_r0359_sub_apply(term, ctx))
    results.extend(_r0360_zpow_apply(term, ctx))
    results.extend(_r0361_map_sub_eq_div(term, ctx))
    results.extend(_r0362_inv_mulShift(term, ctx))
    results.extend(_r0363_mulShift_one(term, ctx))
    results.extend(_r0364_mulShift_unit_eq_one_iff(term, ctx))
    results.extend(_r0365_ite_pow(term, ctx))
    results.extend(_r0366_inv_eq_iff_eq_inv(term, ctx))
    results.extend(_r0367_one_div_one(term, ctx))
    results.extend(_r0368_one_div_div(term, ctx))
    results.extend(_r0369_one_div_pow(term, ctx))
    results.extend(_r0370_one_eq_inv(term, ctx))
    results.extend(_r0371_div_mul_eq_div_div_swap(term, ctx))
    results.extend(_r0372_mul_div_mul_right_eq_div(term, ctx))
    results.extend(_r0373_div_left_inj(term, ctx))
    results.extend(_r0374_mul_mul_inv_mul_cancel(term, ctx))
    results.extend(_r0375_mul_inv_mul_mul_cancel(term, ctx))
    results.extend(_r0376_div_div_div_cancel_right(term, ctx))
    results.extend(_r0377_div_eq_one(term, ctx))
    results.extend(_r0378_pow_sub(term, ctx))
    results.extend(_r0379_div_div_cancel_left(term, ctx))
    results.extend(_r0380_mul_div_cancel(term, ctx))
    results.extend(_r0381_div_mul_cancel_left(term, ctx))
    results.extend(_r0382_div_mul_mul_cancel(term, ctx))
    results.extend(_r0383_mul_div_div_cancel(term, ctx))
    results.extend(_r0384_div_div_div_cancel_left(term, ctx))
    results.extend(_r0385_div_eq_div_iff_mul_eq_mul(term, ctx))
    results.extend(_r0386_centralizer_eq_univ(term, ctx))
    results.extend(_r0387_div_mul_div_comm(term, ctx))
    results.extend(_r0388_pow_ofPowEqOne(term, ctx))
    results.extend(_r0389_conj_pow(term, ctx))
    results.extend(_r0390_mul_one(term, ctx))
    results.extend(_r0391_left_inv_eq_right_inv(term, ctx))
    results.extend(_r0392_pow_succ(term, ctx))
    results.extend(_r0393_pow_add(term, ctx))
    results.extend(_r0394_zpow_zero(term, ctx))
    results.extend(_r0395_zpow_natCast(term, ctx))
    results.extend(_r0396_zpow_one(term, ctx))
    results.extend(_r0397_zpow_two(term, ctx))
    results.extend(_r0398_inv_eq_of_mul_eq_one_right(term, ctx))
    results.extend(_r0399_inv_mul_cancel_left(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_other rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("vsub_left_injective", "Function_Injective_minus_p_colon_P_to_G", "Not an equality or iff proposition"),
    ("vsub_right_injective", "Function_Injective_p_minus_colon_P_to_G", "Not an equality or iff proposition"),
    ("vadd_right_injective", "Function_Injective_plus_p_colon_G_to_P", "Not an equality or iff proposition"),
    ("AffineAddMonoid_embedding_injective", "Injective_embedding_M", "Not an equality or iff proposition"),
    ("irreducible_mem_submonoidClosure_subset", "p_in_Submonoid_closure_S_pipe_Irreducible_p_sub_S", "Not an equality or iff proposition"),
    ("irreducible_subset_of_submonoidClosure_eq_top", "p_pipe_Irreducible_p_sub_S", "Not an equality or iff proposition"),
    ("finite_irreducible", "p_colon_M_pipe_Irreducible_p_Finite", "Not an equality or iff proposition"),
    ("cardinalMk_le_mul", "hash_x_colon_A_slash_slash_IsAlgebraic_R_x_le_hash_R_X_star_0", "Not an equality or iff proposition"),
    ("cardinalMk_le_max", "hash_x_colon_A_slash_slash_IsAlgebraic_R_x_le_max_hash_R_0", "Not an equality or iff proposition"),
    ("IsAzumaya_AlgHom_mulLeftRight_bij", "Function_Bijective_AlgHom_mulLeftRight_R_A", "Not an equality or iff proposition"),
    ("IsAzumaya_of_AlgEquiv", "IsAzumaya_R_B", "Not an equality or iff proposition"),
    ("IsAzumaya_matrix", "IsAzumaya_R_Matrix_n_n_R", "Not an equality or iff proposition"),
    ("Associated_prod", "i_in_s_f_i_tilde_i_in_s_g_i", "Not an equality or iff proposition"),
    ("exists_associated_mem_of_dvd_prod", "forall_r_in_s_Prime_r_to_p_s_prod_to_exists_q_in_s_p_tilde_q", "Not an equality or iff proposition"),
    ("divisor_closure_eq_closure", "x_in_closure_r_colon_M_0_pipe_IsUnit_r_or_Prime_r", "Not an equality or iff proposition"),
    ("Associates_prod_le_prod", "p_prod_le_q_prod", "Not an equality or iff proposition"),
    ("exists_mem_multiset_le_of_prime", "p_le_s_prod_to_exists_a_in_s_p_le_a", "Not an equality or iff proposition"),
    ("expect_bij", "_unknown", "Empty proposition"),
    ("expect_nbij", "_unknown", "Empty proposition"),
    ("expect_product", "_unknown", "Empty proposition"),
    ("expect_boole_mul", "_unknown", "Empty proposition"),
    ("partialProd_succ", "_unknown", "Empty proposition"),
    ("finprod_induction", "p_i_f_i", "Not an equality or iff proposition"),
    ("finprod_nonneg", "_0_le_x_f_x", "Not an equality or iff proposition"),
    ("one_le_finprod", "_unknown", "Empty proposition"),
    ("one_le_finprod", "_1_le_i_f_i", "Not an equality or iff proposition"),
    ("hasFiniteMulSupport_of_finprod_ne_one", "HasFiniteMulSupport_f", "Not an equality or iff proposition"),
    ("hasFiniteSupport_of_finsum_eq_one", "HasFiniteSupport_f", "Not an equality or iff proposition"),
    ("finprod_mem_inter_mulSupport_eq", "_unknown", "Empty proposition"),
    ("one_lt_finprod_cond", "_1_lt_i_colon_p_i_f_i", "Not an equality or iff proposition"),
    ("one_lt_finprod", "_1_lt_i_f_i", "Not an equality or iff proposition"),
    ("finprod_le_finprod", "_unknown", "Empty proposition"),
    ("finprod_le_finprod", "a_f_a_le_a_g_a", "Not an equality or iff proposition"),
    ("finprod_zero_le_one", "colon_a_0_colon_M_le_1", "Not an equality or iff proposition"),
    ("finprod_mem_mul_distrib", "_unknown", "Empty proposition"),
    ("exists_ne_one_of_finprod_mem_ne_one", "exists_x_in_s_f_x_ne_1", "Not an equality or iff proposition"),
    ("finsum_smul", "_unknown", "Empty proposition"),
    ("smul_finsum", "_unknown", "Empty proposition"),
    ("nonempty_of_finprod_mem_ne_one", "s_Nonempty", "Not an equality or iff proposition"),
    ("finprod_mem_union_inter", "_unknown", "Empty proposition"),
    ("finprod_mem_union", "_unknown", "Empty proposition"),
    ("finprod_mem_union", "_unknown", "Empty proposition"),
    ("finprod_mem_insert", "_unknown", "Empty proposition"),
    ("finprod_mem_dvd", "f_a_finprod_f", "Not an equality or iff proposition"),
    ("finprod_mem_image", "_unknown", "Empty proposition"),
    ("finprod_mem_range", "_unknown", "Empty proposition"),
    ("finprod_mem_inter_mul_diff", "_unknown", "Empty proposition"),
    ("finprod_mem_mul_diff", "_unknown", "Empty proposition"),
    ("finprod_mem_induction", "p_i_in_s_f_i", "Not an equality or iff proposition"),
    ("finprod_cond_nonneg", "_0_le_x_colon_p_x_f_x", "Not an equality or iff proposition"),
    ("single_le_finprod", "f_i_le_j_f_j", "Not an equality or iff proposition"),
    ("mul_finsum", "_unknown", "Empty proposition"),
    ("mul_finsum_mem", "_unknown", "Empty proposition"),
    ("finsum_mul", "_unknown", "Empty proposition"),
    ("finsum_mem_mul", "_unknown", "Empty proposition"),
    ("finprod_mem_finset_product", "_unknown", "Empty proposition"),
    ("finprod_emb_domain", "_unknown", "Empty proposition"),
    ("finTwoArrowEquiv", "_unknown", "Empty proposition"),
    ("prod_image", "_unknown", "Empty proposition"),
    ("exists_ne_one_of_prod_ne_one", "exists_a_in_s_f_a_ne_1", "Not an equality or iff proposition"),
    ("prod_range_succ", "_unknown", "Empty proposition"),
    ("prod_erase_lt_of_one_lt", "m_in_s_erase_d_f_m_lt_m_in_s_f_m", "Not an equality or iff proposition"),
    ("prod_dvd_prod_of_dvd", "i_in_s_f_i_i_in_s_g_i", "Not an equality or iff proposition"),
    ("prod_range_div", "_unknown", "Empty proposition"),
    ("eq_prod_range_div", "_unknown", "Empty proposition"),
    ("card_biUnion_le", "hash_s_biUnion_t_le_a_in_s_hash_t_a", "Not an equality or iff proposition"),
    ("prod_hom_rel", "r_x_in_s_f_x_x_in_s_g_x", "Not an equality or iff proposition"),
    ("nonempty_of_prod_ne_one", "s_Nonempty", "Not an equality or iff proposition"),
    ("prod_induction", "p_lt_pipe_x_in_s_f_x", "Not an equality or iff proposition"),
    ("prod_induction_nonempty", "p_lt_pipe_x_in_s_f_x", "Not an equality or iff proposition"),
    ("prod_dvd_prod_of_subset", "i_in_s_f_i_i_in_t_f_i", "Not an equality or iff proposition"),
    ("prod_range_div", "_unknown", "Empty proposition"),
    ("prod_set", "_unknown", "Empty proposition"),
    ("headI_le_sum", "L_headI_le_L_sum", "Not an equality or iff proposition"),
    ("alternatingProd_cons_cons", "_unknown", "Empty proposition"),
    ("alternatingProd_cons", "_unknown", "Empty proposition"),
    ("prod_induction", "p_l_prod", "Not an equality or iff proposition"),
    ("prod_induction_nonempty", "p_l_prod", "Not an equality or iff proposition"),
    ("prod_hom_rel", "r_l_map_f_prod_l_map_g_prod", "Not an equality or iff proposition"),
    ("prod_dvd_prod_of_dvd", "Multiset_map_g1_S_prod_Multiset_map_g2_S_prod", "Not an equality or iff proposition"),
    ("coe_sumAddMonoidHom", "sumAddMonoidHom_colon_Multiset_M_to_M_eq_sum", "Not an equality or iff proposition"),
    ("prod_map_inv", "_unknown", "Empty proposition"),
    ("smul_finprod", "_unknown", "Empty proposition"),
    ("pi_eq_sum_univ", "_unknown", "Empty proposition"),
    ("Pi_single_induction", "p_f", "Not an equality or iff proposition"),
    ("Pi_mulSingle_induction", "p_f", "Not an equality or iff proposition"),
    ("eqOn_finsetProd", "Set_EqOn_i_in_v_f_i_i_in_v_f_prime_i_s", "Not an equality or iff proposition"),
    ("eqOn_fun_finsetProd", "Set_EqOn_fun_b_i_in_v_f_i_b_fun_b_i_in_v_f_prime_i_b_s", "Not an equality or iff proposition"),
    ("Commute_sum_right", "Commute_b_i_in_s_f_i", "Not an equality or iff proposition"),
    ("Commute_sum_left", "Commute_i_in_s_f_i_b", "Not an equality or iff proposition"),
    ("dvd_sum", "a_i_in_s_f_i", "Not an equality or iff proposition"),
    ("sum_pow", "_unknown", "Empty proposition"),
    ("Commute_list_sum_right", "Commute_a_l_sum", "Not an equality or iff proposition"),
    ("Commute_list_sum_left", "Commute_l_sum_b", "Not an equality or iff proposition"),
    ("prod_ne_zero", "l_prod_ne_0", "Not an equality or iff proposition"),
    ("dvd_sum", "a_l_sum", "Not an equality or iff proposition"),
    ("prod_ne_zero", "s_prod_ne_0", "Not an equality or iff proposition"),
    ("dvd_sum", "forall_x_in_s_a_x_to_a_s_sum", "Not an equality or iff proposition"),
    ("Commute_multiset_sum_right", "Commute_a_s_sum", "Not an equality or iff proposition"),
    ("Commute_multiset_sum_left", "Commute_s_sum_b", "Not an equality or iff proposition"),
    ("prod_ne_top", "i_in_s_f_i_ne_top", "Not an equality or iff proposition"),
    ("prod_lt_top", "i_in_s_f_i_lt_top", "Not an equality or iff proposition"),
    ("prod_eq_top_ne_zero", "f_i_ne_0", "Not an equality or iff proposition"),
    ("WithBot_sum_lt_bot", "bot_lt_i_in_s_f_i", "Not an equality or iff proposition"),
    ("prod_ne_bot", "i_in_s_f_i_ne_bot", "Not an equality or iff proposition"),
    ("bot_lt_prod", "bot_lt_i_in_s_f_i", "Not an equality or iff proposition"),
    ("IsBrauerEquivalent_refl", "IsBrauerEquivalent_A_A", "Not an equality or iff proposition"),
    ("IsBrauerEquivalent_symm", "IsBrauerEquivalent_B_A", "Not an equality or iff proposition"),
    ("IsBrauerEquivalent_trans", "IsBrauerEquivalent_A_C", "Not an equality or iff proposition"),
    ("IsBrauerEquivalent_is_eqv", "Equivalence_IsBrauerEquivalent_K_colon_eq_K", "Not an equality or iff proposition"),
    ("AlgCat_hasLimitsOfSize", "HasLimitsOfSize_t_v_AlgCat_w_R", "Not an equality or iff proposition"),
    ("BialgCat_Hom_toBialgHom_injective", "Function_Injective_Hom_toBialgHom_colon_Hom_V_W_to", "Not an equality or iff proposition"),
    ("CoalgCat_Hom_toCoalgHom_injective", "Function_Injective_Hom_toCoalgHom_prime_colon_Hom_V_W_to", "Not an equality or iff proposition"),
    ("essentiallySmall_of_le", "EssentiallySmall_u_MorphismProperty_Under_Q_top_R", "Not an equality or iff proposition"),
    ("FGModuleCatEvaluation_apply", "_unknown", "Empty proposition"),
    ("coevaluation_evaluation", "letI_V_prime_colon_FGModuleCat_K", "Not an equality or iff proposition"),
    ("GrpCat_coe_id", "_1_X_colon_X_to_X_eq_id", "Not an equality or iff proposition"),
    ("GrpCat_coe_comp", "f_g_colon_X_to_Z_eq_g_comp_f", "Not an equality or iff proposition"),
    ("GrpCat_one_apply", "_1_colon_G_H_colon_G_to_H_g_eq_1", "Not an equality or iff proposition"),
    ("GrpCat_ofHom_injective", "Function_Injective_fun_f_colon_X_to_star_Y_ofHom_f", "Not an equality or iff proposition"),
    ("CommGrpCat_coe_id", "_1_X_colon_X_to_X_eq_id", "Not an equality or iff proposition"),
    ("CommGrpCat_coe_comp", "f_g_colon_X_to_Z_eq_g_comp_f", "Not an equality or iff proposition"),
    ("CommGrpCat_one_apply", "_1_colon_G_H_colon_G_to_H_g_eq_1", "Not an equality or iff proposition"),
    ("CommGrpCat_ofHom_injective", "Function_Injective_fun_f_colon_X_to_star_Y_ofHom_f", "Not an equality or iff proposition"),
    ("GrpCat_surjective_of_epi", "Function_Surjective_f", "Not an equality or iff proposition"),
    ("GrpCat_isZero_of_subsingleton", "IsZero_G", "Not an equality or iff proposition"),
    ("GrpCat_subsingleton_of_isZero", "Subsingleton_G", "Not an equality or iff proposition"),
    ("CommGrpCat_isZero_of_subsingleton", "IsZero_G", "Not an equality or iff proposition"),
    ("CommGrpCat_subsingleton_of_isZero", "Subsingleton_G", "Not an equality or iff proposition"),
    ("GrpWithZero_coe_id", "_1_X_colon_X_to_X_eq_id", "Not an equality or iff proposition"),
    ("GrpWithZero_coe_comp", "f_g_colon_X_to_Z_eq_g_comp_f", "Not an equality or iff proposition"),
    ("HopfAlgCat_Hom_toBialgHom_injective", "Function_Injective_Hom_toBialgHom_colon_Hom_V_W_to", "Not an equality or iff proposition"),
    ("isZero_of_subsingleton", "IsZero_M", "Not an equality or iff proposition"),
    ("mkOfSMul", "_unknown", "Empty proposition"),
    ("restrictScalarsComp", "_unknown", "Empty proposition"),
    ("restrictScalarsComp", "_unknown", "Empty proposition"),
    ("restrictScalarsComp", "_unknown", "Empty proposition"),
    ("restrictScalarsComp", "_unknown", "Empty proposition"),
    ("ExtendScalars_map", "_unknown", "Empty proposition"),
    ("ExtendScalars_map", "_unknown", "Empty proposition"),
    ("CoextendScalars_smul_apply", "_unknown", "Empty proposition"),
    ("extendScalars_assoc", "_unknown", "Empty proposition"),
    ("PresheafOfModules_DifferentialsConstruction_relativeDifferentials", "_unknown", "Empty proposition"),
    ("precomp_extClass_surjective_of_projective_X_2", "Function_Surjective_h_extClass_precomp_M_add_comm_1_n", "Not an equality or iff proposition"),
    ("postcomp_extClass_surjective_of_projective_X_2", "Function_Surjective_h_extClass_postcomp_M_rfl_colon_n_plus_1_eq_n_plus_1", "Not an equality or iff proposition"),
    ("linearIndependent_shortExact", "LinearIndependent_R_Sum_elim_S_f_comp_v_S_g_hom_toFun_invFun_comp_w", "Not an equality or iff proposition"),
    ("span_exact", "top_le_span_R_range_u", "Not an equality or iff proposition"),
    ("span_rightExact", "top_le_span_R_range_Sum_elim_S_f_comp_v_S_g_hom_toFun_invFun_comp_w", "Not an equality or iff proposition"),
    ("free_shortExact", "Module_Free_R_S_X_2", "Not an equality or iff proposition"),
    ("hasKernels_moduleCat", "HasKernels_ModuleCat_R", "Not an equality or iff proposition"),
    ("hasCokernels_moduleCat", "HasCokernels_ModuleCat_R", "Not an equality or iff proposition"),
    ("SemimoduleCat_tensor_ext_3", "_unknown", "Empty proposition"),
    ("PresheafOfModules_epi_of_surjective", "Epi_f", "Not an equality or iff proposition"),
    ("PresheafOfModules_mono_of_injective", "Mono_f", "Not an equality or iff proposition"),
    ("PresheafOfModules_surjective_of_epi", "Function_Surjective_f_app_X", "Not an equality or iff proposition"),
    ("PresheafOfModules_injective_of_mono", "Function_Injective_f_app_X", "Not an equality or iff proposition"),
    ("PresheafOfModules_freeYoneda_isSeparating", "ObjectProperty_IsSeparating_freeYoneda_R", "Not an equality or iff proposition"),
    ("PresheafOfModules_freeYoneda_isDetecting", "ObjectProperty_IsDetecting_freeYoneda_R", "Not an equality or iff proposition"),
    ("pullbackObjIsDefined_free_yoneda", "pullbackObjIsDefined_phi_free_S_obj_yoneda_obj_X", "Not an equality or iff proposition"),
    ("PresheafOfModules_pushforward_obj_map_apply", "_unknown", "Empty proposition"),
    ("PresheafOfModules_pushforward_map_app_apply", "_unknown", "Empty proposition"),
    ("PresheafOfModules_toSheafify_app_apply", "_unknown", "Empty proposition"),
    ("PresheafOfModules_comp_toPresheaf_map_sheafifyHomEquiv", "_unknown", "Empty proposition"),
    ("hasProjectiveDimensionLE_of_linearEquiv", "HasProjectiveDimensionLE_N_n", "Not an equality or iff proposition"),
    ("SemimoduleCat_hom_bijective", "Function_Bijective_Hom_hom_colon_M_N_to_M_to_R_N", "Not an equality or iff proposition"),
    ("SemimoduleCat_hom_injective", "Function_Injective_Hom_hom_colon_M_N_to_M_to_R_N", "Not an equality or iff proposition"),
    ("SemimoduleCat_hom_surjective", "Function_Surjective_Hom_hom_colon_M_N_to_M_to_R_N", "Not an equality or iff proposition"),
    ("isZero_of_subsingleton", "IsZero_M", "Not an equality or iff proposition"),
    ("SemimoduleCat_subsingleton_of_isZero", "Subsingleton_M", "Not an equality or iff proposition"),
    ("PresheafOfModules_isSheaf_of_isLimit", "Presheaf_IsSheaf_J_c_pt_presheaf", "Not an equality or iff proposition"),
    ("SheafOfModules_bijective_pushforwardSections", "Function_Bijective_pushforwardSections_phi_M_colon_eq_M", "Not an equality or iff proposition"),
    ("QuasicoherentData_isQuasicoherent", "M_IsQuasicoherent", "Not an equality or iff proposition"),
    ("Presentation_isQuasicoherent", "IsQuasicoherent_M", "Not an equality or iff proposition"),
    ("IsQuasicoherent_of_coversTop", "IsQuasicoherent_M", "Not an equality or iff proposition"),
    ("simple_iff_isSimpleModule", "_unknown", "Empty proposition"),
    ("simple_of_finrank_eq_one", "Simple_V", "Not an equality or iff proposition"),
    ("MonCat_coe_id", "_1_X_colon_X_to_X_eq_id", "Not an equality or iff proposition"),
    ("MonCat_coe_comp", "f_g_colon_X_to_Z_eq_g_comp_f", "Not an equality or iff proposition"),
    ("CommMonCat_coe_id", "_1_X_colon_X_to_X_eq_id", "Not an equality or iff proposition"),
    ("CommMonCat_coe_comp", "f_g_colon_X_to_Z_eq_g_comp_f", "Not an equality or iff proposition"),
    ("subsingleton_of_isTerminal", "Subsingleton_X", "Not an equality or iff proposition"),
    ("equalizer_i_isLocalHom", "IsLocalHom_limit_pi_F_WalkingParallelPair_zero_hom", "Not an equality or iff proposition"),
    ("Opposite_regularEpiOfFaithfullyFlat", "IsRegularEpi_f", "Not an equality or iff proposition"),
    ("Opposite_effectiveEpi_of_faithfullyFlat", "EffectiveEpi_f", "Not an equality or iff proposition"),
    ("IsLocalization_epi", "Epi_CommRingCat_ofHom_lt_pipe_algebraMap_R_S", "Not an equality or iff proposition"),
    ("isLocalHom_of_iso", "IsLocalHom_f_hom_hom", "Not an equality or iff proposition"),
    ("isLocalHom_of_isIso", "IsLocalHom_f_hom", "Not an equality or iff proposition"),
    ("equalizerFork", "_unknown", "Empty proposition"),
    ("preservesFiniteLimits_of_flat", "PreservesFiniteLimits_Under_pushout_f", "Not an equality or iff proposition"),
    ("MagmaCat_coe_id", "_1_X_colon_X_to_X_eq_id", "Not an equality or iff proposition"),
    ("MagmaCat_coe_comp", "f_g_colon_X_to_Z_eq_g_comp_f", "Not an equality or iff proposition"),
    ("MagmaCat_mulEquiv_coe_eq", "ofHom_e_colon_X_to_star_Y_hom_eq_e", "Not an equality or iff proposition"),
    ("Semigrp_coe_id", "_1_X_colon_X_to_X_eq_id", "Not an equality or iff proposition"),
    ("Semigrp_coe_comp", "f_g_colon_X_to_Z_eq_g_comp_f", "Not an equality or iff proposition"),
    ("Semigrp_mulEquiv_coe_eq", "ofHom_e_colon_X_to_star_Y_hom_eq_e", "Not an equality or iff proposition"),
    ("charP_of_injective_ringHom", "CharP_A_p", "Not an equality or iff proposition"),
    ("charP_of_injective_algebraMap", "CharP_A_p", "Not an equality or iff proposition"),
    ("charP_of_injective_algebraMap", "_unknown", "Empty proposition"),
    ("charZero_of_injective_ringHom", "CharZero_A", "Not an equality or iff proposition"),
    ("charZero_of_injective_algebraMap", "CharZero_A", "Not an equality or iff proposition"),
]
