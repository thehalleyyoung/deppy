"""Mathlib: Nat Basic — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 3090 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_nat_basic"
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

def _r0000_balance_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.balance_add
    # balance (f + g) = balance f + balance g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "balance", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("balance", (OVar("f"),)), OOp("balance", (OVar("g"),))))
            results.append((rhs, "Mathlib: Fintype_balance_add"))
        except Exception:
            pass
    return results


def _r0001_sum_balance(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.sum_balance
    # ∑ x, balance f x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Fintype_sum_balance"))
        except Exception:
            pass
    return results


def _r0002_expect_balance(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.expect_balance
    # 𝔼 x, balance f x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Fintype_expect_balance"))
        except Exception:
            pass
    return results


def _r0003_balance_idem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.balance_idem
    # balance (balance f) = balance f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "balance", 1)
    if args is not None:
        try:
            rhs = OOp("balance", (OVar("f"),))
            results.append((rhs, "Mathlib: Fintype_balance_idem"))
        except Exception:
            pass
    return results


def _r0004_map_balance(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.map_balance
    # g (balance f a) = balance (g ∘ f) a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 1)
    if args is not None:
        try:
            rhs = OOp("balance", (OOp("comp", (OVar("g"), OVar("f"))), OVar("a"),))
            results.append((rhs, "Mathlib: Fintype_map_balance"))
        except Exception:
            pass
    return results


def _r0005_expect_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.expect_singleton
    # 𝔼 j ∈ {i}, f j = f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("i"),))
            results.append((rhs, "Mathlib: Finset_expect_singleton"))
        except Exception:
            pass
    return results


def _r0006_expect_const_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.expect_const_zero
    # 𝔼 _i ∈ s, (0 : M) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Finset_expect_const_zero"))
        except Exception:
            pass
    return results


def _r0007_expect_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.expect_congr
    # 𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("t", (OVar("g"), OVar("i"),))))
            results.append((rhs, "Mathlib: Finset_expect_congr"))
        except Exception:
            pass
    return results


def _r0008_expect_ite_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.expect_ite_eq
    # 𝔼 j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i /ℚ #s else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("if", (OVar("i"),)), OOp("s", (OVar("then"), OVar("f"), OVar("i"), OVar("slash"), OVar("hash_s"), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: Finset_expect_ite_eq"))
        except Exception:
            pass
    return results


def _r0009_card_mul_expect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.card_mul_expect
    # Fintype.card ι * 𝔼 i, f i = ∑ i, f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("f"), OVar("i"),))
            results.append((rhs, "Mathlib: Fintype_card_mul_expect"))
        except Exception:
            pass
    return results


def _r0010_expect_dite_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.expect_dite_eq
    # 𝔼 j, (if h : i = j then f j h else 0) = f i rfl /ℚ card ι
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("i"), OVar("rfl"), OVar("slash"), OVar("card"), OVar("i"),))
            results.append((rhs, "Mathlib: Fintype_expect_dite_eq"))
        except Exception:
            pass
    return results


def _r0011_prod_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.prod_comm
    # (f.prod fun x v => g.prod fun x' v' => h x v x' v') =       g.prod fun x' v' => f.prod fun x v => h x v x' v'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_prod", 14)
    if args is not None:
        try:
            rhs = OOp("g_prod", (args[5], args[12], args[13], args[8], OVar("f_prod"), args[5], args[10], args[11], args[8], args[9], args[10], args[11], args[12], args[13],))
            results.append((rhs, "Mathlib: Finsupp_prod_comm"))
        except Exception:
            pass
    return results


def _r0012_support_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.support_sum
    # (f.sum g).support ⊆ f.support.biUnion fun a => (g a (f a)).support
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("g_a_f_a_support"),))
            results.append((rhs, "Mathlib: Finsupp_support_sum"))
        except Exception:
            pass
    return results


def _r0013_prod_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_eq_one_iff
    # ∏ i ∈ s, f i = 1 ↔ ∀ i ∈ s, f i = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OOp("in", (OOp("forall", (OVar("i"),)), OOp("s", (OVar("f"), OVar("i"),)))))), OLit(1)))
            results.append((rhs, "Mathlib: Finset_prod_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0014_prod_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_map
    # ∏ x ∈ s.map e, f x = ∏ x ∈ s, f (e x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (OVar("f"), OOp("e", (OVar("x"),)),))))
            results.append((rhs, "Mathlib: Finset_prod_map"))
        except Exception:
            pass
    return results


def _r0015_mul_prod_eq_prod_insertNone(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.mul_prod_eq_prod_insertNone
    # x * ∏ i ∈ s, f i = ∏ i ∈ insertNone s, i.elim x f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("insertNone", (OVar("s"), OVar("i_elim"), args[0], OVar("f"),))))
            results.append((rhs, "Mathlib: Finset_mul_prod_eq_prod_insertNone"))
        except Exception:
            pass
    return results


def _r0016_cast_list_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_list_prod
    # (↑s.prod : R) = (s.map (↑)).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_prod", 2)
    if args is not None:
        try:
            rhs = OVar("s_map_prod")
            results.append((rhs, "Mathlib: Nat_cast_list_prod"))
        except Exception:
            pass
    return results


def _r0017_cast_multiset_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_multiset_sum
    # (↑s.sum : R) = (s.map (↑)).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sum", 2)
    if args is not None:
        try:
            rhs = OVar("s_map_sum")
            results.append((rhs, "Mathlib: Nat_cast_multiset_sum"))
        except Exception:
            pass
    return results


def _r0018_cast_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_sum
    # ↑(∑ x ∈ s, f x : ℕ) = ∑ x ∈ s, (f x : R)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_in_s_f_x_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (OOp("f", (OVar("x"), OVar("colon"), OVar("R"),)),))))
            results.append((rhs, "Mathlib: Nat_cast_sum"))
    except Exception:
        pass
    return results


def _r0019_cast_list_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.cast_list_prod
    # (↑s.prod : R) = (s.map (↑)).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_prod", 2)
    if args is not None:
        try:
            rhs = OVar("s_map_prod")
            results.append((rhs, "Mathlib: Int_cast_list_prod"))
        except Exception:
            pass
    return results


def _r0020_cast_multiset_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.cast_multiset_sum
    # (↑s.sum : R) = (s.map (↑)).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sum", 2)
    if args is not None:
        try:
            rhs = OVar("s_map_sum")
            results.append((rhs, "Mathlib: Int_cast_multiset_sum"))
        except Exception:
            pass
    return results


def _r0021_cast_ringChar(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ringChar.Nat.cast_ringChar
    # (ringChar R : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ringChar", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ringChar_Nat_cast_ringChar"))
        except Exception:
            pass
    return results


def _r0022_cast_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_eq_zero
    # (n : R) = 0 ↔ n = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("n"))), OLit(0)))
            results.append((rhs, "Mathlib: Nat_cast_eq_zero"))
        except Exception:
            pass
    return results


def _r0023_normalize_lcm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.normalize_lcm
    # normalize (s.lcm f) = s.lcm f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = OOp("s_lcm", (OVar("f"),))
            results.append((rhs, "Mathlib: Finset_normalize_lcm"))
        except Exception:
            pass
    return results


def _r0024_lcm_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.lcm_union
    # (s₁ ∪ s₂).lcm f = GCDMonoid.lcm (s₁.lcm f) (s₂.lcm f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_1_union_s_2_lcm", 1)
    if args is not None:
        try:
            rhs = OOp("GCDMonoid_lcm", (OOp("s_1_lcm", (args[0],)), OOp("s_2_lcm", (args[0],)),))
            results.append((rhs, "Mathlib: Finset_lcm_union"))
        except Exception:
            pass
    return results


def _r0025_lt_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.lt_one_iff
    # x < 1 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Fin_lt_one_iff"))
        except Exception:
            pass
    return results


def _r0026_lt_sub_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.lt_sub_one_iff
    # k < k - 1 ↔ k = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Fin_lt_sub_one_iff"))
        except Exception:
            pass
    return results


def _r0027_neg_natCast_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.neg_natCast_eq_one
    # -(n : Fin (n + 1)) = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_n_colon_Fin_n_plus_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Fin_neg_natCast_eq_one"))
    except Exception:
        pass
    return results


def _r0028_zeroHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.mapRange.zeroHom_comp
    # mapRange.zeroHom (ι := ι) (f.comp f₂) = (mapRange.zeroHom f).comp (mapRange.zeroHom f₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapRange_zeroHom", 2)
    if args is not None:
        try:
            rhs = OOp("mapRange_zeroHom_f_comp", (OOp("mapRange_zeroHom", (OVar("f_2"),)),))
            results.append((rhs, "Mathlib: Finsupp_mapRange_zeroHom_comp"))
        except Exception:
            pass
    return results


def _r0029_zsmul_eq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.zsmul_eq_mul
    # n • a = n * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("n"), args[1]))
            results.append((rhs, "Mathlib: Int_zsmul_eq_mul"))
        except Exception:
            pass
    return results


def _r0030_one_emod_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.one_emod_two
    # (1 : Int) % 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_Int", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Int_one_emod_two"))
        except Exception:
            pass
    return results


def _r0031_emod_two_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.emod_two_ne_zero
    # ¬n % 2 = 0 ↔ n % 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not_n", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("n", (args[0], OLit(2),)))), OLit(1)))
            results.append((rhs, "Mathlib: Int_emod_two_ne_zero"))
        except Exception:
            pass
    return results


def _r0032_even_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.even_iff
    # Even n ↔ n % 2 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Int_even_iff"))
        except Exception:
            pass
    return results


def _r0033_isUnit_eq_one_or(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.isUnit_eq_one_or
    # u = 1 ∨ u = -1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("u")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("or", (OLit(1), OVar("u"))), OVar("minus_1")))
            results.append((rhs, "Mathlib: Int_isUnit_eq_one_or"))
    except Exception:
        pass
    return results


def _r0034_succ_mod_two_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.succ_mod_two_eq_zero_iff
    # (m + 1) % 2 = 0 ↔ m % 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_plus_1", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("m", (args[0], OLit(2),)))), OLit(1)))
            results.append((rhs, "Mathlib: Nat_succ_mod_two_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0035_succ_mod_two_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.succ_mod_two_eq_one_iff
    # (m + 1) % 2 = 1 ↔ m % 2 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_plus_1", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OOp("m", (args[0], OLit(2),)))), OLit(0)))
            results.append((rhs, "Mathlib: Nat_succ_mod_two_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0036_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.coe_one
    # ↑(1 : Finset α) = (1 : Set α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Finset_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("colon"), OVar("Set"), OVar("a"),))
            results.append((rhs, "Mathlib: Finset_coe_one"))
    except Exception:
        pass
    return results


def _r0037_coe_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.coe_eq_one
    # (s : Set α) = 1 ↔ s = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("s"))), OLit(1)))
            results.append((rhs, "Mathlib: Finset_coe_eq_one"))
        except Exception:
            pass
    return results


def _r0038_map_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.map_one
    # map f 1 = {f 1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OVar("f_1")
            results.append((rhs, "Mathlib: Finset_map_one"))
        except Exception:
            pass
    return results


def _r0039_image_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_one
    # image f 1 = {f 1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image", 2)
    if args is not None:
        try:
            rhs = OVar("f_1")
            results.append((rhs, "Mathlib: Finset_image_one"))
        except Exception:
            pass
    return results


def _r0040_subset_one_iff_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.subset_one_iff_eq
    # s ⊆ 1 ↔ s = ∅ ∨ s = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OVar("empty"), args[1])), OLit(1)))
            results.append((rhs, "Mathlib: Finset_subset_one_iff_eq"))
        except Exception:
            pass
    return results


def _r0041_singletonOneHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.singletonOneHom_apply
    # singletonOneHom a = {a}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "singletonOneHom", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Finset_singletonOneHom_apply"))
        except Exception:
            pass
    return results


def _r0042_inf_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.inf_one
    # inf 1 f = f 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inf", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(1),))
            results.append((rhs, "Mathlib: Finset_inf_one"))
        except Exception:
            pass
    return results


def _r0043_max_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.max_one
    # (1 : Finset α).max = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Finset_a_max")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Finset_max_one"))
    except Exception:
        pass
    return results


def _r0044_min_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.min_one
    # (1 : Finset α).min = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Finset_a_min")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Finset_min_one"))
    except Exception:
        pass
    return results


def _r0045_image_op_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.image_op_one
    # (1 : Finset α).image op = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_Finset_a_image", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Finset_image_op_one"))
        except Exception:
            pass
    return results


def _r0046_map_op_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.map_op_one
    # (1 : Finset α).map opEquiv.toEmbedding = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_Finset_a_map", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Finset_map_op_one"))
        except Exception:
            pass
    return results


def _r0047_one_product_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.one_product_one
    # (1 ×ˢ 1 : Finset (α × β)) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 5)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Finset_one_product_one"))
        except Exception:
            pass
    return results


def _r0048_prod_neg_index(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_neg_index
    # ∏ i ∈ -s, f i = ∏ i ∈ s, f (-i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f"), OVar("minus_i"),))))
            results.append((rhs, "Mathlib: Finset_prod_neg_index"))
        except Exception:
            pass
    return results


def _r0049_dens_smul_finset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.dens_smul_finset
    # (a • s).dens = s.dens
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_s_dens")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_dens")
            results.append((rhs, "Mathlib: Finset_dens_smul_finset"))
    except Exception:
        pass
    return results


def _r0050_smul_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.smul_empty
    # s • (∅ : Finset β) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Finset_smul_empty"))
        except Exception:
            pass
    return results


def _r0051_smul_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.smul_eq_empty
    # s • t = ∅ ↔ s = ∅ ∨ t = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("s"))), OOp("==", (OOp("or", (OVar("empty"), args[1])), OVar("empty")))))
            results.append((rhs, "Mathlib: Finset_smul_eq_empty"))
        except Exception:
            pass
    return results


def _r0052_card_additive(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.card_additive
    # card (Additive α) = card α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("a"),))
            results.append((rhs, "Mathlib: Fintype_card_additive"))
        except Exception:
            pass
    return results


def _r0053_equiv_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ComplexShape.Embedding.AreComplementary.equiv_inr
    # ac.equiv (Sum.inr i₂) = e₂.f i₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ac_equiv", 1)
    if args is not None:
        try:
            rhs = OOp("e_2_f", (OVar("i_2"),))
            results.append((rhs, "Mathlib: ComplexShape_Embedding_AreComplementary_equiv_inr"))
        except Exception:
            pass
    return results


def _r0054_f_eq_of_r_eq_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ComplexShape.f_eq_of_r_eq_some
    # e.f i = i'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_f", 1)
    if args is not None:
        try:
            rhs = OVar("i_prime")
            results.append((rhs, "Mathlib: ComplexShape_f_eq_of_r_eq_some"))
        except Exception:
            pass
    return results


def _r0055_boundaryGE_embeddingUpIntGE_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ComplexShape.boundaryGE_embeddingUpIntGE_iff
    # (embeddingUpIntGE p).BoundaryGE n ↔ n = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ComplexShape_boundaryGE_embeddingUpIntGE_iff"))
        except Exception:
            pass
    return results


def _r0056_finsuppAntidiag_empty_of_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.finsuppAntidiag_empty_of_ne_zero
    # finsuppAntidiag (∅ : Finset ι) n = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finsuppAntidiag", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Finset_finsuppAntidiag_empty_of_ne_zero"))
        except Exception:
            pass
    return results


def _r0057_finsuppAntidiag_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.finsuppAntidiag_empty
    # finsuppAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finsuppAntidiag", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[1],)), OOp("_0", (OVar("then"), OVar("_0"), OVar("else"), OVar("empty"),))))
            results.append((rhs, "Mathlib: Finset_finsuppAntidiag_empty"))
        except Exception:
            pass
    return results


def _r0058_finMulAntidiag_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.finMulAntidiag_one
    # finMulAntidiag d 1 = {fun _ => 1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finMulAntidiag", 2)
    if args is not None:
        try:
            rhs = OVar("fun_eq_gt_1")
            results.append((rhs, "Mathlib: Nat_finMulAntidiag_one"))
        except Exception:
            pass
    return results


def _r0059_piAntidiag_empty_of_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.piAntidiag_empty_of_ne_zero
    # piAntidiag (∅ : Finset ι) n = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "piAntidiag", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Finset_piAntidiag_empty_of_ne_zero"))
        except Exception:
            pass
    return results


def _r0060_piAntidiag_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.piAntidiag_empty
    # piAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "piAntidiag", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[1],)), OOp("_0", (OVar("then"), OVar("_0"), OVar("else"), OVar("empty"),))))
            results.append((rhs, "Mathlib: Finset_piAntidiag_empty"))
        except Exception:
            pass
    return results


def _r0061_floorRing_ceil_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floorRing_ceil_eq
    # @FloorRing.ceil = @Int.ceil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("at_FloorRing_ceil")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("at_Int_ceil")
            results.append((rhs, "Mathlib: Int_floorRing_ceil_eq"))
    except Exception:
        pass
    return results


def _r0062_floor_eq_on_Ico(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_eq_on_Ico
    # ∀ a ∈ Set.Ico (n : R) (n + 1), ⌊a⌋ = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Int_floor_eq_on_Ico"))
    except Exception:
        pass
    return results


def _r0063_floor_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_intCast
    # ⌊(z : R)⌋ = z
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z")
            results.append((rhs, "Mathlib: Int_floor_intCast"))
    except Exception:
        pass
    return results


def _r0064_floor_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_natCast
    # ⌊(n : R)⌋ = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Int_floor_natCast"))
    except Exception:
        pass
    return results


def _r0065_floor_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_zero
    # ⌊(0 : R)⌋ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Int_floor_zero"))
    except Exception:
        pass
    return results


def _r0066_floor_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_one
    # ⌊(1 : R)⌋ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Int_floor_one"))
    except Exception:
        pass
    return results


def _r0067_floor_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_ofNat
    # ⌊(ofNat(n) : R)⌋ = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: Int_floor_ofNat"))
    except Exception:
        pass
    return results


def _r0068_floor_add_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_add_intCast
    # ⌊a + z⌋ = ⌊a⌋ + z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: Int_floor_add_intCast"))
        except Exception:
            pass
    return results


def _r0069_floor_add_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_add_natCast
    # ⌊a + n⌋ = ⌊a⌋ + n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: Int_floor_add_natCast"))
        except Exception:
            pass
    return results


def _r0070_floor_add_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_add_ofNat
    # ⌊a + ofNat(n)⌋ = ⌊a⌋ + ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: Int_floor_add_ofNat"))
        except Exception:
            pass
    return results


def _r0071_floor_ofNat_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_ofNat_add
    # ⌊ofNat(n) + a⌋ = ofNat(n) + ⌊a⌋
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: Int_floor_ofNat_add"))
        except Exception:
            pass
    return results


def _r0072_floor_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_sub_one
    # ⌊a - 1⌋ = ⌊a⌋ - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], OLit(1)))
            results.append((rhs, "Mathlib: Int_floor_sub_one"))
        except Exception:
            pass
    return results


def _r0073_floor_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.floor_one
    # ⌊(1 : R)⌋₊ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Nat_floor_one"))
    except Exception:
        pass
    return results


def _r0074_floor_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.floor_ofNat
    # ⌊(ofNat(n) : R)⌋₊ = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: Nat_floor_ofNat"))
    except Exception:
        pass
    return results


def _r0075_floor_of_nonpos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.floor_of_nonpos
    # ⌊a⌋₊ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Nat_floor_of_nonpos"))
    except Exception:
        pass
    return results


def _r0076_abs_le_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.abs_le_one_iff
    # |a| ≤ 1 ↔ a = 0 ∨ a = 1 ∨ a = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(0), OVar("a"))), OOp("==", (OOp("or", (OLit(1), OVar("a"))), OVar("minus_1")))))
            results.append((rhs, "Mathlib: Int_abs_le_one_iff"))
        except Exception:
            pass
    return results


def _r0077_mul_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.mul_bot
    # s * ⊥ = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Interval_mul_bot"))
        except Exception:
            pass
    return results


def _r0078_length_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.length_neg
    # ∀ s : Interval α, (-s).length = s.length   | ⊥ => rfl   | (s : NonemptyInterval α) => s.length_neg  omit [IsOrderedAddMo
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_s_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("s_length", (OVar("pipe"), OVar("bot"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OOp("s", (OVar("colon"), OVar("NonemptyInterval"), OVar("a"),)), OVar("eq_gt"), OVar("s_length_neg_omit"), OSeq((OOp("IsOrderedAddMonoid", (OVar("a"),)),)), OVar("in_at_simp_theorem"), OVar("length_bot"), OVar("colon"), OVar("bot_colon_Interval_a_length"),)), OLit(0)))
            results.append((rhs, "Mathlib: Interval_length_neg"))
    except Exception:
        pass
    return results


def _r0079_val_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.val_one
    # (1 : FiniteElement K).1 = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_FiniteElement_K_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_val_one"))
    except Exception:
        pass
    return results


def _r0080_mk_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.mk_one
    # FiniteElement.mk (1 : K) (by simp) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FiniteElement_mk", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_mk_one"))
        except Exception:
            pass
    return results


def _r0081_negOnePow_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.negOnePow_one
    # negOnePow 1 = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "negOnePow", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Int_negOnePow_one"))
        except Exception:
            pass
    return results


def _r0082_negOnePow_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.negOnePow_succ
    # (n + 1).negOnePow = -n.negOnePow
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_plus_1_negOnePow")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_n_negOnePow")
            results.append((rhs, "Mathlib: Int_negOnePow_succ"))
    except Exception:
        pass
    return results


def _r0083_negOnePow_odd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.negOnePow_odd
    # n.negOnePow = -1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_negOnePow")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Int_negOnePow_odd"))
    except Exception:
        pass
    return results


def _r0084_negOnePow_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.negOnePow_eq_one_iff
    # n.negOnePow = 1 ↔ Even n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_negOnePow")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OLit(1), OOp("Even", (OVar("n"),))))
            results.append((rhs, "Mathlib: Int_negOnePow_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0085_cast_negOnePow_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.cast_negOnePow_natCast
    # negOnePow n = (-1 : R) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "negOnePow", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("minus_1", (OVar("colon"), OVar("R"),)), args[0]))
            results.append((rhs, "Mathlib: Int_cast_negOnePow_natCast"))
        except Exception:
            pass
    return results


def _r0086_mkRat_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.mkRat_pow
    # mkRat num den ^ n = mkRat (num ^ n) (den ^ n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("mkRat", (OOp("**", (OVar("num"), args[1])), OOp("**", (OVar("den"), args[1])),))
            results.append((rhs, "Mathlib: Rat_mkRat_pow"))
        except Exception:
            pass
    return results


def _r0087_cast_analyticOrderNatAt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.cast_analyticOrderNatAt
    # analyticOrderNatAt f z₀ = analyticOrderAt f z₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "analyticOrderNatAt", 2)
    if args is not None:
        try:
            rhs = OOp("analyticOrderAt", (args[0], args[1],))
            results.append((rhs, "Mathlib: Nat_cast_analyticOrderNatAt"))
        except Exception:
            pass
    return results


def _r0088_conjLIE_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.conjLIE_symm
    # conjLIE.symm = conjLIE
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("conjLIE_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("conjLIE")
            results.append((rhs, "Mathlib: Complex_conjLIE_symm"))
    except Exception:
        pass
    return results


def _r0089_nndist_conj_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.nndist_conj_conj
    # nndist (conj z) (conj w) = nndist z w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nndist", 2)
    if args is not None:
        try:
            rhs = OOp("nndist", (OVar("z"), OVar("w"),))
            results.append((rhs, "Mathlib: Complex_nndist_conj_conj"))
        except Exception:
            pass
    return results


def _r0090_dist_conj_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.dist_conj_comm
    # dist (conj z) w = dist z (conj w)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dist", 2)
    if args is not None:
        try:
            rhs = OOp("dist", (OVar("z"), OOp("conj", (args[1],)),))
            results.append((rhs, "Mathlib: Complex_dist_conj_comm"))
        except Exception:
            pass
    return results


def _r0091_conjCAE_toAlgEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.conjCAE_toAlgEquiv
    # conjCAE.toAlgEquiv = conjAe
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("conjCAE_toAlgEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("conjAe")
            results.append((rhs, "Mathlib: Complex_conjCAE_toAlgEquiv"))
    except Exception:
        pass
    return results


def _r0092_conjCLE_toLinearEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.conjCLE_toLinearEquiv
    # conjCLE.toLinearEquiv = conjAe.toLinearEquiv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("conjCLE_toLinearEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("conjAe_toLinearEquiv")
            results.append((rhs, "Mathlib: Complex_conjCLE_toLinearEquiv"))
    except Exception:
        pass
    return results


def _r0093_conjCAE_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.conjCAE_apply
    # conjCAE z = conj z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "conjCAE", 1)
    if args is not None:
        try:
            rhs = OOp("conj", (args[0],))
            results.append((rhs, "Mathlib: Complex_conjCAE_apply"))
        except Exception:
            pass
    return results


def _r0094_ofRealCLM_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofRealCLM_apply
    # ofRealCLM x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofRealCLM", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Complex_ofRealCLM_apply"))
        except Exception:
            pass
    return results


def _r0095_ofReal_tsum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_tsum
    # (↑(∑'[L] a, f a) : ℂ) = ∑'[L] a, ↑(f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime_L_a_f_a", 2)
    if args is not None:
        try:
            rhs = OOp("prime_L", (OVar("a"), OVar("f_a"),))
            results.append((rhs, "Mathlib: Complex_ofReal_tsum"))
        except Exception:
            pass
    return results


def _r0096_ofReal_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_exp
    # (Real.exp x : ℂ) = exp x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_exp", 3)
    if args is not None:
        try:
            rhs = OOp("exp", (args[0],))
            results.append((rhs, "Mathlib: Complex_ofReal_exp"))
        except Exception:
            pass
    return results


def _r0097_exp_ofReal_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_ofReal_im
    # (exp x).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("exp_x_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_exp_ofReal_im"))
    except Exception:
        pass
    return results


def _r0098_exp_ofReal_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_ofReal_re
    # (exp x).re = Real.exp x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("exp_x_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Real_exp", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_exp_ofReal_re"))
    except Exception:
        pass
    return results


def _r0099_exp_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.exp_eq_one_iff
    # exp x = 1 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Real_exp_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0100_nnnorm_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.nnnorm_I
    # ‖I‖₊ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("I")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_nnnorm_I"))
    except Exception:
        pass
    return results


def _r0101_norm_real(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_real
    # ‖(r : ℂ)‖ = ‖r‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("r")
            results.append((rhs, "Mathlib: Complex_norm_real"))
    except Exception:
        pass
    return results


def _r0102_norm_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_natCast
    # ‖(n : ℂ)‖ = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Complex_norm_natCast"))
    except Exception:
        pass
    return results


def _r0103_norm_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_two
    # ‖(2 : ℂ)‖ = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_2_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(2)
            results.append((rhs, "Mathlib: Complex_norm_two"))
    except Exception:
        pass
    return results


def _r0104_nnnorm_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.nnnorm_ofNat
    # ‖(ofNat(n) : ℂ)‖₊ = OfNat.ofNat n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("OfNat_ofNat", (OVar("n"),))
            results.append((rhs, "Mathlib: Complex_nnnorm_ofNat"))
    except Exception:
        pass
    return results


def _r0105_norm_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_intCast
    # ‖(n : ℂ)‖ = |(n : ℝ)|
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("pipe_n_colon_pipe")
            results.append((rhs, "Mathlib: Complex_norm_intCast"))
    except Exception:
        pass
    return results


def _r0106_norm_nnratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_nnratCast
    # ‖(q : ℂ)‖ = q
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q")
            results.append((rhs, "Mathlib: Complex_norm_nnratCast"))
    except Exception:
        pass
    return results


def _r0107_nnnorm_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.nnnorm_ratCast
    # ‖(q : ℂ)‖₊ = ‖(q : ℝ)‖₊
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q_colon")
            results.append((rhs, "Mathlib: Complex_nnnorm_ratCast"))
    except Exception:
        pass
    return results


def _r0108_nnnorm_nnratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.nnnorm_nnratCast
    # ‖(q : ℂ)‖₊ = q
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q")
            results.append((rhs, "Mathlib: Complex_nnnorm_nnratCast"))
    except Exception:
        pass
    return results


def _r0109_normSq_eq_norm_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.normSq_eq_norm_sq
    # normSq z = ‖z‖ ^ 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normSq", 1)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OLit(2)))
            results.append((rhs, "Mathlib: Complex_normSq_eq_norm_sq"))
        except Exception:
            pass
    return results


def _r0110_norm_add_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_add_mul_I
    # ‖x + y * I‖ = √(x ^ 2 + y ^ 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("x_pow_2_plus_y_pow_2")
            results.append((rhs, "Mathlib: Complex_norm_add_mul_I"))
        except Exception:
            pass
    return results


def _r0111_abs_re_eq_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.abs_re_eq_norm
    # |z.re| = ‖z‖ ↔ z.im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_z_repipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("z"), OVar("z_im"))), OLit(0)))
            results.append((rhs, "Mathlib: Complex_abs_re_eq_norm"))
    except Exception:
        pass
    return results


def _r0112_abs_im_eq_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.abs_im_eq_norm
    # |z.im| = ‖z‖ ↔ z.re = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_z_impipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("z"), OVar("z_re"))), OLit(0)))
            results.append((rhs, "Mathlib: Complex_abs_im_eq_norm"))
    except Exception:
        pass
    return results


def _r0113_reCLM_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.reCLM_norm
    # ‖reCLM‖ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("reCLM")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_reCLM_norm"))
    except Exception:
        pass
    return results


def _r0114_reCLM_nnnorm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.reCLM_nnnorm
    # ‖reCLM‖₊ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("reCLM")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_reCLM_nnnorm"))
    except Exception:
        pass
    return results


def _r0115_imCLM_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.imCLM_norm
    # ‖imCLM‖ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("imCLM")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_imCLM_norm"))
    except Exception:
        pass
    return results


def _r0116_imCLM_nnnorm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.imCLM_nnnorm
    # ‖imCLM‖₊ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("imCLM")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_imCLM_nnnorm"))
    except Exception:
        pass
    return results


def _r0117_ofRealCLM_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofRealCLM_norm
    # ‖ofRealCLM‖ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofRealCLM")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_ofRealCLM_norm"))
    except Exception:
        pass
    return results


def _r0118_ofRealCLM_enorm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofRealCLM_enorm
    # ‖ofRealCLM‖ₑ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofRealCLM")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_ofRealCLM_enorm"))
    except Exception:
        pass
    return results


def _r0119_ofRealCLM_nnnorm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofRealCLM_nnnorm
    # ‖ofRealCLM‖₊ = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofRealCLM")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_ofRealCLM_nnnorm"))
    except Exception:
        pass
    return results


def _r0120_interior_setOf_im_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.interior_setOf_im_le
    # interior { z : ℂ | z.im ≤ a } = { z | z.im < a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "interior", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_im_lt_a")
            results.append((rhs, "Mathlib: Complex_interior_setOf_im_le"))
        except Exception:
            pass
    return results


def _r0121_interior_setOf_le_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.interior_setOf_le_re
    # interior { z : ℂ | a ≤ z.re } = { z | a < z.re }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "interior", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_a_lt_z_re")
            results.append((rhs, "Mathlib: Complex_interior_setOf_le_re"))
        except Exception:
            pass
    return results


def _r0122_interior_setOf_le_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.interior_setOf_le_im
    # interior { z : ℂ | a ≤ z.im } = { z | a < z.im }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "interior", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_a_lt_z_im")
            results.append((rhs, "Mathlib: Complex_interior_setOf_le_im"))
        except Exception:
            pass
    return results


def _r0123_frontier_setOf_re_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.frontier_setOf_re_le
    # frontier { z : ℂ | z.re ≤ a } = { z | z.re = a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frontier", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_re_eq_a")
            results.append((rhs, "Mathlib: Complex_frontier_setOf_re_le"))
        except Exception:
            pass
    return results


def _r0124_frontier_setOf_im_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.frontier_setOf_im_le
    # frontier { z : ℂ | z.im ≤ a } = { z | z.im = a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frontier", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_im_eq_a")
            results.append((rhs, "Mathlib: Complex_frontier_setOf_im_le"))
        except Exception:
            pass
    return results


def _r0125_frontier_setOf_le_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.frontier_setOf_le_re
    # frontier { z : ℂ | a ≤ z.re } = { z | z.re = a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frontier", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_re_eq_a")
            results.append((rhs, "Mathlib: Complex_frontier_setOf_le_re"))
        except Exception:
            pass
    return results


def _r0126_frontier_setOf_le_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.frontier_setOf_le_im
    # frontier { z : ℂ | a ≤ z.im } = { z | z.im = a }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "frontier", 1)
    if args is not None:
        try:
            rhs = OVar("z_pipe_z_im_eq_a")
            results.append((rhs, "Mathlib: Complex_frontier_setOf_le_im"))
        except Exception:
            pass
    return results


def _r0127_closure_reProdIm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.closure_reProdIm
    # closure (s ×ℂ t) = closure s ×ℂ closure t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("closure", (OVar("s"), OVar("times"), OVar("closure"), OVar("t"),))
            results.append((rhs, "Mathlib: Complex_closure_reProdIm"))
        except Exception:
            pass
    return results


def _r0128_sinh_add_aux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sinh_add_aux
    # (a - b) * (c + d) + (a + b) * (c - d) = 2 * (a * c - b * d)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OLit(2), OOp("*", (OVar("a"), OOp("*", (OOp("-", (OVar("c"), OVar("b"))), OVar("d")))))))
            results.append((rhs, "Mathlib: Complex_sinh_add_aux"))
        except Exception:
            pass
    return results


def _r0129_cosh_add_aux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cosh_add_aux
    # (a + b) * (c + d) + (a - b) * (c - d) = 2 * (a * c + b * d)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OLit(2), OOp("+", (OOp("*", (OVar("a"), OVar("c"))), OOp("*", (OVar("b"), OVar("d")))))))
            results.append((rhs, "Mathlib: Complex_cosh_add_aux"))
        except Exception:
            pass
    return results


def _r0130_ofReal_sinh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_sinh
    # (Real.sinh x : ℂ) = sinh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_sinh", 3)
    if args is not None:
        try:
            rhs = OOp("sinh", (args[0],))
            results.append((rhs, "Mathlib: Complex_ofReal_sinh"))
        except Exception:
            pass
    return results


def _r0131_sinh_ofReal_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sinh_ofReal_im
    # (sinh x).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sinh_x_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_sinh_ofReal_im"))
    except Exception:
        pass
    return results


def _r0132_sinh_ofReal_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sinh_ofReal_re
    # (sinh x).re = Real.sinh x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sinh_x_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Real_sinh", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sinh_ofReal_re"))
    except Exception:
        pass
    return results


def _r0133_cosh_ofReal_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cosh_ofReal_im
    # (cosh x).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cosh_x_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_cosh_ofReal_im"))
    except Exception:
        pass
    return results


def _r0134_cosh_ofReal_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cosh_ofReal_re
    # (cosh x).re = Real.cosh x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cosh_x_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Real_cosh", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_cosh_ofReal_re"))
    except Exception:
        pass
    return results


def _r0135_tanh_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tanh_conj
    # tanh (conj x) = conj (tanh x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tanh", 1)
    if args is not None:
        try:
            rhs = OOp("conj", (OOp("tanh", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Complex_tanh_conj"))
        except Exception:
            pass
    return results


def _r0136_ofReal_tanh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_tanh
    # (Real.tanh x : ℂ) = tanh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_tanh", 3)
    if args is not None:
        try:
            rhs = OOp("tanh", (args[0],))
            results.append((rhs, "Mathlib: Complex_ofReal_tanh"))
        except Exception:
            pass
    return results


def _r0137_tanh_ofReal_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tanh_ofReal_im
    # (tanh x).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("tanh_x_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_tanh_ofReal_im"))
    except Exception:
        pass
    return results


def _r0138_tanh_ofReal_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tanh_ofReal_re
    # (tanh x).re = Real.tanh x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("tanh_x_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Real_tanh", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_tanh_ofReal_re"))
    except Exception:
        pass
    return results


def _r0139_sinh_add_cosh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sinh_add_cosh
    # sinh x + cosh x = exp x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sinh_add_cosh"))
        except Exception:
            pass
    return results


def _r0140_cosh_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cosh_sq
    # cosh x ^ 2 = sinh x ^ 2 + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("**", (OOp("sinh", (OVar("x"),)), OLit(2))), OLit(1)))
            results.append((rhs, "Mathlib: Complex_cosh_sq"))
        except Exception:
            pass
    return results


def _r0141_two_sin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.two_sin
    # 2 * sin x = (exp (-x * I) - exp (x * I)) * I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("-", (OOp("exp", (OOp("*", (OVar("minus_x"), OVar("I"))),)), OOp("exp", (OOp("*", (OVar("x"), OVar("I"))),)))), OVar("I")))
            results.append((rhs, "Mathlib: Complex_two_sin"))
        except Exception:
            pass
    return results


def _r0142_cos_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_add
    # cos (x + y) = cos x * cos y - sin x * sin y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("cos", (OVar("x"),)), OOp("*", (OOp("-", (OOp("cos", (OVar("y"),)), OOp("sin", (OVar("x"),)))), OOp("sin", (OVar("y"),))))))
            results.append((rhs, "Mathlib: Complex_cos_add"))
        except Exception:
            pass
    return results


def _r0143_ofReal_sin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_sin
    # (Real.sin x : ℂ) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_sin", 3)
    if args is not None:
        try:
            rhs = OOp("sin", (args[0],))
            results.append((rhs, "Mathlib: Complex_ofReal_sin"))
        except Exception:
            pass
    return results


def _r0144_sin_ofReal_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_ofReal_im
    # (sin x).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sin_x_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_sin_ofReal_im"))
    except Exception:
        pass
    return results


def _r0145_sin_ofReal_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_ofReal_re
    # (sin x).re = Real.sin x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sin_x_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Real_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sin_ofReal_re"))
    except Exception:
        pass
    return results


def _r0146_ofReal_cos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_cos
    # (Real.cos x : ℂ) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_cos", 3)
    if args is not None:
        try:
            rhs = OOp("cos", (args[0],))
            results.append((rhs, "Mathlib: Complex_ofReal_cos"))
        except Exception:
            pass
    return results


def _r0147_cos_ofReal_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_ofReal_im
    # (cos x).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cos_x_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_cos_ofReal_im"))
    except Exception:
        pass
    return results


def _r0148_cos_ofReal_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_ofReal_re
    # (cos x).re = Real.cos x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cos_x_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Real_cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_cos_ofReal_re"))
    except Exception:
        pass
    return results


def _r0149_tan_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tan_conj
    # tan (conj x) = conj (tan x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OOp("conj", (OOp("tan", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Complex_tan_conj"))
        except Exception:
            pass
    return results


def _r0150_ofReal_cot_ofReal_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_cot_ofReal_re
    # ((cot x).re : ℂ) = cot x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cot_x_re", 2)
    if args is not None:
        try:
            rhs = OOp("cot", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_ofReal_cot_ofReal_re"))
        except Exception:
            pass
    return results


def _r0151_ofReal_tan(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_tan
    # (Real.tan x : ℂ) = tan x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_tan", 3)
    if args is not None:
        try:
            rhs = OOp("tan", (args[0],))
            results.append((rhs, "Mathlib: Complex_ofReal_tan"))
        except Exception:
            pass
    return results


def _r0152_ofReal_cot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_cot
    # (Real.cot x : ℂ) = cot x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_cot", 3)
    if args is not None:
        try:
            rhs = OOp("cot", (args[0],))
            results.append((rhs, "Mathlib: Complex_ofReal_cot"))
        except Exception:
            pass
    return results


def _r0153_tan_ofReal_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tan_ofReal_im
    # (tan x).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("tan_x_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_tan_ofReal_im"))
    except Exception:
        pass
    return results


def _r0154_tan_ofReal_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tan_ofReal_re
    # (tan x).re = Real.tan x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("tan_x_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Real_tan", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_tan_ofReal_re"))
    except Exception:
        pass
    return results


def _r0155_exp_ofReal_mul_I_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_ofReal_mul_I_im
    # (exp (x * I)).im = Real.sin x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("exp_x_star_I_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Real_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_exp_ofReal_mul_I_im"))
    except Exception:
        pass
    return results


def _r0156_exp_ofReal_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_ofReal_mul_I
    # exp (x * I) = Real.cos x + (Real.sin x) * I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("Real_cos", (OVar("x"),)), OOp("*", (OOp("Real_sin", (OVar("x"),)), OVar("I")))))
            results.append((rhs, "Mathlib: Complex_exp_ofReal_mul_I"))
        except Exception:
            pass
    return results


def _r0157_tan_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tan_zero
    # tan 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_tan_zero"))
        except Exception:
            pass
    return results


def _r0158_cos_sq_add_sin_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_sq_add_sin_sq
    # cos x ^ 2 + sin x ^ 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_cos_sq_add_sin_sq"))
        except Exception:
            pass
    return results


def _r0159_cosh_add_sinh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cosh_add_sinh
    # cosh x + sinh x = exp x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cosh_add_sinh"))
        except Exception:
            pass
    return results


def _r0160_sinh_add_cosh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sinh_add_cosh
    # sinh x + cosh x = exp x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sinh_add_cosh"))
        except Exception:
            pass
    return results


def _r0161_norm_exp_I_mul_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_exp_I_mul_ofReal
    # ‖exp (I * x)‖ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_norm_exp_I_mul_ofReal"))
        except Exception:
            pass
    return results


def _r0162_nnnorm_exp_ofReal_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.nnnorm_exp_ofReal_mul_I
    # ‖exp (x * I)‖₊ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_nnnorm_exp_ofReal_mul_I"))
        except Exception:
            pass
    return results


def _r0163_nnnorm_exp_I_mul_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.nnnorm_exp_I_mul_ofReal
    # ‖exp (I * x)‖₊ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_nnnorm_exp_I_mul_ofReal"))
        except Exception:
            pass
    return results


def _r0164_enorm_exp_ofReal_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.enorm_exp_ofReal_mul_I
    # ‖exp (x * I)‖ₑ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_enorm_exp_ofReal_mul_I"))
        except Exception:
            pass
    return results


def _r0165_enorm_exp_I_mul_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.enorm_exp_I_mul_ofReal
    # ‖exp (I * x)‖ₑ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_enorm_exp_I_mul_ofReal"))
        except Exception:
            pass
    return results


def _r0166_norm_exp_I_mul_ofReal_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_exp_I_mul_ofReal_sub_one
    # ‖exp (I * x) - 1‖ = ‖2 * Real.sin (x / 2)‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("_2"), OOp("Real_sin", (OVar("x_slash_2"),))))
            results.append((rhs, "Mathlib: Complex_norm_exp_I_mul_ofReal_sub_one"))
        except Exception:
            pass
    return results


def _r0167_mk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.mk_coe
    # mk z hz = z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Complex_UnitDisc_mk_coe"))
        except Exception:
            pass
    return results


def _r0168_mk_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.mk_inj
    # mk z hz = mk w hw ↔ z = w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("pair", (OVar("w"), OVar("hw"),)), args[0])), OVar("w")))
            results.append((rhs, "Mathlib: Complex_UnitDisc_mk_inj"))
        except Exception:
            pass
    return results


def _r0169_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.coe_zero
    # ((0 : 𝔻) : ℂ) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_UnitDisc_coe_zero"))
        except Exception:
            pass
    return results


def _r0170_coe_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.coe_eq_zero
    # (z : ℂ) = 0 ↔ z = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("z"))), OLit(0)))
            results.append((rhs, "Mathlib: Complex_UnitDisc_coe_eq_zero"))
        except Exception:
            pass
    return results


def _r0171_mk_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.mk_zero
    # mk 0 (by simp) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_UnitDisc_mk_zero"))
        except Exception:
            pass
    return results


def _r0172_mk_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.mk_eq_zero
    # mk z hz = 0 ↔ z = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Complex_UnitDisc_mk_eq_zero"))
        except Exception:
            pass
    return results


def _r0173_im_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.im_coe
    # (z : ℂ).im = z.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_colon_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z_im")
            results.append((rhs, "Mathlib: Complex_UnitDisc_im_coe"))
    except Exception:
        pass
    return results


def _r0174_re_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.re_zero
    # re 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "re", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_UnitDisc_re_zero"))
        except Exception:
            pass
    return results


def _r0175_im_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.im_zero
    # im 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "im", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_UnitDisc_im_zero"))
        except Exception:
            pass
    return results


def _r0176_star_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.star_zero
    # star (0 : 𝔻) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "star", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_UnitDisc_star_zero"))
        except Exception:
            pass
    return results


def _r0177_norm_cast_rat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.norm_cast_rat
    # ‖(m : ℚ)‖ = ‖m‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("m")
            results.append((rhs, "Mathlib: Int_norm_cast_rat"))
    except Exception:
        pass
    return results


def _r0178_enorm_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.enorm_natCast
    # ‖(n : ℝ)‖ₑ = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Real_enorm_natCast"))
    except Exception:
        pass
    return results


def _r0179_norm_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.norm_ofNat
    # ‖(ofNat(n) : ℝ)‖ = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: Real_norm_ofNat"))
    except Exception:
        pass
    return results


def _r0180_nnnorm_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.nnnorm_ofNat
    # ‖(ofNat(n) : ℝ)‖₊ = ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofNat_n")
            results.append((rhs, "Mathlib: Real_nnnorm_ofNat"))
    except Exception:
        pass
    return results


def _r0181_norm_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.norm_two
    # ‖(2 : ℝ)‖ = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_2_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(2)
            results.append((rhs, "Mathlib: Real_norm_two"))
    except Exception:
        pass
    return results


def _r0182_nnnorm_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.nnnorm_two
    # ‖(2 : ℝ)‖₊ = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_2_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(2)
            results.append((rhs, "Mathlib: Real_nnnorm_two"))
    except Exception:
        pass
    return results


def _r0183_nnnorm_nnratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.nnnorm_nnratCast
    # ‖(q : ℝ)‖₊ = q
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q")
            results.append((rhs, "Mathlib: Real_nnnorm_nnratCast"))
    except Exception:
        pass
    return results


def _r0184_enorm_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.enorm_abs
    # ‖|r|‖ₑ = ‖r‖ₑ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_rpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("r")
            results.append((rhs, "Mathlib: Real_enorm_abs"))
    except Exception:
        pass
    return results


def _r0185_enorm_eq_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.enorm_eq_ofReal
    # ‖r‖ₑ = .ofReal r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ofReal", (OVar("r"),))
            results.append((rhs, "Mathlib: Real_enorm_eq_ofReal"))
    except Exception:
        pass
    return results


def _r0186_enorm_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.enorm_natCast
    # ‖(n : ℤ)‖ₑ = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Int_enorm_natCast"))
    except Exception:
        pass
    return results


def _r0187_sqrt_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sqrt_one
    # (1 : ℂ).sqrt = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_sqrt")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_sqrt_one"))
    except Exception:
        pass
    return results


def _r0188_sqrt_eq_real_add_ite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sqrt_eq_real_add_ite
    # a.sqrt = √((‖a‖ + a.re) / 2) + (if 0 ≤ a.im then 1 else -1) * √((‖a‖ - a.re) / 2) * I
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_sqrt")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("a_plus_a_re_slash_2"), OOp("*", (OOp("<=", (OOp("if", (OLit(0),)), OOp("a_im", (OVar("then"), OLit(1), OVar("else"), OVar("minus_1"),)))), OOp("*", (OVar("a_minus_a_re_slash_2"), OVar("I")))))))
            results.append((rhs, "Mathlib: Complex_sqrt_eq_real_add_ite"))
    except Exception:
        pass
    return results


def _r0189_re_sqrt_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.re_sqrt_ofReal
    # (sqrt (a : ℂ)).re = √a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sqrt_a_colon_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Complex_re_sqrt_ofReal"))
    except Exception:
        pass
    return results


def _r0190_cosh_arsinh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cosh_arsinh
    # cosh (arsinh x) = √(1 + x ^ 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cosh", 1)
    if args is not None:
        try:
            rhs = OVar("_1_plus_x_pow_2")
            results.append((rhs, "Mathlib: Real_cosh_arsinh"))
        except Exception:
            pass
    return results


def _r0191_tanh_arsinh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tanh_arsinh
    # tanh (arsinh x) = x / √(1 + x ^ 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tanh", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("x"), OVar("_1_plus_x_pow_2")))
            results.append((rhs, "Mathlib: Real_tanh_arsinh"))
        except Exception:
            pass
    return results


def _r0192_arsinh_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arsinh_eq_zero_iff
    # arsinh x = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arsinh", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Real_arsinh_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0193_sinh_artanh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sinh_artanh
    # sinh (artanh x) = x / √(1 - x ^ 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sinh", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("x"), OVar("_1_minus_x_pow_2")))
            results.append((rhs, "Mathlib: Real_sinh_artanh"))
        except Exception:
            pass
    return results


def _r0194_binEntropy_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.binEntropy_one
    # binEntropy 1 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "binEntropy", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_binEntropy_one"))
        except Exception:
            pass
    return results


def _r0195_qaryEntropy_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.qaryEntropy_one
    # qaryEntropy q 1 = log (q - 1 : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "qaryEntropy", 2)
    if args is not None:
        try:
            rhs = OOp("log", (OOp("-", (args[0], OOp("_1", (OVar("colon"), OVar("_unknown"),)))),))
            results.append((rhs, "Mathlib: Real_qaryEntropy_one"))
        except Exception:
            pass
    return results


def _r0196_qaryEntropy_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.qaryEntropy_two
    # qaryEntropy 2 = binEntropy
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "qaryEntropy", 1)
    if args is not None:
        try:
            rhs = OVar("binEntropy")
            results.append((rhs, "Mathlib: Real_qaryEntropy_two"))
        except Exception:
            pass
    return results


def _r0197_norm_mul_cos_arg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_mul_cos_arg
    # ‖x‖ * Real.cos (arg x) = x.re
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("x_re")
            results.append((rhs, "Mathlib: Complex_norm_mul_cos_arg"))
        except Exception:
            pass
    return results


def _r0198_norm_mul_sin_arg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_mul_sin_arg
    # ‖x‖ * Real.sin (arg x) = x.im
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("x_im")
            results.append((rhs, "Mathlib: Complex_norm_mul_sin_arg"))
        except Exception:
            pass
    return results


def _r0199_norm_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_eq_one_iff
    # ‖z‖ = 1 ↔ ∃ θ : ℝ, exp (θ * I) = z
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(1), OOp("exists", (OVar("th"), OVar("colon"), OVar("_unknown"), OVar("exp"), OOp("*", (OVar("th"), OVar("I"))),)))), OVar("z")))
            results.append((rhs, "Mathlib: Complex_norm_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0200_ext_norm_arg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ext_norm_arg
    # x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: Complex_ext_norm_arg"))
    except Exception:
        pass
    return results


def _r0201_arg_real_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_real_mul
    # arg (r * x) = arg x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("arg", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_arg_real_mul"))
        except Exception:
            pass
    return results


def _r0202_arg_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_neg_one
    # arg (-1) = π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OVar("pi")
            results.append((rhs, "Mathlib: Complex_arg_neg_one"))
        except Exception:
            pass
    return results


def _r0203_arg_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_I
    # arg I = π / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pi"), OLit(2)))
            results.append((rhs, "Mathlib: Complex_arg_I"))
        except Exception:
            pass
    return results


def _r0204_tan_arg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tan_arg
    # Real.tan (arg x) = x.im / x.re
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_tan", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("x_im"), OVar("x_re")))
            results.append((rhs, "Mathlib: Complex_tan_arg"))
        except Exception:
            pass
    return results


def _r0205_ofNat_arg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofNat_arg
    # arg ofNat(n) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_ofNat_arg"))
        except Exception:
            pass
    return results


def _r0206_arg_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_eq_zero_iff
    # arg z = 0 ↔ 0 ≤ z.re ∧ z.im = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("<=", (OOp("iff", (OLit(0), OLit(0))), OOp("and", (OVar("z_re"), OVar("z_im"))))), OLit(0)))
            results.append((rhs, "Mathlib: Complex_arg_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0207_arg_mul_eq_add_arg_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_mul_eq_add_arg_iff
    # (x * y).arg = x.arg + y.arg ↔ arg x + arg y ∈ Set.Ioc (-π) π
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_star_y_arg")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("+", (OVar("x_arg"), OVar("y_arg"))), OOp("+", (OOp("arg", (OVar("x"),)), OOp("in", (OOp("arg", (OVar("y"),)), OOp("Set_Ioc", (OVar("minus_pi"), OVar("pi"),))))))))
            results.append((rhs, "Mathlib: Complex_arg_mul_eq_add_arg_iff"))
    except Exception:
        pass
    return results


def _r0208_ofNat_log(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofNat_log
    # Real.log ofNat(n) = log (OfNat.ofNat n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_log", 1)
    if args is not None:
        try:
            rhs = OOp("log", (OOp("OfNat_ofNat", (OVar("n"),)),))
            results.append((rhs, "Mathlib: Complex_ofNat_log"))
        except Exception:
            pass
    return results


def _r0209_log_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_one
    # log 1 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_log_one"))
        except Exception:
            pass
    return results


def _r0210_log_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_neg_one
    # log (-1) = π * I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("pi"), OVar("I")))
            results.append((rhs, "Mathlib: Complex_log_neg_one"))
        except Exception:
            pass
    return results


def _r0211_log_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_I
    # log I = π / 2 * I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("//", (OVar("pi"), OLit(2))), args[0]))
            results.append((rhs, "Mathlib: Complex_log_I"))
        except Exception:
            pass
    return results


def _r0212_map_exp_comap_re_atTop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.map_exp_comap_re_atTop
    # map exp (comap re atTop) = cobounded ℂ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("cobounded", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: Complex_map_exp_comap_re_atTop"))
        except Exception:
            pass
    return results


def _r0213_rpowIntegrand_0_1_zero_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpowIntegrand₀₁_zero_left
    # rpowIntegrand₀₁ p 0 x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rpowIntegrand_0_1", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_rpowIntegrand_0_1_zero_left"))
        except Exception:
            pass
    return results


def _r0214_coe_comp_expOrderIso(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.coe_comp_expOrderIso
    # (↑) ∘ expOrderIso = exp
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("exp")
            results.append((rhs, "Mathlib: Real_coe_comp_expOrderIso"))
        except Exception:
            pass
    return results


def _r0215_map_exp_atTop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.map_exp_atTop
    # map exp atTop = atTop
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Real_map_exp_atTop"))
        except Exception:
            pass
    return results


def _r0216_comap_exp_atTop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.comap_exp_atTop
    # comap exp atTop = atTop
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Real_comap_exp_atTop"))
        except Exception:
            pass
    return results


def _r0217_comap_exp_nhdsGT_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.comap_exp_nhdsGT_zero
    # comap exp (𝓝[>] 0) = atBot
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 2)
    if args is not None:
        try:
            rhs = OVar("atBot")
            results.append((rhs, "Mathlib: Real_comap_exp_nhdsGT_zero"))
        except Exception:
            pass
    return results


def _r0218_comap_exp_nhds_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.comap_exp_nhds_exp
    # comap exp (𝓝 (exp x)) = 𝓝 x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_comap_exp_nhds_exp"))
        except Exception:
            pass
    return results


def _r0219_deriv_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.deriv_exp
    # deriv exp = exp
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "deriv", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Complex_deriv_exp"))
        except Exception:
            pass
    return results


def _r0220_iter_deriv_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.iter_deriv_exp
    # ∀ n : ℕ, deriv^[n] exp = exp   | 0 => rfl   | n + 1 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "derivpow_n", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("exp", (OVar("pipe"), OLit(0), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("n"),)), OOp("_1", (OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Complex_iter_deriv_exp"))
        except Exception:
            pass
    return results


def _r0221_deriv_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.deriv_exp
    # deriv exp = exp
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "deriv", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Real_deriv_exp"))
        except Exception:
            pass
    return results


def _r0222_iter_deriv_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.iter_deriv_exp
    # ∀ n : ℕ, deriv^[n] exp = exp   | 0 => rfl   | n + 1 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "derivpow_n", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("exp", (OVar("pipe"), OLit(0), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("n"),)), OOp("_1", (OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Real_iter_deriv_exp"))
        except Exception:
            pass
    return results


def _r0223_Gamma_ofReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.Gamma_ofReal
    # Complex.Gamma (s : ℂ) = Gamma s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Complex_Gamma", 1)
    if args is not None:
        try:
            rhs = OOp("Gamma", (OVar("s"),))
            results.append((rhs, "Mathlib: Complex_Gamma_ofReal"))
        except Exception:
            pass
    return results


def _r0224_digamma_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.digamma_one
    # digamma 1 = - Real.eulerMascheroniConstant
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "digamma", 1)
    if args is not None:
        try:
            rhs = OOp("minus", (OVar("Real_eulerMascheroniConstant"),))
            results.append((rhs, "Mathlib: Complex_digamma_one"))
        except Exception:
            pass
    return results


def _r0225_logb_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_one
    # logb b 1 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_logb_one"))
        except Exception:
            pass
    return results


def _r0226_logb_zero_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_zero_left
    # logb 0 x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_logb_zero_left"))
        except Exception:
            pass
    return results


def _r0227_logb_one_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_one_left
    # logb 1 x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_logb_one_left"))
        except Exception:
            pass
    return results


def _r0228_logb_one_left_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_one_left_eq_zero
    # logb 1 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_logb_one_left_eq_zero"))
        except Exception:
            pass
    return results


def _r0229_logb_self_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_self_eq_one
    # logb b b = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_logb_self_eq_one"))
        except Exception:
            pass
    return results


def _r0230_logb_self_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_self_eq_one_iff
    # logb b b = 1 ↔ b ≠ 0 ∧ b ≠ 1 ∧ b ≠ -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OLit(1), args[1])), OOp("!=", (OOp("and", (OLit(0), args[1])), OOp("!=", (OOp("and", (OLit(1), args[1])), OVar("minus_1")))))))
            results.append((rhs, "Mathlib: Real_logb_self_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0231_logb_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_mul
    # logb b (x * y) = logb b x + logb b y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("logb", (args[0], OVar("x"),)), OOp("logb", (args[0], OVar("y"),))))
            results.append((rhs, "Mathlib: Real_logb_mul"))
        except Exception:
            pass
    return results


def _r0232_log_comp_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.log_comp_exp
    # log ∘ exp = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Real_log_comp_exp"))
        except Exception:
            pass
    return results


def _r0233_log_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.log_zero
    # log 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_log_zero"))
        except Exception:
            pass
    return results


def _r0234_log_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.log_one
    # log 1 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_log_one"))
        except Exception:
            pass
    return results


def _r0235_sinh_log(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sinh_log
    # sinh (log x) = (x - x⁻¹) / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sinh", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("-", (OVar("x"), OVar("xinv"))), OLit(2)))
            results.append((rhs, "Mathlib: Real_sinh_log"))
        except Exception:
            pass
    return results


def _r0236_deriv_log(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.deriv_log
    # deriv log x = x⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "deriv", 2)
    if args is not None:
        try:
            rhs = OVar("xinv")
            results.append((rhs, "Mathlib: Real_deriv_log"))
        except Exception:
            pass
    return results


def _r0237_negMulLog_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.negMulLog_one
    # negMulLog (1 : ℝ) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "negMulLog", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_negMulLog_one"))
        except Exception:
            pass
    return results


def _r0238_posLog_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.posLog_one
    # log⁺ 1 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logpos", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_posLog_one"))
        except Exception:
            pass
    return results


def _r0239_posLog_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.posLog_eq_zero_iff
    # log⁺ x = 0 ↔ |x| ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logpos", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OLit(0), OVar("pipe_xpipe"))), OLit(1)))
            results.append((rhs, "Mathlib: Real_posLog_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0240_cpow_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_def
    # x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0],)), OOp("==", (OOp("_0", (OVar("then"), OVar("if"), args[1],)), OOp("_0", (OVar("then"), OLit(1), OVar("else"), OLit(0), OVar("else"), OVar("exp"), OOp("*", (OOp("log", (args[0],)), args[1])),))))))
            results.append((rhs, "Mathlib: Complex_cpow_def"))
        except Exception:
            pass
    return results


def _r0241_cpow_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_eq_zero_iff
    # x ^ y = 0 ↔ x = 0 ∧ y ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OOp("!=", (OOp("and", (OLit(0), args[1])), OLit(0)))))
            results.append((rhs, "Mathlib: Complex_cpow_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0242_zero_cpow_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.zero_cpow_eq_iff
    # (0 : ℂ) ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("!=", (OOp("iff", (OVar("a"), args[1])), OOp("and", (OLit(0), OVar("a"))))), OOp("==", (OOp("or", (OLit(0), args[1])), OOp("==", (OOp("and", (OLit(0), OVar("a"))), OLit(1)))))))
            results.append((rhs, "Mathlib: Complex_zero_cpow_eq_iff"))
        except Exception:
            pass
    return results


def _r0243_cpow_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_ofNat
    # x ^ (ofNat(n) : ℂ) = x ^ ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OVar("ofNat_n")))
            results.append((rhs, "Mathlib: Complex_cpow_ofNat"))
        except Exception:
            pass
    return results


def _r0244_nthRoot_one_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.nthRoot_one_left
    # nthRoot 1 = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nthRoot", 1)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Nat_nthRoot_one_left"))
        except Exception:
            pass
    return results


def _r0245_nthRoot_zero_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.nthRoot_zero_right
    # nthRoot n 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nthRoot", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Nat_nthRoot_zero_right"))
        except Exception:
            pass
    return results


def _r0246_nthRoot_one_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.nthRoot_one_right
    # nthRoot n 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nthRoot", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Nat_nthRoot_one_right"))
        except Exception:
            pass
    return results


def _r0247_nthRoot_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.nthRoot_pow
    # nthRoot n (a ^ n) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nthRoot", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Nat_nthRoot_pow"))
        except Exception:
            pass
    return results


def _r0248_rpow_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_def
    # x ^ y = ((x : ℂ) ^ (y : ℂ)).re
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x_colon_pow_y_colon_re")
            results.append((rhs, "Mathlib: Real_rpow_def"))
        except Exception:
            pass
    return results


def _r0249_rpow_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_ofNat
    # x ^ (ofNat(n) : ℝ) = x ^ (ofNat(n) : ℕ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OOp("ofNat_n", (OVar("colon"), OVar("_unknown"),))))
            results.append((rhs, "Mathlib: Real_rpow_ofNat"))
        except Exception:
            pass
    return results


def _r0250_exp_one_rpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.exp_one_rpow
    # exp 1 ^ x = exp x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (args[1],))
            results.append((rhs, "Mathlib: Real_exp_one_rpow"))
        except Exception:
            pass
    return results


def _r0251_exp_one_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.exp_one_pow
    # exp 1 ^ n = exp n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (args[1],))
            results.append((rhs, "Mathlib: Real_exp_one_pow"))
        except Exception:
            pass
    return results


def _r0252_rpow_eq_zero_iff_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_eq_zero_iff_of_nonneg
    # x ^ y = 0 ↔ x = 0 ∧ y ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OOp("!=", (OOp("and", (OLit(0), args[1])), OLit(0)))))
            results.append((rhs, "Mathlib: Real_rpow_eq_zero_iff_of_nonneg"))
        except Exception:
            pass
    return results


def _r0253_zero_rpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.zero_rpow
    # (0 : ℝ) ^ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_zero_rpow"))
        except Exception:
            pass
    return results


def _r0254_zero_rpow_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.zero_rpow_eq_iff
    # 0 ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("!=", (OOp("iff", (OVar("a"), args[1])), OOp("and", (OLit(0), OVar("a"))))), OOp("==", (OOp("or", (OLit(0), args[1])), OOp("==", (OOp("and", (OLit(0), OVar("a"))), OLit(1)))))))
            results.append((rhs, "Mathlib: Real_zero_rpow_eq_iff"))
        except Exception:
            pass
    return results


def _r0255_pi_rpow_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.pi_rpow_one
    # f ^ (1 : ℝ) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Real_pi_rpow_one"))
        except Exception:
            pass
    return results


def _r0256_one_rpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.one_rpow
    # (1 : ℝ) ^ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_one_rpow"))
        except Exception:
            pass
    return results


def _r0257_norm_cpow_eq_rpow_re_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_cpow_eq_rpow_re_of_pos
    # ‖(x : ℂ) ^ y‖ = x ^ y.re
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("x"), OVar("y_re")))
            results.append((rhs, "Mathlib: Complex_norm_cpow_eq_rpow_re_of_pos"))
        except Exception:
            pass
    return results


def _r0258_zero_of_nonpos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.smoothTransition.zero_of_nonpos
    # smoothTransition x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "smoothTransition", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_smoothTransition_zero_of_nonpos"))
        except Exception:
            pass
    return results


def _r0259_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.smoothTransition.one
    # smoothTransition 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "smoothTransition", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_smoothTransition_one"))
        except Exception:
            pass
    return results


def _r0260_zsmul_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.zsmul_eq_iff
    # z • ψ = z • θ ↔ ∃ k : Fin z.natAbs, ψ = θ + (k : ℕ) • (2 * π / z : ℝ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("z", (args[0], OVar("th"),)), OOp("exists", (OVar("k"), OVar("colon"), OVar("Fin"), OVar("z_natAbs"), args[1],)))), OOp("+", (OVar("th"), OOp("k_colon", (args[0], OOp("*", (OLit(2), OOp("//", (OVar("pi"), OOp("z", (OVar("colon"), args[0],)))))),))))))
            results.append((rhs, "Mathlib: Real_Angle_zsmul_eq_iff"))
        except Exception:
            pass
    return results


def _r0261_cos_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_zero
    # cos (0 : Angle) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_Angle_cos_zero"))
        except Exception:
            pass
    return results


def _r0262_cos_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_eq_zero_iff
    # cos θ = 0 ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OOp("==", (OOp("or", (OOp("//", (OVar("pi"), OOp("_2", (OVar("colon"), OVar("_unknown"),)))), args[0])), OOp("//", (OVar("minus_pi"), OOp("_2", (OVar("colon"), OVar("_unknown"),))))))))
            results.append((rhs, "Mathlib: Real_Angle_cos_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0263_tan_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.tan_zero
    # tan (0 : Angle) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_Angle_tan_zero"))
        except Exception:
            pass
    return results


def _r0264_sign_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sign_eq_zero_iff
    # θ.sign = 0 ↔ θ = 0 ∨ θ = π
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("th_sign")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("th"))), OOp("==", (OOp("or", (OLit(0), OVar("th"))), OVar("pi")))))
            results.append((rhs, "Mathlib: Real_Angle_sign_eq_zero_iff"))
    except Exception:
        pass
    return results


def _r0265_arctan_tan(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_tan
    # arctan (tan x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arctan", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Real_arctan_tan"))
        except Exception:
            pass
    return results


def _r0266_arctan_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_eq_zero_iff
    # arctan x = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arctan", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Real_arctan_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0267_arctan_sqrt_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_sqrt_three
    # arctan (√3) = π / 3
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arctan", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pi"), OLit(3)))
            results.append((rhs, "Mathlib: Real_arctan_sqrt_three"))
        except Exception:
            pass
    return results


def _r0268_arctan_eq_arccos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_eq_arccos
    # arctan x = arccos (√(1 + x ^ 2))⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arctan", 1)
    if args is not None:
        try:
            rhs = OOp("arccos", (OVar("_1_plus_x_pow_2_inv"),))
            results.append((rhs, "Mathlib: Real_arctan_eq_arccos"))
        except Exception:
            pass
    return results


def _r0269_cos_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi
    # cos π = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Real_cos_pi"))
        except Exception:
            pass
    return results


def _r0270_cos_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_two_pi
    # cos (2 * π) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_cos_two_pi"))
        except Exception:
            pass
    return results


def _r0271_sin_add_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_add_two_pi
    # sin (x + 2 * π) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_add_two_pi"))
        except Exception:
            pass
    return results


def _r0272_sin_nat_mul_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_nat_mul_pi
    # sin (n * π) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_sin_nat_mul_pi"))
        except Exception:
            pass
    return results


def _r0273_sin_int_mul_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_int_mul_pi
    # sin (n * π) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_sin_int_mul_pi"))
        except Exception:
            pass
    return results


def _r0274_sin_add_nat_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_add_nat_mul_two_pi
    # sin (x + n * (2 * π)) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_add_nat_mul_two_pi"))
        except Exception:
            pass
    return results


def _r0275_sin_add_int_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_add_int_mul_two_pi
    # sin (x + n * (2 * π)) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_add_int_mul_two_pi"))
        except Exception:
            pass
    return results


def _r0276_sin_add_int_mul_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_add_int_mul_pi
    # sin (x + n * π) = (-1) ^ n * sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("sin", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_sin_add_int_mul_pi"))
        except Exception:
            pass
    return results


def _r0277_cos_add_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_add_pi
    # cos (x + π) = -cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("minus_cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_add_pi"))
        except Exception:
            pass
    return results


def _r0278_cos_add_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_add_two_pi
    # cos (x + 2 * π) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_add_two_pi"))
        except Exception:
            pass
    return results


def _r0279_cos_nat_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_nat_mul_two_pi
    # cos (n * (2 * π)) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_cos_nat_mul_two_pi"))
        except Exception:
            pass
    return results


def _r0280_cos_int_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_int_mul_two_pi
    # cos (n * (2 * π)) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_cos_int_mul_two_pi"))
        except Exception:
            pass
    return results


def _r0281_cos_add_nat_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_add_nat_mul_two_pi
    # cos (x + n * (2 * π)) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_add_nat_mul_two_pi"))
        except Exception:
            pass
    return results


def _r0282_cos_add_int_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_add_int_mul_two_pi
    # cos (x + n * (2 * π)) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_add_int_mul_two_pi"))
        except Exception:
            pass
    return results


def _r0283_cos_add_int_mul_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_add_int_mul_pi
    # cos (x + n * π) = (-1) ^ n * cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("cos", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_cos_add_int_mul_pi"))
        except Exception:
            pass
    return results


def _r0284_range_sin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.range_sin
    # range sin = (Icc (-1) 1 : Set ℝ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("Icc", (OVar("minus_1"), OLit(1), OVar("colon"), OVar("Set"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: Real_range_sin"))
        except Exception:
            pass
    return results


def _r0285_cos_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_pi
    # cos π = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Complex_cos_pi"))
        except Exception:
            pass
    return results


def _r0286_sin_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_two_pi
    # sin (2 * π) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_sin_two_pi"))
        except Exception:
            pass
    return results


def _r0287_cos_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_two_pi
    # cos (2 * π) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_cos_two_pi"))
        except Exception:
            pass
    return results


def _r0288_exp_two_pi_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_two_pi_mul_I
    # exp (2 * π * I) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_exp_two_pi_mul_I"))
        except Exception:
            pass
    return results


def _r0289_exp_int_mul_two_pi_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_int_mul_two_pi_mul_I
    # exp (n * (2 * π * I)) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_exp_int_mul_two_pi_mul_I"))
        except Exception:
            pass
    return results


def _r0290_exp_add_pi_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_add_pi_mul_I
    # exp (z + π * I) = -exp z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OOp("minus_exp", (OVar("z"),))
            results.append((rhs, "Mathlib: Complex_exp_add_pi_mul_I"))
        except Exception:
            pass
    return results


def _r0291_deriv_tan(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.deriv_tan
    # deriv tan x = 1 / cos x ^ 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "deriv", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OLit(1), OOp("**", (OOp("cos", (args[1],)), OLit(2)))))
            results.append((rhs, "Mathlib: Complex_deriv_tan"))
        except Exception:
            pass
    return results


def _r0292_sinh_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sinh_eq_zero
    # sinh x = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sinh", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Real_sinh_eq_zero"))
        except Exception:
            pass
    return results


def _r0293_arcsin_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arcsin_one
    # arcsin 1 = π / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arcsin", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pi"), OLit(2)))
            results.append((rhs, "Mathlib: Real_arcsin_one"))
        except Exception:
            pass
    return results


def _r0294_arcsin_of_one_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arcsin_of_one_le
    # arcsin x = π / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arcsin", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pi"), OLit(2)))
            results.append((rhs, "Mathlib: Real_arcsin_of_one_le"))
        except Exception:
            pass
    return results


def _r0295_arcsin_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arcsin_eq_zero_iff
    # arcsin x = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arcsin", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Real_arcsin_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0296_zero_eq_arcsin_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.zero_eq_arcsin_iff
    # 0 = arcsin x ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    if _is_lit(term, 0):
        try:
            rhs = OOp("==", (OOp("iff", (OOp("arcsin", (OVar("x"),)), OVar("x"))), OLit(0)))
            results.append((rhs, "Mathlib: Real_zero_eq_arcsin_iff"))
        except Exception:
            pass
    return results


def _r0297_cos_arccos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_arccos
    # cos (arccos x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Real_cos_arccos"))
        except Exception:
            pass
    return results


def _r0298_arccos_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arccos_one
    # arccos 1 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arccos", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Real_arccos_one"))
        except Exception:
            pass
    return results


def _r0299_arccos_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arccos_neg_one
    # arccos (-1) = π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arccos", 1)
    if args is not None:
        try:
            rhs = OVar("pi")
            results.append((rhs, "Mathlib: Real_arccos_neg_one"))
        except Exception:
            pass
    return results


def _r0300_arccos_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arccos_eq_zero
    # arccos x = 0 ↔ 1 ≤ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arccos", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OLit(0), OLit(1))), args[0]))
            results.append((rhs, "Mathlib: Real_arccos_eq_zero"))
        except Exception:
            pass
    return results


def _r0301_arccos_eq_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arccos_eq_pi
    # arccos x = π ↔ x ≤ -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arccos", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OVar("pi"), args[0])), OVar("minus_1")))
            results.append((rhs, "Mathlib: Real_arccos_eq_pi"))
        except Exception:
            pass
    return results


def _r0302_sinc_of_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sinc_of_ne_zero
    # sinc x = sin x / x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sinc", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("sin", (args[0],)), args[0]))
            results.append((rhs, "Mathlib: Real_sinc_of_ne_zero"))
        except Exception:
            pass
    return results


def _r0303_toEndHom_trivial_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Action.FintypeCat.toEndHom_trivial_of_mem
    # toEndHom N n = 𝟙 (G ⧸ₐ N)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toEndHom", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("G", (OVar("_unknown"), args[0],)),))
            results.append((rhs, "Mathlib: Action_FintypeCat_toEndHom_trivial_of_mem"))
        except Exception:
            pass
    return results


def _r0304_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NatTrans.congr
    # α.app X = F.map (eqToHom h) ≫ α.app Y ≫ G.map (eqToHom h.symm)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_app", 1)
    if args is not None:
        try:
            rhs = OOp("F_map", (OOp("eqToHom", (OVar("h"),)), OVar("_unknown"), OVar("a_app"), OVar("Y"), OVar("_unknown"), OVar("G_map"), OOp("eqToHom", (OVar("h_symm"),)),))
            results.append((rhs, "Mathlib: NatTrans_congr"))
        except Exception:
            pass
    return results


def _r0305_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FintypeCat.comp_apply
    # (f ≫ g) x = g (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: FintypeCat_comp_apply"))
        except Exception:
            pass
    return results


def _r0306_hom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FintypeCat.hom_apply
    # f.hom x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_hom", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: FintypeCat_hom_apply"))
        except Exception:
            pass
    return results


def _r0307_id_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FintypeCat.id_hom
    # 𝟙 X.obj = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 1)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: FintypeCat_id_hom"))
        except Exception:
            pass
    return results


def _r0308_comp_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FintypeCat.comp_hom
    # f.hom ≫ g.hom = g.hom ∘ f.hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_hom", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (args[1], OVar("f_hom")))
            results.append((rhs, "Mathlib: FintypeCat_comp_hom"))
        except Exception:
            pass
    return results


def _r0309_homMk_eq_id_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FintypeCat.homMk_eq_id_iff
    # homMk f = 𝟙 X ↔ f = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homMk", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("_1", (OVar("X"),)), args[0])), OVar("id")))
            results.append((rhs, "Mathlib: FintypeCat_homMk_eq_id_iff"))
        except Exception:
            pass
    return results


def _r0310_op_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NatTrans.op_comp
    # NatTrans.op (α ≫ β) = NatTrans.op β ≫ NatTrans.op α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NatTrans_op", 1)
    if args is not None:
        try:
            rhs = OOp("NatTrans_op", (OVar("b"), OVar("_unknown"), OVar("NatTrans_op"), OVar("a"),))
            results.append((rhs, "Mathlib: NatTrans_op_comp"))
        except Exception:
            pass
    return results


def _r0311_unop_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NatTrans.unop_comp
    # NatTrans.unop (α ≫ β) = NatTrans.unop β ≫ NatTrans.unop α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NatTrans_unop", 1)
    if args is not None:
        try:
            rhs = OOp("NatTrans_unop", (OVar("b"), OVar("_unknown"), OVar("NatTrans_unop"), OVar("a"),))
            results.append((rhs, "Mathlib: NatTrans_unop_comp"))
        except Exception:
            pass
    return results


def _r0312_op_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NatIso.op_trans
    # NatIso.op (α ≪≫ β) = NatIso.op β ≪≫ NatIso.op α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NatIso_op", 1)
    if args is not None:
        try:
            rhs = OOp("NatIso_op", (OVar("b"), OVar("_unknown"), OVar("NatIso_op"), OVar("a"),))
            results.append((rhs, "Mathlib: NatIso_op_trans"))
        except Exception:
            pass
    return results


def _r0313_unop_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NatIso.unop_trans
    # NatIso.unop (α ≪≫ β) = NatIso.unop β ≪≫ NatIso.unop α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NatIso_unop", 1)
    if args is not None:
        try:
            rhs = OOp("NatIso_unop", (OVar("b"), OVar("_unknown"), OVar("NatIso_unop"), OVar("a"),))
            results.append((rhs, "Mathlib: NatIso_unop_trans"))
        except Exception:
            pass
    return results


def _r0314_op_isoWhiskerRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NatIso.op_isoWhiskerRight
    # NatIso.op (isoWhiskerRight α H) =     (Functor.opComp _ _) ≪≫ isoWhiskerRight (NatIso.op α) H.op ≪≫ (Functor.opComp _ _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NatIso_op", 1)
    if args is not None:
        try:
            rhs = OOp("Functor_opComp", (OVar("_unknown"), OVar("isoWhiskerRight"), OOp("NatIso_op", (OVar("a"),)), OVar("H_op"), OVar("_unknown"), OVar("Functor_opComp_symm"),))
            results.append((rhs, "Mathlib: NatIso_op_isoWhiskerRight"))
        except Exception:
            pass
    return results


def _r0315_card_mul_divConst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.card_mul_divConst
    # #A * δₘ[A, B] = #(A / B)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("hash_A_slash_B")
            results.append((rhs, "Mathlib: Finset_card_mul_divConst"))
        except Exception:
            pass
    return results


def _r0316_mulConst_empty_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.mulConst_empty_left
    # σₘ[∅, B] = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sig_empty_B")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Finset_mulConst_empty_left"))
    except Exception:
        pass
    return results


def _r0317_divConst_empty_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.divConst_empty_left
    # δₘ[∅, B] = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("d_empty_B")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Finset_divConst_empty_left"))
    except Exception:
        pass
    return results


def _r0318_mulConst_empty_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.mulConst_empty_right
    # σₘ[A, ∅] = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sig_A_empty")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Finset_mulConst_empty_right"))
    except Exception:
        pass
    return results


def _r0319_divConst_empty_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.divConst_empty_right
    # δₘ[A, ∅] = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("d_A_empty")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Finset_divConst_empty_right"))
    except Exception:
        pass
    return results


def _r0320_mulConst_inv_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.mulConst_inv_right
    # σₘ[A, B⁻¹] = δₘ[A, B]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sig_A_Binv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("d_A_B")
            results.append((rhs, "Mathlib: Finset_mulConst_inv_right"))
    except Exception:
        pass
    return results


def _r0321_divConst_inv_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.divConst_inv_right
    # δₘ[A, B⁻¹] = σₘ[A, B]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("d_A_Binv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("sig_A_B")
            results.append((rhs, "Mathlib: Finset_divConst_inv_right"))
    except Exception:
        pass
    return results


def _r0322_mulEnergy_empty_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.mulEnergy_empty_right
    # Eₘ[s, ∅] = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("E_s_empty")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Finset_mulEnergy_empty_right"))
    except Exception:
        pass
    return results


def _r0323_mulEnergy_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.mulEnergy_eq_zero_iff
    # Eₘ[s, t] = 0 ↔ s = ∅ ∨ t = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("E_s_t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("s"))), OOp("==", (OOp("or", (OVar("empty"), OVar("t"))), OVar("empty")))))
            results.append((rhs, "Mathlib: Finset_mulEnergy_eq_zero_iff"))
    except Exception:
        pass
    return results


def _r0324_bell_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.bell_one
    # Nat.bell 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Nat_bell", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Nat_bell_one"))
        except Exception:
            pass
    return results


def _r0325_bell_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.bell_two
    # Nat.bell 2 = 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Nat_bell", 1)
    if args is not None:
        try:
            rhs = OLit(2)
            results.append((rhs, "Mathlib: Nat_bell_two"))
        except Exception:
            pass
    return results


def _r0326_coe_bipartiteAbove(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.coe_bipartiteAbove
    # t.bipartiteAbove r a = ({b ∈ t | r a b} : Set β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "t_bipartiteAbove", 2)
    if args is not None:
        try:
            rhs = OOp("b_in_t_pipe_r_a_b", (OVar("colon"), OVar("Set"), OVar("b"),))
            results.append((rhs, "Mathlib: Finset_coe_bipartiteAbove"))
        except Exception:
            pass
    return results


def _r0327_prod_prod_bipartiteAbove_eq_prod_prod_bi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow
    # ∏ a ∈ s, ∏ b ∈ t.bipartiteAbove r a, f a b = ∏ b ∈ t, ∏ a ∈ s.bipartiteBelow r b, f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("b"),)), OOp("in", (OOp("t", (OVar("_unknown"), OVar("a"),)), OOp("s_bipartiteBelow", (OVar("r"), OVar("b"), OVar("f"), OVar("a"), OVar("b"),))))))
            results.append((rhs, "Mathlib: Finset_prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow"))
        except Exception:
            pass
    return results


def _r0328_partition_zero_parts(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.Partition.partition_zero_parts
    # p.parts = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_parts")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Nat_Partition_partition_zero_parts"))
    except Exception:
        pass
    return results


def _r0329_count_ofSums_of_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.Partition.count_ofSums_of_ne_zero
    # (ofSums n l hl).parts.count i = l.count i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofSums_n_l_hl_parts_count", 1)
    if args is not None:
        try:
            rhs = OOp("l_count", (args[0],))
            results.append((rhs, "Mathlib: Nat_Partition_count_ofSums_of_ne_zero"))
        except Exception:
            pass
    return results


def _r0330_largeSchroder_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.largeSchroder_one
    # largeSchroder 1 = 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "largeSchroder", 1)
    if args is not None:
        try:
            rhs = OLit(2)
            results.append((rhs, "Mathlib: Nat_largeSchroder_one"))
        except Exception:
            pass
    return results


def _r0331_smallSchroder_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.smallSchroder_one
    # smallSchroder 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "smallSchroder", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Nat_smallSchroder_one"))
        except Exception:
            pass
    return results


def _r0332_stirlingFirst_zero_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.stirlingFirst_zero_succ
    # stirlingFirst 0 (succ k) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stirlingFirst", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Nat_stirlingFirst_zero_succ"))
        except Exception:
            pass
    return results


def _r0333_stirlingFirst_succ_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.stirlingFirst_succ_zero
    # stirlingFirst (succ n) 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stirlingFirst", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Nat_stirlingFirst_succ_zero"))
        except Exception:
            pass
    return results


def _r0334_stirlingSecond_zero_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.stirlingSecond_zero_succ
    # stirlingSecond 0 (succ k) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stirlingSecond", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Nat_stirlingSecond_zero_succ"))
        except Exception:
            pass
    return results


def _r0335_stirlingSecond_succ_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.stirlingSecond_succ_zero
    # stirlingSecond (succ n) 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "stirlingSecond", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Nat_stirlingSecond_succ_zero"))
        except Exception:
            pass
    return results


def _r0336_truncatedSup_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.truncatedSup_singleton
    # truncatedSup {b} a = if a ≤ b then b else ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "truncatedSup", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("if", (args[1],)), OOp("b", (OVar("then"), args[0], OVar("else"), OVar("top"),))))
            results.append((rhs, "Mathlib: Finset_truncatedSup_singleton"))
        except Exception:
            pass
    return results


def _r0337_shadow_iterate_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.shadow_iterate_empty
    # ∂^[k] (∅ : Finset (Finset α)) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pow_k", 1)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Finset_shadow_iterate_empty"))
        except Exception:
            pass
    return results


def _r0338_shadow_singleton_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.shadow_singleton_empty
    # ∂ ({∅} : Finset (Finset α)) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Finset_shadow_singleton_empty"))
        except Exception:
            pass
    return results


def _r0339_shadow_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.shadow_singleton
    # ∂ {{a}} = {∅}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Finset_shadow_singleton"))
        except Exception:
            pass
    return results


def _r0340_shatterer_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.shatterer_eq
    # 𝒜.shatterer = 𝒜 ↔ IsLowerSet (𝒜 : Set (Finset α))
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("shatterer")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("_unknown"), OOp("IsLowerSet", (OOp("_unknown", (OVar("colon"), OVar("Set"), OOp("Finset", (OVar("a"),)),)),))))
            results.append((rhs, "Mathlib: Finset_shatterer_eq"))
    except Exception:
        pass
    return results


def _r0341_ofEquiv_F(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ctop.Realizer.ofEquiv_F
    # (F.ofEquiv E).F s = F.F (E.symm s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_ofEquiv_E_F", 1)
    if args is not None:
        try:
            rhs = OOp("F_F", (OOp("E_symm", (args[0],)),))
            results.append((rhs, "Mathlib: Ctop_Realizer_ofEquiv_F"))
        except Exception:
            pass
    return results


def _r0342_nhds_F(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ctop.Realizer.nhds_F
    # (F.nhds a).F s = F.F s.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_nhds_a_F", 1)
    if args is not None:
        try:
            rhs = OOp("F_F", (OVar("s_1"),))
            results.append((rhs, "Mathlib: Ctop_Realizer_nhds_F"))
        except Exception:
            pass
    return results


def _r0343_ofReal_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_im
    # (r : ℂ).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_colon_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_ofReal_im"))
    except Exception:
        pass
    return results


def _r0344_ofReal_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_def
    # (r : ℂ) = ⟨r, 0⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r", 2)
    if args is not None:
        try:
            rhs = OVar("r_0")
            results.append((rhs, "Mathlib: Complex_ofReal_def"))
        except Exception:
            pass
    return results


def _r0345_zero_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.zero_im
    # (0 : ℂ).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_zero_im"))
    except Exception:
        pass
    return results


def _r0346_ofReal_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_zero
    # ((0 : ℝ) : ℂ) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_ofReal_zero"))
        except Exception:
            pass
    return results


def _r0347_ofReal_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_eq_zero
    # (z : ℂ) = 0 ↔ z = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("z"))), OLit(0)))
            results.append((rhs, "Mathlib: Complex_ofReal_eq_zero"))
        except Exception:
            pass
    return results


def _r0348_one_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.one_im
    # (1 : ℂ).im = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_one_im"))
    except Exception:
        pass
    return results


def _r0349_ofReal_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_one
    # ((1 : ℝ) : ℂ) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_ofReal_one"))
        except Exception:
            pass
    return results


def _r0350_ofReal_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_eq_one
    # (z : ℂ) = 1 ↔ z = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("z"))), OLit(1)))
            results.append((rhs, "Mathlib: Complex_ofReal_eq_one"))
        except Exception:
            pass
    return results


def _r0351_add_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.add_im
    # (z + w).im = z.im + w.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_plus_w_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("z_im"), OVar("w_im")))
            results.append((rhs, "Mathlib: Complex_add_im"))
    except Exception:
        pass
    return results


def _r0352_ofReal_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_add
    # ((r + s : ℝ) : ℂ) = r + s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r_plus_s_colon", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("r"), OVar("s")))
            results.append((rhs, "Mathlib: Complex_ofReal_add"))
        except Exception:
            pass
    return results


def _r0353_mul_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.mul_im
    # (z * w).im = z.re * w.im + z.im * w.re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_star_w_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OOp("*", (OVar("z_re"), OVar("w_im"))), OOp("*", (OVar("z_im"), OVar("w_re")))))
            results.append((rhs, "Mathlib: Complex_mul_im"))
    except Exception:
        pass
    return results


def _r0354_ofReal_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_mul
    # ((r * s : ℝ) : ℂ) = r * s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r_star_s_colon", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("r"), OVar("s")))
            results.append((rhs, "Mathlib: Complex_ofReal_mul"))
        except Exception:
            pass
    return results


def _r0355_re_ofReal_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.re_ofReal_mul
    # (r * z).re = r * z.re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_star_z_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("r"), OVar("z_re")))
            results.append((rhs, "Mathlib: Complex_re_ofReal_mul"))
    except Exception:
        pass
    return results


def _r0356_I_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.I_im
    # I.im = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("I_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_I_im"))
    except Exception:
        pass
    return results


def _r0357_I_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.I_mul_I
    # I * I = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Complex_I_mul_I"))
        except Exception:
            pass
    return results


def _r0358_I_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.I_mul
    # I * z = ⟨-z.im, z.re⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("minus_z_im_z_re")
            results.append((rhs, "Mathlib: Complex_I_mul"))
        except Exception:
            pass
    return results


def _r0359_mk_eq_add_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.mk_eq_add_mul_I
    # Complex.mk a b = a + b * I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Complex_mk", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], OOp("*", (args[1], OVar("I")))))
            results.append((rhs, "Mathlib: Complex_mk_eq_add_mul_I"))
        except Exception:
            pass
    return results


def _r0360_mul_I_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.mul_I_re
    # (z * I).re = -z.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_star_I_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_z_im")
            results.append((rhs, "Mathlib: Complex_mul_I_re"))
    except Exception:
        pass
    return results


def _r0361_equivRealProdAddHom_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.equivRealProdAddHom_symm_apply
    # equivRealProdAddHom.symm p = p.1 + p.2 * I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "equivRealProdAddHom_symm", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("p_1"), OOp("*", (OVar("p_2"), OVar("I")))))
            results.append((rhs, "Mathlib: Complex_equivRealProdAddHom_symm_apply"))
        except Exception:
            pass
    return results


def _r0362_ofReal_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_sum
    # ((∑ i ∈ s, f i : ℝ) : ℂ) = ∑ i ∈ s, (f i : ℂ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_in_s_f_i_colon", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OOp("f", (OVar("i"), args[0], args[1],)),))))
            results.append((rhs, "Mathlib: Complex_ofReal_sum"))
        except Exception:
            pass
    return results


def _r0363_ofReal_expect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_expect
    # (𝔼 i ∈ s, f i : ℝ) = 𝔼 i ∈ s, (f i : ℂ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OOp("f", (OVar("i"), OVar("colon"), OVar("_unknown"),)),))))
            results.append((rhs, "Mathlib: Complex_ofReal_expect"))
        except Exception:
            pass
    return results


def _r0364_ofReal_balance(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_balance
    # ((balance f a : ℝ) : ℂ) = balance ((↑) ∘ f) a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "balance_f_a_colon", 2)
    if args is not None:
        try:
            rhs = OOp("balance", (OOp("comp", (args[1], OVar("f"))), OVar("a"),))
            results.append((rhs, "Mathlib: Complex_ofReal_balance"))
        except Exception:
            pass
    return results


def _r0365_ofReal_comp_balance(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_comp_balance
    # ofReal ∘ balance f = balance (ofReal ∘ f : ι → ℂ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("balance", (OOp("implies", (OOp("comp", (args[0], OOp("f", (OVar("colon"), OVar("i"),)))), OVar("_unknown"))),))
            results.append((rhs, "Mathlib: Complex_ofReal_comp_balance"))
        except Exception:
            pass
    return results


def _r0366_re_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.re_sum
    # (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_in_s_f_i_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f_i_re"),))))
            results.append((rhs, "Mathlib: Complex_re_sum"))
    except Exception:
        pass
    return results


def _r0367_re_expect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.re_expect
    # (𝔼 i ∈ s, f i).re = 𝔼 i ∈ s, (f i).re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_in_s_f_i_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f_i_re"),))))
            results.append((rhs, "Mathlib: Complex_re_expect"))
    except Exception:
        pass
    return results


def _r0368_re_balance(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.re_balance
    # re (balance f a) = balance (re ∘ f) a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "re", 1)
    if args is not None:
        try:
            rhs = OOp("balance", (OOp("comp", (OVar("re"), OVar("f"))), OVar("a"),))
            results.append((rhs, "Mathlib: Complex_re_balance"))
        except Exception:
            pass
    return results


def _r0369_re_comp_balance(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.re_comp_balance
    # re ∘ balance f = balance (re ∘ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("balance", (OOp("comp", (args[0], OVar("f"))),))
            results.append((rhs, "Mathlib: Complex_re_comp_balance"))
        except Exception:
            pass
    return results


def _r0370_im_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.im_sum
    # (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_in_s_f_i_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f_i_im"),))))
            results.append((rhs, "Mathlib: Complex_im_sum"))
    except Exception:
        pass
    return results


def _r0371_im_expect(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.im_expect
    # (𝔼 i ∈ s, f i).im = 𝔼 i ∈ s, (f i).im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_in_s_f_i_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f_i_im"),))))
            results.append((rhs, "Mathlib: Complex_im_expect"))
    except Exception:
        pass
    return results


def _r0372_im_balance(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.im_balance
    # im (balance f a) = balance (im ∘ f) a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "im", 1)
    if args is not None:
        try:
            rhs = OOp("balance", (OOp("comp", (OVar("im"), OVar("f"))), OVar("a"),))
            results.append((rhs, "Mathlib: Complex_im_balance"))
        except Exception:
            pass
    return results


def _r0373_im_comp_balance(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.im_comp_balance
    # im ∘ balance f = balance (im ∘ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("balance", (OOp("comp", (args[0], OVar("f"))),))
            results.append((rhs, "Mathlib: Complex_im_comp_balance"))
        except Exception:
            pass
    return results


def _r0374_one_eq_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.one_eq_mk
    # 1 = (⟨a, ha⟩ : Fin (n + 2)) ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    if _is_lit(term, 1):
        try:
            rhs = OOp("==", (OOp("iff", (OOp("a_ha", (OVar("colon"), OVar("Fin"), OOp("+", (OVar("n"), OLit(2))),)), OVar("a"))), OLit(1)))
            results.append((rhs, "Mathlib: Fin_one_eq_mk"))
        except Exception:
            pass
    return results


def _r0375_rev_rev(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin2.rev_rev
    # i.rev.rev = i
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_rev_rev")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("i")
            results.append((rhs, "Mathlib: Fin2_rev_rev"))
    except Exception:
        pass
    return results


def _r0376_toFin_ofFin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin2.toFin_ofFin
    # toFin (ofFin i) = i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFin", 1)
    if args is not None:
        try:
            rhs = OVar("i")
            results.append((rhs, "Mathlib: Fin2_toFin_ofFin"))
        except Exception:
            pass
    return results


def _r0377_ofFin_toFin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin2.ofFin_toFin
    # ofFin (toFin i) = i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFin", 1)
    if args is not None:
        try:
            rhs = OVar("i")
            results.append((rhs, "Mathlib: Fin2_ofFin_toFin"))
        except Exception:
            pass
    return results


def _r0378_cast_rev(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.cast_rev
    # i.rev.cast h = (i.cast h).rev
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_rev_cast", 1)
    if args is not None:
        try:
            rhs = OVar("i_cast_h_rev")
            results.append((rhs, "Mathlib: Fin_cast_rev"))
        except Exception:
            pass
    return results


def _r0379_exists_succ_eq_of_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.exists_succ_eq_of_ne_zero
    # ∃ y, Fin.succ y = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Fin_exists_succ_eq_of_ne_zero"))
        except Exception:
            pass
    return results


def _r0380_castAdd_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.castAdd_inj
    # castAdd n a = castAdd n b ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "castAdd", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("castAdd", (args[0], OVar("b"),)), args[1])), OVar("b")))
            results.append((rhs, "Mathlib: Fin_castAdd_inj"))
        except Exception:
            pass
    return results


def _r0381_castLE_rfl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.castLE_rfl
    # Fin.castLE (le_refl n) = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fin_castLE", 1)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Fin_castLE_rfl"))
        except Exception:
            pass
    return results


def _r0382_coe_of_injective_castLE_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.coe_of_injective_castLE_symm
    # ((Equiv.ofInjective _ (castLE_injective h)).symm ⟨i, hi⟩ : ℕ) = i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_ofInjective_castLE_injective_h_symm", 3)
    if args is not None:
        try:
            rhs = OVar("i")
            results.append((rhs, "Mathlib: Fin_coe_of_injective_castLE_symm"))
        except Exception:
            pass
    return results


def _r0383_finCongr_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: finCongr_refl
    # finCongr h = Equiv.refl (Fin n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finCongr", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_refl", (OOp("Fin", (OVar("n"),)),))
            results.append((rhs, "Mathlib: finCongr_refl"))
        except Exception:
            pass
    return results


def _r0384_finCongr_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: finCongr_symm
    # (finCongr h).symm = finCongr h.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("finCongr_h_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("finCongr", (OVar("h_symm"),))
            results.append((rhs, "Mathlib: finCongr_symm"))
    except Exception:
        pass
    return results


def _r0385_finCongr_apply_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: finCongr_apply_coe
    # (finCongr h k : ℕ) = k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finCongr", 4)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: finCongr_apply_coe"))
        except Exception:
            pass
    return results


def _r0386_finCongr_symm_apply_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: finCongr_symm_apply_coe
    # ((finCongr h).symm k : ℕ) = k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finCongr_h_symm", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: finCongr_symm_apply_coe"))
        except Exception:
            pass
    return results


def _r0387_coe_of_injective_castSucc_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.coe_of_injective_castSucc_symm
    # ((Equiv.ofInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : ℕ) = i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Equiv_ofInjective_castSucc_castSucc_injective_symm", 3)
    if args is not None:
        try:
            rhs = OVar("i")
            results.append((rhs, "Mathlib: Fin_coe_of_injective_castSucc_symm"))
        except Exception:
            pass
    return results


def _r0388_cons_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.cons_succ
    # cons x p i.succ = p i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons", 3)
    if args is not None:
        try:
            rhs = OOp("p", (OVar("i"),))
            results.append((rhs, "Mathlib: Fin_cons_succ"))
        except Exception:
            pass
    return results


def _r0389_cons_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.cons_zero
    # cons x p 0 = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Fin_cons_zero"))
        except Exception:
            pass
    return results


def _r0390_cons_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.cons_one
    # cons x p 1 = p 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons", 3)
    if args is not None:
        try:
            rhs = OOp("p", (OLit(0),))
            results.append((rhs, "Mathlib: Fin_cons_one"))
        except Exception:
            pass
    return results


def _r0391_tail_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.Embedding.tail_cons
    # tail (cons x ha) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tail", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Fin_Embedding_tail_cons"))
        except Exception:
            pass
    return results


def _r0392_init_snoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.Embedding.init_snoc
    # init (snoc x ha) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "init", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Fin_Embedding_init_snoc"))
        except Exception:
            pass
    return results


def _r0393_antidiagonalTuple_zero_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Nat.antidiagonalTuple_zero_succ
    # antidiagonalTuple 0 n.succ = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Finset_Nat_antidiagonalTuple_zero_succ"))
        except Exception:
            pass
    return results


def _r0394_mem_antidiagonalTuple(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Nat.mem_antidiagonalTuple
    # x ∈ antidiagonalTuple k n ↔ ∑ i, x i = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Finset_Nat_mem_antidiagonalTuple"))
        except Exception:
            pass
    return results


def _r0395_antidiagonalTuple_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Nat.antidiagonalTuple_two
    # antidiagonalTuple 2 n = (antidiagonal n).map (piFinTwoEquiv fun _ => ℕ).symm.toEmbedding
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OOp("antidiagonal_n_map", (OVar("piFinTwoEquiv_fun_eq_gt_symm_toEmbedding"),))
            results.append((rhs, "Mathlib: Finset_Nat_antidiagonalTuple_two"))
        except Exception:
            pass
    return results


def _r0396_prod_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FinVec.prod_eq
    # ∀ {m} (a : Fin m → α), prod a = ∏ i, a i   | 0, _ => rfl   | 1, a => (Fintype.prod_unique a).symm   | n + 2, a =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("_unknown", (OVar("i"), args[0], OVar("i"), OVar("pipe"), OVar("_0"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_1"), args[0], OVar("eq_gt"), OVar("Fintype_prod_unique_a_symm"), OVar("pipe"), OVar("n"),)), OOp("_2", (args[0], OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: FinVec_prod_eq"))
        except Exception:
            pass
    return results


def _r0397_take_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.take_zero
    # take 0 n.zero_le v = fun i ↦ elim0 i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "take", 3)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("i"), OVar("_unknown"), OVar("elim0"), OVar("i"),))
            results.append((rhs, "Mathlib: Fin_take_zero"))
        except Exception:
            pass
    return results


def _r0398_take_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.take_one
    # take 1 (Nat.le_add_left 1 n) v = (fun i => v (castLE (Nat.le_add_left 1 n) i))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "take", 3)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("i"), OVar("eq_gt"), args[2], OOp("castLE", (OOp("Nat_le_add_left", (OLit(1), OVar("n"),)), OVar("i"),)),))
            results.append((rhs, "Mathlib: Fin_take_one"))
        except Exception:
            pass
    return results


def _r0399_take_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.take_eq_self
    # take n (le_refl n) v = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "take", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Fin_take_eq_self"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_nat_basic rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "**", "+", "-", "<", "<=", "==", "Additive", "Complex_Gamma", "Complex_mk", "Equiv_ofInjective_castLE_injective_h_symm", "Equiv_ofInjective_castSucc_castSucc_injective_symm", "Even", "F_nhds_a_F", "F_ofEquiv_E_F", "Fin_castLE", "FiniteElement_mk", "Finset", "Fintype_card", "NatIso_op", "NatIso_unop", "NatTrans_op", "NatTrans_unop", "Nat_bell", "Nat_le_add_left", "Real_cos", "Real_cot", "Real_exp", "Real_log", "Real_sin", "Real_sinh", "Real_tan", "Real_tanh", "Sum_inr", "_0", "_0_colon", "_1", "_1_colon", "_1_colon_Finset_a_image", "_1_colon_Finset_a_map", "_1_colon_Int", "_unknown", "a", "a_app", "ac_equiv", "analyticOrderNatAt", "antidiagonalTuple", "arccos", "arcsin", "arctan",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_nat_basic axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_nat_basic rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_balance_add(term, ctx))
    results.extend(_r0001_sum_balance(term, ctx))
    results.extend(_r0002_expect_balance(term, ctx))
    results.extend(_r0003_balance_idem(term, ctx))
    results.extend(_r0004_map_balance(term, ctx))
    results.extend(_r0005_expect_singleton(term, ctx))
    results.extend(_r0006_expect_const_zero(term, ctx))
    results.extend(_r0007_expect_congr(term, ctx))
    results.extend(_r0008_expect_ite_eq(term, ctx))
    results.extend(_r0009_card_mul_expect(term, ctx))
    results.extend(_r0010_expect_dite_eq(term, ctx))
    results.extend(_r0011_prod_comm(term, ctx))
    results.extend(_r0012_support_sum(term, ctx))
    results.extend(_r0013_prod_eq_one_iff(term, ctx))
    results.extend(_r0014_prod_map(term, ctx))
    results.extend(_r0015_mul_prod_eq_prod_insertNone(term, ctx))
    results.extend(_r0016_cast_list_prod(term, ctx))
    results.extend(_r0017_cast_multiset_sum(term, ctx))
    results.extend(_r0018_cast_sum(term, ctx))
    results.extend(_r0019_cast_list_prod(term, ctx))
    results.extend(_r0020_cast_multiset_sum(term, ctx))
    results.extend(_r0021_cast_ringChar(term, ctx))
    results.extend(_r0022_cast_eq_zero(term, ctx))
    results.extend(_r0023_normalize_lcm(term, ctx))
    results.extend(_r0024_lcm_union(term, ctx))
    results.extend(_r0025_lt_one_iff(term, ctx))
    results.extend(_r0026_lt_sub_one_iff(term, ctx))
    results.extend(_r0027_neg_natCast_eq_one(term, ctx))
    results.extend(_r0028_zeroHom_comp(term, ctx))
    results.extend(_r0029_zsmul_eq_mul(term, ctx))
    results.extend(_r0030_one_emod_two(term, ctx))
    results.extend(_r0031_emod_two_ne_zero(term, ctx))
    results.extend(_r0032_even_iff(term, ctx))
    results.extend(_r0033_isUnit_eq_one_or(term, ctx))
    results.extend(_r0034_succ_mod_two_eq_zero_iff(term, ctx))
    results.extend(_r0035_succ_mod_two_eq_one_iff(term, ctx))
    results.extend(_r0036_coe_one(term, ctx))
    results.extend(_r0037_coe_eq_one(term, ctx))
    results.extend(_r0038_map_one(term, ctx))
    results.extend(_r0039_image_one(term, ctx))
    results.extend(_r0040_subset_one_iff_eq(term, ctx))
    results.extend(_r0041_singletonOneHom_apply(term, ctx))
    results.extend(_r0042_inf_one(term, ctx))
    results.extend(_r0043_max_one(term, ctx))
    results.extend(_r0044_min_one(term, ctx))
    results.extend(_r0045_image_op_one(term, ctx))
    results.extend(_r0046_map_op_one(term, ctx))
    results.extend(_r0047_one_product_one(term, ctx))
    results.extend(_r0048_prod_neg_index(term, ctx))
    results.extend(_r0049_dens_smul_finset(term, ctx))
    results.extend(_r0050_smul_empty(term, ctx))
    results.extend(_r0051_smul_eq_empty(term, ctx))
    results.extend(_r0052_card_additive(term, ctx))
    results.extend(_r0053_equiv_inr(term, ctx))
    results.extend(_r0054_f_eq_of_r_eq_some(term, ctx))
    results.extend(_r0055_boundaryGE_embeddingUpIntGE_iff(term, ctx))
    results.extend(_r0056_finsuppAntidiag_empty_of_ne_zero(term, ctx))
    results.extend(_r0057_finsuppAntidiag_empty(term, ctx))
    results.extend(_r0058_finMulAntidiag_one(term, ctx))
    results.extend(_r0059_piAntidiag_empty_of_ne_zero(term, ctx))
    results.extend(_r0060_piAntidiag_empty(term, ctx))
    results.extend(_r0061_floorRing_ceil_eq(term, ctx))
    results.extend(_r0062_floor_eq_on_Ico(term, ctx))
    results.extend(_r0063_floor_intCast(term, ctx))
    results.extend(_r0064_floor_natCast(term, ctx))
    results.extend(_r0065_floor_zero(term, ctx))
    results.extend(_r0066_floor_one(term, ctx))
    results.extend(_r0067_floor_ofNat(term, ctx))
    results.extend(_r0068_floor_add_intCast(term, ctx))
    results.extend(_r0069_floor_add_natCast(term, ctx))
    results.extend(_r0070_floor_add_ofNat(term, ctx))
    results.extend(_r0071_floor_ofNat_add(term, ctx))
    results.extend(_r0072_floor_sub_one(term, ctx))
    results.extend(_r0073_floor_one(term, ctx))
    results.extend(_r0074_floor_ofNat(term, ctx))
    results.extend(_r0075_floor_of_nonpos(term, ctx))
    results.extend(_r0076_abs_le_one_iff(term, ctx))
    results.extend(_r0077_mul_bot(term, ctx))
    results.extend(_r0078_length_neg(term, ctx))
    results.extend(_r0079_val_one(term, ctx))
    results.extend(_r0080_mk_one(term, ctx))
    results.extend(_r0081_negOnePow_one(term, ctx))
    results.extend(_r0082_negOnePow_succ(term, ctx))
    results.extend(_r0083_negOnePow_odd(term, ctx))
    results.extend(_r0084_negOnePow_eq_one_iff(term, ctx))
    results.extend(_r0085_cast_negOnePow_natCast(term, ctx))
    results.extend(_r0086_mkRat_pow(term, ctx))
    results.extend(_r0087_cast_analyticOrderNatAt(term, ctx))
    results.extend(_r0088_conjLIE_symm(term, ctx))
    results.extend(_r0089_nndist_conj_conj(term, ctx))
    results.extend(_r0090_dist_conj_comm(term, ctx))
    results.extend(_r0091_conjCAE_toAlgEquiv(term, ctx))
    results.extend(_r0092_conjCLE_toLinearEquiv(term, ctx))
    results.extend(_r0093_conjCAE_apply(term, ctx))
    results.extend(_r0094_ofRealCLM_apply(term, ctx))
    results.extend(_r0095_ofReal_tsum(term, ctx))
    results.extend(_r0096_ofReal_exp(term, ctx))
    results.extend(_r0097_exp_ofReal_im(term, ctx))
    results.extend(_r0098_exp_ofReal_re(term, ctx))
    results.extend(_r0099_exp_eq_one_iff(term, ctx))
    results.extend(_r0100_nnnorm_I(term, ctx))
    results.extend(_r0101_norm_real(term, ctx))
    results.extend(_r0102_norm_natCast(term, ctx))
    results.extend(_r0103_norm_two(term, ctx))
    results.extend(_r0104_nnnorm_ofNat(term, ctx))
    results.extend(_r0105_norm_intCast(term, ctx))
    results.extend(_r0106_norm_nnratCast(term, ctx))
    results.extend(_r0107_nnnorm_ratCast(term, ctx))
    results.extend(_r0108_nnnorm_nnratCast(term, ctx))
    results.extend(_r0109_normSq_eq_norm_sq(term, ctx))
    results.extend(_r0110_norm_add_mul_I(term, ctx))
    results.extend(_r0111_abs_re_eq_norm(term, ctx))
    results.extend(_r0112_abs_im_eq_norm(term, ctx))
    results.extend(_r0113_reCLM_norm(term, ctx))
    results.extend(_r0114_reCLM_nnnorm(term, ctx))
    results.extend(_r0115_imCLM_norm(term, ctx))
    results.extend(_r0116_imCLM_nnnorm(term, ctx))
    results.extend(_r0117_ofRealCLM_norm(term, ctx))
    results.extend(_r0118_ofRealCLM_enorm(term, ctx))
    results.extend(_r0119_ofRealCLM_nnnorm(term, ctx))
    results.extend(_r0120_interior_setOf_im_le(term, ctx))
    results.extend(_r0121_interior_setOf_le_re(term, ctx))
    results.extend(_r0122_interior_setOf_le_im(term, ctx))
    results.extend(_r0123_frontier_setOf_re_le(term, ctx))
    results.extend(_r0124_frontier_setOf_im_le(term, ctx))
    results.extend(_r0125_frontier_setOf_le_re(term, ctx))
    results.extend(_r0126_frontier_setOf_le_im(term, ctx))
    results.extend(_r0127_closure_reProdIm(term, ctx))
    results.extend(_r0128_sinh_add_aux(term, ctx))
    results.extend(_r0129_cosh_add_aux(term, ctx))
    results.extend(_r0130_ofReal_sinh(term, ctx))
    results.extend(_r0131_sinh_ofReal_im(term, ctx))
    results.extend(_r0132_sinh_ofReal_re(term, ctx))
    results.extend(_r0133_cosh_ofReal_im(term, ctx))
    results.extend(_r0134_cosh_ofReal_re(term, ctx))
    results.extend(_r0135_tanh_conj(term, ctx))
    results.extend(_r0136_ofReal_tanh(term, ctx))
    results.extend(_r0137_tanh_ofReal_im(term, ctx))
    results.extend(_r0138_tanh_ofReal_re(term, ctx))
    results.extend(_r0139_sinh_add_cosh(term, ctx))
    results.extend(_r0140_cosh_sq(term, ctx))
    results.extend(_r0141_two_sin(term, ctx))
    results.extend(_r0142_cos_add(term, ctx))
    results.extend(_r0143_ofReal_sin(term, ctx))
    results.extend(_r0144_sin_ofReal_im(term, ctx))
    results.extend(_r0145_sin_ofReal_re(term, ctx))
    results.extend(_r0146_ofReal_cos(term, ctx))
    results.extend(_r0147_cos_ofReal_im(term, ctx))
    results.extend(_r0148_cos_ofReal_re(term, ctx))
    results.extend(_r0149_tan_conj(term, ctx))
    results.extend(_r0150_ofReal_cot_ofReal_re(term, ctx))
    results.extend(_r0151_ofReal_tan(term, ctx))
    results.extend(_r0152_ofReal_cot(term, ctx))
    results.extend(_r0153_tan_ofReal_im(term, ctx))
    results.extend(_r0154_tan_ofReal_re(term, ctx))
    results.extend(_r0155_exp_ofReal_mul_I_im(term, ctx))
    results.extend(_r0156_exp_ofReal_mul_I(term, ctx))
    results.extend(_r0157_tan_zero(term, ctx))
    results.extend(_r0158_cos_sq_add_sin_sq(term, ctx))
    results.extend(_r0159_cosh_add_sinh(term, ctx))
    results.extend(_r0160_sinh_add_cosh(term, ctx))
    results.extend(_r0161_norm_exp_I_mul_ofReal(term, ctx))
    results.extend(_r0162_nnnorm_exp_ofReal_mul_I(term, ctx))
    results.extend(_r0163_nnnorm_exp_I_mul_ofReal(term, ctx))
    results.extend(_r0164_enorm_exp_ofReal_mul_I(term, ctx))
    results.extend(_r0165_enorm_exp_I_mul_ofReal(term, ctx))
    results.extend(_r0166_norm_exp_I_mul_ofReal_sub_one(term, ctx))
    results.extend(_r0167_mk_coe(term, ctx))
    results.extend(_r0168_mk_inj(term, ctx))
    results.extend(_r0169_coe_zero(term, ctx))
    results.extend(_r0170_coe_eq_zero(term, ctx))
    results.extend(_r0171_mk_zero(term, ctx))
    results.extend(_r0172_mk_eq_zero(term, ctx))
    results.extend(_r0173_im_coe(term, ctx))
    results.extend(_r0174_re_zero(term, ctx))
    results.extend(_r0175_im_zero(term, ctx))
    results.extend(_r0176_star_zero(term, ctx))
    results.extend(_r0177_norm_cast_rat(term, ctx))
    results.extend(_r0178_enorm_natCast(term, ctx))
    results.extend(_r0179_norm_ofNat(term, ctx))
    results.extend(_r0180_nnnorm_ofNat(term, ctx))
    results.extend(_r0181_norm_two(term, ctx))
    results.extend(_r0182_nnnorm_two(term, ctx))
    results.extend(_r0183_nnnorm_nnratCast(term, ctx))
    results.extend(_r0184_enorm_abs(term, ctx))
    results.extend(_r0185_enorm_eq_ofReal(term, ctx))
    results.extend(_r0186_enorm_natCast(term, ctx))
    results.extend(_r0187_sqrt_one(term, ctx))
    results.extend(_r0188_sqrt_eq_real_add_ite(term, ctx))
    results.extend(_r0189_re_sqrt_ofReal(term, ctx))
    results.extend(_r0190_cosh_arsinh(term, ctx))
    results.extend(_r0191_tanh_arsinh(term, ctx))
    results.extend(_r0192_arsinh_eq_zero_iff(term, ctx))
    results.extend(_r0193_sinh_artanh(term, ctx))
    results.extend(_r0194_binEntropy_one(term, ctx))
    results.extend(_r0195_qaryEntropy_one(term, ctx))
    results.extend(_r0196_qaryEntropy_two(term, ctx))
    results.extend(_r0197_norm_mul_cos_arg(term, ctx))
    results.extend(_r0198_norm_mul_sin_arg(term, ctx))
    results.extend(_r0199_norm_eq_one_iff(term, ctx))
    results.extend(_r0200_ext_norm_arg(term, ctx))
    results.extend(_r0201_arg_real_mul(term, ctx))
    results.extend(_r0202_arg_neg_one(term, ctx))
    results.extend(_r0203_arg_I(term, ctx))
    results.extend(_r0204_tan_arg(term, ctx))
    results.extend(_r0205_ofNat_arg(term, ctx))
    results.extend(_r0206_arg_eq_zero_iff(term, ctx))
    results.extend(_r0207_arg_mul_eq_add_arg_iff(term, ctx))
    results.extend(_r0208_ofNat_log(term, ctx))
    results.extend(_r0209_log_one(term, ctx))
    results.extend(_r0210_log_neg_one(term, ctx))
    results.extend(_r0211_log_I(term, ctx))
    results.extend(_r0212_map_exp_comap_re_atTop(term, ctx))
    results.extend(_r0213_rpowIntegrand_0_1_zero_left(term, ctx))
    results.extend(_r0214_coe_comp_expOrderIso(term, ctx))
    results.extend(_r0215_map_exp_atTop(term, ctx))
    results.extend(_r0216_comap_exp_atTop(term, ctx))
    results.extend(_r0217_comap_exp_nhdsGT_zero(term, ctx))
    results.extend(_r0218_comap_exp_nhds_exp(term, ctx))
    results.extend(_r0219_deriv_exp(term, ctx))
    results.extend(_r0220_iter_deriv_exp(term, ctx))
    results.extend(_r0221_deriv_exp(term, ctx))
    results.extend(_r0222_iter_deriv_exp(term, ctx))
    results.extend(_r0223_Gamma_ofReal(term, ctx))
    results.extend(_r0224_digamma_one(term, ctx))
    results.extend(_r0225_logb_one(term, ctx))
    results.extend(_r0226_logb_zero_left(term, ctx))
    results.extend(_r0227_logb_one_left(term, ctx))
    results.extend(_r0228_logb_one_left_eq_zero(term, ctx))
    results.extend(_r0229_logb_self_eq_one(term, ctx))
    results.extend(_r0230_logb_self_eq_one_iff(term, ctx))
    results.extend(_r0231_logb_mul(term, ctx))
    results.extend(_r0232_log_comp_exp(term, ctx))
    results.extend(_r0233_log_zero(term, ctx))
    results.extend(_r0234_log_one(term, ctx))
    results.extend(_r0235_sinh_log(term, ctx))
    results.extend(_r0236_deriv_log(term, ctx))
    results.extend(_r0237_negMulLog_one(term, ctx))
    results.extend(_r0238_posLog_one(term, ctx))
    results.extend(_r0239_posLog_eq_zero_iff(term, ctx))
    results.extend(_r0240_cpow_def(term, ctx))
    results.extend(_r0241_cpow_eq_zero_iff(term, ctx))
    results.extend(_r0242_zero_cpow_eq_iff(term, ctx))
    results.extend(_r0243_cpow_ofNat(term, ctx))
    results.extend(_r0244_nthRoot_one_left(term, ctx))
    results.extend(_r0245_nthRoot_zero_right(term, ctx))
    results.extend(_r0246_nthRoot_one_right(term, ctx))
    results.extend(_r0247_nthRoot_pow(term, ctx))
    results.extend(_r0248_rpow_def(term, ctx))
    results.extend(_r0249_rpow_ofNat(term, ctx))
    results.extend(_r0250_exp_one_rpow(term, ctx))
    results.extend(_r0251_exp_one_pow(term, ctx))
    results.extend(_r0252_rpow_eq_zero_iff_of_nonneg(term, ctx))
    results.extend(_r0253_zero_rpow(term, ctx))
    results.extend(_r0254_zero_rpow_eq_iff(term, ctx))
    results.extend(_r0255_pi_rpow_one(term, ctx))
    results.extend(_r0256_one_rpow(term, ctx))
    results.extend(_r0257_norm_cpow_eq_rpow_re_of_pos(term, ctx))
    results.extend(_r0258_zero_of_nonpos(term, ctx))
    results.extend(_r0259_one(term, ctx))
    results.extend(_r0260_zsmul_eq_iff(term, ctx))
    results.extend(_r0261_cos_zero(term, ctx))
    results.extend(_r0262_cos_eq_zero_iff(term, ctx))
    results.extend(_r0263_tan_zero(term, ctx))
    results.extend(_r0264_sign_eq_zero_iff(term, ctx))
    results.extend(_r0265_arctan_tan(term, ctx))
    results.extend(_r0266_arctan_eq_zero_iff(term, ctx))
    results.extend(_r0267_arctan_sqrt_three(term, ctx))
    results.extend(_r0268_arctan_eq_arccos(term, ctx))
    results.extend(_r0269_cos_pi(term, ctx))
    results.extend(_r0270_cos_two_pi(term, ctx))
    results.extend(_r0271_sin_add_two_pi(term, ctx))
    results.extend(_r0272_sin_nat_mul_pi(term, ctx))
    results.extend(_r0273_sin_int_mul_pi(term, ctx))
    results.extend(_r0274_sin_add_nat_mul_two_pi(term, ctx))
    results.extend(_r0275_sin_add_int_mul_two_pi(term, ctx))
    results.extend(_r0276_sin_add_int_mul_pi(term, ctx))
    results.extend(_r0277_cos_add_pi(term, ctx))
    results.extend(_r0278_cos_add_two_pi(term, ctx))
    results.extend(_r0279_cos_nat_mul_two_pi(term, ctx))
    results.extend(_r0280_cos_int_mul_two_pi(term, ctx))
    results.extend(_r0281_cos_add_nat_mul_two_pi(term, ctx))
    results.extend(_r0282_cos_add_int_mul_two_pi(term, ctx))
    results.extend(_r0283_cos_add_int_mul_pi(term, ctx))
    results.extend(_r0284_range_sin(term, ctx))
    results.extend(_r0285_cos_pi(term, ctx))
    results.extend(_r0286_sin_two_pi(term, ctx))
    results.extend(_r0287_cos_two_pi(term, ctx))
    results.extend(_r0288_exp_two_pi_mul_I(term, ctx))
    results.extend(_r0289_exp_int_mul_two_pi_mul_I(term, ctx))
    results.extend(_r0290_exp_add_pi_mul_I(term, ctx))
    results.extend(_r0291_deriv_tan(term, ctx))
    results.extend(_r0292_sinh_eq_zero(term, ctx))
    results.extend(_r0293_arcsin_one(term, ctx))
    results.extend(_r0294_arcsin_of_one_le(term, ctx))
    results.extend(_r0295_arcsin_eq_zero_iff(term, ctx))
    results.extend(_r0296_zero_eq_arcsin_iff(term, ctx))
    results.extend(_r0297_cos_arccos(term, ctx))
    results.extend(_r0298_arccos_one(term, ctx))
    results.extend(_r0299_arccos_neg_one(term, ctx))
    results.extend(_r0300_arccos_eq_zero(term, ctx))
    results.extend(_r0301_arccos_eq_pi(term, ctx))
    results.extend(_r0302_sinc_of_ne_zero(term, ctx))
    results.extend(_r0303_toEndHom_trivial_of_mem(term, ctx))
    results.extend(_r0304_congr(term, ctx))
    results.extend(_r0305_comp_apply(term, ctx))
    results.extend(_r0306_hom_apply(term, ctx))
    results.extend(_r0307_id_hom(term, ctx))
    results.extend(_r0308_comp_hom(term, ctx))
    results.extend(_r0309_homMk_eq_id_iff(term, ctx))
    results.extend(_r0310_op_comp(term, ctx))
    results.extend(_r0311_unop_comp(term, ctx))
    results.extend(_r0312_op_trans(term, ctx))
    results.extend(_r0313_unop_trans(term, ctx))
    results.extend(_r0314_op_isoWhiskerRight(term, ctx))
    results.extend(_r0315_card_mul_divConst(term, ctx))
    results.extend(_r0316_mulConst_empty_left(term, ctx))
    results.extend(_r0317_divConst_empty_left(term, ctx))
    results.extend(_r0318_mulConst_empty_right(term, ctx))
    results.extend(_r0319_divConst_empty_right(term, ctx))
    results.extend(_r0320_mulConst_inv_right(term, ctx))
    results.extend(_r0321_divConst_inv_right(term, ctx))
    results.extend(_r0322_mulEnergy_empty_right(term, ctx))
    results.extend(_r0323_mulEnergy_eq_zero_iff(term, ctx))
    results.extend(_r0324_bell_one(term, ctx))
    results.extend(_r0325_bell_two(term, ctx))
    results.extend(_r0326_coe_bipartiteAbove(term, ctx))
    results.extend(_r0327_prod_prod_bipartiteAbove_eq_prod_prod_bi(term, ctx))
    results.extend(_r0328_partition_zero_parts(term, ctx))
    results.extend(_r0329_count_ofSums_of_ne_zero(term, ctx))
    results.extend(_r0330_largeSchroder_one(term, ctx))
    results.extend(_r0331_smallSchroder_one(term, ctx))
    results.extend(_r0332_stirlingFirst_zero_succ(term, ctx))
    results.extend(_r0333_stirlingFirst_succ_zero(term, ctx))
    results.extend(_r0334_stirlingSecond_zero_succ(term, ctx))
    results.extend(_r0335_stirlingSecond_succ_zero(term, ctx))
    results.extend(_r0336_truncatedSup_singleton(term, ctx))
    results.extend(_r0337_shadow_iterate_empty(term, ctx))
    results.extend(_r0338_shadow_singleton_empty(term, ctx))
    results.extend(_r0339_shadow_singleton(term, ctx))
    results.extend(_r0340_shatterer_eq(term, ctx))
    results.extend(_r0341_ofEquiv_F(term, ctx))
    results.extend(_r0342_nhds_F(term, ctx))
    results.extend(_r0343_ofReal_im(term, ctx))
    results.extend(_r0344_ofReal_def(term, ctx))
    results.extend(_r0345_zero_im(term, ctx))
    results.extend(_r0346_ofReal_zero(term, ctx))
    results.extend(_r0347_ofReal_eq_zero(term, ctx))
    results.extend(_r0348_one_im(term, ctx))
    results.extend(_r0349_ofReal_one(term, ctx))
    results.extend(_r0350_ofReal_eq_one(term, ctx))
    results.extend(_r0351_add_im(term, ctx))
    results.extend(_r0352_ofReal_add(term, ctx))
    results.extend(_r0353_mul_im(term, ctx))
    results.extend(_r0354_ofReal_mul(term, ctx))
    results.extend(_r0355_re_ofReal_mul(term, ctx))
    results.extend(_r0356_I_im(term, ctx))
    results.extend(_r0357_I_mul_I(term, ctx))
    results.extend(_r0358_I_mul(term, ctx))
    results.extend(_r0359_mk_eq_add_mul_I(term, ctx))
    results.extend(_r0360_mul_I_re(term, ctx))
    results.extend(_r0361_equivRealProdAddHom_symm_apply(term, ctx))
    results.extend(_r0362_ofReal_sum(term, ctx))
    results.extend(_r0363_ofReal_expect(term, ctx))
    results.extend(_r0364_ofReal_balance(term, ctx))
    results.extend(_r0365_ofReal_comp_balance(term, ctx))
    results.extend(_r0366_re_sum(term, ctx))
    results.extend(_r0367_re_expect(term, ctx))
    results.extend(_r0368_re_balance(term, ctx))
    results.extend(_r0369_re_comp_balance(term, ctx))
    results.extend(_r0370_im_sum(term, ctx))
    results.extend(_r0371_im_expect(term, ctx))
    results.extend(_r0372_im_balance(term, ctx))
    results.extend(_r0373_im_comp_balance(term, ctx))
    results.extend(_r0374_one_eq_mk(term, ctx))
    results.extend(_r0375_rev_rev(term, ctx))
    results.extend(_r0376_toFin_ofFin(term, ctx))
    results.extend(_r0377_ofFin_toFin(term, ctx))
    results.extend(_r0378_cast_rev(term, ctx))
    results.extend(_r0379_exists_succ_eq_of_ne_zero(term, ctx))
    results.extend(_r0380_castAdd_inj(term, ctx))
    results.extend(_r0381_castLE_rfl(term, ctx))
    results.extend(_r0382_coe_of_injective_castLE_symm(term, ctx))
    results.extend(_r0383_finCongr_refl(term, ctx))
    results.extend(_r0384_finCongr_symm(term, ctx))
    results.extend(_r0385_finCongr_apply_coe(term, ctx))
    results.extend(_r0386_finCongr_symm_apply_coe(term, ctx))
    results.extend(_r0387_coe_of_injective_castSucc_symm(term, ctx))
    results.extend(_r0388_cons_succ(term, ctx))
    results.extend(_r0389_cons_zero(term, ctx))
    results.extend(_r0390_cons_one(term, ctx))
    results.extend(_r0391_tail_cons(term, ctx))
    results.extend(_r0392_init_snoc(term, ctx))
    results.extend(_r0393_antidiagonalTuple_zero_succ(term, ctx))
    results.extend(_r0394_mem_antidiagonalTuple(term, ctx))
    results.extend(_r0395_antidiagonalTuple_two(term, ctx))
    results.extend(_r0396_prod_eq(term, ctx))
    results.extend(_r0397_take_zero(term, ctx))
    results.extend(_r0398_take_one(term, ctx))
    results.extend(_r0399_take_eq_self(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_nat_basic rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Finset_prod_primes_dvd", "p_in_s_p_n", "Not an equality or iff proposition"),
    ("Fintype_balance_zero", "balance_0_colon_i_to_G_eq_0", "Not an equality or iff proposition"),
    ("Finset_exists_ne_zero_of_expect_ne_zero", "exists_i_in_s_f_i_ne_0", "Not an equality or iff proposition"),
    ("Finset_expect_dite_eq", "_unknown", "Empty proposition"),
    ("Finset_expect_ite_eq", "_unknown", "Empty proposition"),
    ("Fintype_expect_dite_eq", "_unknown", "Empty proposition"),
    ("Fintype_expect_ite_eq", "_unknown", "Empty proposition"),
    ("Finset_dens_biUnion_le", "s_biUnion_t_dens_le_a_in_s_t_a_dens", "Not an equality or iff proposition"),
    ("Fin_prod_cons", "i_colon_Fin_n_succ_cons_x_f_colon_Fin_n_succ_to_M_i_eq_x_star_i_colon_Fin_n_f_i", "Not an equality or iff proposition"),
    ("Fin_prod_univ_two", "_unknown", "Empty proposition"),
    ("Fin_prod_congr", "_unknown", "Empty proposition"),
    ("Fin_prod_insertNth", "_unknown", "Empty proposition"),
    ("Fin_mul_prod_removeNth", "_unknown", "Empty proposition"),
    ("Nat_cast_finprod", "_unknown", "Empty proposition"),
    ("Finsupp_prod_zero_index", "_0_colon_a_to_0_M_prod_h_eq_1", "Not an equality or iff proposition"),
    ("SubmonoidClass_finsuppProd_mem", "f_prod_g_in_s", "Not an equality or iff proposition"),
    ("Finsupp_prod_add_index", "_unknown", "Empty proposition"),
    ("Finsupp_liftAddHom_singleAddHom", "liftAddHom_a_colon_eq_a_M_colon_eq_M_N_colon_eq_a_to_0_M_singleAddHom_colon_a_to_M_to_plus_a_to_0_M_eq", "Not an equality or iff proposition"),
    ("Finset_sum_apply", "_unknown", "Empty proposition"),
    ("Finsupp_sum_sum_index", "_unknown", "Empty proposition"),
    ("Nat_prod_pow_pos_of_zero_notMem_support", "_0_lt_f_prod_pow", "Not an equality or iff proposition"),
    ("Finsupp_sum_cons", "_unknown", "Empty proposition"),
    ("Finset_prod_cons", "_unknown", "Empty proposition"),
    ("Finset_prod_insert", "_unknown", "Empty proposition"),
    ("Finset_prod_singleton", "_unknown", "Empty proposition"),
    ("Finset_prod_fiberwise_eq_prod_filter", "_unknown", "Empty proposition"),
    ("Finset_prod_fiberwise_of_maps_to", "_unknown", "Empty proposition"),
    ("Finset_prod_fiberwise", "_unknown", "Empty proposition"),
    ("Fintype_prod_fiberwise", "_unknown", "Empty proposition"),
    ("Finset_prod_empty", "_unknown", "Empty proposition"),
    ("Finset_prod_map", "_unknown", "Empty proposition"),
    ("Finset_prod_bij", "_unknown", "Empty proposition"),
    ("Finset_prod_nbij", "_unknown", "Empty proposition"),
    ("Finset_mulSupport_prod", "mulSupport_fun_x_i_in_s_f_i_x_sub_i_in_s_mulSupport_f_i", "Not an equality or iff proposition"),
    ("Finset_isSquare_prod", "IsSquare_i_in_s_f_i", "Not an equality or iff proposition"),
    ("Finset_prod_dite_eq", "_unknown", "Empty proposition"),
    ("Finset_prod_ite_eq", "_unknown", "Empty proposition"),
    ("Finset_prod_ite_eq_of_mem", "_unknown", "Empty proposition"),
    ("Finset_dvd_prod_of_mem", "f_a_i_in_s_f_i", "Not an equality or iff proposition"),
    ("Fintype_prod_dite_eq", "_unknown", "Empty proposition"),
    ("Fintype_prod_ite_eq", "_unknown", "Empty proposition"),
    ("Finset_prod_sigma", "_unknown", "Empty proposition"),
    ("Finset_prod_finset_product", "_unknown", "Empty proposition"),
    ("Finset_prod_finset_product_right", "_unknown", "Empty proposition"),
    ("Finset_prod_product", "_unknown", "Empty proposition"),
    ("Finset_prod_product_right", "_unknown", "Empty proposition"),
    ("Finset_prod_comm", "_unknown", "Empty proposition"),
    ("Finset_smul_prod", "_unknown", "Empty proposition"),
    ("Finset_prod_Ico_add", "_unknown", "Empty proposition"),
    ("Finset_sum_Ico_Ico_comm", "_unknown", "Empty proposition"),
    ("Nat_ModEq_listProd_map", "l_map_f_prod_l_map_g_prod_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_listProd_map_one", "l_map_f_prod_1_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_listProd_one", "l_prod_1_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_listSum_map", "l_map_f_sum_l_map_g_sum_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_listSum_map_zero", "l_map_f_sum_0_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_listSum_zero", "l_sum_0_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_multisetProd_map", "s_map_f_prod_s_map_g_prod_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_multisetProd_map_one", "s_map_f_prod_1_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_multisetProd_one", "s_prod_1_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_multisetSum_map", "s_map_f_sum_s_map_g_sum_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_multisetSum_map_zero", "s_map_f_sum_0_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_multisetSum_zero", "s_sum_0_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_prod_one", "x_in_s_f_x_1_MOD_n", "Not an equality or iff proposition"),
    ("Nat_ModEq_sum_zero", "x_in_s_f_x_0_MOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_listProd_map", "l_map_f_prod_l_map_g_prod_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_listProd_map_one", "l_map_f_prod_1_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_listProd_one", "l_prod_1_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_listSum_map", "l_map_f_sum_l_map_g_sum_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_listSum_map_zero", "l_map_f_sum_0_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_listSum_zero", "l_sum_0_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_multisetProd_map", "s_map_f_prod_s_map_g_prod_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_multisetProd_map_one", "s_map_f_prod_1_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_multisetProd_one", "s_prod_1_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_multisetSum_map", "s_map_f_sum_s_map_g_sum_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_multisetSum_map_zero", "s_map_f_sum_0_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_multisetSum_zero", "s_sum_0_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_prod_one", "x_in_s_f_x_1_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_ModEq_sum_zero", "x_in_s_f_x_0_ZMOD_n", "Not an equality or iff proposition"),
    ("Int_cast_injOn_of_ringChar_ne_two", "_0_1_minus_1_colon_Set_InjOn_colon_to_R", "Not an equality or iff proposition"),
    ("Nat_cast_injective", "Function_Injective_Nat_cast_colon_to_R", "Not an equality or iff proposition"),
    ("Nat_cast_add_one_ne_zero", "n_plus_1_colon_R_ne_0", "Not an equality or iff proposition"),
    ("GenContFract_IntFractPair_nth_stream_fr_nonneg", "_0_le_ifp_n_fr", "Not an equality or iff proposition"),
    ("IntFractPair_coe_stream", "_unknown", "Empty proposition"),
    ("IntFractPair_stream_succ_nth_fr_num_lt_nth_fr_num_rat", "ifp_succ_n_fr_num_lt_ifp_n_fr_num", "Not an equality or iff proposition"),
    ("IntFractPair_get", "_unknown", "Empty proposition"),
    ("IntFractPair_exists_succ_get", "_unknown", "Empty proposition"),
    ("Rat_cast_mk", "_unknown", "Empty proposition"),
    ("Int_fract_periodic", "Function_Periodic_Int_fract_1_colon_a", "Not an equality or iff proposition"),
    ("Finset_lcm_dvd", "forall_b_in_s_f_b_a_to_s_lcm_f_a", "Not an equality or iff proposition"),
    ("Finset_dvd_lcm", "f_b_s_lcm_f", "Not an equality or iff proposition"),
    ("Finset_lcm_mono_fun", "s_lcm_f_s_lcm_g", "Not an equality or iff proposition"),
    ("Finset_lcm_mono", "s_1_lcm_f_s_2_lcm_f", "Not an equality or iff proposition"),
    ("Finset_lcm_dvd_prod", "s_lcm_f_s_prod_f", "Not an equality or iff proposition"),
    ("Finset_associated_lcm_prod", "Associated_s_lcm_f_s_prod_f", "Not an equality or iff proposition"),
    ("Int_associated_natAbs", "Associated_k_k_natAbs", "Not an equality or iff proposition"),
    ("Fin_intCast_def", "_unknown", "Empty proposition"),
    ("Fin_lt_add_one_of_succ_lt", "a_lt_a_plus_1", "Not an equality or iff proposition"),
    ("Int_not_even_one", "not_Even_1_colon", "Not an equality or iff proposition"),
    ("Int_two_not_dvd_two_mul_add_one", "not_2_2_star_n_plus_1", "Not an equality or iff proposition"),
    ("Int_even_pow", "_unknown", "Empty proposition"),
    ("Int_eq_one_or_neg_one_of_mul_eq_one", "_unknown", "Empty proposition"),
    ("Int_eq_one_or_neg_one_of_mul_eq_neg_one", "_unknown", "Empty proposition"),
    ("Nat_not_even_one", "not_Even_1", "Not an equality or iff proposition"),
    ("Nat_two_not_dvd_two_mul_add_one", "not_2_2_star_n_plus_1", "Not an equality or iff proposition"),
    ("Nat_two_not_dvd_two_mul_sub_one", "_0_lt_n_to_not_2_2_star_n_minus_1", "Not an equality or iff proposition"),
    ("Nat_even_pow", "_unknown", "Empty proposition"),
    ("Nat_one_lt_of_ne_zero_of_even", "_1_lt_n", "Not an equality or iff proposition"),
    ("Nat_add_one_lt_of_even", "n_plus_1_lt_m", "Not an equality or iff proposition"),
    ("Finset_disjoint_range_addRightEmbedding", "Disjoint_range_a_map_addRightEmbedding_a_s", "Not an equality or iff proposition"),
    ("Finset_one_mem_one", "_1_colon_a_in_1_colon_Finset_a", "Not an equality or iff proposition"),
    ("Finset_one_nonempty", "_1_colon_Finset_a_Nonempty", "Not an equality or iff proposition"),
    ("Finset_coe_singletonOneHom", "singletonOneHom_colon_a_to_Finset_a_eq_singleton", "Not an equality or iff proposition"),
    ("Finset_smul_mem_smul", "a_in_s_to_b_in_t_to_a_b_in_s_t", "Not an equality or iff proposition"),
    ("Finset_card_smul_le", "hash_s_t_le_hash_s_star_hash_t", "Not an equality or iff proposition"),
    ("Finset_Nonempty_smul", "s_Nonempty_to_t_Nonempty_to_s_t_Nonempty", "Not an equality or iff proposition"),
    ("Finset_Nonempty_of_smul_left", "s_t_Nonempty_to_s_Nonempty", "Not an equality or iff proposition"),
    ("Finset_Nonempty_of_smul_right", "s_t_Nonempty_to_t_Nonempty", "Not an equality or iff proposition"),
    ("Finset_inter_smul_union_subset_union", "s_1_inter_s_2_t_1_union_t_2_sub_s_1_t_1_union_s_2_t_2", "Not an equality or iff proposition"),
    ("Finset_union_smul_inter_subset_union", "s_1_union_s_2_t_1_inter_t_2_sub_s_1_t_1_union_s_2_t_2", "Not an equality or iff proposition"),
    ("Finite_mul", "s_Finite_to_t_Finite_to_s_star_t_Finite", "Not an equality or iff proposition"),
    ("Finite_smul", "s_Finite_to_t_Finite_to_s_t_Finite", "Not an equality or iff proposition"),
    ("Finite_smul_set", "s_Finite_to_a_s_Finite", "Not an equality or iff proposition"),
    ("Finite_exists_type_univ_nonempty_mulEquiv", "exists_G_prime_colon_Type_v_colon_Group_G_prime_colon_Fintype_G_prime_Nonempty_G_star_G_prime", "Not an equality or iff proposition"),
    ("Finset_smul_zero_subset", "s_0_colon_Finset_b_sub_0", "Not an equality or iff proposition"),
    ("Finset_zero_mem_smul_finset", "_0_colon_b_in_a_t", "Not an equality or iff proposition"),
    ("Finset_card_le_card_mul_left_0", "hash_t_le_hash_s_star_t", "Not an equality or iff proposition"),
    ("Finset_card_le_card_mul_right_0", "hash_s_le_hash_s_star_t", "Not an equality or iff proposition"),
    ("Finset_card_le_card_mul_self_0", "hash_s_le_hash_s_star_s", "Not an equality or iff proposition"),
    ("ComplexShape_up_nat_odd_add", "Odd_i_plus_j", "Not an equality or iff proposition"),
    ("ComplexShape_down_nat_odd_add", "Odd_i_plus_j", "Not an equality or iff proposition"),
    ("ComplexShape_symm_bijective", "Function_Bijective_ComplexShape_symm_colon_ComplexShape_i_to_ComplexShape_i", "Not an equality or iff proposition"),
    ("ComplexShape_next_eq", "_unknown", "Empty proposition"),
    ("ComplexShape_next_eq_self", "_unknown", "Empty proposition"),
    ("ComplexShape_up", "_unknown", "Empty proposition"),
    ("ComplexShape_up_mk", "up_a_Rel_i_j", "Not an equality or iff proposition"),
    ("ComplexShape_rel_pi_1", "c_1_2_Rel_pi_c_1_c_2_c_1_2_i_1_i_2_pi_c_1_c_2_c_1_2_i_1_prime_i_2", "Not an equality or iff proposition"),
    ("ComplexShape_rel_pi_2", "c_1_2_Rel_pi_c_1_c_2_c_1_2_i_1_i_2_pi_c_1_c_2_c_1_2_i_1_i_2_prime", "Not an equality or iff proposition"),
    ("ComplexShape_rel_add", "c_Rel_p_plus_r_q_plus_r", "Not an equality or iff proposition"),
    ("ComplexShape_add_rel", "c_Rel_r_plus_p_r_plus_q", "Not an equality or iff proposition"),
    ("ComplexShape_next_add", "_unknown", "Empty proposition"),
    ("ComplexShape_Embedding_AreComplementary_symm", "AreComplementary_e_2_e_1", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_AreComplementary_fromSum_bijective", "Function_Bijective_fromSum_e_1_e_2", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_AreComplementary_desc", "_unknown", "Empty proposition"),
    ("ComplexShape_Embedding_AreComplementary_desc", "_unknown", "Empty proposition"),
    ("ComplexShape_Embedding_hom_ext", "_unknown", "Empty proposition"),
    ("ComplexShape_Embedding_Boundary_fst", "e_1_BoundaryLE_i_1", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_Boundary_snd", "e_2_BoundaryGE_i_2", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_exists_1", "exists_i_2_ac_Boundary_i_1_i_2", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_exists_2", "exists_i_1_ac_Boundary_i_1_i_2", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_of_boundaryLE", "ac_Boundary_i_1_indexOfBoundaryLE_ac_h", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_of_boundaryGE", "ac_Boundary_indexOfBoundaryGE_ac_h_i_2", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_boundaryGE", "e_BoundaryGE_j", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_not_boundaryGE_next", "not_e_BoundaryGE_k", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_not_boundaryGE_next", "_unknown", "Empty proposition"),
    ("ComplexShape_Embedding_BoundaryGE_notMem", "e_f_a_ne_i_prime", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_BoundaryGE_false_of_isTruncLE", "False", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_boundaryLE", "e_BoundaryLE_j", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_not_boundaryLE_prev", "not_e_BoundaryLE_i", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_not_boundaryLE_prev", "_unknown", "Empty proposition"),
    ("ComplexShape_Embedding_BoundaryLE_notMem", "e_f_a_ne_k_prime", "Not an equality or iff proposition"),
    ("ComplexShape_Embedding_BoundaryLE_false_of_isTruncGE", "False", "Not an equality or iff proposition"),
    ("ComplexShape_homRestrict_hasLift", "e_HasLift_e_homRestrict_psi", "Not an equality or iff proposition"),
    ("ComplexShape_not_rel_self", "not_c_Rel_j_j", "Not an equality or iff proposition"),
    ("ComplexShape_not_rel_of_eq", "not_c_Rel_j_j_prime", "Not an equality or iff proposition"),
    ("ComplexShape_exists_distinct_prev_or", "exists_k_colon_i_c_Rel_j_k_and_j_ne_k_or_forall_k_colon_i_not_c_Rel_j_k", "Not an equality or iff proposition"),
    ("ComplexShape_exists_distinct_next_or", "exists_i_colon_i_c_Rel_i_j_and_i_ne_j_or_forall_i_colon_i_not_c_Rel_i_j", "Not an equality or iff proposition"),
    ("ComplexShape_hasNoLoop_up", "_unknown", "Empty proposition"),
    ("ComplexShape_hasNoLoop_down", "_unknown", "Empty proposition"),
    ("ComplexShape_hasNoLoop_up", "up_a_HasNoLoop", "Not an equality or iff proposition"),
    ("ComplexShape_hasNoLoop_down", "down_a_HasNoLoop", "Not an equality or iff proposition"),
    ("ComplexShape_quotient_isLocalization", "HomotopyCategory_quotient_C_c_IsLocalization_HomologicalComplex_homotop", "Not an equality or iff proposition"),
    ("ComplexShape_QFactorsThroughHomotopy_of_exists_prev", "c_QFactorsThroughHomotopy_C", "Not an equality or iff proposition"),
    ("Nat_Prime_isPrimePow", "IsPrimePow_p", "Not an equality or iff proposition"),
    ("Finset_mem_finsuppAntidiag", "_unknown", "Empty proposition"),
    ("Finset_finsuppAntidiag_mono", "finsuppAntidiag_s_n_sub_finsuppAntidiag_t_n", "Not an equality or iff proposition"),
    ("Finset_mapRange_finsuppAntidiag_subset", "finsuppAntidiag_s_n_map_mapRange_addEquiv_e_toEmbedding_sub_finsuppAntidiag_s", "Not an equality or iff proposition"),
    ("Nat_dvd_of_mem_finMulAntidiag", "f_i_n", "Not an equality or iff proposition"),
    ("Nat_ne_zero_of_mem_finMulAntidiag", "f_i_ne_0", "Not an equality or iff proposition"),
    ("Nat_finMulAntidiag_existsUnique_prime_dvd", "exists_bang_i_p_f_i", "Not an equality or iff proposition"),
    ("Nat_primeFactorsPiBij_img", "Nat_primeFactorsPiBij_d_n_f_hf_in_finMulAntidiag_d_n", "Not an equality or iff proposition"),
    ("Nat_card_pair_lcm_eq_f_img", "f_a_ha_in_Finset_filter_fun_x_y_eq_gt_x_lcm_y_eq_n_n_divisors_times_n_divisors", "Not an equality or iff proposition"),
    ("Nat_card_pair_lcm_eq_f_surj", "exists_a_colon_Fin_3_to_ha_colon_a_in_finMulAntidiag_3_n_f_a_ha_eq_b", "Not an equality or iff proposition"),
    ("FiniteMulArchimedeanClass_ind", "forall_x_motive_x", "Not an equality or iff proposition"),
    ("Finset_one_le_prod", "_unknown", "Empty proposition"),
    ("Finset_one_le_prod", "_unknown", "Empty proposition"),
    ("Finset_prod_le_one", "_unknown", "Empty proposition"),
    ("Finset_prod_le_prod_of_subset_of_one_le", "_unknown", "Empty proposition"),
    ("Finset_prod_le_prod_of_subset_of_le_one", "_unknown", "Empty proposition"),
    ("Finset_prod_mono_set_of_one_le", "_unknown", "Empty proposition"),
    ("Finset_prod_anti_set_of_le_one", "_unknown", "Empty proposition"),
    ("Finset_prod_le_univ_prod_of_one_le", "_unknown", "Empty proposition"),
    ("Finset_prod_eq_one_iff_of_one_le", "_unknown", "Empty proposition"),
    ("Finset_prod_eq_one_iff_of_le_one", "_unknown", "Empty proposition"),
    ("Finset_prod_le_pow_card", "s_prod_f_le_n_pow_hash_s", "Not an equality or iff proposition"),
    ("Finset_pow_card_le_prod", "n_pow_hash_s_le_s_prod_f", "Not an equality or iff proposition"),
    ("Finset_card_biUnion_le_card_mul", "hash_s_biUnion_f_le_hash_s_star_n", "Not an equality or iff proposition"),
    ("Finset_prod_fiberwise_le_prod_of_one_le_prod_fiber", "_unknown", "Empty proposition"),
    ("Finset_prod_le_prod_fiberwise_of_prod_fiber_le_one", "_unknown", "Empty proposition"),
    ("Fintype_prod_mono", "_unknown", "Empty proposition"),
    ("Fintype_one_le_prod", "_1_le_i_f_i", "Not an equality or iff proposition"),
]
