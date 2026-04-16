"""Mathlib: List Map — auto-generated from Mathlib4.

Contains 149 rewrite rules derived from Mathlib theorems.
Plus 50 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_list_map"
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
# Rewrite rules (149 total)
# ════════════════════════════════════════════════════════════

def _r0000_norm_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.norm_prod
    # ‖l.prod‖ = (l.map norm).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_map_norm_prod")
            results.append((rhs, "Mathlib: List_norm_prod"))
    except Exception:
        pass
    return results


def _r0001_lookmap_cons_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookmap_cons_none
    # (a :: l).lookmap f = a :: l.lookmap f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_lookmap", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("l_lookmap"), args[0],))
            results.append((rhs, "Mathlib: List_lookmap_cons_none"))
        except Exception:
            pass
    return results


def _r0002_map_permutationsAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_permutationsAux
    # ∀ ts is :     List α, map (map f) (permutationsAux ts is) = permutationsAux (map f ts) (map f is)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("permutationsAux", (OOp("map", (OVar("f"), OVar("ts"),)), OOp("map", (OVar("f"), OVar("is"),)),))
            results.append((rhs, "Mathlib: List_map_permutationsAux"))
        except Exception:
            pass
    return results


def _r0003_cons_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Pi.cons_map
    # cons _ _ (φ a) (fun j hj ↦ φ (f j hj)) = (fun j hj ↦ φ ((cons _ _ a f) j hj))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons", 4)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("j"), OVar("hj"), args[1], OVar("phi"), OOp("cons_a_f", (OVar("j"), OVar("hj"),)),))
            results.append((rhs, "Mathlib: List_Pi_cons_map"))
        except Exception:
            pass
    return results


def _r0004_pi_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.pi_cons
    # pi (i :: l) t = ((t i).flatMap fun b ↦ (pi l t).map <| Pi.cons _ _ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pi", 2)
    if args is not None:
        try:
            rhs = OOp("t_i_flatMap", (OVar("fun"), OVar("b"), OVar("_unknown"), OVar("pi_l_t_map"), OVar("lt_pipe"), OVar("Pi_cons"), OVar("_unknown"), OVar("_unknown"), OVar("b"),))
            results.append((rhs, "Mathlib: List_pi_cons"))
        except Exception:
            pass
    return results


def _r0005_product_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.product_cons
    # (a :: l₁) ×ˢ l₂ = map (fun b => (a, b)) l₂ ++ (l₁ ×ˢ l₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_1", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("map", (OOp("fun", (OVar("b"), OVar("eq_gt"), OOp("a", (OVar("b"),)),)), args[1],)), OOp("l_1", (args[0], args[1],))))
            results.append((rhs, "Mathlib: List_product_cons"))
        except Exception:
            pass
    return results


def _r0006_sigma_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sigma_cons
    # (a :: l₁).sigma l₂ = map (Sigma.mk a) (l₂ a) ++ l₁.sigma l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_1_sigma", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("map", (OOp("Sigma_mk", (OVar("a"),)), OOp("l_2", (OVar("a"),)),)), OOp("l_1_sigma", (args[0],))))
            results.append((rhs, "Mathlib: List_sigma_cons"))
        except Exception:
            pass
    return results


def _r0007_reduceOption_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_map
    # reduceOption (map (Option.map f) l) = map f (reduceOption l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reduceOption", 1)
    if args is not None:
        try:
            rhs = OOp("map", (OVar("f"), OOp("reduceOption", (OVar("l"),)),))
            results.append((rhs, "Mathlib: List_reduceOption_map"))
        except Exception:
            pass
    return results


def _r0008_sublistsLen_succ_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsLen_succ_cons
    # sublistsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublistsLen", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("sublistsLen", (OOp("+", (OVar("n"), OLit(1))), OVar("l"),)), OOp("sublistsLen_n_l_map", (OOp("cons", (OVar("a"),)),))))
            results.append((rhs, "Mathlib: List_sublistsLen_succ_cons"))
        except Exception:
            pass
    return results


def _r0009_revzip_map_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.revzip_map_fst
    # (revzip l).map Prod.fst = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "revzip_l_map", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_revzip_map_fst"))
        except Exception:
            pass
    return results


def _r0010_revzip_map_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.revzip_map_snd
    # (revzip l).map Prod.snd = l.reverse
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "revzip_l_map", 1)
    if args is not None:
        try:
            rhs = OVar("l_reverse")
            results.append((rhs, "Mathlib: List_revzip_map_snd"))
        except Exception:
            pass
    return results


def _r0011_sum_fib_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsZeckendorfRep.sum_fib_lt
    # ∀ {n l}, IsZeckendorfRep l → (∀ a ∈ (l ++ [0]).head?, a < n) →     (l.map fib).sum < fib n   | _, [], _, hn => fib_pos.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("fib_pos_2"), OVar("lt_pipe"), OVar("hn"), OVar("_unknown"), OVar("rfl"), OVar("pipe"), OVar("n"), OVar("a"), OVar("colon_colon"), OVar("l"), OVar("hl"), OVar("hn"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_IsZeckendorfRep_sum_fib_lt"))
        except Exception:
            pass
    return results


def _r0012_pmap_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.pmap_cons
    # (cons a v).pmap f hp = cons (f a (by       simp only [Nat.succ_eq_add_one, toList_cons, List.mem_cons, forall_eq_or_imp]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons_a_v_pmap", 2)
    if args is not None:
        try:
            rhs = OOp("cons", (OOp("f", (OVar("a"), OOp("by", (OVar("simp"), OVar("only"), OVar("Nat_succ_eq_add_one_toList_cons_List_mem_cons_forall_eq_or_imp"), OVar("at"), args[1], OVar("exact"), OVar("hp_1"),)),)), OOp("v_pmap", (args[0], OOp("by", (OVar("simp"), OVar("only"), OVar("Nat_succ_eq_add_one_toList_cons_List_mem_cons_forall_eq_or_imp"), OVar("at"), args[1], OVar("exact"), OVar("hp_2"),)),)),))
            results.append((rhs, "Mathlib: List_Vector_pmap_cons"))
        except Exception:
            pass
    return results


def _r0013_head_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.head_map
    # (v.map f).head = f v.head
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_map_f_head")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("v_head"),))
            results.append((rhs, "Mathlib: List_Vector_head_map"))
    except Exception:
        pass
    return results


def _r0014_get_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.get_map
    # (v.map f).get i = f (v.get i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_map_f_get", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("v_get", (args[0],)),))
            results.append((rhs, "Mathlib: List_Vector_get_map"))
        except Exception:
            pass
    return results


def _r0015_map_2_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.map₂_cons
    # Vector.map₂ f (hd₁ ::ᵥ tl₁) (hd₂ ::ᵥ tl₂) = f hd₁ hd₂ ::ᵥ (Vector.map₂ f tl₁ tl₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Vector_map_2", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("hd_1"), OVar("hd_2"), OVar("colon_colon"), OOp("Vector_map_2", (args[0], OVar("tl_1"), OVar("tl_2"),)),))
            results.append((rhs, "Mathlib: List_Vector_map_2_cons"))
        except Exception:
            pass
    return results


def _r0016_prod_toFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_toFinset
    # ∀ {l : List ι} (_hl : l.Nodup), l.toFinset.prod f = (l.map f).prod   | [], _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 1)
    if args is not None:
        try:
            rhs = OOp("l_map_f_prod", (OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_prod_toFinset"))
        except Exception:
            pass
    return results


def _r0017_prod_hom_nonempty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_hom_nonempty
    # (l.map f).prod = f l.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_map_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("l_prod"),))
            results.append((rhs, "Mathlib: List_prod_hom_nonempty"))
    except Exception:
        pass
    return results


def _r0018_prod_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_hom
    # (l.map f).prod = f l.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_map_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("l_prod"),))
            results.append((rhs, "Mathlib: List_prod_hom"))
    except Exception:
        pass
    return results


def _r0019_prod_hom_2_nonempty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_hom₂_nonempty
    # (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_map_fun_i_eq_gt_f_f_1_i_f_2_i_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("l_map_f_1_prod"), OVar("l_map_f_2_prod"),))
            results.append((rhs, "Mathlib: List_prod_hom_2_nonempty"))
    except Exception:
        pass
    return results


def _r0020_prod_hom_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_hom₂
    # (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_map_fun_i_eq_gt_f_f_1_i_f_2_i_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("l_map_f_1_prod"), OVar("l_map_f_2_prod"),))
            results.append((rhs, "Mathlib: List_prod_hom_2"))
    except Exception:
        pass
    return results


def _r0021_prod_map_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_map_mul
    # (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_map_fun_i_eq_gt_f_i_star_g_i_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("l_map_f_prod"), OVar("l_map_g_prod")))
            results.append((rhs, "Mathlib: List_prod_map_mul"))
    except Exception:
        pass
    return results


def _r0022_prod_map_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_map_hom
    # (L.map (g ∘ f)).prod = g (L.map f).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L_map_g_comp_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g", (OVar("L_map_f_prod"),))
            results.append((rhs, "Mathlib: List_prod_map_hom"))
    except Exception:
        pass
    return results


def _r0023_prod_range_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_range_succ
    # ((range n.succ).map f).prod = ((range n).map f).prod * f n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("range_n_succ_map_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("range_n_map_f_prod"), OOp("f", (OVar("n"),))))
            results.append((rhs, "Mathlib: List_prod_range_succ"))
    except Exception:
        pass
    return results


def _r0024_prod_map_eq_pow_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_map_eq_pow_single
    # (l.map f).prod = f a ^ l.count a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_map_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OOp("f", (OVar("a"),)), OOp("l_count", (OVar("a"),))))
            results.append((rhs, "Mathlib: List_prod_map_eq_pow_single"))
    except Exception:
        pass
    return results


def _r0025_smul_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.smul_sum
    # r • l.sum = (l.map (r • ·)).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r", 2)
    if args is not None:
        try:
            rhs = OVar("l_map_r_sum")
            results.append((rhs, "Mathlib: List_smul_sum"))
        except Exception:
            pass
    return results


def _r0026_sum_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sum_smul
    # l.sum • x = (l.map fun r ↦ r • x).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_sum", 2)
    if args is not None:
        try:
            rhs = OVar("l_map_fun_r_r_x_sum")
            results.append((rhs, "Mathlib: List_sum_smul"))
        except Exception:
            pass
    return results


def _r0027_trop_minimum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.trop_minimum
    # trop l.minimum = List.sum (l.map (trop ∘ WithTop.some))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trop", 1)
    if args is not None:
        try:
            rhs = OOp("sum", (OOp("l_map", (OOp("comp", (OVar("trop"), OVar("WithTop_some"))),)),))
            results.append((rhs, "Mathlib: List_trop_minimum"))
        except Exception:
            pass
    return results


def _r0028_norm_prod_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.norm_prod_le
    # ∀ l : List α, ‖l.prod‖ ≤ (l.map norm).prod   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_norm_prod_le"))
        except Exception:
            pass
    return results


def _r0029_nnnorm_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nnnorm_prod
    # ‖l.prod‖₊ = (l.map nnnorm).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_map_nnnorm_prod")
            results.append((rhs, "Mathlib: List_nnnorm_prod"))
    except Exception:
        pass
    return results


def _r0030_map_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.map_mk
    # (ListBlank.mk l).map f = ListBlank.mk (l.map f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ListBlank_mk_l_map", 1)
    if args is not None:
        try:
            rhs = OOp("ListBlank_mk", (OOp("l_map", (args[0],)),))
            results.append((rhs, "Mathlib: Turing_ListBlank_map_mk"))
        except Exception:
            pass
    return results


def _r0031_head_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.head_map
    # (l.map f).head = f l.head
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_map_f_head")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("l_head"),))
            results.append((rhs, "Mathlib: Turing_ListBlank_head_map"))
    except Exception:
        pass
    return results


def _r0032_tail_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.tail_map
    # (l.map f).tail = l.tail.map f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_map_f_tail")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_tail_map", (OVar("f"),))
            results.append((rhs, "Mathlib: Turing_ListBlank_tail_map"))
    except Exception:
        pass
    return results


def _r0033_map_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.map_cons
    # (l.cons a).map f = (l.map f).cons (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_cons_a_map", 1)
    if args is not None:
        try:
            rhs = OOp("l_map_f_cons", (OOp("f", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Turing_ListBlank_map_cons"))
        except Exception:
            pass
    return results


def _r0034_nth_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.nth_map
    # (l.map f).nth n = f (l.nth n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map_f_nth", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("l_nth", (args[0],)),))
            results.append((rhs, "Mathlib: Turing_ListBlank_nth_map"))
        except Exception:
            pass
    return results


def _r0035_map_modifyNth(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.map_modifyNth
    # (L.modifyNth f n).map F = (L.map F).modifyNth f' n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_modifyNth_f_n_map", 1)
    if args is not None:
        try:
            rhs = OOp("L_map_F_modifyNth", (OVar("f_prime"), OVar("n"),))
            results.append((rhs, "Mathlib: Turing_ListBlank_map_modifyNth"))
        except Exception:
            pass
    return results


def _r0036_flatMap_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.flatMap_mk
    # (ListBlank.mk l).flatMap f hf = ListBlank.mk (l.flatMap f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ListBlank_mk_l_flatMap", 2)
    if args is not None:
        try:
            rhs = OOp("ListBlank_mk", (OOp("l_flatMap", (args[0],)),))
            results.append((rhs, "Mathlib: Turing_ListBlank_flatMap_mk"))
        except Exception:
            pass
    return results


def _r0037_cons_flatMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.cons_flatMap
    # (l.cons a).flatMap f hf = (l.flatMap f hf).append (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_cons_a_flatMap", 2)
    if args is not None:
        try:
            rhs = OOp("l_flatMap_f_hf_append", (OOp("f", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Turing_ListBlank_cons_flatMap"))
        except Exception:
            pass
    return results


def _r0038_antidiagonalTuple_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.antidiagonalTuple_two
    # antidiagonalTuple 2 n = (antidiagonal n).map fun i => ![i.1, i.2]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OOp("antidiagonal_n_map", (OVar("fun"), OVar("i"), OVar("eq_gt"), OOp("not", (OVar("i_1_i_2"),)),))
            results.append((rhs, "Mathlib: List_Nat_antidiagonalTuple_two"))
        except Exception:
            pass
    return results


def _r0039_toFinset_filterMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_filterMap
    # (s.filterMap f).toFinset = s.toFinset.filterMap f f_inj
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_filterMap_f_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s_toFinset_filterMap", (OVar("f"), OVar("f_inj"),))
            results.append((rhs, "Mathlib: List_toFinset_filterMap"))
    except Exception:
        pass
    return results


def _r0040_nat_divisors_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nat_divisors_prod
    # divisors l.prod = (l.map divisors).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "divisors", 1)
    if args is not None:
        try:
            rhs = OVar("l_map_divisors_prod")
            results.append((rhs, "Mathlib: List_nat_divisors_prod"))
        except Exception:
            pass
    return results


def _r0041_bind_eq_flatMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.bind_eq_flatMap
    # l >>= f = l.flatMap f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = OOp("l_flatMap", (args[1],))
            results.append((rhs, "Mathlib: List_bind_eq_flatMap"))
        except Exception:
            pass
    return results


def _r0042_map_reverseAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_reverseAux
    # map f (reverseAux l₁ l₂) = reverseAux (map f l₁) (map f l₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("reverseAux", (OOp("map", (args[0], OVar("l_1"),)), OOp("map", (args[0], OVar("l_2"),)),))
            results.append((rhs, "Mathlib: List_map_reverseAux"))
        except Exception:
            pass
    return results


def _r0043_count_map_of_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_map_of_injective
    # count (f x) (map f l) = count x l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("count", (OVar("x"), OVar("l"),))
            results.append((rhs, "Mathlib: List_count_map_of_injective"))
        except Exception:
            pass
    return results


def _r0044_pmap_next_eq_rotate_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.pmap_next_eq_rotate_one
    # (l.pmap l.next fun _ h => h) = l.rotate 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_pmap", 6)
    if args is not None:
        try:
            rhs = OOp("l_rotate", (OLit(1),))
            results.append((rhs, "Mathlib: List_pmap_next_eq_rotate_one"))
        except Exception:
            pass
    return results


def _r0045_dedup_map_of_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_map_of_injective
    # (xs.map f).dedup = xs.dedup.map f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("xs_map_f_dedup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("xs_dedup_map", (OVar("f"),))
            results.append((rhs, "Mathlib: List_dedup_map_of_injective"))
    except Exception:
        pass
    return results


def _r0046_destutter_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.destutter_eq_nil
    # ∀ {l : List α}, destutter R l = [] ↔ l = []   | [] => Iff.rfl   | _ :: l => ⟨fun h => absurd h <| l.destutter'_ne_nil R,
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_destutter_R_map", 1)
    if args is not None:
        try:
            rhs = OOp("l_map_f_destutter", (OVar("R_2"), OVar("pipe"), OVar("_unknown"), OVar("hl"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_destutter_eq_nil"))
        except Exception:
            pass
    return results


def _r0047_map_destutter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_destutter
    # ∀ {l : List α}, (∀ a ∈ l, ∀ b ∈ l, R a b ↔ R₂ (f a) (f b)) →     (l.destutter R).map f = (l.map f).destutter R₂   | [], 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_destutter_R_map", 1)
    if args is not None:
        try:
            rhs = OOp("l_map_f_destutter", (OVar("R_2"), OVar("pipe"), OVar("_unknown"), OVar("hl"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_map_destutter"))
        except Exception:
            pass
    return results


def _r0048_map_destutter_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_destutter_ne
    # (l.destutter (· ≠ ·)).map f = (l.map f).destutter (· ≠ ·)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_destutter_ne_map", 1)
    if args is not None:
        try:
            rhs = OOp("l_map_f_destutter", (OOp("!=", (OVar("_unknown"), OVar("_unknown"))),))
            results.append((rhs, "Mathlib: List_map_destutter_ne"))
        except Exception:
            pass
    return results


def _r0049_finRange_succ_eq_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.finRange_succ_eq_map
    # finRange n.succ = 0 :: (finRange n).map Fin.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finRange", 1)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("colon_colon"), OVar("finRange_n_map"), OVar("Fin_succ"),))
            results.append((rhs, "Mathlib: List_finRange_succ_eq_map"))
        except Exception:
            pass
    return results


def _r0050_ofFn_eq_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_eq_pmap
    # ofFn f = pmap (fun i hi => f ⟨i, hi⟩) (range n) fun _ => mem_range.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn", 1)
    if args is not None:
        try:
            rhs = OOp("pmap", (OOp("fun", (OVar("i"), OVar("hi"), OVar("eq_gt"), args[0], OVar("i_hi"),)), OOp("range", (OVar("n"),)), OVar("fun"), OVar("_unknown"), OVar("eq_gt"), OVar("mem_range_1"),))
            results.append((rhs, "Mathlib: List_ofFn_eq_pmap"))
        except Exception:
            pass
    return results


def _r0051_ofFn_eq_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_eq_map
    # ofFn f = (finRange n).map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn", 1)
    if args is not None:
        try:
            rhs = OOp("finRange_n_map", (args[0],))
            results.append((rhs, "Mathlib: List_ofFn_eq_map"))
        except Exception:
            pass
    return results


def _r0052_append_flatten_map_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.append_flatten_map_append
    # x ++ (L.map (· ++ x)).flatten = (L.map (x ++ ·)).flatten ++ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("L_map_x_plus_plus_flatten"), args[0]))
            results.append((rhs, "Mathlib: List_append_flatten_map_append"))
        except Exception:
            pass
    return results


def _r0053_getD_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getD_map
    # (map f l).getD n (f d) = f (l.getD n d)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_f_l_getD", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("l_getD", (args[0], OVar("d"),)),))
            results.append((rhs, "Mathlib: List_getD_map"))
        except Exception:
            pass
    return results


def _r0054_insertIdx_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.insertIdx_pmap
    # (l.pmap f hl).insertIdx n (f a ha) = (l.insertIdx n a).pmap f       (fun _ h ↦ (eq_or_mem_of_mem_insertIdx h).elim (fun 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_pmap_f_hl_insertIdx", 2)
    if args is not None:
        try:
            rhs = OOp("l_insertIdx_n_a_pmap", (OVar("f"), OOp("fun", (OVar("_unknown"), OVar("h"), OVar("_unknown"), OVar("eq_or_mem_of_mem_insertIdx_h_elim"), OOp("subst", (OOp("fun", (OVar("heq"), OVar("_unknown"), OVar("heq"),)), OVar("ha"))), OOp("hl", (OVar("_unknown"),)),)),))
            results.append((rhs, "Mathlib: List_insertIdx_pmap"))
        except Exception:
            pass
    return results


def _r0055_map_insertIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_insertIdx
    # (l.insertIdx n a).map f = (l.map f).insertIdx n (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_insertIdx_n_a_map", 1)
    if args is not None:
        try:
            rhs = OOp("l_map_f_insertIdx", (OVar("n"), OOp("f", (OVar("a"),)),))
            results.append((rhs, "Mathlib: List_map_insertIdx"))
        except Exception:
            pass
    return results


def _r0056_eraseIdx_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.eraseIdx_pmap
    # (pmap f l hl).eraseIdx n = (l.eraseIdx n).pmap f fun a ha ↦ hl a (eraseIdx_subset ha)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pmap_f_l_hl_eraseIdx", 1)
    if args is not None:
        try:
            rhs = OOp("l_eraseIdx_n_pmap", (OVar("f"), OVar("fun"), OVar("a"), OVar("ha"), OVar("_unknown"), OVar("hl"), OVar("a"), OOp("eraseIdx_subset", (OVar("ha"),)),))
            results.append((rhs, "Mathlib: List_eraseIdx_pmap"))
        except Exception:
            pass
    return results


def _r0057_eraseIdx_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.eraseIdx_map
    # (map f l).eraseIdx n = (l.eraseIdx n).map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_f_l_eraseIdx", 1)
    if args is not None:
        try:
            rhs = OOp("l_eraseIdx_n_map", (OVar("f"),))
            results.append((rhs, "Mathlib: List_eraseIdx_map"))
        except Exception:
            pass
    return results


def _r0058_map_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.map_add
    # (Ico n m).map (k + ·) = Ico (n + k) (m + k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico_n_m_map", 1)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("+", (OVar("n"), OVar("k"))), OOp("+", (OVar("m"), OVar("k"))),))
            results.append((rhs, "Mathlib: List_Ico_map_add"))
        except Exception:
            pass
    return results


def _r0059_map_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.map_sub
    # ((Ico n m).map fun x => x - k) = Ico (n - k) (m - k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("-", (OVar("n"), args[1])), OOp("-", (OVar("m"), args[1])),))
            results.append((rhs, "Mathlib: List_Ico_map_sub"))
        except Exception:
            pass
    return results


def _r0060_range_map_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.range_map_iterate
    # (List.range n).map (f^[·] a) = List.iterate f a n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_range_n_map", 1)
    if args is not None:
        try:
            rhs = OOp("List_iterate", (OVar("f"), OVar("a"), OVar("n"),))
            results.append((rhs, "Mathlib: List_range_map_iterate"))
        except Exception:
            pass
    return results


def _r0061_lookmap_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookmap_nil
    # [].lookmap f = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lookmap", 1)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_lookmap_nil"))
        except Exception:
            pass
    return results


def _r0062_lookmap_cons_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookmap_cons_some
    # (a :: l).lookmap f = b :: l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_lookmap", 1)
    if args is not None:
        try:
            rhs = OOp("b", (OVar("colon_colon"), OVar("l"),))
            results.append((rhs, "Mathlib: List_lookmap_cons_some"))
        except Exception:
            pass
    return results


def _r0063_lookmap_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookmap_cons
    # (a :: l).lookmap f = match f a with     | none => a :: l.lookmap f     | some b => b :: l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_lookmap", 1)
    if args is not None:
        try:
            rhs = OOp("match", (args[0], OVar("a"), OVar("with"), OVar("pipe"), OVar("none"), OVar("eq_gt"), OVar("a"), OVar("colon_colon"), OVar("l_lookmap"), args[0], OVar("pipe"), OVar("some"), OVar("b"), OVar("eq_gt"), OVar("b"), OVar("colon_colon"), OVar("l"),))
            results.append((rhs, "Mathlib: List_lookmap_cons"))
        except Exception:
            pass
    return results


def _r0064_lookmap_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookmap_some
    # ∀ l : List α, l.lookmap some = l   | [] => rfl   | _ :: _ => rfl  theorem lookmap_none : ∀ l : List α, (l.lookmap fun _ 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_lookmap", 1)
    if args is not None:
        try:
            rhs = OOp("l_lookmap", (OVar("g"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a"), OVar("colon_colon"), OVar("l"), OVar("H"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_lookmap_some"))
        except Exception:
            pass
    return results


def _r0065_lookmap_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookmap_none
    # ∀ l : List α, (l.lookmap fun _ => none) = l   | [] => rfl   | a :: l => (lookmap_cons_none _ l rfl).trans (congr_arg (co
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_lookmap", 1)
    if args is not None:
        try:
            rhs = OOp("l_lookmap", (OVar("g"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a"), OVar("colon_colon"), OVar("l"), OVar("H"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_lookmap_none"))
        except Exception:
            pass
    return results


def _r0066_lookmap_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookmap_congr
    # ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.lookmap f = l.lookmap g   | [], _ => rfl   | a :: l, H =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_lookmap", 1)
    if args is not None:
        try:
            rhs = OOp("l_lookmap", (OVar("g"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a"), OVar("colon_colon"), OVar("l"), OVar("H"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_lookmap_congr"))
        except Exception:
            pass
    return results


def _r0067_lookmap_map_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookmap_map_eq
    # ∀ l : List α, map g (l.lookmap f) = map g l   | [] => rfl   | a :: l =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("map", (args[0], OVar("l"), OVar("pipe"), OSeq(()), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a"), OVar("colon_colon"), OVar("l"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_lookmap_map_eq"))
        except Exception:
            pass
    return results


def _r0068_antidiagonal_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.antidiagonal_succ
    # antidiagonal (n + 1) = (0, n + 1) :: (antidiagonal n).map (Prod.map Nat.succ id)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonal", 1)
    if args is not None:
        try:
            rhs = OOp("_0_n_plus_1", (OVar("colon_colon"), OVar("antidiagonal_n_map"), OOp("Prod_map", (OVar("Nat_succ"), OVar("id"),)),))
            results.append((rhs, "Mathlib: List_Nat_antidiagonal_succ"))
        except Exception:
            pass
    return results


def _r0069_map_swap_antidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.map_swap_antidiagonal
    # (antidiagonal n).map Prod.swap = (antidiagonal n).reverse
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonal_n_map", 1)
    if args is not None:
        try:
            rhs = OVar("antidiagonal_n_reverse")
            results.append((rhs, "Mathlib: List_Nat_map_swap_antidiagonal"))
        except Exception:
            pass
    return results


def _r0070_inj_on_of_nodup_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.inj_on_of_nodup_map
    # ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_inj_on_of_nodup_map"))
    except Exception:
        pass
    return results


def _r0071_nodup_map_iff_inj_on(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_map_iff_inj_on
    # Nodup (map f l) ↔ ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_nodup_map_iff_inj_on"))
    except Exception:
        pass
    return results


def _r0072_map_update(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.map_update
    # l.map (Function.update f x y) =       if x ∈ l then (l.map f).set (l.idxOf x) y else l.map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("if", (OVar("x"),)), OOp("l", (OVar("then"), OVar("l_map_f_set"), OOp("l_idxOf", (OVar("x"),)), OVar("y"), OVar("else"), OVar("l_map"), OVar("f"),))))
            results.append((rhs, "Mathlib: List_Nodup_map_update"))
        except Exception:
            pass
    return results


def _r0073_map_prodMap_offDiag(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_prodMap_offDiag
    # map (Prod.map f f) l.offDiag = (map f l).offDiag
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OVar("map_f_l_offDiag")
            results.append((rhs, "Mathlib: List_map_prodMap_offDiag"))
        except Exception:
            pass
    return results


def _r0074_eq_map_comp_perm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.eq_map_comp_perm
    # (· = map f ·) ∘r (· ~ ·) = (· ~ map f ·)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eq_map_f", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("tilde"), OVar("map"), OVar("f"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: List_eq_map_comp_perm"))
        except Exception:
            pass
    return results


def _r0075_map_permutationsAux2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_permutationsAux2
    # (permutationsAux2 t ts [] ys id).2.map f = (permutationsAux2 t ts [] ys f).2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "permutationsAux2_t_ts_ys_id_2_map", 1)
    if args is not None:
        try:
            rhs = OVar("permutationsAux2_t_ts_ys_f_2")
            results.append((rhs, "Mathlib: List_map_permutationsAux2"))
        except Exception:
            pass
    return results


def _r0076_permutationsAux2_snd_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutationsAux2_snd_eq
    # (permutationsAux2 t ts r ys f).2 =       ((permutationsAux2 t [] [] ys id).2.map fun x => f (x ++ ts)) ++ r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("permutationsAux2_t_ts_r_ys_f_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OOp("permutationsAux2_t_ys_id_2_map", (OVar("fun"), OVar("x"), OVar("eq_gt"), OVar("f"), OOp("concat", (OVar("x"), OVar("ts"))),)), OVar("r")))
            results.append((rhs, "Mathlib: List_permutationsAux2_snd_eq"))
    except Exception:
        pass
    return results


def _r0077_map_map_permutationsAux2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_map_permutationsAux2
    # map (map g) (permutationsAux2 t ts [] ys id).2 =       (permutationsAux2 (g t) (map g ts) [] (map g ys) id).2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OVar("permutationsAux2_g_t_map_g_ts_map_g_ys_id_2")
            results.append((rhs, "Mathlib: List_map_map_permutationsAux2"))
        except Exception:
            pass
    return results


def _r0078_map_permutations(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_permutations
    # map (map f) (permutations ts) = permutations (map f ts)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("permutations", (OOp("map", (OVar("f"), OVar("ts"),)),))
            results.append((rhs, "Mathlib: List_map_permutations"))
        except Exception:
            pass
    return results


def _r0079_permutationsAux_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutationsAux_append
    # permutationsAux (is ++ ts) is' =       (permutationsAux is is').map (· ++ ts) ++ permutationsAux ts (is.reverse ++ is')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "permutationsAux", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("permutationsAux_is_is_prime_map", (OOp("concat", (OVar("_unknown"), OVar("ts"))),)), OOp("permutationsAux", (OVar("ts"), OOp("concat", (OVar("is_reverse"), args[1])),))))
            results.append((rhs, "Mathlib: List_permutationsAux_append"))
        except Exception:
            pass
    return results


def _r0080_permutations_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutations_append
    # permutations (is ++ ts) = (permutations is).map (· ++ ts) ++ permutationsAux ts is.reverse
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "permutations", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("permutations_is_map", (OOp("concat", (OVar("_unknown"), OVar("ts"))),)), OOp("permutationsAux", (OVar("ts"), OVar("is_reverse"),))))
            results.append((rhs, "Mathlib: List_permutations_append"))
        except Exception:
            pass
    return results


def _r0081_map_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_rotate
    # map f (l.rotate n) = (map f l).rotate n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("map_f_l_rotate", (OVar("n"),))
            results.append((rhs, "Mathlib: List_map_rotate"))
        except Exception:
            pass
    return results


def _r0082_rel_sections(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rel_sections
    # (Forall₂ (Forall₂ r) ⇒ Forall₂ (Forall₂ r)) sections sections   | _, _, Forall₂.nil => Forall₂.cons Forall₂.nil Forall₂.
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2_Forall_2_r_Forall_2_Forall_2_r", 6)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("Forall_2_cons"), args[5], args[5], args[2], args[4], args[4], OVar("Forall_2_cons"), OVar("h_0"), OVar("h_1"), OVar("eq_gt"), OVar("rel_flatMap"), OOp("rel_sections", (OVar("h_1"),)), OVar("fun"), args[4], args[4], OVar("hl"), OVar("eq_gt"), OVar("rel_map"), OOp("fun", (args[4], args[4], OVar("ha"), OVar("eq_gt"), OVar("Forall_2_cons"), OVar("ha"), OVar("hl"),)), OVar("h_0_end"), OVar("List"),))
            results.append((rhs, "Mathlib: List_rel_sections"))
        except Exception:
            pass
    return results


def _r0083_map_dlookup_eq_find(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_dlookup_eq_find
    # (dlookup a l).map (Sigma.mk a) = find? (fun s => a = s.1) l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup_a_l_map", 1)
    if args is not None:
        try:
            rhs = OOp("find", (OOp("==", (OOp("fun", (OVar("s"), OVar("eq_gt"), OVar("a"),)), OVar("s_1"))), OVar("l"),))
            results.append((rhs, "Mathlib: List_map_dlookup_eq_find"))
        except Exception:
            pass
    return results


def _r0084_dlookup_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_map
    # (l.map (.map f g)).dlookup (f a) = (l.dlookup a).map (g a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map_map_f_g_dlookup", 1)
    if args is not None:
        try:
            rhs = OOp("l_dlookup_a_map", (OOp("g", (OVar("a"),)),))
            results.append((rhs, "Mathlib: List_dlookup_map"))
        except Exception:
            pass
    return results


def _r0085_dlookup_map_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_map₁
    # (l.map (.map f fun _ => id) : List (Σ _ : α', β)).dlookup (f a) = l.dlookup a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map_map_f_fun_eq_gt_id_colon_List_Sig_colon_a_prime_b_dlookup", 1)
    if args is not None:
        try:
            rhs = OOp("l_dlookup", (OVar("a"),))
            results.append((rhs, "Mathlib: List_dlookup_map_1"))
        except Exception:
            pass
    return results


def _r0086_dlookup_map_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_map₂
    # (l.map (.map id f) : List (Σ a, δ a)).dlookup a = (l.dlookup a).map (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map_map_id_f_colon_List_Sig_a_d_a_dlookup", 1)
    if args is not None:
        try:
            rhs = OOp("l_dlookup_a_map", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: List_dlookup_map_2"))
        except Exception:
            pass
    return results


def _r0087_map_2_keys(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map₂_keys
    # (l.map (.map id f)).keys = l.keys
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_map_map_id_f_keys")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_keys")
            results.append((rhs, "Mathlib: List_map_2_keys"))
    except Exception:
        pass
    return results


def _r0088_lookupAll_sublist(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookupAll_sublist
    # ∀ l : List (Sigma β), (lookupAll a l).map (Sigma.mk a) <+ l   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lookupAll_a_l_map", 5)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_lookupAll_sublist"))
        except Exception:
            pass
    return results


def _r0089_map_orderedInsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_orderedInsert
    # (l.orderedInsert r x).map f = (l.map f).orderedInsert s (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_orderedInsert_r_x_map", 1)
    if args is not None:
        try:
            rhs = OOp("l_map_f_orderedInsert", (OVar("s"), OOp("f", (OVar("x"),)),))
            results.append((rhs, "Mathlib: List_map_orderedInsert"))
        except Exception:
            pass
    return results


def _r0090_map_insertionSort(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_insertionSort
    # (l.insertionSort r).map f = (l.map f).insertionSort s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_insertionSort_r_map", 1)
    if args is not None:
        try:
            rhs = OOp("l_map_f_insertionSort", (OVar("s"),))
            results.append((rhs, "Mathlib: List_map_insertionSort"))
        except Exception:
            pass
    return results


def _r0091_sublistsAux_eq_flatMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsAux_eq_flatMap
    # sublistsAux = fun (a : α) (r : List (List α)) => r.flatMap fun l => [l, a :: l]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sublistsAux")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("fun", (OOp("a", (OVar("colon"), OVar("a"),)), OOp("r", (OVar("colon"), OVar("List"), OOp("List", (OVar("a"),)),)), OVar("eq_gt"), OVar("r_flatMap"), OVar("fun"), OVar("l"), OVar("eq_gt"), OVar("l_a_colon_colon_l"),))
            results.append((rhs, "Mathlib: List_sublistsAux_eq_flatMap"))
    except Exception:
        pass
    return results


def _r0092_sublists_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublists_append
    # sublists (l₁ ++ l₂) = (sublists l₂) >>= (fun x => (sublists l₁).map (· ++ x))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublists", 1)
    if args is not None:
        try:
            rhs = OOp("sublists_l_2", (OVar("gt_gt_eq"), OOp("fun", (OVar("x"), OVar("eq_gt"), OVar("sublists_l_1_map"), OOp("concat", (OVar("_unknown"), OVar("x"))),)),))
            results.append((rhs, "Mathlib: List_sublists_append"))
        except Exception:
            pass
    return results


def _r0093_sublists_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublists_concat
    # sublists (l ++ [a]) = sublists l ++ map (fun x => x ++ [a]) (sublists l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublists", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("sublists", (OVar("l"),)), OOp("map", (OOp("concat", (OOp("fun", (OVar("x"), OVar("eq_gt"), OVar("x"),)), OSeq((OVar("a"),)))), OOp("sublists", (OVar("l"),)),))))
            results.append((rhs, "Mathlib: List_sublists_concat"))
        except Exception:
            pass
    return results


def _r0094_sublists_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublists_reverse
    # sublists (reverse l) = map reverse (sublists' l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublists", 1)
    if args is not None:
        try:
            rhs = OOp("map", (OVar("reverse"), OOp("sublists_prime", (OVar("l"),)),))
            results.append((rhs, "Mathlib: List_sublists_reverse"))
        except Exception:
            pass
    return results


def _r0095_sublistsLenAux_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsLenAux_append
    # ∀ (n : ℕ) (l : List α) (f : List α → β) (g : β → γ) (r : List β) (s : List γ),       sublistsLenAux n l (g ∘ f) (r.map g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublistsLenAux", 4)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("sublistsLenAux_n_l_f_r_map", (OVar("g"),)), OOp("s", (OVar("pipe"), OVar("_0"), args[1], OVar("f"), OVar("g"), OVar("r"), OVar("s"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_sublistsLenAux_append"))
        except Exception:
            pass
    return results


def _r0096_sublistsLenAux_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsLenAux_eq
    # sublistsLenAux n l f r = (sublistsLen n l).map f ++ r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublistsLenAux", 4)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("sublistsLen_n_l_map", (args[2],)), args[3]))
            results.append((rhs, "Mathlib: List_sublistsLenAux_eq"))
        except Exception:
            pass
    return results


def _r0097_sublistsLen_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsLen_one
    # sublistsLen 1 l = l.reverse.map ([·])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublistsLen", 2)
    if args is not None:
        try:
            rhs = OOp("l_reverse_map", (OSeq((OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: List_sublistsLen_one"))
        except Exception:
            pass
    return results


def _r0098_sublists_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublists_map
    # ∀ (l : List α),     sublists (map f l) = map (map f) (sublists l)   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublists", 1)
    if args is not None:
        try:
            rhs = OOp("map", (OOp("map", (OVar("f"),)), OOp("sublists", (OVar("l"),)), OVar("pipe"), OSeq(()), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_sublists_map"))
        except Exception:
            pass
    return results


def _r0099_sym2_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sym2_map
    # (xs.map f).sym2 = xs.sym2.map (Sym2.map f)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("xs_map_f_sym2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("xs_sym2_map", (OOp("Sym2_map", (OVar("f"),)),))
            results.append((rhs, "Mathlib: List_sym2_map"))
    except Exception:
        pass
    return results


def _r0100_toFinsupp_eq_sum_mapIdx_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_eq_sum_mapIdx_single
    # toFinsupp l = (l.mapIdx fun n r => Finsupp.single n r).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OVar("l_mapIdx_fun_n_r_eq_gt_Finsupp_single_n_r_sum")
            results.append((rhs, "Mathlib: List_toFinsupp_eq_sum_mapIdx_single"))
        except Exception:
            pass
    return results


def _r0101_zip_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.zip_swap
    # ∀ (l₁ : List α) (l₂ : List β), (zip l₁ l₂).map Prod.swap = zip l₂ l₁   | [], _ => zip_nil_right.symm   | l₁, [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zip_l_1_l_2_map", 1)
    if args is not None:
        try:
            rhs = OOp("zip", (OVar("l_2"), OVar("l_1"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("zip_nil_right_symm"), OVar("pipe"), OVar("l_1"), OSeq(()), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_zip_swap"))
        except Exception:
            pass
    return results


def _r0102_unzip_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.unzip_swap
    # unzip (l.map Prod.swap) = (unzip l).swap
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unzip", 1)
    if args is not None:
        try:
            rhs = OVar("unzip_l_swap")
            results.append((rhs, "Mathlib: List_unzip_swap"))
        except Exception:
            pass
    return results


def _r0103_revzip_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.revzip_swap
    # (revzip l).map Prod.swap = revzip l.reverse
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "revzip_l_map", 1)
    if args is not None:
        try:
            rhs = OOp("revzip", (OVar("l_reverse"),))
            results.append((rhs, "Mathlib: List_revzip_swap"))
        except Exception:
            pass
    return results


def _r0104_toList_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.toList_map
    # (v.map f).toList = v.toList.map f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_map_f_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("map", (OVar("f"),))
            results.append((rhs, "Mathlib: List_Vector_toList_map"))
    except Exception:
        pass
    return results


def _r0105_tail_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.tail_map
    # (v.map f).tail = v.tail.map f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_map_f_tail")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("v_tail_map", (OVar("f"),))
            results.append((rhs, "Mathlib: List_Vector_tail_map"))
    except Exception:
        pass
    return results


def _r0106_toList_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.toList_pmap
    # (v.pmap f hp).toList = v.toList.pmap f hp
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_pmap_f_hp_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("v_toList_pmap", (OVar("f"), OVar("hp"),))
            results.append((rhs, "Mathlib: List_Vector_toList_pmap"))
    except Exception:
        pass
    return results


def _r0107_map_2_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.map₂_nil
    # Vector.map₂ f nil nil = nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Vector_map_2", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: List_Vector_map_2_nil"))
        except Exception:
            pass
    return results


def _r0108_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.map_id
    # Vector.map id v = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Vector_map", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: List_Vector_map_id"))
        except Exception:
            pass
    return results


def _r0109_map_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.map_nil
    # map f nil = nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: List_Vector_map_nil"))
        except Exception:
            pass
    return results


def _r0110_map_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.map_cons
    # ∀ v : Vector α n, map f (cons a v) = cons (f a) (map f v)   | ⟨_, _⟩ => rfl   def pmap (f : (a : α) → p a → β) :     (v 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Vector", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("List_pmap_f_l_hp"),))
            results.append((rhs, "Mathlib: List_Vector_map_cons"))
        except Exception:
            pass
    return results


def _r0111_pmap_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.pmap_nil
    # nil.pmap f hp = nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nil_pmap", 2)
    if args is not None:
        try:
            rhs = OVar("nil")
            results.append((rhs, "Mathlib: List_Vector_pmap_nil"))
        except Exception:
            pass
    return results


def _r0112_mapAccumr_mapAccumr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.mapAccumr_mapAccumr
    # mapAccumr f₁ (mapAccumr f₂ xs s₂).snd s₁     = let m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr", 3)
    if args is not None:
        try:
            rhs = OOp("let", (OVar("m"),))
            results.append((rhs, "Mathlib: List_Vector_mapAccumr_mapAccumr"))
        except Exception:
            pass
    return results


def _r0113_mapAccumr_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.mapAccumr_map
    # (mapAccumr f₁ (map f₂ xs) s) = (mapAccumr (fun x s => f₁ (f₂ x) s) xs s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr", 3)
    if args is not None:
        try:
            rhs = OOp("mapAccumr", (OOp("fun", (OVar("x"), args[2], OVar("eq_gt"), args[0], OOp("f_2", (OVar("x"),)), args[2],)), OVar("xs"), args[2],))
            results.append((rhs, "Mathlib: List_Vector_mapAccumr_map"))
        except Exception:
            pass
    return results


def _r0114_map_mapAccumr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.map_mapAccumr
    # (map f₁ (mapAccumr f₂ xs s).snd) = (mapAccumr (fun x s =>         let r := (f₂ x s); (r.fst, f₁ r.snd)       ) xs s).snd
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OVar("mapAccumr_fun_x_s_eq_gt_let_r_colon_eq_f_2_x_s_r_fst_f_1_r_snd_xs_s_snd")
            results.append((rhs, "Mathlib: List_Vector_map_mapAccumr"))
        except Exception:
            pass
    return results


def _r0115_map_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.map_map
    # map f₁ (map f₂ xs) = map (fun x => f₁ <| f₂ x) xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("map", (OOp("fun", (OVar("x"), OVar("eq_gt"), args[0], OVar("lt_pipe"), OVar("f_2"), OVar("x"),)), OVar("xs"),))
            results.append((rhs, "Mathlib: List_Vector_map_map"))
        except Exception:
            pass
    return results


def _r0116_map_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.map_pmap
    # map f₁ (pmap f₂ xs H) = pmap (fun x hx => f₁ <| f₂ x hx) xs H
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("pmap", (OOp("fun", (OVar("x"), OVar("hx"), OVar("eq_gt"), args[0], OVar("lt_pipe"), OVar("f_2"), OVar("x"), OVar("hx"),)), OVar("xs"), OVar("H"),))
            results.append((rhs, "Mathlib: List_Vector_map_pmap"))
        except Exception:
            pass
    return results


def _r0117_pmap_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.pmap_map
    # pmap f₁ (map f₂ xs) H = pmap (fun x hx => f₁ (f₂ x) hx) xs (by simpa using H)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pmap", 3)
    if args is not None:
        try:
            rhs = OOp("pmap", (OOp("fun", (OVar("x"), OVar("hx"), OVar("eq_gt"), args[0], OOp("f_2", (OVar("x"),)), OVar("hx"),)), OVar("xs"), OOp("by", (OVar("simpa"), OVar("using"), args[2],)),))
            results.append((rhs, "Mathlib: List_Vector_pmap_map"))
        except Exception:
            pass
    return results


def _r0118_mapAccumr_2_mapAccumr_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapAccumr₂_mapAccumr_left
    # (mapAccumr₂ f₁ (mapAccumr f₂ xs s₂).snd ys s₁)     = let m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr_2", 4)
    if args is not None:
        try:
            rhs = OOp("let", (OVar("m"),))
            results.append((rhs, "Mathlib: List_mapAccumr_2_mapAccumr_left"))
        except Exception:
            pass
    return results


def _r0119_map_2_map_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map₂_map_left
    # map₂ f₁ (map f₂ xs) ys = map₂ (fun x y => f₁ (f₂ x) y) xs ys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2", (OOp("fun", (OVar("x"), OVar("y"), OVar("eq_gt"), args[0], OOp("f_2", (OVar("x"),)), OVar("y"),)), OVar("xs"), args[2],))
            results.append((rhs, "Mathlib: List_map_2_map_left"))
        except Exception:
            pass
    return results


def _r0120_mapAccumr_2_mapAccumr_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapAccumr₂_mapAccumr_right
    # (mapAccumr₂ f₁ xs (mapAccumr f₂ ys s₂).snd s₁)     = let m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr_2", 4)
    if args is not None:
        try:
            rhs = OOp("let", (OVar("m"),))
            results.append((rhs, "Mathlib: List_mapAccumr_2_mapAccumr_right"))
        except Exception:
            pass
    return results


def _r0121_map_2_map_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map₂_map_right
    # map₂ f₁ xs (map f₂ ys) = map₂ (fun x y => f₁ x (f₂ y)) xs ys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2", (OOp("fun", (OVar("x"), OVar("y"), OVar("eq_gt"), args[0], OVar("x"), OOp("f_2", (OVar("y"),)),)), args[1], OVar("ys"),))
            results.append((rhs, "Mathlib: List_map_2_map_right"))
        except Exception:
            pass
    return results


def _r0122_mapAccumr_mapAccumr_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapAccumr_mapAccumr₂
    # (mapAccumr f₁ (mapAccumr₂ f₂ xs ys s₂).snd s₁)     = let m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr", 3)
    if args is not None:
        try:
            rhs = OOp("let", (OVar("m"),))
            results.append((rhs, "Mathlib: List_mapAccumr_mapAccumr_2"))
        except Exception:
            pass
    return results


def _r0123_map_map_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_map₂
    # map f₁ (map₂ f₂ xs ys) = map₂ (fun x y => f₁ <| f₂ x y) xs ys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("map_2", (OOp("fun", (OVar("x"), OVar("y"), OVar("eq_gt"), args[0], OVar("lt_pipe"), OVar("f_2"), OVar("x"), OVar("y"),)), OVar("xs"), OVar("ys"),))
            results.append((rhs, "Mathlib: List_map_map_2"))
        except Exception:
            pass
    return results


def _r0124_mapAccumr_2_mapAccumr_2_left_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapAccumr₂_mapAccumr₂_left_left
    # (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂).snd xs s₁)     = let m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr_2", 4)
    if args is not None:
        try:
            rhs = OOp("let", (OVar("m"),))
            results.append((rhs, "Mathlib: List_mapAccumr_2_mapAccumr_2_left_left"))
        except Exception:
            pass
    return results


def _r0125_mapAccumr_2_mapAccumr_2_left_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapAccumr₂_mapAccumr₂_left_right
    # (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂).snd ys s₁)     = let m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr_2", 4)
    if args is not None:
        try:
            rhs = OOp("let", (OVar("m"),))
            results.append((rhs, "Mathlib: List_mapAccumr_2_mapAccumr_2_left_right"))
        except Exception:
            pass
    return results


def _r0126_mapAccumr_2_mapAccumr_2_right_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapAccumr₂_mapAccumr₂_right_left
    # (mapAccumr₂ f₁ xs (mapAccumr₂ f₂ xs ys s₂).snd s₁)     = let m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr_2", 4)
    if args is not None:
        try:
            rhs = OOp("let", (OVar("m"),))
            results.append((rhs, "Mathlib: List_mapAccumr_2_mapAccumr_2_right_left"))
        except Exception:
            pass
    return results


def _r0127_mapAccumr_2_mapAccumr_2_right_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapAccumr₂_mapAccumr₂_right_right
    # (mapAccumr₂ f₁ ys (mapAccumr₂ f₂ xs ys s₂).snd s₁)     = let m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr_2", 4)
    if args is not None:
        try:
            rhs = OOp("let", (OVar("m"),))
            results.append((rhs, "Mathlib: List_mapAccumr_2_mapAccumr_2_right_right"))
        except Exception:
            pass
    return results


def _r0128_mem_map_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.mem_map_iff
    # b ∈ (v.map f).toList ↔ ∃ a : α, a ∈ v.toList ∧ f a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: List_Vector_mem_map_iff"))
        except Exception:
            pass
    return results


def _r0129_aestronglyMeasurable_fun_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.aestronglyMeasurable_fun_prod
    # AEStronglyMeasurable (fun x => (l.map fun f : α → M => f x).prod) μ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("M")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("gt", (OVar("f"), OVar("x_prod_mu"),))
            results.append((rhs, "Mathlib: List_aestronglyMeasurable_fun_prod"))
    except Exception:
        pass
    return results


def _r0130_stronglyMeasurable_fun_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.stronglyMeasurable_fun_prod
    # StronglyMeasurable fun x => (l.map fun f : α → M => f x).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("M")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("gt", (OVar("f"), OVar("x_prod"),))
            results.append((rhs, "Mathlib: List_stronglyMeasurable_fun_prod"))
    except Exception:
        pass
    return results


def _r0131_measurable_fun_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.measurable_fun_prod
    # Measurable fun x => (l.map fun f : α → M => f x).prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("M")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("gt", (OVar("f"), OVar("x_prod"),))
            results.append((rhs, "Mathlib: List_measurable_fun_prod"))
    except Exception:
        pass
    return results


def _r0132_aemeasurable_fun_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.aemeasurable_fun_prod
    # AEMeasurable (fun x => (l.map fun f : α → M => f x).prod) μ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("M")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("gt", (OVar("f"), OVar("x_prod_mu"),))
            results.append((rhs, "Mathlib: List_aemeasurable_fun_prod"))
    except Exception:
        pass
    return results


def _r0133_list_wbtw_map_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.list_wbtw_map_iff
    # (l.map f).Wbtw R ↔ l.Wbtw R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map_f_Wbtw", 1)
    if args is not None:
        try:
            rhs = OOp("l_Wbtw", (args[0],))
            results.append((rhs, "Mathlib: Function_Injective_list_wbtw_map_iff"))
        except Exception:
            pass
    return results


def _r0134_list_sbtw_map_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Injective.list_sbtw_map_iff
    # (l.map f).Sbtw R ↔ l.Sbtw R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map_f_Sbtw", 1)
    if args is not None:
        try:
            rhs = OOp("l_Sbtw", (args[0],))
            results.append((rhs, "Mathlib: Function_Injective_list_sbtw_map_iff"))
        except Exception:
            pass
    return results


def _r0135_list_wbtw_map_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AffineEquiv.list_wbtw_map_iff
    # (l.map f).Wbtw R ↔ l.Wbtw R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map_f_Wbtw", 1)
    if args is not None:
        try:
            rhs = OOp("l_Wbtw", (args[0],))
            results.append((rhs, "Mathlib: AffineEquiv_list_wbtw_map_iff"))
        except Exception:
            pass
    return results


def _r0136_list_sbtw_map_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AffineEquiv.list_sbtw_map_iff
    # (l.map f).Sbtw R ↔ l.Sbtw R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map_f_Sbtw", 1)
    if args is not None:
        try:
            rhs = OOp("l_Sbtw", (args[0],))
            results.append((rhs, "Mathlib: AffineEquiv_list_sbtw_map_iff"))
        except Exception:
            pass
    return results


def _r0137_mem_map_of_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_map_of_injective
    # f a ∈ map f l ↔ a ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("a"), OVar("l")))
            results.append((rhs, "Mathlib: List_mem_map_of_injective"))
        except Exception:
            pass
    return results


def _r0138_mem_map_of_involutive(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_map_of_involutive
    # a ∈ map f l ↔ f a ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("f", (args[0],)), OVar("l")))
            results.append((rhs, "Mathlib: List_mem_map_of_involutive"))
        except Exception:
            pass
    return results


def _r0139_map_subset_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_subset_iff
    # map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("subset", (OVar("l_1"), OVar("l_2")))
            results.append((rhs, "Mathlib: List_map_subset_iff"))
        except Exception:
            pass
    return results


def _r0140_isChain_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_map
    # IsChain R (map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("IsChain", (OOp("fun", (OVar("a"), OVar("b"), OVar("colon"), OVar("b"), OVar("eq_gt"), args[0], OOp("f", (OVar("a"),)), OOp("f", (OVar("b"),)),)), OVar("l"),))
            results.append((rhs, "Mathlib: List_isChain_map"))
        except Exception:
            pass
    return results


def _r0141_isChain_cons_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons_map
    # IsChain R (f b :: map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) (b :: l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("IsChain", (OOp("fun", (OVar("a"), OVar("b"), OVar("colon"), OVar("b"), OVar("eq_gt"), args[0], OOp("f", (OVar("a"),)), OOp("f", (OVar("b"),)),)), OOp("b", (OVar("colon_colon"), OVar("l"),)),))
            results.append((rhs, "Mathlib: List_isChain_cons_map"))
        except Exception:
            pass
    return results


def _r0142_isChain_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_pmap
    # IsChain S (pmap f l hl) ↔     IsChain (fun a b => ∃ ha, ∃ hb, S (f a ha) (f b hb)) l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("IsChain", (OOp("fun", (OVar("a"), OVar("b"), OVar("eq_gt"), OVar("exists"), OVar("ha"), OVar("exists"), OVar("hb"), args[0], OOp("f", (OVar("a"), OVar("ha"),)), OOp("f", (OVar("b"), OVar("hb"),)),)), OVar("l"),))
            results.append((rhs, "Mathlib: List_isChain_pmap"))
        except Exception:
            pass
    return results


def _r0143_isChain_cons_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons_pmap
    # IsChain R (f a ha :: pmap f l hl) ↔     IsChain (fun a b => ∃ ha, ∃ hb, R (f a ha) (f b hb)) (a :: l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("IsChain", (OOp("fun", (OVar("a"), OVar("b"), OVar("eq_gt"), OVar("exists"), OVar("ha"), OVar("exists"), OVar("hb"), args[0], OOp("f", (OVar("a"), OVar("ha"),)), OOp("f", (OVar("b"), OVar("hb"),)),)), OOp("a", (OVar("colon_colon"), OVar("l"),)),))
            results.append((rhs, "Mathlib: List_isChain_cons_pmap"))
        except Exception:
            pass
    return results


def _r0144_nodup_map_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_map_iff
    # Nodup (map f l) ↔ Nodup l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("nodup", (OVar("l"),))
            results.append((rhs, "Mathlib: List_nodup_map_iff"))
        except Exception:
            pass
    return results


def _r0145_nodup_flatMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_flatMap
    # Nodup (l₁.flatMap f) ↔       (∀ x ∈ l₁, Nodup (f x)) ∧ Pairwise (Disjoint on f) l₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (OOp("forall", (OVar("x"),)), OOp("l_1", (OVar("Nodup"), OOp("f", (OVar("x"),)),)))), OOp("Pairwise", (OOp("Disjoint", (OVar("on"), OVar("f"),)), OVar("l_1"),))))
            results.append((rhs, "Mathlib: List_nodup_flatMap"))
        except Exception:
            pass
    return results


def _r0146_mem_map_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_map_swap
    # (y, x) ∈ map Prod.swap xs ↔ (x, y) ∈ xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("x", (OVar("y"),)), OVar("xs")))
            results.append((rhs, "Mathlib: List_mem_map_swap"))
        except Exception:
            pass
    return results


def _r0147_nodupKeys_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodupKeys_flatten
    # NodupKeys (flatten L) ↔ (∀ l ∈ L, NodupKeys l) ∧ Pairwise Disjoint (L.map keys)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NodupKeys", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (OOp("forall", (OVar("l"),)), OOp("L", (OVar("NodupKeys"), OVar("l"),)))), OOp("Pairwise", (OVar("Disjoint"), OOp("L_map", (OVar("keys"),)),))))
            results.append((rhs, "Mathlib: List_nodupKeys_flatten"))
        except Exception:
            pass
    return results


def _r0148_triplewise_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.triplewise_map
    # (l.map f).Triplewise p' ↔ l.Triplewise (fun a b c ↦ p' (f a) (f b) (f c))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map_f_Triplewise", 1)
    if args is not None:
        try:
            rhs = OOp("l_Triplewise", (OOp("fun", (OVar("a"), OVar("b"), OVar("c"), OVar("_unknown"), args[0], OOp("f", (OVar("a"),)), OOp("f", (OVar("b"),)), OOp("f", (OVar("c"),)),)),))
            results.append((rhs, "Mathlib: List_triplewise_map"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_list_map rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("+", "-", "<", "<=", "Forall_2_Forall_2_r_Forall_2_Forall_2_r", "Function_update", "Ico_n_m_map", "IsChain", "L_modifyNth_f_n_map", "ListBlank_mk_l_flatMap", "ListBlank_mk_l_map", "List_range_n_map", "NodupKeys", "Prod_map", "Sigma_mk", "Vector", "Vector_map", "Vector_map_2", "_unknown", "a", "a_colon_colon_l_1", "a_colon_colon_l_1_sigma", "a_colon_colon_l_lookmap", "and", "antidiagonal", "antidiagonalTuple", "antidiagonal_n_map", "comp", "concat", "cons", "cons_a_v_pmap", "count", "divisors", "dlookup_a_l_map", "eq_map_f", "exists", "f", "fib", "finRange", "flatten", "fpow", "fun", "hd_1", "hd_2", "i", "iff", "in", "l", "l_1_flatMap", "l_cons_a_flatMap",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_list_map axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_list_map rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_norm_prod(term, ctx))
    results.extend(_r0001_lookmap_cons_none(term, ctx))
    results.extend(_r0002_map_permutationsAux(term, ctx))
    results.extend(_r0003_cons_map(term, ctx))
    results.extend(_r0004_pi_cons(term, ctx))
    results.extend(_r0005_product_cons(term, ctx))
    results.extend(_r0006_sigma_cons(term, ctx))
    results.extend(_r0007_reduceOption_map(term, ctx))
    results.extend(_r0008_sublistsLen_succ_cons(term, ctx))
    results.extend(_r0009_revzip_map_fst(term, ctx))
    results.extend(_r0010_revzip_map_snd(term, ctx))
    results.extend(_r0011_sum_fib_lt(term, ctx))
    results.extend(_r0012_pmap_cons(term, ctx))
    results.extend(_r0013_head_map(term, ctx))
    results.extend(_r0014_get_map(term, ctx))
    results.extend(_r0015_map_2_cons(term, ctx))
    results.extend(_r0016_prod_toFinset(term, ctx))
    results.extend(_r0017_prod_hom_nonempty(term, ctx))
    results.extend(_r0018_prod_hom(term, ctx))
    results.extend(_r0019_prod_hom_2_nonempty(term, ctx))
    results.extend(_r0020_prod_hom_2(term, ctx))
    results.extend(_r0021_prod_map_mul(term, ctx))
    results.extend(_r0022_prod_map_hom(term, ctx))
    results.extend(_r0023_prod_range_succ(term, ctx))
    results.extend(_r0024_prod_map_eq_pow_single(term, ctx))
    results.extend(_r0025_smul_sum(term, ctx))
    results.extend(_r0026_sum_smul(term, ctx))
    results.extend(_r0027_trop_minimum(term, ctx))
    results.extend(_r0028_norm_prod_le(term, ctx))
    results.extend(_r0029_nnnorm_prod(term, ctx))
    results.extend(_r0030_map_mk(term, ctx))
    results.extend(_r0031_head_map(term, ctx))
    results.extend(_r0032_tail_map(term, ctx))
    results.extend(_r0033_map_cons(term, ctx))
    results.extend(_r0034_nth_map(term, ctx))
    results.extend(_r0035_map_modifyNth(term, ctx))
    results.extend(_r0036_flatMap_mk(term, ctx))
    results.extend(_r0037_cons_flatMap(term, ctx))
    results.extend(_r0038_antidiagonalTuple_two(term, ctx))
    results.extend(_r0039_toFinset_filterMap(term, ctx))
    results.extend(_r0040_nat_divisors_prod(term, ctx))
    results.extend(_r0041_bind_eq_flatMap(term, ctx))
    results.extend(_r0042_map_reverseAux(term, ctx))
    results.extend(_r0043_count_map_of_injective(term, ctx))
    results.extend(_r0044_pmap_next_eq_rotate_one(term, ctx))
    results.extend(_r0045_dedup_map_of_injective(term, ctx))
    results.extend(_r0046_destutter_eq_nil(term, ctx))
    results.extend(_r0047_map_destutter(term, ctx))
    results.extend(_r0048_map_destutter_ne(term, ctx))
    results.extend(_r0049_finRange_succ_eq_map(term, ctx))
    results.extend(_r0050_ofFn_eq_pmap(term, ctx))
    results.extend(_r0051_ofFn_eq_map(term, ctx))
    results.extend(_r0052_append_flatten_map_append(term, ctx))
    results.extend(_r0053_getD_map(term, ctx))
    results.extend(_r0054_insertIdx_pmap(term, ctx))
    results.extend(_r0055_map_insertIdx(term, ctx))
    results.extend(_r0056_eraseIdx_pmap(term, ctx))
    results.extend(_r0057_eraseIdx_map(term, ctx))
    results.extend(_r0058_map_add(term, ctx))
    results.extend(_r0059_map_sub(term, ctx))
    results.extend(_r0060_range_map_iterate(term, ctx))
    results.extend(_r0061_lookmap_nil(term, ctx))
    results.extend(_r0062_lookmap_cons_some(term, ctx))
    results.extend(_r0063_lookmap_cons(term, ctx))
    results.extend(_r0064_lookmap_some(term, ctx))
    results.extend(_r0065_lookmap_none(term, ctx))
    results.extend(_r0066_lookmap_congr(term, ctx))
    results.extend(_r0067_lookmap_map_eq(term, ctx))
    results.extend(_r0068_antidiagonal_succ(term, ctx))
    results.extend(_r0069_map_swap_antidiagonal(term, ctx))
    results.extend(_r0070_inj_on_of_nodup_map(term, ctx))
    results.extend(_r0071_nodup_map_iff_inj_on(term, ctx))
    results.extend(_r0072_map_update(term, ctx))
    results.extend(_r0073_map_prodMap_offDiag(term, ctx))
    results.extend(_r0074_eq_map_comp_perm(term, ctx))
    results.extend(_r0075_map_permutationsAux2(term, ctx))
    results.extend(_r0076_permutationsAux2_snd_eq(term, ctx))
    results.extend(_r0077_map_map_permutationsAux2(term, ctx))
    results.extend(_r0078_map_permutations(term, ctx))
    results.extend(_r0079_permutationsAux_append(term, ctx))
    results.extend(_r0080_permutations_append(term, ctx))
    results.extend(_r0081_map_rotate(term, ctx))
    results.extend(_r0082_rel_sections(term, ctx))
    results.extend(_r0083_map_dlookup_eq_find(term, ctx))
    results.extend(_r0084_dlookup_map(term, ctx))
    results.extend(_r0085_dlookup_map_1(term, ctx))
    results.extend(_r0086_dlookup_map_2(term, ctx))
    results.extend(_r0087_map_2_keys(term, ctx))
    results.extend(_r0088_lookupAll_sublist(term, ctx))
    results.extend(_r0089_map_orderedInsert(term, ctx))
    results.extend(_r0090_map_insertionSort(term, ctx))
    results.extend(_r0091_sublistsAux_eq_flatMap(term, ctx))
    results.extend(_r0092_sublists_append(term, ctx))
    results.extend(_r0093_sublists_concat(term, ctx))
    results.extend(_r0094_sublists_reverse(term, ctx))
    results.extend(_r0095_sublistsLenAux_append(term, ctx))
    results.extend(_r0096_sublistsLenAux_eq(term, ctx))
    results.extend(_r0097_sublistsLen_one(term, ctx))
    results.extend(_r0098_sublists_map(term, ctx))
    results.extend(_r0099_sym2_map(term, ctx))
    results.extend(_r0100_toFinsupp_eq_sum_mapIdx_single(term, ctx))
    results.extend(_r0101_zip_swap(term, ctx))
    results.extend(_r0102_unzip_swap(term, ctx))
    results.extend(_r0103_revzip_swap(term, ctx))
    results.extend(_r0104_toList_map(term, ctx))
    results.extend(_r0105_tail_map(term, ctx))
    results.extend(_r0106_toList_pmap(term, ctx))
    results.extend(_r0107_map_2_nil(term, ctx))
    results.extend(_r0108_map_id(term, ctx))
    results.extend(_r0109_map_nil(term, ctx))
    results.extend(_r0110_map_cons(term, ctx))
    results.extend(_r0111_pmap_nil(term, ctx))
    results.extend(_r0112_mapAccumr_mapAccumr(term, ctx))
    results.extend(_r0113_mapAccumr_map(term, ctx))
    results.extend(_r0114_map_mapAccumr(term, ctx))
    results.extend(_r0115_map_map(term, ctx))
    results.extend(_r0116_map_pmap(term, ctx))
    results.extend(_r0117_pmap_map(term, ctx))
    results.extend(_r0118_mapAccumr_2_mapAccumr_left(term, ctx))
    results.extend(_r0119_map_2_map_left(term, ctx))
    results.extend(_r0120_mapAccumr_2_mapAccumr_right(term, ctx))
    results.extend(_r0121_map_2_map_right(term, ctx))
    results.extend(_r0122_mapAccumr_mapAccumr_2(term, ctx))
    results.extend(_r0123_map_map_2(term, ctx))
    results.extend(_r0124_mapAccumr_2_mapAccumr_2_left_left(term, ctx))
    results.extend(_r0125_mapAccumr_2_mapAccumr_2_left_right(term, ctx))
    results.extend(_r0126_mapAccumr_2_mapAccumr_2_right_left(term, ctx))
    results.extend(_r0127_mapAccumr_2_mapAccumr_2_right_right(term, ctx))
    results.extend(_r0128_mem_map_iff(term, ctx))
    results.extend(_r0129_aestronglyMeasurable_fun_prod(term, ctx))
    results.extend(_r0130_stronglyMeasurable_fun_prod(term, ctx))
    results.extend(_r0131_measurable_fun_prod(term, ctx))
    results.extend(_r0132_aemeasurable_fun_prod(term, ctx))
    results.extend(_r0133_list_wbtw_map_iff(term, ctx))
    results.extend(_r0134_list_sbtw_map_iff(term, ctx))
    results.extend(_r0135_list_wbtw_map_iff(term, ctx))
    results.extend(_r0136_list_sbtw_map_iff(term, ctx))
    results.extend(_r0137_mem_map_of_injective(term, ctx))
    results.extend(_r0138_mem_map_of_involutive(term, ctx))
    results.extend(_r0139_map_subset_iff(term, ctx))
    results.extend(_r0140_isChain_map(term, ctx))
    results.extend(_r0141_isChain_cons_map(term, ctx))
    results.extend(_r0142_isChain_pmap(term, ctx))
    results.extend(_r0143_isChain_cons_pmap(term, ctx))
    results.extend(_r0144_nodup_map_iff(term, ctx))
    results.extend(_r0145_nodup_flatMap(term, ctx))
    results.extend(_r0146_mem_map_swap(term, ctx))
    results.extend(_r0147_nodupKeys_flatten(term, ctx))
    results.extend(_r0148_triplewise_map(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_list_map rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("List_prod_lt_prod_of_ne_nil", "l_map_f_prod_lt_l_map_g_prod", "Not an equality or iff proposition"),
    ("List_max_prod_le", "max_l_map_f_prod_l_map_g_prod_le_l_map_fun_i_max_f_i_g_i_prod", "Not an equality or iff proposition"),
    ("List_prod_min_le", "l_map_fun_i_min_f_i_g_i_prod_le_min_l_map_f_prod_l_map_g_prod", "Not an equality or iff proposition"),
    ("List_prod_map_le_prod_map_0", "map_f_s_prod_le_map_g_s_prod", "Not an equality or iff proposition"),
    ("List_prod_map_lt_prod_map", "map_f_s_prod_lt_map_g_s_prod", "Not an equality or iff proposition"),
    ("List_nnnorm_prod_le", "l_prod_le_l_map_nnnorm_prod", "Not an equality or iff proposition"),
    ("List_isChain_of_isChain_map", "IsChain_R_l", "Not an equality or iff proposition"),
    ("List_isChain_map_of_isChain", "IsChain_S_map_f_l", "Not an equality or iff proposition"),
    ("List_isChain_cons_of_isChain_cons_map", "IsChain_R_a_colon_colon_l", "Not an equality or iff proposition"),
    ("List_isChain_cons_map_of_isChain_cons", "IsChain_S_f_a_colon_colon_map_f_l", "Not an equality or iff proposition"),
    ("List_isChain_pmap_of_isChain", "IsChain_S_pmap_f_l_hl_2", "Not an equality or iff proposition"),
    ("List_isChain_of_isChain_pmap", "IsChain_R_l", "Not an equality or iff proposition"),
    ("List_isChain_cons_pmap_of_isChain_cons", "IsChain_S_f_a_ha_colon_colon_pmap_f_l_hl_2", "Not an equality or iff proposition"),
    ("List_isChain_cons_of_isChain_cons_pmap", "IsChain_R_a_colon_colon_l", "Not an equality or iff proposition"),
    ("List_Sublist_flatMap", "l_1_flatMap_f_lt_plus_l_2_flatMap_f", "Not an equality or iff proposition"),
    ("List_Sublist_flatMap_right", "l_flatMap_f_lt_plus_l_flatMap_g", "Not an equality or iff proposition"),
    ("List_rel_flatMap", "Forall_2_R_R_Forall_2_P_Forall_2_P_Function_swap_List_flatMap_Func", "Not an equality or iff proposition"),
    ("List_IsPrefix_flatMap", "l_1_flatMap_f_lt_plus_colon_l_2_flatMap_f", "Not an equality or iff proposition"),
    ("List_IsSuffix_flatMap", "l_1_flatMap_f_lt_colon_plus_l_2_flatMap_f", "Not an equality or iff proposition"),
    ("List_IsInfix_flatMap", "l_1_flatMap_f_lt_colon_plus_colon_l_2_flatMap_f", "Not an equality or iff proposition"),
    ("List_lookmap_id", "_unknown", "Empty proposition"),
    ("List_perm_lookmap", "lookmap_f_l_1_tilde_lookmap_f_l_2", "Not an equality or iff proposition"),
    ("List_map_2Left", "_unknown", "Empty proposition"),
    ("List_Nodup_of_map", "Nodup_map_f_l_to_Nodup_l", "Not an equality or iff proposition"),
    ("List_Nodup_map_on", "map_f_l_Nodup", "Not an equality or iff proposition"),
    ("List_Nodup_map", "Nodup_l_to_Nodup_map_f_l", "Not an equality or iff proposition"),
    ("List_Nodup_pmap", "Nodup_pmap_f_l_H", "Not an equality or iff proposition"),
    ("List_Nodup_filterMap", "Nodup_l_to_Nodup_filterMap_f_l", "Not an equality or iff proposition"),
    ("List_offDiag_cons_perm", "offDiag_a_colon_colon_l_tilde_map_a_l_plus_plus_map_a_l_plus_plus_l_offDiag", "Not an equality or iff proposition"),
    ("List_Palindrome_map", "Palindrome_map_f_l", "Not an equality or iff proposition"),
    ("List_map_permutationsAux2", "_unknown", "Empty proposition"),
    ("List_map_map_permutations", "_unknown", "Empty proposition"),
    ("List_map_permutations", "_unknown", "Empty proposition"),
    ("List_IsRotated_map", "map_f_l_1_tilde_r_map_f_l_2", "Not an equality or iff proposition"),
    ("List_nodup_zipIdx_map_snd", "l_zipIdx_map_Prod_snd_Nodup", "Not an equality or iff proposition"),
    ("List_NodupKeys_map_1", "l_map_map_f_fun_eq_gt_id_colon_List_Sig_colon_a_prime_b_NodupKeys", "Not an equality or iff proposition"),
    ("List_NodupKeys_map_2", "l_map_map_id_f_NodupKeys", "Not an equality or iff proposition"),
    ("List_map_pure_sublist_sublists", "map_pure_l_lt_plus_sublists_l", "Not an equality or iff proposition"),
    ("List_sublists_cons_perm_append", "sublists_a_colon_colon_l_tilde_sublists_l_plus_plus_map_cons_a_sublists_l", "Not an equality or iff proposition"),
    ("List_map_mk_sublist_sym2", "map_fun_y_s_x_y_xs_lt_plus_xs_sym2", "Not an equality or iff proposition"),
    ("List_map_mk_disjoint_sym2", "map_fun_y_s_x_y_xs_Disjoint_xs_sym2", "Not an equality or iff proposition"),
    ("List_forall_tfae", "l_map_fun_p_forall_a_p_a_TFAE", "Not an equality or iff proposition"),
    ("List_exists_tfae", "l_map_fun_p_exists_a_p_a_TFAE", "Not an equality or iff proposition"),
    ("List_Triplewise_of_map", "l_Triplewise_p", "Not an equality or iff proposition"),
    ("List_Triplewise_map", "l_map_f_Triplewise_p_prime", "Not an equality or iff proposition"),
    ("List_Vector_pmap_cons", "_unknown", "Empty proposition"),
    ("List_iSup_mem_map_of_exists_sSup_empty_le", "x_in_l_f_x_in_l_map_f", "Not an equality or iff proposition"),
    ("List_iInf_mem_map_of_exists_le_sInf_empty", "x_in_l_f_x_in_l_map_f", "Not an equality or iff proposition"),
    ("List_iSup_mem_map_of_ne_nil", "x_in_l_f_x_in_l_map_f", "Not an equality or iff proposition"),
    ("Mathlib_Meta_List_range_succ_eq_map", "_unknown", "Empty proposition"),
]
