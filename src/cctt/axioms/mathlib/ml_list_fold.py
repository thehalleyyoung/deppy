"""Mathlib: List Fold — auto-generated from Mathlib4.

Contains 22 rewrite rules derived from Mathlib theorems.
Plus 12 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_list_fold"
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
# Rewrite rules (22 total)
# ════════════════════════════════════════════════════════════

def _r0000_permutationsAux_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutationsAux_cons
    # permutationsAux (t :: ts) is =       foldr (fun y r => (permutationsAux2 t ts r y id).2) (permutationsAux ts (t :: is)) 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "permutationsAux", 2)
    if args is not None:
        try:
            rhs = OOp("foldr", (OOp("fun", (OVar("y"), OVar("r"), OVar("eq_gt"), OVar("permutationsAux2_t_ts_r_y_id_2"),)), OOp("permutationsAux", (OVar("ts"), OOp("t", (OVar("colon_colon"), args[1],)),)), OOp("permutations", (args[1],)),))
            results.append((rhs, "Mathlib: List_permutationsAux_cons"))
        except Exception:
            pass
    return results


def _r0001_support_sum_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.support_sum_eq
    # l.sum.support = l.foldr (Finsupp.support · ⊔ ·) ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_sum_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_foldr", (OOp("Finsupp_support", (OVar("_unknown"), OVar("_unknown"), OVar("_unknown"),)), OVar("empty"),))
            results.append((rhs, "Mathlib: List_support_sum_eq"))
    except Exception:
        pass
    return results


def _r0002_foldl_cons_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldl_cons_nil
    # l.foldl (flip cons) [] = l.reverse
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_foldl", 2)
    if args is not None:
        try:
            rhs = OVar("l_reverse")
            results.append((rhs, "Mathlib: List_foldl_cons_nil"))
        except Exception:
            pass
    return results


def _r0003_foldl_cons_eq_apply_foldl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldl_cons_eq_apply_foldl
    # (a :: l).foldl v b = v (l.foldl v b) a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_foldl", 2)
    if args is not None:
        try:
            rhs = OOp("v", (OOp("l_foldl", (args[0], args[1],)), OVar("a"),))
            results.append((rhs, "Mathlib: List_foldl_cons_eq_apply_foldl"))
        except Exception:
            pass
    return results


def _r0004_foldr_cons_eq_foldr_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldr_cons_eq_foldr_apply
    # (a :: l).foldr f b = l.foldr f (f a b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_foldr", 2)
    if args is not None:
        try:
            rhs = OOp("l_foldr", (args[0], OOp("f", (OVar("a"), args[1],)),))
            results.append((rhs, "Mathlib: List_foldr_cons_eq_foldr_apply"))
        except Exception:
            pass
    return results


def _r0005_foldl1_eq_foldr1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldl1_eq_foldr1
    # f (l.foldl f a) b = f a (l.foldr f b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"), OOp("l_foldr", (OVar("f"), args[1],)),))
            results.append((rhs, "Mathlib: List_foldl1_eq_foldr1"))
        except Exception:
            pass
    return results


def _r0006_foldl_eq_foldr_of_commute(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldl_eq_foldr_of_commute
    # l.foldl f a = l.foldr f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_foldl", 2)
    if args is not None:
        try:
            rhs = OOp("l_foldr", (args[0], args[1],))
            results.append((rhs, "Mathlib: List_foldl_eq_foldr_of_commute"))
        except Exception:
            pass
    return results


def _r0007_foldl_eq_foldr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldl_eq_foldr
    # l.foldl f a = l.foldr f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_foldl", 2)
    if args is not None:
        try:
            rhs = OOp("l_foldr", (args[0], args[1],))
            results.append((rhs, "Mathlib: List_foldl_eq_foldr"))
        except Exception:
            pass
    return results


def _r0008_foldl_flip_eq_foldr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldl_flip_eq_foldr
    # l.foldl (flip f) b = l.foldr f b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_foldl", 2)
    if args is not None:
        try:
            rhs = OOp("l_foldr", (OVar("f"), args[1],))
            results.append((rhs, "Mathlib: List_foldl_flip_eq_foldr"))
        except Exception:
            pass
    return results


def _r0009_foldr_flip_eq_foldl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldr_flip_eq_foldl
    # l.foldr (flip v) b = l.foldl v b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_foldr", 2)
    if args is not None:
        try:
            rhs = OOp("l_foldl", (OVar("v"), args[1],))
            results.append((rhs, "Mathlib: List_foldr_flip_eq_foldl"))
        except Exception:
            pass
    return results


def _r0010_foldr_range_eq_of_range_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldr_range_eq_of_range_eq
    # Set.range (foldr f a) = Set.range (foldr g a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OOp("Set_range", (OOp("foldr", (OVar("g"), OVar("a"),)),))
            results.append((rhs, "Mathlib: List_foldr_range_eq_of_range_eq"))
        except Exception:
            pass
    return results


def _r0011_foldl_range_eq_of_range_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldl_range_eq_of_range_eq
    # Set.range (foldl f a) = Set.range (foldl g a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OOp("Set_range", (OOp("foldl", (OVar("g"), OVar("a"),)),))
            results.append((rhs, "Mathlib: List_foldl_range_eq_of_range_eq"))
        except Exception:
            pass
    return results


def _r0012_mapAccumr_eq_foldr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapAccumr_eq_foldr
    # ∀ (as : List α) (s : σ),     mapAccumr f as s = List.foldr (fun a s =>                                     let r := f a 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr", 3)
    if args is not None:
        try:
            rhs = OOp("foldr", (OOp("fun", (OVar("a"), args[2], OVar("eq_gt"), OVar("let"), OVar("r"), OVar("colon_eq"), args[0], OVar("a"), OVar("s_1"), OOp("r_1", (OVar("r_2"), OVar("colon_colon"), OVar("s_2"),)),)), OOp("s", (OSeq(()),)), args[1], OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a"), OVar("colon_colon"), args[1], args[2], OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_mapAccumr_eq_foldr"))
        except Exception:
            pass
    return results


def _r0013_mapAccumr_2_eq_foldr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapAccumr₂_eq_foldr
    # ∀ (as : List α) (bs : List β) (s : σ),     mapAccumr₂ f as bs s = foldr (fun ab s =>                               let r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapAccumr_2", 4)
    if args is not None:
        try:
            rhs = OOp("foldr", (OOp("fun", (OVar("ab"), args[3], OVar("eq_gt"), OVar("let"), OVar("r"), OVar("colon_eq"), args[0], OVar("ab_1"), OVar("ab_2"), OVar("s_1"), OOp("r_1", (OVar("r_2"), OVar("colon_colon"), OVar("s_2"),)),)), OOp("s", (OSeq(()),)), OOp("as_zip", (args[2],)), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), OVar("_unknown"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("colon_colon"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a"), OVar("colon_colon"), args[1], OVar("b"), OVar("colon_colon"), args[2], args[3], OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_mapAccumr_2_eq_foldr"))
        except Exception:
            pass
    return results


def _r0014_foldl_argAux_eq_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldl_argAux_eq_none
    # l.foldl (argAux r) o = none ↔ l = [] ∧ o = none
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_foldl", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("none"), OVar("l"))), OOp("==", (OOp("and", (OSeq(()), args[1])), OVar("none")))))
            results.append((rhs, "Mathlib: List_foldl_argAux_eq_none"))
        except Exception:
            pass
    return results


def _r0015_foldr_permutationsAux2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldr_permutationsAux2
    # foldr (fun y r => (permutationsAux2 t ts r y id).2) r L =       (L.flatMap fun y => (permutationsAux2 t ts [] y id).2) +
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "foldr", 3)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("L_flatMap", (OVar("fun"), OVar("y"), OVar("eq_gt"), OVar("permutationsAux2_t_ts_y_id_2"),)), args[1]))
            results.append((rhs, "Mathlib: List_foldr_permutationsAux2"))
        except Exception:
            pass
    return results


def _r0016_mem_foldr_permutationsAux2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_foldr_permutationsAux2
    # l' ∈ foldr (fun y r => (permutationsAux2 t ts r y id).2) r L ↔       l' ∈ r ∨ ∃ l₁ l₂, l₁ ++ l₂ ∈ L ∧ l₂ ≠ [] ∧ l' = l₁ 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("l_1"), OOp("concat", (OOp("t", (OVar("colon_colon"), OVar("l_2"),)), OVar("ts")))))
            results.append((rhs, "Mathlib: List_mem_foldr_permutationsAux2"))
        except Exception:
            pass
    return results


def _r0017_length_foldr_permutationsAux2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_foldr_permutationsAux2
    # length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) =       (map length L).sum + length r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("map_length_L_sum"), OOp("len", (OVar("r"),))))
            results.append((rhs, "Mathlib: List_length_foldr_permutationsAux2"))
        except Exception:
            pass
    return results


def _r0018_sublistsAux_eq_array_foldl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsAux_eq_array_foldl
    # sublistsAux = fun (a : α) (r : List (List α)) =>       (r.toArray.foldl (init := #[])         fun r l => (r.push l).push
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sublistsAux")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("fun", (OOp("a", (OVar("colon"), OVar("a"),)), OOp("r", (OVar("colon"), OVar("List"), OOp("List", (OVar("a"),)),)), OVar("eq_gt"), OVar("r_toArray_foldl_init_colon_eq_hash_fun_r_l_eq_gt_r_push_l_push_a_colon_colon_l_toList"),))
            results.append((rhs, "Mathlib: List_sublistsAux_eq_array_foldl"))
    except Exception:
        pass
    return results


def _r0019_foldl_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldl_const
    # l.foldl (fun b _ ↦ f b) a = f^[l.length] a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_foldl", 2)
    if args is not None:
        try:
            rhs = OOp("fpow_l_length", (args[1],))
            results.append((rhs, "Mathlib: List_foldl_const"))
        except Exception:
            pass
    return results


def _r0020_foldr_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.foldr_const
    # ∀ l : List α, l.foldr (fun _ ↦ f) b = f^[l.length] b   | [] => rfl   | a :: l =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_foldr", 2)
    if args is not None:
        try:
            rhs = OOp("fpow_l_length", (args[1], OVar("pipe"), OSeq(()), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a"), OVar("colon_colon"), OVar("l"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_foldr_const"))
        except Exception:
            pass
    return results


def _r0021_mem_foldr_sup_support_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_foldr_sup_support_iff
    # x ∈ l.foldr (Finsupp.support · ⊔ ·) ∅ ↔ ∃ f ∈ l, x ∈ f.support
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("f"),)), OOp("in", (OOp("l", (args[0],)), OVar("f_support")))))
            results.append((rhs, "Mathlib: List_mem_foldr_sup_support_iff"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_list_fold rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "Finsupp_support", "Set_range", "a_colon_colon_l_foldl", "a_colon_colon_l_foldr", "and", "argAux", "concat", "exists", "f", "flip", "foldl", "foldr", "fun", "iff", "in", "l_foldl", "l_foldr", "len", "mapAccumr", "mapAccumr_2", "or", "permutationsAux", "t",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_list_fold axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_list_fold rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_permutationsAux_cons(term, ctx))
    results.extend(_r0001_support_sum_eq(term, ctx))
    results.extend(_r0002_foldl_cons_nil(term, ctx))
    results.extend(_r0003_foldl_cons_eq_apply_foldl(term, ctx))
    results.extend(_r0004_foldr_cons_eq_foldr_apply(term, ctx))
    results.extend(_r0005_foldl1_eq_foldr1(term, ctx))
    results.extend(_r0006_foldl_eq_foldr_of_commute(term, ctx))
    results.extend(_r0007_foldl_eq_foldr(term, ctx))
    results.extend(_r0008_foldl_flip_eq_foldr(term, ctx))
    results.extend(_r0009_foldr_flip_eq_foldl(term, ctx))
    results.extend(_r0010_foldr_range_eq_of_range_eq(term, ctx))
    results.extend(_r0011_foldl_range_eq_of_range_eq(term, ctx))
    results.extend(_r0012_mapAccumr_eq_foldr(term, ctx))
    results.extend(_r0013_mapAccumr_2_eq_foldr(term, ctx))
    results.extend(_r0014_foldl_argAux_eq_none(term, ctx))
    results.extend(_r0015_foldr_permutationsAux2(term, ctx))
    results.extend(_r0016_mem_foldr_permutationsAux2(term, ctx))
    results.extend(_r0017_length_foldr_permutationsAux2(term, ctx))
    results.extend(_r0018_sublistsAux_eq_array_foldl(term, ctx))
    results.extend(_r0019_foldl_const(term, ctx))
    results.extend(_r0020_foldr_const(term, ctx))
    results.extend(_r0021_mem_foldr_sup_support_iff(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_list_fold rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("List_support_sum_subset", "l_sum_support_sub_l_foldr_Finsupp_support_empty", "Not an equality or iff proposition"),
    ("List_rel_foldl", "P_R_P_P_Forall_2_R_P_foldl_foldl_pipe_h_Forall", "Not an equality or iff proposition"),
    ("List_rel_foldr", "R_P_P_P_Forall_2_R_P_foldr_foldr_pipe_h_Forall", "Not an equality or iff proposition"),
    ("List_foldr_range_subset_of_range_subset", "Set_range_foldr_f_a_sub_Set_range_foldr_g_a", "Not an equality or iff proposition"),
    ("List_foldl_range_subset_of_range_subset", "Set_range_foldl_f_a_sub_Set_range_foldl_g_a", "Not an equality or iff proposition"),
    ("List_foldl_argAux_mem", "forall_a_m_colon_a_m_in_foldl_argAux_r_some_a_l_to_m_in_a_colon_colon_l", "Not an equality or iff proposition"),
    ("List_not_of_mem_foldl_argAux", "forall_a_m_colon_a_o_colon_Option_a_a_in_l_to_m_in_foldl_argAux_r_o_l_to_not_r_a_m", "Not an equality or iff proposition"),
    ("List_length_foldr_permutationsAux2", "_unknown", "Empty proposition"),
    ("List_foldl_monotone", "Monotone_fun_a_l_foldl_f_a", "Not an equality or iff proposition"),
    ("List_foldr_monotone", "Monotone_fun_b_l_foldr_f_b", "Not an equality or iff proposition"),
    ("List_foldl_strictMono", "StrictMono_fun_a_l_foldl_f_a", "Not an equality or iff proposition"),
    ("List_foldr_strictMono", "StrictMono_fun_b_l_foldr_f_b", "Not an equality or iff proposition"),
]
