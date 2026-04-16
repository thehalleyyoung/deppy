"""Mathlib: List Sort — auto-generated from Mathlib4.

Contains 62 rewrite rules derived from Mathlib theorems.
Plus 62 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_list_sort"
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
# Rewrite rules (62 total)
# ════════════════════════════════════════════════════════════

def _r0000_coe_getIso_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.SortedLT.coe_getIso_symm_apply
    # ((H.getIso l).symm x : ℕ) = idxOf (↑x) l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_getIso_l_symm", 3)
    if args is not None:
        try:
            rhs = OOp("idxOf", (args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_SortedLT_coe_getIso_symm_apply"))
        except Exception:
            pass
    return results


def _r0001_cyclicPermutations_ne_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cyclicPermutations_ne_nil
    # ∀ l : List α, cyclicPermutations l ≠ []   | a::l, h =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_cyclicPermutations_ne_nil"))
        except Exception:
            pass
    return results


def _r0002_cyclicPermutations_eq_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cyclicPermutations_eq_singleton_iff
    # cyclicPermutations l = [[x]] ↔ l = [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclicPermutations", 1)
    if args is not None:
        try:
            rhs = OSeq((OVar("x_iff_l_eq_x"),))
            results.append((rhs, "Mathlib: List_cyclicPermutations_eq_singleton_iff"))
        except Exception:
            pass
    return results


def _r0003_insertionSort_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.insertionSort_cons
    # (a :: l).insertionSort r = orderedInsert r a (insertionSort r l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_insertionSort", 1)
    if args is not None:
        try:
            rhs = OOp("orderedInsert", (args[0], OVar("a"), OOp("insertionSort", (args[0], OVar("l"),)),))
            results.append((rhs, "Mathlib: List_insertionSort_cons"))
        except Exception:
            pass
    return results


def _r0004_insertionSort_cons_of_forall_rel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.insertionSort_cons_of_forall_rel
    # insertionSort r (a :: l) = a :: insertionSort r l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "insertionSort", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("insertionSort"), args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_insertionSort_cons_of_forall_rel"))
        except Exception:
            pass
    return results


def _r0005_formPerm_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_singleton
    # formPerm [x] = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: List_formPerm_singleton"))
        except Exception:
            pass
    return results


def _r0006_formPerm_cons_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_cons_cons
    # formPerm (x :: y :: l) = swap x y * formPerm (y :: l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("swap", (OVar("x"), OVar("y"),)), OOp("formPerm", (OOp("y", (OVar("colon_colon"), OVar("l"),)),))))
            results.append((rhs, "Mathlib: List_formPerm_cons_cons"))
        except Exception:
            pass
    return results


def _r0007_formPerm_cons_concat_apply_last(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_cons_concat_apply_last
    # formPerm (x :: (xs ++ [y])) y = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: List_formPerm_cons_concat_apply_last"))
        except Exception:
            pass
    return results


def _r0008_toFinset_eq_iff_perm_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_eq_iff_perm_dedup
    # l.toFinset = l'.toFinset ↔ l.dedup ~ l'.dedup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("l_prime_toFinset"), OOp("l_dedup", (OVar("tilde"), OVar("l_prime_dedup"),))))
            results.append((rhs, "Mathlib: List_toFinset_eq_iff_perm_dedup"))
    except Exception:
        pass
    return results


def _r0009_toFinset_eq_of_perm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_eq_of_perm
    # l.toFinset = l'.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_prime_toFinset")
            results.append((rhs, "Mathlib: List_toFinset_eq_of_perm"))
    except Exception:
        pass
    return results


def _r0010_coe_getIso_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.SortedLT.coe_getIso_apply
    # (H.getIso l i : α) = get l i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_getIso", 4)
    if args is not None:
        try:
            rhs = OOp("get", (args[0], args[1],))
            results.append((rhs, "Mathlib: List_SortedLT_coe_getIso_apply"))
        except Exception:
            pass
    return results


def _r0011_forall_2_comp_perm_eq_perm_comp_forall_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_comp_perm_eq_perm_comp_forall₂
    # Forall₂ r ∘r Perm = Perm ∘r Forall₂ r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2", 3)
    if args is not None:
        try:
            rhs = OOp("perm", (args[1], OVar("Forall_2"), args[0],))
            results.append((rhs, "Mathlib: List_forall_2_comp_perm_eq_perm_comp_forall_2"))
        except Exception:
            pass
    return results


def _r0012_bagInter_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Perm.bagInter_left
    # l.bagInter t₁ = l.bagInter t₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_bagInter", 1)
    if args is not None:
        try:
            rhs = OOp("l_bagInter", (OVar("t_2"),))
            results.append((rhs, "Mathlib: List_Perm_bagInter_left"))
        except Exception:
            pass
    return results


def _r0013_permutationsAux2_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutationsAux2_fst
    # ∀ (ys : List α) (f : List α → β), (permutationsAux2 t ts r ys f).1 = ys ++ ts   | [], _ => rfl   | y :: ys, f =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("permutationsAux2_t_ts_r_ys_f_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OVar("ys"), OOp("ts", (OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("y"), OVar("colon_colon"), OVar("ys"), OVar("f"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_permutationsAux2_fst"))
    except Exception:
        pass
    return results


def _r0014_permutationsAux2_snd_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutationsAux2_snd_nil
    # (permutationsAux2 t ts r [] f).2 = r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("permutationsAux2_t_ts_r_f_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("r")
            results.append((rhs, "Mathlib: List_permutationsAux2_snd_nil"))
    except Exception:
        pass
    return results


def _r0015_permutationsAux2_snd_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutationsAux2_snd_cons
    # (permutationsAux2 t ts r (y :: ys) f).2 =       f (t :: y :: ys ++ ts) :: (permutationsAux2 t ts r ys fun x : List α => 
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("permutationsAux2_t_ts_r_y_colon_colon_ys_f_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OOp("concat", (OOp("t", (OVar("colon_colon"), OVar("y"), OVar("colon_colon"), OVar("ys"),)), OVar("ts"))), OVar("colon_colon"), OVar("permutationsAux2_t_ts_r_ys_fun_x_colon_List_a_eq_gt_f_y_colon_colon_x_2"),))
            results.append((rhs, "Mathlib: List_permutationsAux2_snd_cons"))
    except Exception:
        pass
    return results


def _r0016_permutationsAux2_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutationsAux2_append
    # (permutationsAux2 t ts nil ys f).2 ++ r = (permutationsAux2 t ts r ys f).2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OVar("permutationsAux2_t_ts_r_ys_f_2")
            results.append((rhs, "Mathlib: List_permutationsAux2_append"))
        except Exception:
            pass
    return results


def _r0017_permutationsAux2_comp_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutationsAux2_comp_append
    # ((permutationsAux2 t [] r ys) fun x => f (x ++ ts)).2 = (permutationsAux2 t ts r ys f).2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("permutationsAux2_t_r_ys_fun_x_eq_gt_f_x_plus_plus_ts_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("permutationsAux2_t_ts_r_ys_f_2")
            results.append((rhs, "Mathlib: List_permutationsAux2_comp_append"))
    except Exception:
        pass
    return results


def _r0018_mem_permutationsAux2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_permutationsAux2
    # l' ∈ (permutationsAux2 t ts [] ys (l ++ ·)).2 ↔       ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("l_1"), OOp("concat", (OOp("==", (OOp("and", (OVar("l_2"), OVar("l_prime"))), OVar("l"))), OOp("concat", (OVar("l_1"), OOp("concat", (OOp("t", (OVar("colon_colon"), OVar("l_2"),)), OVar("ts")))))))))
            results.append((rhs, "Mathlib: List_mem_permutationsAux2"))
        except Exception:
            pass
    return results


def _r0019_permutationsAux_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutationsAux_nil
    # permutationsAux [] is = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "permutationsAux", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_permutationsAux_nil"))
        except Exception:
            pass
    return results


def _r0020_permutations_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutations_nil
    # permutations ([] : List α) = [[]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "permutations", 1)
    if args is not None:
        try:
            rhs = OSeq((OSeq(()),))
            results.append((rhs, "Mathlib: List_permutations_nil"))
        except Exception:
            pass
    return results


def _r0021_permutations_take_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.permutations_take_two
    # (x :: y :: s).permutations.take 2 = [x :: y :: s, y :: x :: s]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_colon_colon_y_colon_colon_s_permutations_take", 1)
    if args is not None:
        try:
            rhs = OVar("x_colon_colon_y_colon_colon_s_y_colon_colon_x_colon_colon_s")
            results.append((rhs, "Mathlib: List_permutations_take_two"))
        except Exception:
            pass
    return results


def _r0022_cyclicPermutations_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cyclicPermutations_nil
    # cyclicPermutations ([] : List α) = [[]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclicPermutations", 1)
    if args is not None:
        try:
            rhs = OSeq((OSeq(()),))
            results.append((rhs, "Mathlib: List_cyclicPermutations_nil"))
        except Exception:
            pass
    return results


def _r0023_get_cyclicPermutations(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_cyclicPermutations
    # (cyclicPermutations l).get n = l.rotate n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclicPermutations_l_get", 1)
    if args is not None:
        try:
            rhs = OOp("l_rotate", (args[0],))
            results.append((rhs, "Mathlib: List_get_cyclicPermutations"))
        except Exception:
            pass
    return results


def _r0024_head_cyclicPermutations(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.head_cyclicPermutations
    # (cyclicPermutations l).head (cyclicPermutations_ne_nil l) = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclicPermutations_l_head", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_head_cyclicPermutations"))
        except Exception:
            pass
    return results


def _r0025_cyclicPermutations_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cyclicPermutations_inj
    # cyclicPermutations l = cyclicPermutations l' ↔ l = l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclicPermutations", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("cyclicPermutations", (OVar("l_prime"),)), args[0])), OVar("l_prime")))
            results.append((rhs, "Mathlib: List_cyclicPermutations_inj"))
        except Exception:
            pass
    return results


def _r0026_cyclicPermutations_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cyclicPermutations_rotate
    # (l.rotate k).cyclicPermutations = l.cyclicPermutations.rotate k
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_rotate_k_cyclicPermutations")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_cyclicPermutations_rotate", (OVar("k"),))
            results.append((rhs, "Mathlib: List_cyclicPermutations_rotate"))
    except Exception:
        pass
    return results


def _r0027_cyclicPermutations_eq_nil_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cyclicPermutations_eq_nil_iff
    # cyclicPermutations l = [[]] ↔ l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclicPermutations", 1)
    if args is not None:
        try:
            rhs = OSeq((OVar("iff_l_eq"),))
            results.append((rhs, "Mathlib: List_cyclicPermutations_eq_nil_iff"))
        except Exception:
            pass
    return results


def _r0028_perm_dlookup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.perm_dlookup
    # dlookup a l₁ = dlookup a l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("dlookup", (args[0], OVar("l_2"),))
            results.append((rhs, "Mathlib: List_perm_dlookup"))
        except Exception:
            pass
    return results


def _r0029_perm_lookupAll(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.perm_lookupAll
    # lookupAll a l₁ = lookupAll a l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lookupAll", 2)
    if args is not None:
        try:
            rhs = OOp("lookupAll", (args[0], OVar("l_2"),))
            results.append((rhs, "Mathlib: List_perm_lookupAll"))
        except Exception:
            pass
    return results


def _r0030_kunion_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Perm.kunion_left
    # ∀ (l) {l₁ l₂ : List (Sigma β)}, l₁.NodupKeys → l₁ ~ l₂ → kunion l l₁ ~ kunion l l₂   | [], _, _, _, p => p   | s :: l, _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kunion", 12)
    if args is not None:
        try:
            rhs = OOp("gt", (args[11], args[6], OVar("s"), OVar("colon_colon"), args[4], args[10], args[10], OVar("nd_1"), args[11], OVar("eq_gt"), OVar("p_kerase_nd_1_kunion_left_l_lt_pipe_nd_1_kerase_s_1_cons"), OVar("s_theorem"), OVar("Perm_kunion"), OVar("l_1_l_2_l_3_l_4_colon_List_Sigma_b"), OOp("nd_3", (OVar("colon"), OVar("l_3_NodupKeys"),)), OOp("p_1_2", (OVar("colon"), args[1], args[2], args[5],)), OOp("p_3_4", (OVar("colon"), OVar("l_3"), args[2], OVar("l_4"),)), OVar("colon"), args[3], args[1], OVar("l_3"), args[2], args[3], args[5], OVar("l_4"),))
            results.append((rhs, "Mathlib: List_Perm_kunion_left"))
        except Exception:
            pass
    return results


def _r0031_insertionSort_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.insertionSort_nil
    # [].insertionSort r = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "insertionSort", 1)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_insertionSort_nil"))
        except Exception:
            pass
    return results


def _r0032_perm_orderedInsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.perm_orderedInsert
    # ∀ l : List α, orderedInsert r a l ~ a :: l   | [] => Perm.refl _   | b :: l =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "orderedInsert", 9)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("Perm_refl"), OVar("_unknown"), args[7], OVar("b"), args[5], args[6], OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_perm_orderedInsert"))
        except Exception:
            pass
    return results


def _r0033_insertionSort_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Pairwise.insertionSort_eq
    # Pairwise r l → insertionSort r l = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "insertionSort", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: List_Pairwise_insertionSort_eq"))
        except Exception:
            pass
    return results


def _r0034_pairwise_insertionSort(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.pairwise_insertionSort
    # ∀ l, Pairwise r (insertionSort r l)   | [] => Pairwise.nil   | a :: l => (pairwise_insertionSort l).orderedInsert a _  @
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Pairwise", 4)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("Pairwise_nil"), args[2], OVar("a"), OVar("colon_colon"), OVar("l"), OVar("eq_gt"), OVar("pairwise_insertionSort_l_orderedInsert"), OVar("a"), OVar("at_deprecated_since_colon_eq_2025minus_10minus_11_alias"), OVar("sorted_insertionSort"),))
            results.append((rhs, "Mathlib: List_pairwise_insertionSort"))
        except Exception:
            pass
    return results


def _r0035_cycleOf_formPerm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cycleOf_formPerm
    # cycleOf l.attach.formPerm x = l.attach.formPerm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleOf", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: List_cycleOf_formPerm"))
        except Exception:
            pass
    return results


def _r0036_formPerm_apply_mem_eq_next(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_apply_mem_eq_next
    # formPerm l x = next l x hx
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = OOp("next", (args[0], args[1], OVar("hx"),))
            results.append((rhs, "Mathlib: List_formPerm_apply_mem_eq_next"))
        except Exception:
            pass
    return results


def _r0037_formPerm_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_nil
    # formPerm ([] : List α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: List_formPerm_nil"))
        except Exception:
            pass
    return results


def _r0038_formPerm_pair(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_pair
    # formPerm [x, y] = swap x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OOp("swap", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: List_formPerm_pair"))
        except Exception:
            pass
    return results


def _r0039_formPerm_apply_head(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_apply_head
    # formPerm (x :: y :: xs) x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_formPerm_apply_head"))
        except Exception:
            pass
    return results


def _r0040_support_formPerm_of_nodup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.support_formPerm_of_nodup
    # support (formPerm l) = l.toFinset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "support", 1)
    if args is not None:
        try:
            rhs = OVar("l_toFinset")
            results.append((rhs, "Mathlib: List_support_formPerm_of_nodup"))
        except Exception:
            pass
    return results


def _r0041_formPerm_rotate_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_rotate_one
    # formPerm (l.rotate 1) = formPerm l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OOp("formPerm", (OVar("l"),))
            results.append((rhs, "Mathlib: List_formPerm_rotate_one"))
        except Exception:
            pass
    return results


def _r0042_formPerm_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_rotate
    # formPerm (l.rotate n) = formPerm l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OOp("formPerm", (OVar("l"),))
            results.append((rhs, "Mathlib: List_formPerm_rotate"))
        except Exception:
            pass
    return results


def _r0043_formPerm_eq_of_isRotated(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_eq_of_isRotated
    # formPerm l = formPerm l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OOp("formPerm", (OVar("l_prime"),))
            results.append((rhs, "Mathlib: List_formPerm_eq_of_isRotated"))
        except Exception:
            pass
    return results


def _r0044_formPerm_append_pair(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_append_pair
    # ∀ (l : List α) (a b : α),     formPerm (l ++ [a, b]) = formPerm (l ++ [a]) * swap a b   | [], _, _ => rfl   | [_], _, _ 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("formPerm", (OOp("concat", (OVar("l"), OSeq((OVar("a"),)))),)), OOp("swap", (OVar("a"), OVar("b"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("xcolon_colon_ycolon_colon_l"), OVar("a"), OVar("b"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_formPerm_append_pair"))
        except Exception:
            pass
    return results


def _r0045_formPerm_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_reverse
    # ∀ l : List α, formPerm l.reverse = (formPerm l)⁻¹   | [] => rfl   | [_] => rfl   | a::b::l =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OOp("formPerm_l_inv", (OVar("pipe"), OSeq(()), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OSeq((OVar("_unknown"),)), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("acolon_colon_bcolon_colon_l"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_formPerm_reverse"))
        except Exception:
            pass
    return results


def _r0046_formPerm_ext_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_ext_iff
    # formPerm (x :: y :: l) = formPerm (x' :: y' :: l') ↔ (x :: y :: l) ~r (x' :: y' :: l')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("formPerm", (OOp("x_prime", (OVar("colon_colon"), OVar("y_prime"), OVar("colon_colon"), OVar("l_prime"),)),)), OOp("x_colon_colon_y_colon_colon_l", (OVar("tilde_r"), OOp("x_prime", (OVar("colon_colon"), OVar("y_prime"), OVar("colon_colon"), OVar("l_prime"),)),))))
            results.append((rhs, "Mathlib: List_formPerm_ext_iff"))
        except Exception:
            pass
    return results


def _r0047_perm_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.perm_reverse
    # l₁ ~ l₂.reverse ↔ l₁ ~ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_1", 2)
    if args is not None:
        try:
            rhs = OOp("l_1", (args[0], OVar("l_2"),))
            results.append((rhs, "Mathlib: List_perm_reverse"))
        except Exception:
            pass
    return results


def _r0048_nodup_mergeSort(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_mergeSort
    # (l.mergeSort le).Nodup ↔ l.Nodup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_mergeSort_le_Nodup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_Nodup")
            results.append((rhs, "Mathlib: List_nodup_mergeSort"))
    except Exception:
        pass
    return results


def _r0049_subset_congr_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Perm.subset_congr_left
    # l₁ ⊆ l₃ ↔ l₂ ⊆ l₃
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("subset", (OVar("l_2"), args[1]))
            results.append((rhs, "Mathlib: List_Perm_subset_congr_left"))
        except Exception:
            pass
    return results


def _r0050_subset_congr_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Perm.subset_congr_right
    # l₃ ⊆ l₁ ↔ l₃ ⊆ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("subset", (args[0], OVar("l_2")))
            results.append((rhs, "Mathlib: List_Perm_subset_congr_right"))
        except Exception:
            pass
    return results


def _r0051_perm_insertIdx_iff_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.perm_insertIdx_iff_of_le
    # l₁.insertIdx m a ~ l₂.insertIdx n a ↔ l₁ ~ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_1_insertIdx", 6)
    if args is not None:
        try:
            rhs = OOp("l_1", (args[2], OVar("l_2"),))
            results.append((rhs, "Mathlib: List_perm_insertIdx_iff_of_le"))
        except Exception:
            pass
    return results


def _r0052_perm_insertIdx_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.perm_insertIdx_iff
    # l₁.insertIdx n a ~ l₂.insertIdx n a ↔ l₁ ~ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_1_insertIdx", 6)
    if args is not None:
        try:
            rhs = OOp("l_1", (args[2], OVar("l_2"),))
            results.append((rhs, "Mathlib: List_perm_insertIdx_iff"))
        except Exception:
            pass
    return results


def _r0053_mem_permutations(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_permutations
    # s ∈ permutations t ↔ s ~ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("s", (OVar("tilde"), OVar("t"),))
            results.append((rhs, "Mathlib: List_mem_permutations"))
        except Exception:
            pass
    return results


def _r0054_perm_permutations_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.perm_permutations_iff
    # permutations s ~ permutations t ↔ s ~ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "permutations", 4)
    if args is not None:
        try:
            rhs = OOp("s", (args[1], args[3],))
            results.append((rhs, "Mathlib: List_perm_permutations_iff"))
        except Exception:
            pass
    return results


def _r0055_nodup_permutations_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_permutations_iff
    # Nodup s.permutations ↔ Nodup s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("nodup", (OVar("s"),))
            results.append((rhs, "Mathlib: List_nodup_permutations_iff"))
        except Exception:
            pass
    return results


def _r0056_mem_cyclicPermutations_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_cyclicPermutations_iff
    # l ∈ cyclicPermutations l' ↔ l ~r l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("l", (OVar("tilde_r"), OVar("l_prime"),))
            results.append((rhs, "Mathlib: List_mem_cyclicPermutations_iff"))
        except Exception:
            pass
    return results


def _r0057_isRotated_cyclicPermutations_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isRotated_cyclicPermutations_iff
    # l.cyclicPermutations ~r l'.cyclicPermutations ↔ l ~r l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_cyclicPermutations", 2)
    if args is not None:
        try:
            rhs = OOp("l", (args[0], OVar("l_prime"),))
            results.append((rhs, "Mathlib: List_isRotated_cyclicPermutations_iff"))
        except Exception:
            pass
    return results


def _r0058_perm_nodupKeys(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.perm_nodupKeys
    # NodupKeys l₁ ↔ NodupKeys l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NodupKeys", 1)
    if args is not None:
        try:
            rhs = OOp("NodupKeys", (OVar("l_2"),))
            results.append((rhs, "Mathlib: List_perm_nodupKeys"))
        except Exception:
            pass
    return results


def _r0059_mem_insertionSort(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_insertionSort
    # x ∈ l.insertionSort r ↔ x ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("l")))
            results.append((rhs, "Mathlib: List_mem_insertionSort"))
        except Exception:
            pass
    return results


def _r0060_formPerm_disjoint_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_disjoint_iff
    # Perm.Disjoint (formPerm l) (formPerm l') ↔ l.Disjoint l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Perm_Disjoint", 2)
    if args is not None:
        try:
            rhs = OOp("l_Disjoint", (OVar("l_prime"),))
            results.append((rhs, "Mathlib: List_formPerm_disjoint_iff"))
        except Exception:
            pass
    return results


def _r0061_formPerm_mem_iff_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_mem_iff_mem
    # l.formPerm x ∈ l ↔ x ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("x"), args[1]))
            results.append((rhs, "Mathlib: List_formPerm_mem_iff_mem"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_list_sort rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "Forall_2", "H_getIso", "H_getIso_l_symm", "NodupKeys", "Pairwise", "Perm_Disjoint", "_unknown", "a", "a_colon_colon_l_insertionSort", "and", "concat", "cycleOf", "cyclicPermutations", "cyclicPermutations_l_get", "cyclicPermutations_l_head", "cyclicPermutations_ne_nil", "dlookup", "exists", "formPerm", "iff", "in", "insertionSort", "kunion", "l_1", "l_1_insertIdx", "l_bagInter", "l_cyclicPermutations", "l_formPerm", "l_insertionSort", "l_rotate", "lookupAll", "nodup", "orderedInsert", "permutations", "permutationsAux", "subset", "support", "x", "x_colon_colon_y_colon_colon_s_permutations_take",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_list_sort axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_list_sort rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_coe_getIso_symm_apply(term, ctx))
    results.extend(_r0001_cyclicPermutations_ne_nil(term, ctx))
    results.extend(_r0002_cyclicPermutations_eq_singleton_iff(term, ctx))
    results.extend(_r0003_insertionSort_cons(term, ctx))
    results.extend(_r0004_insertionSort_cons_of_forall_rel(term, ctx))
    results.extend(_r0005_formPerm_singleton(term, ctx))
    results.extend(_r0006_formPerm_cons_cons(term, ctx))
    results.extend(_r0007_formPerm_cons_concat_apply_last(term, ctx))
    results.extend(_r0008_toFinset_eq_iff_perm_dedup(term, ctx))
    results.extend(_r0009_toFinset_eq_of_perm(term, ctx))
    results.extend(_r0010_coe_getIso_apply(term, ctx))
    results.extend(_r0011_forall_2_comp_perm_eq_perm_comp_forall_2(term, ctx))
    results.extend(_r0012_bagInter_left(term, ctx))
    results.extend(_r0013_permutationsAux2_fst(term, ctx))
    results.extend(_r0014_permutationsAux2_snd_nil(term, ctx))
    results.extend(_r0015_permutationsAux2_snd_cons(term, ctx))
    results.extend(_r0016_permutationsAux2_append(term, ctx))
    results.extend(_r0017_permutationsAux2_comp_append(term, ctx))
    results.extend(_r0018_mem_permutationsAux2(term, ctx))
    results.extend(_r0019_permutationsAux_nil(term, ctx))
    results.extend(_r0020_permutations_nil(term, ctx))
    results.extend(_r0021_permutations_take_two(term, ctx))
    results.extend(_r0022_cyclicPermutations_nil(term, ctx))
    results.extend(_r0023_get_cyclicPermutations(term, ctx))
    results.extend(_r0024_head_cyclicPermutations(term, ctx))
    results.extend(_r0025_cyclicPermutations_inj(term, ctx))
    results.extend(_r0026_cyclicPermutations_rotate(term, ctx))
    results.extend(_r0027_cyclicPermutations_eq_nil_iff(term, ctx))
    results.extend(_r0028_perm_dlookup(term, ctx))
    results.extend(_r0029_perm_lookupAll(term, ctx))
    results.extend(_r0030_kunion_left(term, ctx))
    results.extend(_r0031_insertionSort_nil(term, ctx))
    results.extend(_r0032_perm_orderedInsert(term, ctx))
    results.extend(_r0033_insertionSort_eq(term, ctx))
    results.extend(_r0034_pairwise_insertionSort(term, ctx))
    results.extend(_r0035_cycleOf_formPerm(term, ctx))
    results.extend(_r0036_formPerm_apply_mem_eq_next(term, ctx))
    results.extend(_r0037_formPerm_nil(term, ctx))
    results.extend(_r0038_formPerm_pair(term, ctx))
    results.extend(_r0039_formPerm_apply_head(term, ctx))
    results.extend(_r0040_support_formPerm_of_nodup(term, ctx))
    results.extend(_r0041_formPerm_rotate_one(term, ctx))
    results.extend(_r0042_formPerm_rotate(term, ctx))
    results.extend(_r0043_formPerm_eq_of_isRotated(term, ctx))
    results.extend(_r0044_formPerm_append_pair(term, ctx))
    results.extend(_r0045_formPerm_reverse(term, ctx))
    results.extend(_r0046_formPerm_ext_iff(term, ctx))
    results.extend(_r0047_perm_reverse(term, ctx))
    results.extend(_r0048_nodup_mergeSort(term, ctx))
    results.extend(_r0049_subset_congr_left(term, ctx))
    results.extend(_r0050_subset_congr_right(term, ctx))
    results.extend(_r0051_perm_insertIdx_iff_of_le(term, ctx))
    results.extend(_r0052_perm_insertIdx_iff(term, ctx))
    results.extend(_r0053_mem_permutations(term, ctx))
    results.extend(_r0054_perm_permutations_iff(term, ctx))
    results.extend(_r0055_nodup_permutations_iff(term, ctx))
    results.extend(_r0056_mem_cyclicPermutations_iff(term, ctx))
    results.extend(_r0057_isRotated_cyclicPermutations_iff(term, ctx))
    results.extend(_r0058_perm_nodupKeys(term, ctx))
    results.extend(_r0059_mem_insertionSort(term, ctx))
    results.extend(_r0060_formPerm_disjoint_iff(term, ctx))
    results.extend(_r0061_formPerm_mem_iff_mem(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_list_sort rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("List_Perm_prod_eq", "_unknown", "Empty proposition"),
    ("List_perm_of_nodup_nodup_toFinset_eq", "l_tilde_l_prime", "Not an equality or iff proposition"),
    ("List_reverse_perm", "_unknown", "Empty proposition"),
    ("List_Perm_dedup", "dedup_l_1_tilde_dedup_l_2", "Not an equality or iff proposition"),
    ("List_Perm_offDiag", "l_1_offDiag_tilde_l_2_offDiag", "Not an equality or iff proposition"),
    ("List_perm_rfl", "l_tilde_l", "Not an equality or iff proposition"),
    ("List_set_perm_cons_eraseIdx", "l_set_n_a_tilde_a_colon_colon_l_eraseIdx_n", "Not an equality or iff proposition"),
    ("List_Perm_insertIdx", "l_1_insertIdx_n_a_tilde_l_2_insertIdx_n_a", "Not an equality or iff proposition"),
    ("List_perm_comp_perm", "Perm_comp_r_Perm_colon_List_a_to_List_a_to_Prop_eq_Perm", "Not an equality or iff proposition"),
    ("List_perm_comp_forall_2", "Forall_2_r_comp_r_Perm_l_v", "Not an equality or iff proposition"),
    ("List_rel_perm_imp", "Forall_2_r_Forall_2_r_to_Perm_Perm", "Not an equality or iff proposition"),
    ("List_rel_perm", "Forall_2_r_Forall_2_r_iff_Perm_Perm", "Not an equality or iff proposition"),
    ("List_Perm_bagInter_right", "l_1_bagInter_t_tilde_l_2_bagInter_t", "Not an equality or iff proposition"),
    ("List_Perm_bagInter", "l_1_bagInter_t_1_tilde_l_2_bagInter_t_2", "Not an equality or iff proposition"),
    ("List_Perm_inter_append", "l_inter_t_1_plus_plus_t_2_tilde_l_inter_t_1_plus_plus_l_inter_t_2", "Not an equality or iff proposition"),
    ("List_Perm_take_inter", "xs_take_n_tilde_ys_inter_xs_take_n", "Not an equality or iff proposition"),
    ("List_Perm_drop_inter", "xs_drop_n_tilde_ys_inter_xs_drop_n", "Not an equality or iff proposition"),
    ("List_Perm_dropSlice_inter", "List_dropSlice_n_m_xs_tilde_ys_inter_List_dropSlice_n_m_xs", "Not an equality or iff proposition"),
    ("List_permutations", "_unknown", "Empty proposition"),
    ("List_mem_permutationsAux2", "_unknown", "Empty proposition"),
    ("List_perm_of_mem_permutationsAux", "forall_ts_is_l_colon_List_a_l_in_permutationsAux_ts_is_to_l_tilde_ts_plus_plus_is", "Not an equality or iff proposition"),
    ("List_perm_of_mem_permutations", "l_1_tilde_l_2", "Not an equality or iff proposition"),
    ("List_mem_permutations_of_perm_lemma", "l_tilde_is_to_l_in_permutations_is", "Not an equality or iff proposition"),
    ("List_mem_permutationsAux_of_perm", "forall_ts_is_l_colon_List_a_l_tilde_is_plus_plus_ts_to_exists_is_prime_colon_colon_is_prime_tilde_is_l_eq_is_prime", "Not an equality or iff proposition"),
    ("List_perm_permutations", "_unknown", "Empty proposition"),
    ("List_Perm_permutations", "_unknown", "Empty proposition"),
    ("List_permutations_perm_permutations", "_unknown", "Empty proposition"),
    ("List_mem_permutations", "_unknown", "Empty proposition"),
    ("List_Perm_permutations", "permutations_s_tilde_permutations_t", "Not an equality or iff proposition"),
    ("List_perm_permutations", "_unknown", "Empty proposition"),
    ("List_get_permutations", "_unknown", "Empty proposition"),
    ("List_count_permutations", "_unknown", "Empty proposition"),
    ("List_injective_permutations", "_unknown", "Empty proposition"),
    ("List_nodup_permutations", "_unknown", "Empty proposition"),
    ("List_nodup_permutations", "_unknown", "Empty proposition"),
    ("List_nodup_permutations", "Nodup_s_permutations", "Not an equality or iff proposition"),
    ("List_rotate_perm", "l_rotate_n_tilde_l", "Not an equality or iff proposition"),
    ("List_IsRotated_perm", "l_tilde_l_prime", "Not an equality or iff proposition"),
    ("List_mem_cyclicPermutations_self", "l_in_cyclicPermutations_l", "Not an equality or iff proposition"),
    ("List_Nodup_cyclicPermutations", "Nodup_cyclicPermutations_l", "Not an equality or iff proposition"),
    ("List_IsRotated_cyclicPermutations", "l_cyclicPermutations_tilde_r_l_prime_cyclicPermutations", "Not an equality or iff proposition"),
    ("List_Perm_kreplace", "l_1_tilde_l_2_to_kreplace_a_b_l_1_tilde_kreplace_a_b_l_2", "Not an equality or iff proposition"),
    ("List_Perm_kerase", "l_1_tilde_l_2_to_kerase_a_l_1_tilde_kerase_a_l_2", "Not an equality or iff proposition"),
    ("List_Perm_kinsert", "kinsert_a_b_l_1_tilde_kinsert_a_b_l_2", "Not an equality or iff proposition"),
    ("List_Perm_kunion_right", "kunion_l_1_l_tilde_kunion_l_2_l", "Not an equality or iff proposition"),
    ("List_Perm_kunion", "kunion_l_1_l_3_tilde_kunion_l_2_l_4", "Not an equality or iff proposition"),
    ("List_perm_insertionSort", "insertionSort_r_l_tilde_l", "Not an equality or iff proposition"),
    ("List_sublists_perm_sublists", "_unknown", "Empty proposition"),
    ("List_subperm_of_sublists", "_unknown", "Empty proposition"),
    ("List_Perm_sym2", "xs_sym2_tilde_ys_sym2", "Not an equality or iff proposition"),
    ("List_Subperm_sym2", "xs_sym2_lt_plus_tilde_ys_sym2", "Not an equality or iff proposition"),
    ("List_Nodup_isCycleOn_formPerm", "l_formPerm_IsCycleOn_a_pipe_a_in_l", "Not an equality or iff proposition"),
    ("List_isCycle_formPerm", "IsCycle_formPerm_l", "Not an equality or iff proposition"),
    ("List_pairwise_sameCycle_formPerm", "Pairwise_l_formPerm_SameCycle_l", "Not an equality or iff proposition"),
    ("List_support_formPerm_le", "_unknown", "Empty proposition"),
    ("List_support_formPerm_le", "support_formPerm_l_le_l_toFinset", "Not an equality or iff proposition"),
    ("List_mem_of_formPerm_apply_ne", "x_in_l", "Not an equality or iff proposition"),
    ("List_formPerm_apply_mem_of_mem", "formPerm_l_x_in_l", "Not an equality or iff proposition"),
    ("List_mem_of_formPerm_apply_mem", "x_in_l", "Not an equality or iff proposition"),
    ("List_support_formPerm_of_nodup", "_unknown", "Empty proposition"),
    ("List_form_perm_zpow_apply_mem_imp_mem", "formPerm_l_pow_n_x_in_l", "Not an equality or iff proposition"),
    ("List_SortedGT_lt_ord_of_lt", "forall_i_in_m_Ordinal_typein_a_colon_eq_a_lt_i_lt_o", "Not an equality or iff proposition"),
]
