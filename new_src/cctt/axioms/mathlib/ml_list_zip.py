"""Mathlib: List Zip — auto-generated from Mathlib4.

Contains 19 rewrite rules derived from Mathlib theorems.
Plus 7 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_list_zip"
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
# Rewrite rules (19 total)
# ════════════════════════════════════════════════════════════

def _r0000_zipWith_rotate_distrib(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.zipWith_rotate_distrib
    # (zipWith f l l').rotate n = zipWith f (l.rotate n) (l'.rotate n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zipWith_f_l_l_prime_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("zip_with", (OVar("f"), OOp("l_rotate", (args[0],)), OOp("l_prime_rotate", (args[0],)),))
            results.append((rhs, "Mathlib: List_zipWith_rotate_distrib"))
        except Exception:
            pass
    return results


def _r0001_cyclicPermutations_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cyclicPermutations_cons
    # cyclicPermutations (x :: l) = dropLast (zipWith (· ++ ·) (tails (x :: l)) (inits (x :: l)))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclicPermutations", 1)
    if args is not None:
        try:
            rhs = OOp("dropLast", (OOp("zip_with", (OOp("concat", (OVar("_unknown"), OVar("_unknown"))), OOp("tails", (OOp("x", (OVar("colon_colon"), OVar("l"),)),)), OOp("inits", (OOp("x", (OVar("colon_colon"), OVar("l"),)),)),)),))
            results.append((rhs, "Mathlib: List_cyclicPermutations_cons"))
        except Exception:
            pass
    return results


def _r0002_unzip_revzip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.unzip_revzip
    # (revzip l).unzip = (l, l.reverse)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("revzip_l_unzip")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l", (OVar("l_reverse"),))
            results.append((rhs, "Mathlib: List_unzip_revzip"))
    except Exception:
        pass
    return results


def _r0003_reverse_revzip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reverse_revzip
    # reverse l.revzip = revzip l.reverse
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reverse", 1)
    if args is not None:
        try:
            rhs = OOp("revzip", (OVar("l_reverse"),))
            results.append((rhs, "Mathlib: List_reverse_revzip"))
        except Exception:
            pass
    return results


def _r0004_zipWith_rotate_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.zipWith_rotate_one
    # zipWith f (x :: y :: l) ((x :: y :: l).rotate 1) = f x y :: zipWith f (y :: l) (l ++ [x])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zip_with", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"), OVar("y"), OVar("colon_colon"), OVar("zipWith"), args[0], OOp("y", (OVar("colon_colon"), OVar("l"),)), OOp("concat", (OVar("l"), OSeq((OVar("x"),)))),))
            results.append((rhs, "Mathlib: List_zipWith_rotate_one"))
        except Exception:
            pass
    return results


def _r0005_cyclicPermutations_of_ne_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cyclicPermutations_of_ne_nil
    # cyclicPermutations l = dropLast (zipWith (· ++ ·) (tails l) (inits l))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclicPermutations", 1)
    if args is not None:
        try:
            rhs = OOp("dropLast", (OOp("zip_with", (OOp("concat", (OVar("_unknown"), OVar("_unknown"))), OOp("tails", (args[0],)), OOp("inits", (args[0],)),)),))
            results.append((rhs, "Mathlib: List_cyclicPermutations_of_ne_nil"))
        except Exception:
            pass
    return results


def _r0006_forall_zipWith(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall_zipWith
    # ∀ {l₁ : List α} {l₂ : List β}, length l₁ = length l₂ →       (Forall p (zipWith f l₁ l₂) ↔ Forall₂ (fun x y => p (f x y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_p_zipWith_f_l_1_l_2_iff_Forall_2_fun_x_y_eq_gt_p_f_x_y_l_1_l_2", 4)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_forall_zipWith"))
        except Exception:
            pass
    return results


def _r0007_zipWith_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.zipWith_congr
    # zipWith f la lb = zipWith g la lb
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zip_with", 3)
    if args is not None:
        try:
            rhs = OOp("zip_with", (OVar("g"), args[1], args[2],))
            results.append((rhs, "Mathlib: List_zipWith_congr"))
        except Exception:
            pass
    return results


def _r0008_zipWith_zipWith_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.zipWith_zipWith_left
    # ∀ (la : List α) (lb : List β) (lc : List γ),       zipWith f (zipWith g la lb) lc = zipWith3 (fun a b c => f (g a b) c) 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_colon_forall_la", 8)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("gt", (OVar("f"), args[6], args[7], OVar("b_la_lb_pipe_eq_gt_rfl_pipe_colon_colon_eq_gt_rfl_pipe_colon_colon_as_colon_colon_bs_eq_gt_congr_arg_cons"), OVar("lt_pipe_zipWith3_same_right_f_as_bs_instance_f"), args[3], args[6],)), OOp("implies", (args[6], OOp("b_IsSymmOp", (OVar("f_colon_IsSymmOp_zipWith"), OVar("f"),))))))
            results.append((rhs, "Mathlib: List_zipWith_zipWith_left"))
        except Exception:
            pass
    return results


def _r0009_zipWith_zipWith_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.zipWith_zipWith_right
    # ∀ (la : List α) (lb : List β) (lc : List γ),       zipWith f la (zipWith g lb lc) = zipWith3 (fun a b c => f a (g b c)) 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_colon_forall_la", 8)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("gt", (OVar("f"), args[6], args[7], OVar("b_la_lb_pipe_eq_gt_rfl_pipe_colon_colon_eq_gt_rfl_pipe_colon_colon_as_colon_colon_bs_eq_gt_congr_arg_cons"), OVar("lt_pipe_zipWith3_same_right_f_as_bs_instance_f"), args[3], args[6],)), OOp("implies", (args[6], OOp("b_IsSymmOp", (OVar("f_colon_IsSymmOp_zipWith"), OVar("f"),))))))
            results.append((rhs, "Mathlib: List_zipWith_zipWith_right"))
        except Exception:
            pass
    return results


def _r0010_zipWith3_same_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.zipWith3_same_left
    # ∀ (la : List α) (lb : List β), zipWith3 f la la lb = zipWith (fun a b => f a a b) la lb   | [], _ => rfl   | _ :: _, [] 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_colon_forall_la", 8)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("gt", (OVar("f"), args[6], args[7], OVar("b_la_lb_pipe_eq_gt_rfl_pipe_colon_colon_eq_gt_rfl_pipe_colon_colon_as_colon_colon_bs_eq_gt_congr_arg_cons"), OVar("lt_pipe_zipWith3_same_right_f_as_bs_instance_f"), args[3], args[6],)), OOp("implies", (args[6], OOp("b_IsSymmOp", (OVar("f_colon_IsSymmOp_zipWith"), OVar("f"),))))))
            results.append((rhs, "Mathlib: List_zipWith3_same_left"))
        except Exception:
            pass
    return results


def _r0011_zipWith3_same_mid(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.zipWith3_same_mid
    # ∀ (la : List α) (lb : List β), zipWith3 f la lb la = zipWith (fun a b => f a b a) la lb   | [], _ => rfl   | _ :: _, [] 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_colon_forall_la", 8)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("gt", (OVar("f"), args[6], args[7], OVar("b_la_lb_pipe_eq_gt_rfl_pipe_colon_colon_eq_gt_rfl_pipe_colon_colon_as_colon_colon_bs_eq_gt_congr_arg_cons"), OVar("lt_pipe_zipWith3_same_right_f_as_bs_instance_f"), args[3], args[6],)), OOp("implies", (args[6], OOp("b_IsSymmOp", (OVar("f_colon_IsSymmOp_zipWith"), OVar("f"),))))))
            results.append((rhs, "Mathlib: List_zipWith3_same_mid"))
        except Exception:
            pass
    return results


def _r0012_zipWith3_same_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.zipWith3_same_right
    # ∀ (la : List α) (lb : List β), zipWith3 f la lb lb = zipWith (fun a b => f a b b) la lb   | [], _ => rfl   | _ :: _, [] 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zipWith3", 4)
    if args is not None:
        try:
            rhs = OOp("zip_with", (OOp("fun", (OVar("a"), OVar("b"), OVar("eq_gt"), args[0], OVar("a"), OVar("b"), OVar("b"),)), args[1], args[3], OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), OVar("_unknown"), OSeq(()), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), OVar("as"), OVar("_unknown"), OVar("colon_colon"), OVar("bs"), OVar("eq_gt"), OVar("congr_arg"), OOp("cons", (OVar("_unknown"),)), OVar("lt_pipe"), OVar("zipWith3_same_right"), args[0], OVar("as"), OVar("bs_instance"), OOp("implies", (OOp("f", (OVar("colon"), OVar("a"),)), OOp("implies", (OVar("a"), OVar("b"))))), OSeq((OOp("IsSymmOp", (args[0],)),)), OVar("colon"), OVar("IsSymmOp"), OOp("zip_with", (args[0],)),))
            results.append((rhs, "Mathlib: List_zipWith3_same_right"))
        except Exception:
            pass
    return results


def _r0013_mem_zip_inits_tails(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_zip_inits_tails
    # (init, tail) ∈ zip l.inits l.tails ↔ init ++ tail = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_mem_zip_inits_tails"))
        except Exception:
            pass
    return results


def _r0014_zipWith_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.zipWith_toList
    # (Vector.zipWith f x y).toList = List.zipWith f x.toList y.toList
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Vector_zipWith_f_x_y_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("zip_with", (OVar("f"), OVar("x_toList"), OVar("y_toList"),))
            results.append((rhs, "Mathlib: List_Vector_zipWith_toList"))
    except Exception:
        pass
    return results


def _r0015_zipWith_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.zipWith_get
    # (Vector.zipWith f x y).get i = f (x.get i) (y.get i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Vector_zipWith_f_x_y_get", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("x_get", (args[0],)), OOp("y_get", (args[0],)),))
            results.append((rhs, "Mathlib: List_Vector_zipWith_get"))
        except Exception:
            pass
    return results


def _r0016_zipWith_tail(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.zipWith_tail
    # (Vector.zipWith f x y).tail = Vector.zipWith f x.tail y.tail
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Vector_zipWith_f_x_y_tail")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Vector_zipWith", (OVar("f"), OVar("x_tail"), OVar("y_tail"),))
            results.append((rhs, "Mathlib: List_Vector_zipWith_tail"))
    except Exception:
        pass
    return results


def _r0017_prod_mul_prod_eq_prod_zipWith(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.prod_mul_prod_eq_prod_zipWith
    # x.toList.prod * y.toList.prod = (Vector.zipWith (· * ·) x y).toList.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("Vector_zipWith_star_x_y_toList_prod")
            results.append((rhs, "Mathlib: List_Vector_prod_mul_prod_eq_prod_zipWith"))
        except Exception:
            pass
    return results


def _r0018_mem_or_mem_of_zipWith_swap_prod_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_or_mem_of_zipWith_swap_prod_ne
    # ∀ {l l' : List α} {x : α},     (zipWith swap l l').prod x ≠ x → x ∈ l ∨ x ∈ l'   | [], _, _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_mem_or_mem_of_zipWith_swap_prod_ne"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_list_zip rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "Forall_p_zipWith_f_l_1_l_2_iff_Forall_2_fun_x_y_eq_gt_p_f_x_y_l_1_l_2", "Vector_zipWith_f_x_y_get", "concat", "cyclicPermutations", "g_colon_forall_la", "iff", "in", "init", "l_prime", "or", "reverse", "x", "x_colon_colon_y_colon_colon_l_rotate", "zip", "zipWith3", "zipWith_f_l_l_prime_rotate", "zip_with",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_list_zip axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_list_zip rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_zipWith_rotate_distrib(term, ctx))
    results.extend(_r0001_cyclicPermutations_cons(term, ctx))
    results.extend(_r0002_unzip_revzip(term, ctx))
    results.extend(_r0003_reverse_revzip(term, ctx))
    results.extend(_r0004_zipWith_rotate_one(term, ctx))
    results.extend(_r0005_cyclicPermutations_of_ne_nil(term, ctx))
    results.extend(_r0006_forall_zipWith(term, ctx))
    results.extend(_r0007_zipWith_congr(term, ctx))
    results.extend(_r0008_zipWith_zipWith_left(term, ctx))
    results.extend(_r0009_zipWith_zipWith_right(term, ctx))
    results.extend(_r0010_zipWith3_same_left(term, ctx))
    results.extend(_r0011_zipWith3_same_mid(term, ctx))
    results.extend(_r0012_zipWith3_same_right(term, ctx))
    results.extend(_r0013_mem_zip_inits_tails(term, ctx))
    results.extend(_r0014_zipWith_toList(term, ctx))
    results.extend(_r0015_zipWith_get(term, ctx))
    results.extend(_r0016_zipWith_tail(term, ctx))
    results.extend(_r0017_prod_mul_prod_eq_prod_zipWith(term, ctx))
    results.extend(_r0018_mem_or_mem_of_zipWith_swap_prod_ne(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_list_zip rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("List_forall_mem_zipIdx", "_unknown", "Empty proposition"),
    ("List_exists_mem_zipIdx", "_unknown", "Empty proposition"),
    ("List_revzip_sublists", "l_1_plus_plus_l_2_tilde_l", "Not an equality or iff proposition"),
    ("List_revzip_sublists", "_unknown", "Empty proposition"),
    ("List_rightInverse_unzip_zip", "RightInverse_unzip_colon_List_a_times_b_to_List_a_times_List_b_uncurry_zip", "Not an equality or iff proposition"),
    ("List_zipWith_swap_prod_support", "_unknown", "Empty proposition"),
    ("List_zipWith_swap_prod_support", "zipWith_swap_l_l_prime_prod_support_le_l_toFinset_l_prime_toFinset", "Not an equality or iff proposition"),
]
