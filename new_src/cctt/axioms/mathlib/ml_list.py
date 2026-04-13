"""Mathlib: List — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 288 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_list"
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

def _r0000_antidiagonalTuple_zero_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.antidiagonalTuple_zero_succ
    # antidiagonalTuple 0 (n + 1) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_Nat_antidiagonalTuple_zero_succ"))
        except Exception:
            pass
    return results


def _r0001_mem_antidiagonalTuple(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.mem_antidiagonalTuple
    # x ∈ antidiagonalTuple k n ↔ ∑ i, x i = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: List_Nat_mem_antidiagonalTuple"))
        except Exception:
            pass
    return results


def _r0002_toFinset_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_coe
    # (l : Multiset α).toFinset = l.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_colon_Multiset_a_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_toFinset")
            results.append((rhs, "Mathlib: List_toFinset_coe"))
    except Exception:
        pass
    return results


def _r0003_toFinset_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_eq
    # @Finset.mk α l n = l.toFinset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_Finset_mk", 3)
    if args is not None:
        try:
            rhs = OVar("l_toFinset")
            results.append((rhs, "Mathlib: List_toFinset_eq"))
        except Exception:
            pass
    return results


def _r0004_coe_toFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.coe_toFinset
    # (l.toFinset : Set α) = { a | a ∈ l }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toFinset", 3)
    if args is not None:
        try:
            rhs = OVar("a_pipe_a_in_l")
            results.append((rhs, "Mathlib: List_coe_toFinset"))
        except Exception:
            pass
    return results


def _r0005_toFinset_replicate_of_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_replicate_of_ne_zero
    # (List.replicate n a).toFinset = {a}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("List_replicate_n_a_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: List_toFinset_replicate_of_ne_zero"))
    except Exception:
        pass
    return results


def _r0006_singleton_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.singleton_injective
    # Injective fun a : α => [a]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 4)
    if args is not None:
        try:
            rhs = OOp("gt", (OSeq((args[3],)),))
            results.append((rhs, "Mathlib: List_singleton_injective"))
        except Exception:
            pass
    return results


def _r0007_length_eq_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_eq_two
    # l.length = 2 ↔ ∃ a b, l = [a, b]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(2), OOp("exists", (OVar("a"), OVar("b"), OVar("l"),)))), OVar("a_b")))
            results.append((rhs, "Mathlib: List_length_eq_two"))
    except Exception:
        pass
    return results


def _r0008_head_eq_getElem_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.head_eq_getElem_zero
    # l.head hl = l[0]'(length_pos_iff.2 hl)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_head", 1)
    if args is not None:
        try:
            rhs = OVar("l_0_prime_length_pos_iff_2_hl")
            results.append((rhs, "Mathlib: List_head_eq_getElem_zero"))
        except Exception:
            pass
    return results


def _r0009_antisymm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Sublist.antisymm
    # l₁ = l₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_2")
            results.append((rhs, "Mathlib: List_Sublist_antisymm"))
    except Exception:
        pass
    return results


def _r0010_idxOf_eq_length_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_eq_length_iff
    # idxOf a l = length l ↔ a ∉ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "idxOf", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("len", (args[1],)), OOp("not_in", (args[0], args[1]))))
            results.append((rhs, "Mathlib: List_idxOf_eq_length_iff"))
        except Exception:
            pass
    return results


def _r0011_destutter_pair(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.destutter_pair
    # destutter R [a, b] = if R a b then [a, b] else [a]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "destutter", 2)
    if args is not None:
        try:
            rhs = OOp("if", (args[0], OVar("a"), OVar("b"), OVar("then"), args[1], OVar("else"), OSeq((OVar("a"),)),))
            results.append((rhs, "Mathlib: List_destutter_pair"))
        except Exception:
            pass
    return results


def _r0012_rdropWhile_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdropWhile_eq_self_iff
    # rdropWhile p l = l ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdropWhile", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (args[1], OOp("forall", (OVar("hl"), OVar("colon"), args[1],)))), OOp("_unknown", (OOp("not", (args[0],)), OOp("l_getLast", (OVar("hl"),)),))))
            results.append((rhs, "Mathlib: List_rdropWhile_eq_self_iff"))
        except Exception:
            pass
    return results


def _r0013_rtakeWhile_eq_nil_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtakeWhile_eq_nil_iff
    # rtakeWhile p l = [] ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rtakeWhile", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OSeq(()), OOp("forall", (OVar("hl"), OVar("colon"), args[1],)))), OOp("_unknown", (OOp("not", (args[0],)), OOp("l_getLast", (OVar("hl"),)),))))
            results.append((rhs, "Mathlib: List_rtakeWhile_eq_nil_iff"))
        except Exception:
            pass
    return results


def _r0014_idxOf_finRange(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_finRange
    # (finRange k).idxOf i = i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finRange_k_idxOf", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: List_idxOf_finRange"))
        except Exception:
            pass
    return results


def _r0015_forall_2_nil_right_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_nil_right_iff
    # Forall₂ R l nil ↔ l = nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("nil")
            results.append((rhs, "Mathlib: List_forall_2_nil_right_iff"))
        except Exception:
            pass
    return results


def _r0016_forall_2_cons_left_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_cons_left_iff
    # Forall₂ R (a :: l) u ↔ ∃ b u', R a b ∧ Forall₂ R l u' ∧ u = b :: u'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("b", (OVar("colon_colon"), OVar("u_prime"),))
            results.append((rhs, "Mathlib: List_forall_2_cons_left_iff"))
        except Exception:
            pass
    return results


def _r0017_mem_offDiag_iff_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_offDiag_iff_getElem
    # x ∈ l.offDiag ↔ ∃ (i : ℕ) (_ : i < l.length) (j : ℕ) (_ : j < l.length),       i ≠ j ∧ l[i] = x.1 ∧ l[j] = x.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OVar("x_1"), OVar("l_j"))), OVar("x_2")))
            results.append((rhs, "Mathlib: List_mem_offDiag_iff_getElem"))
        except Exception:
            pass
    return results


def _r0018_rotate_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_zero
    # l.rotate 0 = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_rotate_zero"))
        except Exception:
            pass
    return results


def _r0019_rotate_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_replicate
    # (replicate n a).rotate k = replicate n a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicate_n_a_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("replicate", (OVar("n"), OVar("a"),))
            results.append((rhs, "Mathlib: List_rotate_replicate"))
        except Exception:
            pass
    return results


def _r0020_rotate_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_length
    # rotate l l.length = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rotate", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: List_rotate_length"))
        except Exception:
            pass
    return results


def _r0021_rotate_length_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_length_mul
    # l.rotate (l.length * n) = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_rotate_length_mul"))
        except Exception:
            pass
    return results


def _r0022_rotate_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_eq_iff
    # l.rotate n = l' ↔ l = l'.rotate (l'.length - n % l'.length)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("l_prime"), OVar("l"))), OOp("l_prime_rotate", (OOp("-", (OVar("l_prime_length"), OOp("n", (OVar("_unknown"), OVar("l_prime_length"),)))),))))
            results.append((rhs, "Mathlib: List_rotate_eq_iff"))
        except Exception:
            pass
    return results


def _r0023_reverse_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reverse_rotate
    # (l.rotate n).reverse = l.reverse.rotate (l.length - n % l.length)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_rotate_n_reverse")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_reverse_rotate", (OOp("-", (OVar("l_length"), OOp("n", (OVar("_unknown"), OVar("l_length"),)))),))
            results.append((rhs, "Mathlib: List_reverse_rotate"))
    except Exception:
        pass
    return results


def _r0024_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsRotated.trans
    # ∀ {l l' l'' : List α}, l ~r l' → l' ~r l'' → l ~r l''   | _, _, _, ⟨n, rfl⟩, ⟨m, rfl⟩ => ⟨n + m,
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 8)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("n_plus_m"),))
            results.append((rhs, "Mathlib: List_IsRotated_trans"))
        except Exception:
            pass
    return results


def _r0025_isRotated_iff_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isRotated_iff_mod
    # l ~r l' ↔ ∃ n ≤ l.length, l.rotate n = l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("l_prime")
            results.append((rhs, "Mathlib: List_isRotated_iff_mod"))
        except Exception:
            pass
    return results


def _r0026_getElem_cyclicPermutations(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getElem_cyclicPermutations
    # (cyclicPermutations l)[n] = l.rotate n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cyclicPermutations_l_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_rotate", (OVar("n"),))
            results.append((rhs, "Mathlib: List_getElem_cyclicPermutations"))
    except Exception:
        pass
    return results


def _r0027_length_insertionSort(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_insertionSort
    # (insertionSort r l).length = l.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("insertionSort_r_l_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_length")
            results.append((rhs, "Mathlib: List_length_insertionSort"))
    except Exception:
        pass
    return results


def _r0028_splitLengths_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitLengths_nil
    # [].splitLengths l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "splitLengths", 1)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_splitLengths_nil"))
        except Exception:
            pass
    return results


def _r0029_take_self_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.take_self_eq_iff
    # x = x.take n ↔ x.length ≤ n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("iff", (OOp("x_take", (OVar("n"),)), OVar("x_length"))), OVar("n")))
            results.append((rhs, "Mathlib: List_take_self_eq_iff"))
    except Exception:
        pass
    return results


def _r0030_take_eq_left_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.take_eq_left_iff
    # (x ++ y).take n = x.take n ↔ y = [] ∨ n ≤ x.length
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_plus_plus_y_take", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("x_take", (args[0],)), OVar("y"))), OOp("<=", (OOp("or", (OSeq(()), args[0])), OVar("x_length")))))
            results.append((rhs, "Mathlib: List_take_eq_left_iff"))
        except Exception:
            pass
    return results


def _r0031_left_eq_take_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.left_eq_take_iff
    # x.take n = (x ++ y).take n ↔ y = [] ∨ n ≤ x.length
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_take", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("x_plus_plus_y_take", (args[0],)), OVar("y"))), OOp("<=", (OOp("or", (OSeq(()), args[0])), OVar("x_length")))))
            results.append((rhs, "Mathlib: List_left_eq_take_iff"))
        except Exception:
            pass
    return results


def _r0032_toFinsupp_support(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_support
    # l.toFinsupp.support = {i ∈ Finset.range l.length | getD l i 0 ≠ 0}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_toFinsupp_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("i_in_Finset_range_l_length_pipe_getD_l_i_0_ne_0")
            results.append((rhs, "Mathlib: List_toFinsupp_support"))
    except Exception:
        pass
    return results


def _r0033_snd_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.TProd.snd_mk
    # (TProd.mk.{u, v} (i :: l) f).2 = TProd.mk.{u, v} l f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("TProd_mk_u_v_i_colon_colon_l_f_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("TProd_mk_u_v", (OVar("l"), OVar("f"),))
            results.append((rhs, "Mathlib: List_TProd_snd_mk"))
    except Exception:
        pass
    return results


def _r0034_mk_elim(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.TProd.mk_elim
    # TProd.mk l (v.elim' h) = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OVar("v")
            results.append((rhs, "Mathlib: List_TProd_mk_elim"))
        except Exception:
            pass
    return results


def _r0035_of_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.of_toList
    # ∀ l : Lists' α true, ofList (toList l) = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: Lists_of_toList"))
        except Exception:
            pass
    return results


def _r0036_prod_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_ofFn
    # (ofFn f).prod = ∏ i, f i
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofFn_f_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("f"), OVar("i"),))
            results.append((rhs, "Mathlib: List_prod_ofFn"))
    except Exception:
        pass
    return results


def _r0037_prod_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_eq_one
    # l.prod = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: List_prod_eq_one"))
    except Exception:
        pass
    return results


def _r0038_prod_erase_of_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_erase_of_comm
    # a * (l.erase a).prod = l.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("l_prod")
            results.append((rhs, "Mathlib: List_prod_erase_of_comm"))
        except Exception:
            pass
    return results


def _r0039_prod_insertIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_insertIdx
    # (l.insertIdx i a).prod = a * l.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_insertIdx_i_a_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("a"), OVar("l_prod")))
            results.append((rhs, "Mathlib: List_prod_insertIdx"))
    except Exception:
        pass
    return results


def _r0040_mul_prod_eraseIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mul_prod_eraseIdx
    # l[i] * (l.eraseIdx i).prod = l.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("l_prod")
            results.append((rhs, "Mathlib: List_mul_prod_eraseIdx"))
        except Exception:
            pass
    return results


def _r0041_prod_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_zpow
    # l.prod ^ r = (map (fun x ↦ x ^ r) l).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("map_fun_x_x_pow_r_l_prod")
            results.append((rhs, "Mathlib: List_prod_zpow"))
        except Exception:
            pass
    return results


def _r0042_take_sum_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.take_sum_flatten
    # L.flatten.take ((L.map length).take i).sum = (L.take i).flatten
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_flatten_take", 1)
    if args is not None:
        try:
            rhs = OVar("L_take_i_flatten")
            results.append((rhs, "Mathlib: List_take_sum_flatten"))
        except Exception:
            pass
    return results


def _r0043_prod_isUnit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_isUnit
    # ∀ {L : List M}, (∀ m ∈ L, IsUnit m) → IsUnit L.prod   | [], _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsUnit", 4)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_prod_isUnit"))
        except Exception:
            pass
    return results


def _r0044_length_sigma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_sigma
    # length (l₁.sigma l₂) = (l₁.map fun a ↦ length (l₂ a)).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OVar("l_1_map_fun_a_length_l_2_a_sum")
            results.append((rhs, "Mathlib: List_length_sigma"))
        except Exception:
            pass
    return results


def _r0045_ranges_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ranges_flatten
    # ∀ (l : List ℕ), l.ranges.flatten = range l.sum   | [] => rfl   | a :: l =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_ranges_flatten")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("range", (OVar("l_sum"), OVar("pipe"), OSeq(()), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a"), OVar("colon_colon"), OVar("l"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_ranges_flatten"))
    except Exception:
        pass
    return results


def _r0046_drop_take_succ_flatten_eq_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.drop_take_succ_flatten_eq_getElem
    # (L.flatten.take ((L.map length).take (i + 1)).sum).drop ((L.map length).take i).sum = L[i]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_flatten_take_L_map_length_take_i_plus_1_sum_drop", 1)
    if args is not None:
        try:
            rhs = OVar("L_i")
            results.append((rhs, "Mathlib: List_drop_take_succ_flatten_eq_getElem"))
        except Exception:
            pass
    return results


def _r0047_alternatingProd_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.alternatingProd_append
    # ∀ l₁ l₂ : List G,       alternatingProd (l₁ ++ l₂) = alternatingProd l₁ * alternatingProd l₂ ^ (-1 : ℤ) ^ length l₁   | 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "alternatingProd", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("alternatingProd", (OVar("l_1"),)), OOp("**", (OOp("alternatingProd", (OVar("l_2"),)), OOp("**", (OOp("minus_1", (OVar("colon"), OVar("_unknown"),)), OOp("len", (OVar("l_1"), OVar("pipe"), OVar("_unknown"), OVar("l_2"), OVar("eq_gt"),))))))))
            results.append((rhs, "Mathlib: List_alternatingProd_append"))
        except Exception:
            pass
    return results


def _r0048_alternatingProd_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.alternatingProd_reverse
    # ∀ l : List G, alternatingProd (reverse l) = alternatingProd l ^ (-1 : ℤ) ^ (length l + 1)   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "alternatingProd", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("alternatingProd", (OVar("l"),)), OOp("**", (OOp("minus_1", (OVar("colon"), OVar("_unknown"),)), OOp("length_l_plus_1", (OVar("pipe"), OSeq(()), OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: List_alternatingProd_reverse"))
        except Exception:
            pass
    return results


def _r0049_smul_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.smul_prod
    # m ^ l.length • l.prod = (l.map (m • ·)).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("l_map_m_prod")
            results.append((rhs, "Mathlib: List_smul_prod"))
        except Exception:
            pass
    return results


def _r0050_prod_map_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_map_neg
    # (l.map Neg.neg).prod = (-1) ^ l.length * l.prod
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_map_Neg_neg_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("l_length"))), OVar("l_prod")))
            results.append((rhs, "Mathlib: List_prod_map_neg"))
    except Exception:
        pass
    return results


def _r0051_dProdIndex_eq_map_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dProdIndex_eq_map_sum
    # l.dProdIndex fι = (l.map fι).sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_dProdIndex", 1)
    if args is not None:
        try:
            rhs = OVar("l_map_fi_sum")
            results.append((rhs, "Mathlib: List_dProdIndex_eq_map_sum"))
        except Exception:
            pass
    return results


def _r0052_dProd_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dProd_nil
    # (List.nil : List α).dProd fι fA = GradedMonoid.GOne.one
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_nil_colon_List_a_dProd", 2)
    if args is not None:
        try:
            rhs = OVar("GradedMonoid_GOne_one")
            results.append((rhs, "Mathlib: List_dProd_nil"))
        except Exception:
            pass
    return results


def _r0053_dProd_monoid(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dProd_monoid
    # @List.dProd _ _ (fun _ : ι => R) _ _ l fι fA = (l.map fA).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_List_dProd", 8)
    if args is not None:
        try:
            rhs = OVar("l_map_fA_prod")
            results.append((rhs, "Mathlib: List_dProd_monoid"))
        except Exception:
            pass
    return results


def _r0054_trop_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.trop_sum
    # trop l.sum = List.prod (l.map trop)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trop", 1)
    if args is not None:
        try:
            rhs = OOp("prod", (OOp("l_map", (OVar("trop"),)),))
            results.append((rhs, "Mathlib: List_trop_sum"))
        except Exception:
            pass
    return results


def _r0055_untrop_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.untrop_prod
    # untrop l.prod = List.sum (l.map untrop)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "untrop", 1)
    if args is not None:
        try:
            rhs = OOp("sum", (OOp("l_map", (OVar("untrop"),)),))
            results.append((rhs, "Mathlib: List_untrop_prod"))
        except Exception:
            pass
    return results


def _r0056_length_splitWrtCompositionAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_splitWrtCompositionAux
    # length (l.splitWrtCompositionAux ns) = ns.length
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OVar("ns_length")
            results.append((rhs, "Mathlib: List_length_splitWrtCompositionAux"))
        except Exception:
            pass
    return results


def _r0057_length_splitWrtComposition(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_splitWrtComposition
    # length (l.splitWrtComposition c) = c.length
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OVar("c_length")
            results.append((rhs, "Mathlib: List_length_splitWrtComposition"))
        except Exception:
            pass
    return results


def _r0058_map_length_splitWrtCompositionAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_length_splitWrtCompositionAux
    # ∀ {l : List α}, ns.sum ≤ l.length → map length (l.splitWrtCompositionAux ns) = ns
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OVar("ns")
            results.append((rhs, "Mathlib: List_map_length_splitWrtCompositionAux"))
        except Exception:
            pass
    return results


def _r0059_map_length_splitWrtComposition(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_length_splitWrtComposition
    # map length (l.splitWrtComposition c) = c.blocks
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OVar("c_blocks")
            results.append((rhs, "Mathlib: List_map_length_splitWrtComposition"))
        except Exception:
            pass
    return results


def _r0060_sum_take_map_length_splitWrtComposition(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sum_take_map_length_splitWrtComposition
    # (((l.splitWrtComposition c).map length).take i).sum = c.sizeUpTo i
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_splitWrtComposition_c_map_length_take_i_sum")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("c_sizeUpTo", (OVar("i"),))
            results.append((rhs, "Mathlib: List_sum_take_map_length_splitWrtComposition"))
    except Exception:
        pass
    return results


def _r0061_flatten_splitWrtCompositionAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.flatten_splitWrtCompositionAux
    # ∀ {l : List α}, ns.sum = l.length → (l.splitWrtCompositionAux ns).flatten = l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_splitWrtCompositionAux_ns_flatten")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_flatten_splitWrtCompositionAux"))
    except Exception:
        pass
    return results


def _r0062_flatten_splitWrtComposition(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.flatten_splitWrtComposition
    # (l.splitWrtComposition c).flatten = l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_splitWrtComposition_c_flatten")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_flatten_splitWrtComposition"))
    except Exception:
        pass
    return results


def _r0063_splitWrtComposition_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitWrtComposition_flatten
    # splitWrtComposition (flatten L) c = L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "splitWrtComposition", 2)
    if args is not None:
        try:
            rhs = OVar("L")
            results.append((rhs, "Mathlib: List_splitWrtComposition_flatten"))
        except Exception:
            pass
    return results


def _r0064_id_traverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.id_traverse
    # (List.traverse pure xs : Id _) = pure xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_traverse", 5)
    if args is not None:
        try:
            rhs = OOp("pure", (args[1],))
            results.append((rhs, "Mathlib: List_id_traverse"))
        except Exception:
            pass
    return results


def _r0065_comp_traverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.comp_traverse
    # List.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =     Comp.mk (List.traverse f <$> List.traverse g x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_traverse", 2)
    if args is not None:
        try:
            rhs = OOp("Comp_mk", (OOp("List_traverse", (OVar("f"), OVar("lt_gt"), OVar("List_traverse"), OVar("g"), args[1],)),))
            results.append((rhs, "Mathlib: List_comp_traverse"))
        except Exception:
            pass
    return results


def _r0066_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.naturality
    # η (List.traverse f x) = List.traverse (@η _ ∘ f) x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eta", 1)
    if args is not None:
        try:
            rhs = OOp("List_traverse", (OOp("comp", (OOp("at_eta", (OVar("_unknown"),)), OVar("f"))), OVar("x"),))
            results.append((rhs, "Mathlib: List_naturality"))
        except Exception:
            pass
    return results


def _r0067_antidiagonalTuple_zero_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.antidiagonalTuple_zero_zero
    # antidiagonalTuple 0 0 = [![]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OSeq((OOp("not", (OSeq(()),)),))
            results.append((rhs, "Mathlib: List_Nat_antidiagonalTuple_zero_zero"))
        except Exception:
            pass
    return results


def _r0068_antidiagonalTuple_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.antidiagonalTuple_one
    # antidiagonalTuple 1 n = [![n]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OSeq((OOp("not", (OSeq((args[1],)),)),))
            results.append((rhs, "Mathlib: List_Nat_antidiagonalTuple_one"))
        except Exception:
            pass
    return results


def _r0069_toFinset_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_union
    # (l ∪ l').toFinset = l.toFinset ∪ l'.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_union_l_prime_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("l_toFinset"), OVar("l_prime_toFinset")))
            results.append((rhs, "Mathlib: List_toFinset_union"))
    except Exception:
        pass
    return results


def _r0070_toFinset_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_inter
    # (l ∩ l').toFinset = l.toFinset ∩ l'.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_inter_l_prime_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OVar("l_toFinset"), OVar("l_prime_toFinset")))
            results.append((rhs, "Mathlib: List_toFinset_inter"))
    except Exception:
        pass
    return results


def _r0071_toFinset_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_val
    # l.toFinset.1 = (l.dedup : Multiset α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_toFinset_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_dedup", (OVar("colon"), OVar("Multiset"), OVar("a"),))
            results.append((rhs, "Mathlib: List_toFinset_val"))
    except Exception:
        pass
    return results


def _r0072_ext_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset.ext_iff
    # a.toFinset = b.toFinset ↔ ∀ x, x ∈ a ↔ x ∈ b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("b_toFinset"), OOp("iff", (OOp("in", (OOp("forall", (OVar("x"), OVar("x"),)), OVar("a"))), OOp("in", (OVar("x"), OVar("b")))))))
            results.append((rhs, "Mathlib: List_toFinset_ext_iff"))
    except Exception:
        pass
    return results


def _r0073_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset.ext
    # (∀ x, x ∈ l ↔ x ∈ l') → l.toFinset = l'.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_prime_toFinset")
            results.append((rhs, "Mathlib: List_toFinset_ext"))
    except Exception:
        pass
    return results


def _r0074_toFinset_finRange(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_finRange
    # (List.finRange n).toFinset = Finset.univ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("List_finRange_n_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Finset_univ")
            results.append((rhs, "Mathlib: List_toFinset_finRange"))
    except Exception:
        pass
    return results


def _r0075_eq_or_ne_mem_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Decidable.List.eq_or_ne_mem_of_mem
    # a = b ∨ a ≠ b ∧ a ∈ l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("!=", (OOp("or", (OVar("b"), OVar("a"))), OOp("and", (OVar("b"), OOp("in", (OVar("a"), OVar("l")))))))
            results.append((rhs, "Mathlib: Decidable_List_eq_or_ne_mem_of_mem"))
    except Exception:
        pass
    return results


def _r0076_exists_of_length_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_of_length_succ
    # ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t   | [], H => absurd H.symm <| succ_ne_zero n   | h :: t, _ => ⟨h, t, 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("h", (OVar("colon_colon"), args[1], OVar("pipe"), OVar("_unknown"), OVar("H"), OVar("eq_gt"), OVar("absurd"), OVar("H_symm"), OVar("lt_pipe"), OVar("succ_ne_zero"), OVar("n"), OVar("pipe"), args[0], OVar("colon_colon"), args[1], OVar("_unknown"), OVar("eq_gt"), OVar("h_t_rfl_at_simp"), OVar("lemma"), OVar("length_injective_iff"), OVar("colon"), OVar("Injective"), OOp("implies", (OOp("len", (OVar("colon"), OVar("List"), OVar("a"),)), OVar("_unknown"))),)), OOp("Subsingleton", (OVar("a"),))))
            results.append((rhs, "Mathlib: List_exists_of_length_succ"))
        except Exception:
            pass
    return results


def _r0077_length_eq_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_eq_three
    # l.length = 3 ↔ ∃ a b c, l = [a, b, c]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(3), OOp("exists", (OVar("a"), OVar("b"), OVar("c"), OVar("l"),)))), OVar("a_b_c")))
            results.append((rhs, "Mathlib: List_length_eq_three"))
    except Exception:
        pass
    return results


def _r0078_length_eq_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_eq_four
    # l.length = 4 ↔ ∃ a b c d, l = [a, b, c, d]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(4), OOp("exists", (OVar("a"), OVar("b"), OVar("c"), OVar("d"), OVar("l"),)))), OVar("a_b_c_d")))
            results.append((rhs, "Mathlib: List_length_eq_four"))
    except Exception:
        pass
    return results


def _r0079_insert_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.insert_neg
    # Insert.insert x l = x :: l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Insert_insert", 2)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("colon_colon"), args[1],))
            results.append((rhs, "Mathlib: List_insert_neg"))
        except Exception:
            pass
    return results


def _r0080_insert_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.insert_pos
    # Insert.insert x l = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Insert_insert", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: List_insert_pos"))
        except Exception:
            pass
    return results


def _r0081_doubleton_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.doubleton_eq
    # ({x, y} : List α) = [x, y]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_y", 3)
    if args is not None:
        try:
            rhs = OVar("x_y")
            results.append((rhs, "Mathlib: List_doubleton_eq"))
        except Exception:
            pass
    return results


def _r0082_eq_replicate_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.eq_replicate_length
    # ∀ {l : List α}, l = replicate l.length a ↔ ∀ b ∈ l, b = a   | [] =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("replicate", (OVar("l_length"), OVar("a"),)), OOp("in", (OOp("forall", (OVar("b"),)), OOp("l", (OVar("b"),)))))), OOp("a", (OVar("pipe"), OSeq(()), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_eq_replicate_length"))
    except Exception:
        pass
    return results


def _r0083_replicate_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.replicate_add
    # replicate (m + n) a = replicate m a ++ replicate n a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicate", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("replicate", (OVar("m"), args[1],)), OOp("replicate", (OVar("n"), args[1],))))
            results.append((rhs, "Mathlib: List_replicate_add"))
        except Exception:
            pass
    return results


def _r0084_replicate_right_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.replicate_right_inj
    # replicate n a = replicate n b ↔ a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicate", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("replicate", (args[0], OVar("b"),)), args[1])), OVar("b")))
            results.append((rhs, "Mathlib: List_replicate_right_inj"))
        except Exception:
            pass
    return results


def _r0085_replicate_left_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.replicate_left_inj
    # replicate n a = replicate m a ↔ n = m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicate", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("replicate", (OVar("m"), args[1],)), args[0])), OVar("m")))
            results.append((rhs, "Mathlib: List_replicate_left_inj"))
        except Exception:
            pass
    return results


def _r0086_getLast_replicate_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getLast_replicate_succ
    # (replicate (m + 1) a).getLast (ne_nil_of_length_eq_add_one length_replicate) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicate_m_plus_1_a_getLast", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: List_getLast_replicate_succ"))
        except Exception:
            pass
    return results


def _r0087_idxOf_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_of_notMem
    # a ∉ l → idxOf a l = length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "idxOf", 2)
    if args is not None:
        try:
            rhs = OOp("len", (args[1],))
            results.append((rhs, "Mathlib: List_idxOf_of_notMem"))
        except Exception:
            pass
    return results


def _r0088_idxOf_append_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_append_of_notMem
    # idxOf a (l₁ ++ l₂) = l₁.length + idxOf a l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "idxOf", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("l_1_length"), OOp("idxOf", (args[0], OVar("l_2"),))))
            results.append((rhs, "Mathlib: List_idxOf_append_of_notMem"))
        except Exception:
            pass
    return results


def _r0089_idxOf_eq_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsPrefix.idxOf_eq_of_mem
    # l₁.idxOf a = l₂.idxOf a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_1_idxOf", 1)
    if args is not None:
        try:
            rhs = OOp("l_2_idxOf", (args[0],))
            results.append((rhs, "Mathlib: List_IsPrefix_idxOf_eq_of_mem"))
        except Exception:
            pass
    return results


def _r0090_idxOf_getLast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_getLast
    # l.idxOf (l.getLast hl) = l.length - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_idxOf", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("l_length"), OLit(1)))
            results.append((rhs, "Mathlib: List_idxOf_getLast"))
        except Exception:
            pass
    return results


def _r0091_isChain_cons_iff_forall_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons_iff_forall₂
    # IsChain R (a :: l) ↔ l = [] ∨ Forall₂ R (a :: dropLast l) l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OSeq(()), OOp("Forall_2", (OVar("R"), OOp("a", (OVar("colon_colon"), OVar("dropLast"), args[1],)), args[1],))))
            results.append((rhs, "Mathlib: List_isChain_cons_iff_forall_2"))
        except Exception:
            pass
    return results


def _r0092_iterate_eq_of_apply_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.iterate_eq_of_apply_eq
    # f^[i] l[0] = l[i]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpow_i", 1)
    if args is not None:
        try:
            rhs = OVar("l_i")
            results.append((rhs, "Mathlib: List_IsChain_iterate_eq_of_apply_eq"))
        except Exception:
            pass
    return results


def _r0093_isChain_eq_iff_eq_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_eq_iff_eq_replicate
    # IsChain (· = ·) l ↔ ∀ a ∈ l.head?, l = replicate l.length a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("replicate", (OVar("l_length"), OVar("a"),))
            results.append((rhs, "Mathlib: List_isChain_eq_iff_eq_replicate"))
        except Exception:
            pass
    return results


def _r0094_isChain_cons_eq_iff_eq_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons_eq_iff_eq_replicate
    # IsChain (· = ·) (a :: l) ↔ l = replicate l.length a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("replicate", (OVar("l_length"), OVar("a"),))
            results.append((rhs, "Mathlib: List_isChain_cons_eq_iff_eq_replicate"))
        except Exception:
            pass
    return results


def _r0095_countP_lt_length_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.countP_lt_length_iff
    # l.countP p < l.length ↔ ∃ a ∈ l, p a = false
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OLit(False)
            results.append((rhs, "Mathlib: List_countP_lt_length_iff"))
        except Exception:
            pass
    return results


def _r0096_nextOr_eq_getElem_idxOf_succ_of_mem_drop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nextOr_eq_getElem_idxOf_succ_of_mem_dropLast
    # l.nextOr a d = l[l.idxOf a + 1]'(succ_idxOf_lt_length_of_mem_dropLast ha)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 2)
    if args is not None:
        try:
            rhs = OVar("l_l_idxOf_a_plus_1_prime_succ_idxOf_lt_length_of_mem_dropLast_ha")
            results.append((rhs, "Mathlib: List_nextOr_eq_getElem_idxOf_succ_of_mem_dropLast"))
        except Exception:
            pass
    return results


def _r0097_nextOr_getLast_of_notMem_dropLast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nextOr_getLast_of_notMem_dropLast
    # l.nextOr (l.getLast hl) d = d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: List_nextOr_getLast_of_notMem_dropLast"))
        except Exception:
            pass
    return results


def _r0098_next_eq_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_eq_getElem
    # l.next a ha = l[(l.idxOf a + 1) % l.length]'(Nat.mod_lt _ <| by grind)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_next", 2)
    if args is not None:
        try:
            rhs = OVar("l_l_idxOf_a_plus_1_l_length_prime_Nat_mod_lt_lt_pipe_by_grind")
            results.append((rhs, "Mathlib: List_next_eq_getElem"))
        except Exception:
            pass
    return results


def _r0099_next_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_getElem
    # l.next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt _ (i.zero_le.trans_lt hi))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_next", 2)
    if args is not None:
        try:
            rhs = OVar("l_i_plus_1_l_length_prime_Nat_mod_lt_i_zero_le_trans_lt_hi")
            results.append((rhs, "Mathlib: List_next_getElem"))
        except Exception:
            pass
    return results


def _r0100_prev_eq_getElem_idxOf_pred_of_ne_head(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_eq_getElem_idxOf_pred_of_ne_head
    # l.prev a ha = l[l.idxOf a - 1]'(by grind [idxOf_lt_length_of_mem])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_prev", 2)
    if args is not None:
        try:
            rhs = OVar("l_l_idxOf_a_minus_1_prime_by_grind_idxOf_lt_length_of_mem")
            results.append((rhs, "Mathlib: List_prev_eq_getElem_idxOf_pred_of_ne_head"))
        except Exception:
            pass
    return results


def _r0101_prev_eq_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_eq_getElem
    # l.prev a ha = l[(l.idxOf a + (l.length - 1)) % l.length]'(Nat.mod_lt _ <| by grind)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_prev", 2)
    if args is not None:
        try:
            rhs = OVar("l_l_idxOf_a_plus_l_length_minus_1_l_length_prime_Nat_mod_lt_lt_pipe_by_grind")
            results.append((rhs, "Mathlib: List_prev_eq_getElem"))
        except Exception:
            pass
    return results


def _r0102_prev_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_getElem
    # l.prev l[i] (get_mem ..) = l[(i + (l.length - 1)) % l.length]'(Nat.mod_lt _ (by lia))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_prev", 2)
    if args is not None:
        try:
            rhs = OVar("l_i_plus_l_length_minus_1_l_length_prime_Nat_mod_lt_by_lia")
            results.append((rhs, "Mathlib: List_prev_getElem"))
        except Exception:
            pass
    return results


def _r0103_pmap_prev_eq_rotate_length_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.pmap_prev_eq_rotate_length_sub_one
    # (l.pmap l.prev fun _ h => h) = l.rotate (l.length - 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_pmap", 6)
    if args is not None:
        try:
            rhs = OOp("l_rotate", (OOp("-", (OVar("l_length"), OLit(1))),))
            results.append((rhs, "Mathlib: List_pmap_prev_eq_rotate_length_sub_one"))
        except Exception:
            pass
    return results


def _r0104_dedup_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_eq_self
    # dedup l = l ↔ Nodup l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (args[0], OOp("nodup", (args[0],))))
            results.append((rhs, "Mathlib: List_dedup_eq_self"))
        except Exception:
            pass
    return results


def _r0105_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.dedup
    # l.dedup = l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_dedup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_Nodup_dedup"))
    except Exception:
        pass
    return results


def _r0106_dedup_idem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_idem
    # dedup (dedup l) = dedup l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("dedup", (OVar("l"),))
            results.append((rhs, "Mathlib: List_dedup_idem"))
        except Exception:
            pass
    return results


def _r0107_union_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Disjoint.union_eq
    # xs ∪ ys = xs.dedup ++ ys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("xs_dedup"), args[1]))
            results.append((rhs, "Mathlib: List_Disjoint_union_eq"))
        except Exception:
            pass
    return results


def _r0108_replicate_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.replicate_dedup
    # ∀ {k}, k ≠ 0 → (replicate k x).dedup = [x]   | 0, h => (h rfl).elim   | 1, _ => rfl   | n + 2, _ =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("replicate_k_x_dedup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OOp("x", (OVar("pipe"), OVar("_0"), OVar("h"), OVar("eq_gt"), OVar("h_rfl_elim"), OVar("pipe"), OVar("_1"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("n"),)), OOp("_2", (OVar("_unknown"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_replicate_dedup"))
    except Exception:
        pass
    return results


def _r0109_destutter_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.destutter_eq_self_iff
    # ∀ l : List α, l.destutter R = l ↔ l.IsChain R   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_destutter", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("l"), OOp("l_IsChain", (args[0], OVar("pipe"), OSeq(()), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_destutter_eq_self_iff"))
        except Exception:
            pass
    return results


def _r0110_destutter_idem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.destutter_idem
    # (l.destutter R).destutter R = l.destutter R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_destutter_R_destutter", 1)
    if args is not None:
        try:
            rhs = OOp("l_destutter", (args[0],))
            results.append((rhs, "Mathlib: List_destutter_idem"))
        except Exception:
            pass
    return results


def _r0111_length_destutter_le_length_destutter_con(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_destutter_le_length_destutter_cons
    # ∀ {l : List α}, (l.destutter R).length ≤ ((a :: l).destutter R).length   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_length_destutter_le_length_destutter_cons"))
        except Exception:
            pass
    return results


def _r0112_length_le_length_destutter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.length_le_length_destutter
    # ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → l₁.IsChain R → l₁.length ≤ (l₂.destutter R).length      | [], [], _, _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_IsChain_length_le_length_destutter"))
        except Exception:
            pass
    return results


def _r0113_destutter_eq_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Pairwise.destutter_eq_dedup
    # ∀ {l : List α}, l.Pairwise r → l.destutter (· ≠ ·) = l.dedup   | [], h =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_destutter", 1)
    if args is not None:
        try:
            rhs = OOp("l_dedup", (OVar("pipe"), OVar("_unknown"), OVar("h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_Pairwise_destutter_eq_dedup"))
        except Exception:
            pass
    return results


def _r0114_rdrop_append_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdrop_append_length
    # List.rdrop (l₁ ++ l₂) (List.length l₂) = l₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_rdrop", 2)
    if args is not None:
        try:
            rhs = OVar("l_1")
            results.append((rhs, "Mathlib: List_rdrop_append_length"))
        except Exception:
            pass
    return results


def _r0115_rdrop_append_of_le_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdrop_append_of_le_length
    # k ≤ length l₂ → List.rdrop (l₁ ++ l₂) k = l₁ ++ List.rdrop l₂ k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_rdrop", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("l_1"), OOp("List_rdrop", (OVar("l_2"), args[1],))))
            results.append((rhs, "Mathlib: List_rdrop_append_of_le_length"))
        except Exception:
            pass
    return results


def _r0116_rdrop_append_length_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdrop_append_length_add
    # List.rdrop (l₁ ++ l₂) (length l₂ + k) = List.rdrop l₁ k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_rdrop", 2)
    if args is not None:
        try:
            rhs = OOp("List_rdrop", (OVar("l_1"), OVar("k"),))
            results.append((rhs, "Mathlib: List_rdrop_append_length_add"))
        except Exception:
            pass
    return results


def _r0117_ofFn_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_id
    # ofFn id = finRange n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn", 1)
    if args is not None:
        try:
            rhs = OOp("finRange", (OVar("n"),))
            results.append((rhs, "Mathlib: List_ofFn_id"))
        except Exception:
            pass
    return results


def _r0118_forall_2_same(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_same
    # ∀ {l : List α}, Forall₂ Rₐ l l ↔ ∀ x ∈ l, Rₐ x x   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_forall_2_same"))
        except Exception:
            pass
    return results


def _r0119_forall_2_nil_left_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_nil_left_iff
    # Forall₂ R nil l ↔ l = nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("nil")
            results.append((rhs, "Mathlib: List_forall_2_nil_left_iff"))
        except Exception:
            pass
    return results


def _r0120_forall_2_cons_right_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_cons_right_iff
    # Forall₂ R u (b :: l) ↔ ∃ a u', R a b ∧ Forall₂ R u' l ∧ u = a :: u'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("u_prime"),))
            results.append((rhs, "Mathlib: List_forall_2_cons_right_iff"))
        except Exception:
            pass
    return results


def _r0121_forall_2_and_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_and_left
    # ∀ l u, Forall₂ (fun a b => p a ∧ R a b) l u ↔ (∀ a ∈ l, p a) ∧ Forall₂ R l u   | [], u =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_forall_2_and_left"))
        except Exception:
            pass
    return results


def _r0122_forall_2_map_left_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_map_left_iff
    # ∀ {l u}, Forall₂ R (map f l) u ↔ Forall₂ (fun c b => R (f c) b) l u   | [], _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_forall_2_map_left_iff"))
        except Exception:
            pass
    return results


def _r0123_forall_2_map_right_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_map_right_iff
    # ∀ {l u}, Forall₂ R l (map f u) ↔ Forall₂ (fun a c => R a (f c)) l u   | _, [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_forall_2_map_right_iff"))
        except Exception:
            pass
    return results


def _r0124_length_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Forall₂.length_eq
    # ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → length l₁ = length l₂   | _, _, Forall₂.nil => rfl   | _, _, Forall₂.cons _ h₂ => congr_arg
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2", 8)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("gt", (OVar("Forall_2_nil"), args[3], args[7], OVar("colon_colon"), args[7], args[7], OVar("colon_colon"), args[7], OVar("hl"), OVar("h"), OVar("eq_gt"), OVar("Forall_2_cons"), OOp("h", (OLit(0), OOp("Nat_zero_lt_succ", (args[7],)), OOp("Nat_zero_lt_succ", (args[7],)),)), OVar("forall_2_of_length_eq_of_get_succ_inj_hl_fun_i_h_1_h_2_eq_gt_h_i_succ_succ_lt_succ_h_1_succ_lt_succ_h_2_theorem"), OVar("forall_2_iff_get"), OVar("l_1_colon_List_a"), OVar("l_2_colon_List_b"), OVar("colon"), OVar("Forall_2"), args[0], OVar("l_1"), OVar("l_2"),)), OVar("l_1_length"))), OOp("and", (OVar("l_2_length"), OOp("forall", (OVar("i"), OVar("h_1"), OVar("h_2"), args[0], OOp("l_1_get", (OVar("i_h_1"),)), OOp("l_2_get", (OVar("i_h_2"),)),))))))
            results.append((rhs, "Mathlib: List_Forall_2_length_eq"))
        except Exception:
            pass
    return results


def _r0125_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Forall₂.get
    # ∀ {x : List α} {y : List β}, Forall₂ R x y →       ∀ ⦃i : ℕ⦄ (hx : i < x.length) (hy : i < y.length), R (x.get ⟨i, hx⟩) 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2", 8)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("gt", (OVar("Forall_2_nil"), args[3], args[7], OVar("colon_colon"), args[7], args[7], OVar("colon_colon"), args[7], OVar("hl"), OVar("h"), OVar("eq_gt"), OVar("Forall_2_cons"), OOp("h", (OLit(0), OOp("Nat_zero_lt_succ", (args[7],)), OOp("Nat_zero_lt_succ", (args[7],)),)), OVar("forall_2_of_length_eq_of_get_succ_inj_hl_fun_i_h_1_h_2_eq_gt_h_i_succ_succ_lt_succ_h_1_succ_lt_succ_h_2_theorem"), OVar("forall_2_iff_get"), OVar("l_1_colon_List_a"), OVar("l_2_colon_List_b"), OVar("colon"), OVar("Forall_2"), args[0], OVar("l_1"), OVar("l_2"),)), OVar("l_1_length"))), OOp("and", (OVar("l_2_length"), OOp("forall", (OVar("i"), OVar("h_1"), OVar("h_2"), args[0], OOp("l_1_get", (OVar("i_h_1"),)), OOp("l_2_get", (OVar("i_h_2"),)),))))))
            results.append((rhs, "Mathlib: List_Forall_2_get"))
        except Exception:
            pass
    return results


def _r0126_forall_2_of_length_eq_of_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_of_length_eq_of_get
    # ∀ {x : List α} {y : List β},       x.length = y.length → (∀ i h₁ h₂, R (x.get ⟨i, h₁⟩) (y.get ⟨i, h₂⟩)) → Forall₂ R x y 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2", 8)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("gt", (OVar("Forall_2_nil"), args[3], args[7], OVar("colon_colon"), args[7], args[7], OVar("colon_colon"), args[7], OVar("hl"), OVar("h"), OVar("eq_gt"), OVar("Forall_2_cons"), OOp("h", (OLit(0), OOp("Nat_zero_lt_succ", (args[7],)), OOp("Nat_zero_lt_succ", (args[7],)),)), OVar("forall_2_of_length_eq_of_get_succ_inj_hl_fun_i_h_1_h_2_eq_gt_h_i_succ_succ_lt_succ_h_1_succ_lt_succ_h_2_theorem"), OVar("forall_2_iff_get"), OVar("l_1_colon_List_a"), OVar("l_2_colon_List_b"), OVar("colon"), OVar("Forall_2"), args[0], OVar("l_1"), OVar("l_2"),)), OVar("l_1_length"))), OOp("and", (OVar("l_2_length"), OOp("forall", (OVar("i"), OVar("h_1"), OVar("h_2"), args[0], OOp("l_1_get", (OVar("i_h_1"),)), OOp("l_2_get", (OVar("i_h_2"),)),))))))
            results.append((rhs, "Mathlib: List_forall_2_of_length_eq_of_get"))
        except Exception:
            pass
    return results


def _r0127_forall_2_iff_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_iff_get
    # Forall₂ R l₁ l₂ ↔ l₁.length = l₂.length ∧ ∀ i h₁ h₂, R (l₁.get ⟨i, h₁⟩) (l₂.get ⟨i, h₂⟩)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OVar("l_2_length"), OOp("forall", (OVar("i"), OVar("h_1"), OVar("h_2"), OVar("R"), OOp("l_1_get", (OVar("i_h_1"),)), OOp("l_2_get", (OVar("i_h_2"),)),))))
            results.append((rhs, "Mathlib: List_forall_2_iff_get"))
        except Exception:
            pass
    return results


def _r0128_forall_2_zip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_zip
    # ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b   | _, _, Forall₂.cons h₁ h₂, x, y, hx =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R", 11)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_forall_2_zip"))
        except Exception:
            pass
    return results


def _r0129_forall_2_iff_zip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_iff_zip
    # Forall₂ R l₁ l₂ ↔ length l₁ = length l₂ ∧ ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("len", (OVar("l_2"),)), OOp("implies", (OOp("in", (OOp("forall", (OVar("a_b"), OOp("a", (OVar("b"),)),)), OOp("zip", (OVar("l_1"), OVar("l_2"),)))), OOp("R", (OVar("a"), OVar("b"),))))))
            results.append((rhs, "Mathlib: List_forall_2_iff_zip"))
        except Exception:
            pass
    return results


def _r0130_forall_2_take(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_take
    # ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (take n l₁) (take n l₂)   | 0, _, _, _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2", 8)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_forall_2_take"))
        except Exception:
            pass
    return results


def _r0131_forall_2_drop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_drop
    # ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (drop n l₁) (drop n l₂)   | 0, _, _, h =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2", 8)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_forall_2_drop"))
        except Exception:
            pass
    return results


def _r0132_getD_eq_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getD_eq_getElem
    # l.getD n d = l[n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_getD", 2)
    if args is not None:
        try:
            rhs = OVar("l_n")
            results.append((rhs, "Mathlib: List_getD_eq_getElem"))
        except Exception:
            pass
    return results


def _r0133_getD_eq_default(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getD_eq_default
    # l.getD n d = d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_getD", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: List_getD_eq_default"))
        except Exception:
            pass
    return results


def _r0134_getD_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getD_reverse
    # getD l.reverse i = getD l (l.length - 1 - i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "option_get_or", 2)
    if args is not None:
        try:
            rhs = OOp("option_get_or", (OVar("l"), OOp("-", (OVar("l_length"), OOp("-", (OLit(1), args[1])))),))
            results.append((rhs, "Mathlib: List_getD_reverse"))
        except Exception:
            pass
    return results


def _r0135_getD_append_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getD_append_right
    # (l ++ l').getD n d = l'.getD (n - l.length) d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_plus_plus_l_prime_getD", 2)
    if args is not None:
        try:
            rhs = OOp("l_prime_getD", (OOp("-", (args[0], OVar("l_length"))), args[1],))
            results.append((rhs, "Mathlib: List_getD_append_right"))
        except Exception:
            pass
    return results


def _r0136_mapIdx_append_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapIdx_append_one
    # ∀ {f : ℕ → α → β} {l : List α} {e : α},     mapIdx f (l ++ [e]) = mapIdx f l ++ [f l.length e]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapIdx", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("mapIdx", (args[0], OVar("l"),)), OSeq((OOp("f", (OVar("l_length"), OVar("e"),)),))))
            results.append((rhs, "Mathlib: List_mapIdx_append_one"))
        except Exception:
            pass
    return results


def _r0137_mapIdx_eq_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mapIdx_eq_ofFn
    # l.mapIdx f = ofFn fun i : Fin l.length ↦ f (i : ℕ) (l.get i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_mapIdx", 1)
    if args is not None:
        try:
            rhs = OOp("ofFn", (OVar("fun"), OVar("i"), OVar("colon"), OVar("Fin"), OVar("l_length"), OVar("_unknown"), args[0], OOp("i", (OVar("colon"), OVar("_unknown"),)), OOp("l_get", (OVar("i"),)),))
            results.append((rhs, "Mathlib: List_mapIdx_eq_ofFn"))
        except Exception:
            pass
    return results


def _r0138_prefix_append_drop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prefix_append_drop
    # l₂ = l₁ ++ l₂.drop l₁.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OVar("l_1"), OOp("l_2_drop", (OVar("l_1_length"),))))
            results.append((rhs, "Mathlib: List_prefix_append_drop"))
    except Exception:
        pass
    return results


def _r0139_infix_antisymm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.infix_antisymm
    # l₁ = l₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_2")
            results.append((rhs, "Mathlib: List_infix_antisymm"))
    except Exception:
        pass
    return results


def _r0140_insertIdx_eraseIdx_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.insertIdx_eraseIdx_self
    # (l.eraseIdx n).insertIdx n a = l.set n a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_eraseIdx_n_insertIdx", 2)
    if args is not None:
        try:
            rhs = OOp("l_set", (args[0], args[1],))
            results.append((rhs, "Mathlib: List_insertIdx_eraseIdx_self"))
        except Exception:
            pass
    return results


def _r0141_insertIdx_eraseIdx_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.insertIdx_eraseIdx_getElem
    # (l.eraseIdx n).insertIdx n l[n] = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_eraseIdx_n_insertIdx", 2)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_insertIdx_eraseIdx_getElem"))
        except Exception:
            pass
    return results


def _r0142_eq_or_mem_of_mem_insertIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.eq_or_mem_of_mem_insertIdx
    # a = b ∨ a ∈ l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("or", (OVar("b"), OOp("in", (OVar("a"), OVar("l")))))
            results.append((rhs, "Mathlib: List_eq_or_mem_of_mem_insertIdx"))
    except Exception:
        pass
    return results


def _r0143_get_insertIdx_of_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_insertIdx_of_lt
    # (l.insertIdx n x).get ⟨k, hk'⟩ = l.get ⟨k, hk⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_insertIdx_n_x_get", 1)
    if args is not None:
        try:
            rhs = OOp("l_get", (OVar("k_hk"),))
            results.append((rhs, "Mathlib: List_get_insertIdx_of_lt"))
        except Exception:
            pass
    return results


def _r0144_getElem_insertIdx_add_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getElem_insertIdx_add_succ
    # (l.insertIdx n x)[n + k + 1] = l[n + k]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_insertIdx_n_x_n_plus_k_plus_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_n_plus_k")
            results.append((rhs, "Mathlib: List_getElem_insertIdx_add_succ"))
    except Exception:
        pass
    return results


def _r0145_zero_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.zero_bot
    # Ico 0 n = range n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OOp("range", (args[1],))
            results.append((rhs, "Mathlib: List_Ico_zero_bot"))
        except Exception:
            pass
    return results


def _r0146_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.length
    # length (Ico n m) = m - n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("m"), OVar("n")))
            results.append((rhs, "Mathlib: List_Ico_length"))
        except Exception:
            pass
    return results


def _r0147_succ_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.succ_top
    # Ico n (m + 1) = Ico n m ++ [m]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("Ico", (args[0], OVar("m"),)), OSeq((OVar("m"),))))
            results.append((rhs, "Mathlib: List_Ico_succ_top"))
        except Exception:
            pass
    return results


def _r0148_filter_lt_of_top_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.filter_lt_of_top_le
    # ((Ico n m).filter fun x => x < l) = Ico n m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("n"), OVar("m"),))
            results.append((rhs, "Mathlib: List_Ico_filter_lt_of_top_le"))
        except Exception:
            pass
    return results


def _r0149_filter_lt_of_le_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.filter_lt_of_le_bot
    # ((Ico n m).filter fun x => x < l) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_Ico_filter_lt_of_le_bot"))
        except Exception:
            pass
    return results


def _r0150_filter_lt_of_ge(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.filter_lt_of_ge
    # ((Ico n m).filter fun x => x < l) = Ico n l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("n"), args[1],))
            results.append((rhs, "Mathlib: List_Ico_filter_lt_of_ge"))
        except Exception:
            pass
    return results


def _r0151_filter_le_of_le_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.filter_le_of_le_bot
    # ((Ico n m).filter fun x => l ≤ x) = Ico n m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("n"), OVar("m"),))
            results.append((rhs, "Mathlib: List_Ico_filter_le_of_le_bot"))
        except Exception:
            pass
    return results


def _r0152_filter_le_of_top_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.filter_le_of_top_le
    # ((Ico n m).filter fun x => l ≤ x) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_Ico_filter_le_of_top_le"))
        except Exception:
            pass
    return results


def _r0153_filter_le_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.filter_le_of_le
    # ((Ico n m).filter fun x => l ≤ x) = Ico l m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("l"), OVar("m"),))
            results.append((rhs, "Mathlib: List_Ico_filter_le_of_le"))
        except Exception:
            pass
    return results


def _r0154_filter_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.filter_le
    # ((Ico n m).filter fun x => l ≤ x) = Ico (max n l) m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OOp("max", (OVar("n"), OVar("l"),)), OVar("m"),))
            results.append((rhs, "Mathlib: List_Ico_filter_le"))
        except Exception:
            pass
    return results


def _r0155_filter_le_of_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.filter_le_of_bot
    # ((Ico n m).filter fun x => x ≤ n) = [n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OSeq((args[1],))
            results.append((rhs, "Mathlib: List_Ico_filter_le_of_bot"))
        except Exception:
            pass
    return results


def _r0156_length_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_iterate
    # length (iterate f a n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: List_length_iterate"))
        except Exception:
            pass
    return results


def _r0157_getElem_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getElem_iterate
    # (iterate f a n)[i] = f^[i] a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("iterate_f_a_n_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("fpow_i", (OVar("a"),))
            results.append((rhs, "Mathlib: List_getElem_iterate"))
    except Exception:
        pass
    return results


def _r0158_iterate_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.iterate_add
    # iterate f a (m + n) = iterate f a m ++ iterate f (f^[m] a) n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iterate", 3)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("iterate", (args[0], args[1], OVar("m"),)), OOp("iterate", (args[0], OOp("fpow_m", (args[1],)), OVar("n"),))))
            results.append((rhs, "Mathlib: List_iterate_add"))
        except Exception:
            pass
    return results


def _r0159_lex_nil_or_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lex_nil_or_eq_nil
    # List.Lex r [] l ∨ l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_lex_nil_or_eq_nil"))
        except Exception:
            pass
    return results


def _r0160_append_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Lex.append_right
    # ∀ {s₁ s₂} (t), Lex r s₁ s₂ → Lex r s₁ (s₂ ++ t)   | _, _, _, nil => nil   | _, _, _, cons h => cons (append_right r _ h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OOp("gt", (OVar("to_ne"), OVar("h"), OVar("List_cons_inj_e_2"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("rel"), OVar("r"), OVar("e"), OVar("eq_gt"), OVar("r"), OVar("List_cons_inj_e_1_theorem"), OVar("root_Decidable_List_Lex_ne_iff"), OSeq((OOp("==", (OVar("a"),)),)), OVar("l_1_l_2_colon_List_a"), OOp("<=", (OOp("H", (OVar("colon"), OVar("length"), args[0],)), OOp("len", (OVar("l_2"),)))), OVar("colon"), OVar("Lex"), OOp("!=", (OVar("_unknown"), OVar("_unknown"))), args[0], OVar("l_2"),)), args[0])), OVar("l_2")))
            results.append((rhs, "Mathlib: List_Lex_append_right"))
        except Exception:
            pass
    return results


def _r0161_append_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Lex.append_left
    # ∀ s, Lex R (s ++ t₁) (s ++ t₂)   | [] => h   | _ :: l => cons (append_left R h l)  theorem imp {r s : α → α → Prop} (H :
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OOp("gt", (OVar("to_ne"), OVar("h"), OVar("List_cons_inj_e_2"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("rel"), OVar("r"), OVar("e"), OVar("eq_gt"), OVar("r"), OVar("List_cons_inj_e_1_theorem"), OVar("root_Decidable_List_Lex_ne_iff"), OSeq((OOp("==", (OVar("a"),)),)), OVar("l_1_l_2_colon_List_a"), OOp("<=", (OOp("H", (OVar("colon"), OVar("length"), args[0],)), OOp("len", (OVar("l_2"),)))), OVar("colon"), OVar("Lex"), OOp("!=", (OVar("_unknown"), OVar("_unknown"))), args[0], OVar("l_2"),)), args[0])), OVar("l_2")))
            results.append((rhs, "Mathlib: List_Lex_append_left"))
        except Exception:
            pass
    return results


def _r0162_imp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Lex.imp
    # ∀ l₁ l₂, Lex r l₁ l₂ → Lex s l₁ l₂   | _, _, nil => nil   | _, _, cons h => cons (imp H _ _ h)   | _, _, rel r => rel (H
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OOp("gt", (OVar("to_ne"), OVar("h"), OVar("List_cons_inj_e_2"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("rel"), OVar("r"), OVar("e"), OVar("eq_gt"), OVar("r"), OVar("List_cons_inj_e_1_theorem"), OVar("root_Decidable_List_Lex_ne_iff"), OSeq((OOp("==", (OVar("a"),)),)), OVar("l_1_l_2_colon_List_a"), OOp("<=", (OOp("H", (OVar("colon"), OVar("length"), args[0],)), OOp("len", (OVar("l_2"),)))), OVar("colon"), OVar("Lex"), OOp("!=", (OVar("_unknown"), OVar("_unknown"))), args[0], OVar("l_2"),)), args[0])), OVar("l_2")))
            results.append((rhs, "Mathlib: List_Lex_imp"))
        except Exception:
            pass
    return results


def _r0163_to_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Lex.to_ne
    # ∀ {l₁ l₂ : List α}, Lex (· ≠ ·) l₁ l₂ → l₁ ≠ l₂   | _, _, cons h, e => to_ne h (List.cons.inj e).2   | _, _, rel r, e =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("iff", (OOp("gt", (OVar("to_ne"), OVar("h"), OVar("List_cons_inj_e_2"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("rel"), OVar("r"), OVar("e"), OVar("eq_gt"), OVar("r"), OVar("List_cons_inj_e_1_theorem"), OVar("root_Decidable_List_Lex_ne_iff"), OSeq((OOp("==", (OVar("a"),)),)), OVar("l_1_l_2_colon_List_a"), OOp("<=", (OOp("H", (OVar("colon"), OVar("length"), args[0],)), OOp("len", (OVar("l_2"),)))), OVar("colon"), OVar("Lex"), OOp("!=", (OVar("_unknown"), OVar("_unknown"))), args[0], OVar("l_2"),)), args[0])), OVar("l_2")))
            results.append((rhs, "Mathlib: List_Lex_to_ne"))
        except Exception:
            pass
    return results


def _r0164_lookmap_of_forall_not(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookmap_of_forall_not
    # l.lookmap f = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_lookmap", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_lookmap_of_forall_not"))
        except Exception:
            pass
    return results


def _r0165_length_lookmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_lookmap
    # length (l.lookmap f) = length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("l"),))
            results.append((rhs, "Mathlib: List_length_lookmap"))
        except Exception:
            pass
    return results


def _r0166_argAux_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.argAux_self
    # argAux r (some a) a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "argAux", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: List_argAux_self"))
        except Exception:
            pass
    return results


def _r0167_pure_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.pure_def
    # pure a = [a]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pure", 1)
    if args is not None:
        try:
            rhs = OSeq((args[0],))
            results.append((rhs, "Mathlib: List_pure_def"))
        except Exception:
            pass
    return results


def _r0168_mem_antidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.mem_antidiagonal
    # x ∈ antidiagonal n ↔ x.1 + x.2 = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: List_Nat_mem_antidiagonal"))
        except Exception:
            pass
    return results


def _r0169_length_antidiagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.length_antidiagonal
    # (antidiagonal n).length = n + 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("antidiagonal_n_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("n"), OLit(1)))
            results.append((rhs, "Mathlib: List_Nat_length_antidiagonal"))
    except Exception:
        pass
    return results


def _r0170_antidiagonal_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.antidiagonal_zero
    # antidiagonal 0 = [(0, 0)]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonal", 1)
    if args is not None:
        try:
            rhs = OVar("_0_0")
            results.append((rhs, "Mathlib: List_Nat_antidiagonal_zero"))
        except Exception:
            pass
    return results


def _r0171_getElem_inj_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.getElem_inj_iff
    # l[i] = l[j] ↔ i = j
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("l_j"), OVar("i"))), OVar("j")))
            results.append((rhs, "Mathlib: List_Nodup_getElem_inj_iff"))
    except Exception:
        pass
    return results


def _r0172_idxOf_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_getElem
    # Nodup l → (i : Nat) → (h : i < l.length) →     idxOf l[i] l = i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "idxOf", 2)
    if args is not None:
        try:
            rhs = OVar("i")
            results.append((rhs, "Mathlib: List_idxOf_getElem"))
        except Exception:
            pass
    return results


def _r0173_get_bijective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_bijective_iff
    # l.get.Bijective ↔ ∀ a, l.count a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: List_get_bijective_iff"))
        except Exception:
            pass
    return results


def _r0174_getElem_bijective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getElem_bijective_iff
    # (fun (n : Fin l.length) ↦ l[n]).Bijective ↔ ∀ a, l.count a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: List_getElem_bijective_iff"))
        except Exception:
            pass
    return results


def _r0175_erase_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.erase_getElem
    # l.erase l[i] = l.eraseIdx ↑i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_erase", 1)
    if args is not None:
        try:
            rhs = OOp("l_eraseIdx", (OVar("i"),))
            results.append((rhs, "Mathlib: List_Nodup_erase_getElem"))
        except Exception:
            pass
    return results


def _r0176_ofFn_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_congr
    # ofFn f = ofFn fun i : Fin n => f (Fin.cast h.symm i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn", 1)
    if args is not None:
        try:
            rhs = OOp("ofFn", (OVar("fun"), OVar("i"), OVar("colon"), OVar("Fin"), OVar("n"), OVar("eq_gt"), args[0], OOp("Fin_cast", (OVar("h_symm"), OVar("i"),)),))
            results.append((rhs, "Mathlib: List_ofFn_congr"))
        except Exception:
            pass
    return results


def _r0177_ofFn_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_mul
    # List.ofFn f = List.flatten (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f ⟨i * n + j,     calc       ↑i * n + 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_ofFn", 1)
    if args is not None:
        try:
            rhs = OOp("List_flatten", (OOp("List_ofFn", (OVar("fun"), OVar("i"), OVar("colon"), OVar("Fin"), OVar("m"), OVar("eq_gt"), OVar("List_ofFn"), OVar("fun"), OVar("j"), OVar("colon"), OVar("Fin"), OVar("n"), OVar("eq_gt"), args[0], OVar("i_star_n_plus_j_calc_i_star_n_plus_j_lt_i_plus_1_star_n_colon_eq_Nat_add_lt_add_left_j_prop_trans_eq_by_rw_Nat_add_mul_Nat_one_mul_le_colon_eq_Nat_mul_le_mul_right_i_prop"),)),))
            results.append((rhs, "Mathlib: List_ofFn_mul"))
        except Exception:
            pass
    return results


def _r0178_ofFn_getElem_eq_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_getElem_eq_map
    # ofFn (fun i : Fin l.length => f <| l[(i : Nat)]) = l.map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn", 1)
    if args is not None:
        try:
            rhs = OOp("l_map", (OVar("f"),))
            results.append((rhs, "Mathlib: List_ofFn_getElem_eq_map"))
        except Exception:
            pass
    return results


def _r0179_ofFn_fin_repeat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_fin_repeat
    # List.ofFn (Fin.repeat n a) = (List.replicate n (List.ofFn a)).flatten
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_ofFn", 1)
    if args is not None:
        try:
            rhs = OVar("List_replicate_n_List_ofFn_a_flatten")
            results.append((rhs, "Mathlib: List_ofFn_fin_repeat"))
        except Exception:
            pass
    return results


def _r0180_ofFnRec_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFnRec_ofFn
    # @ofFnRec _ C h (List.ofFn f) = h _ f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_ofFnRec", 4)
    if args is not None:
        try:
            rhs = OOp("h", (args[0], OVar("f"),))
            results.append((rhs, "Mathlib: List_ofFnRec_ofFn"))
        except Exception:
            pass
    return results


def _r0181_ofFn_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_inj
    # ofFn f = ofFn g ↔ f = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("ofFn", (OVar("g"),)), args[0])), OVar("g")))
            results.append((rhs, "Mathlib: List_ofFn_inj"))
        except Exception:
            pass
    return results


def _r0182_length_offDiag(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_offDiag
    # length l.offDiag = length l ^ 2 - length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("**", (OOp("len", (OVar("l"),)), OLit(2))), OOp("len", (OVar("l"),))))
            results.append((rhs, "Mathlib: List_length_offDiag"))
        except Exception:
            pass
    return results


def _r0183_length_permutationsAux2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_permutationsAux2
    # length (permutationsAux2 t ts [] ys f).2 = length ys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("ys"),))
            results.append((rhs, "Mathlib: List_length_permutationsAux2"))
        except Exception:
            pass
    return results


def _r0184_length_permutationsAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_permutationsAux
    # ∀ ts is : List α, length (permutationsAux ts is) + is.length ! = (length ts + length is)!
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("length_ts_plus_length_is_bang")
            results.append((rhs, "Mathlib: List_length_permutationsAux"))
        except Exception:
            pass
    return results


def _r0185_length_permutations(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_permutations
    # length (permutations l) = (length l)!
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OVar("length_l_bang")
            results.append((rhs, "Mathlib: List_length_permutations"))
        except Exception:
            pass
    return results


def _r0186_DecEq_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.DecEq_eq
    # List.instBEq = @instBEqOfDecidableEq (List α) instDecidableEqList
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("List_instBEq")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("List", (OVar("a"),)), OVar("instDecidableEqList"),))
            results.append((rhs, "Mathlib: List_DecEq_eq"))
    except Exception:
        pass
    return results


def _r0187_pi_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.pi_coe
    # (l : Multiset ι).pi (fs ·) = (↑(pi l fs) : Multiset (∀ i ∈ l, α i))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_colon_Multiset_i_pi", 1)
    if args is not None:
        try:
            rhs = OOp("pi_l_fs", (OVar("colon"), OVar("Multiset"), OOp("in", (OOp("forall", (OVar("i"),)), OOp("l", (OVar("a"), OVar("i"),)))),))
            results.append((rhs, "Mathlib: Multiset_pi_coe"))
        except Exception:
            pass
    return results


def _r0188_length_product(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_product
    # length (l₁ ×ˢ l₂) = length l₁ * length l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("len", (OVar("l_1"),)), OOp("len", (OVar("l_2"),))))
            results.append((rhs, "Mathlib: List_length_product"))
        except Exception:
            pass
    return results


def _r0189_ranges_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ranges_length
    # l.ranges.map length = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_ranges_map", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_ranges_length"))
        except Exception:
            pass
    return results


def _r0190_reduceOption_replicate_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_replicate_none
    # (replicate n (@none α)).reduceOption = []
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("replicate_n_at_none_a_reduceOption")
        if term.canon() == lhs_pattern.canon():
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_reduceOption_replicate_none"))
    except Exception:
        pass
    return results


def _r0191_reduceOption_length_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_length_eq
    # l.reduceOption.length = (l.filter Option.isSome).length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_reduceOption_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_filter_Option_isSome_length")
            results.append((rhs, "Mathlib: List_reduceOption_length_eq"))
    except Exception:
        pass
    return results


def _r0192_length_eq_reduceOption_length_add_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_eq_reduceOption_length_add_filter_none
    # l.length = l.reduceOption.length + (l.filter Option.isNone).length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("l_reduceOption_length"), OVar("l_filter_Option_isNone_length")))
            results.append((rhs, "Mathlib: List_length_eq_reduceOption_length_add_filter_none"))
    except Exception:
        pass
    return results


def _r0193_reduceOption_length_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_length_eq_iff
    # l.reduceOption.length = l.length ↔ ∀ x ∈ l, Option.isSome x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_reduceOption_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("l_length"), OOp("in", (OOp("forall", (OVar("x"),)), OOp("l", (OVar("Option_isSome"), OVar("x"),))))))
            results.append((rhs, "Mathlib: List_reduceOption_length_eq_iff"))
    except Exception:
        pass
    return results


def _r0194_rotate_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_mod
    # l.rotate (n % l.length) = l.rotate n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("l_rotate", (OVar("n"),))
            results.append((rhs, "Mathlib: List_rotate_mod"))
        except Exception:
            pass
    return results


def _r0195_length_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_rotate
    # (l.rotate n).length = l.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_rotate_n_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_length")
            results.append((rhs, "Mathlib: List_length_rotate"))
    except Exception:
        pass
    return results


def _r0196_rotate_append_length_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_append_length_eq
    # (l ++ l').rotate l.length = l' ++ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_plus_plus_l_prime_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("l_prime"), OVar("l")))
            results.append((rhs, "Mathlib: List_rotate_append_length_eq"))
        except Exception:
            pass
    return results


def _r0197_rotate_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_rotate
    # (l.rotate n).rotate m = l.rotate (n + m)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate_n_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("l_rotate", (OOp("+", (OVar("n"), args[0])),))
            results.append((rhs, "Mathlib: List_rotate_rotate"))
        except Exception:
            pass
    return results


def _r0198_getElem_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getElem_rotate
    # (l.rotate n)[k] =       l[(k + n) % l.length]'(mod_lt _ (length_rotate l n ▸ k.zero_le.trans_lt h))
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_rotate_n_k")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_k_plus_n_l_length_prime_mod_lt_length_rotate_l_n_k_zero_le_trans_lt_h")
            results.append((rhs, "Mathlib: List_getElem_rotate"))
    except Exception:
        pass
    return results


def _r0199_get_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_rotate
    # (l.rotate n).get k = l.get ⟨(k + n) % l.length, mod_lt _ (length_rotate l n ▸ k.pos)⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate_n_get", 1)
    if args is not None:
        try:
            rhs = OOp("l_get", (OVar("k_plus_n_l_length_mod_lt_length_rotate_l_n_k_pos"),))
            results.append((rhs, "Mathlib: List_get_rotate"))
        except Exception:
            pass
    return results


def _r0200_get_rotate_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_rotate_one
    # (l.rotate 1).get k = l.get ⟨(k + 1) % l.length, mod_lt _ (length_rotate l 1 ▸ k.pos)⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate_1_get", 1)
    if args is not None:
        try:
            rhs = OOp("l_get", (OVar("k_plus_1_l_length_mod_lt_length_rotate_l_1_k_pos"),))
            results.append((rhs, "Mathlib: List_get_rotate_one"))
        except Exception:
            pass
    return results


def _r0201_getElem_eq_getElem_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getElem_eq_getElem_rotate
    # l[k] = ((l.rotate n)[(l.length - n % l.length + k) % l.length]'       ((Nat.mod_lt _ (k.zero_le.trans_lt hk)).trans_eq (
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_k")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_rotate_n_l_length_minus_n_l_length_plus_k_l_length_prime", (OOp("Nat_mod_lt_k_zero_le_trans_lt_hk_trans_eq", (OVar("length_rotate_symm"),)),))
            results.append((rhs, "Mathlib: List_getElem_eq_getElem_rotate"))
    except Exception:
        pass
    return results


def _r0202_get_eq_get_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_eq_get_rotate
    # l.get k = (l.rotate n).get ⟨(l.length - n % l.length + k) % l.length,       (Nat.mod_lt _ (k.1.zero_le.trans_lt k.2)).tr
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_get", 1)
    if args is not None:
        try:
            rhs = OOp("l_rotate_n_get", (OVar("l_length_minus_n_l_length_plus_k_l_length_Nat_mod_lt_k_1_zero_le_trans_lt_k_2_trans_eq_length_rotate_symm"),))
            results.append((rhs, "Mathlib: List_get_eq_get_rotate"))
        except Exception:
            pass
    return results


def _r0203_rotate_eq_self_iff_eq_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_eq_self_iff_eq_replicate
    # ∀ {l : List α}, (∀ n, l.rotate n = l) ↔ ∃ a, l = replicate l.length a   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("replicate", (OVar("l_length"), OVar("a"), OVar("pipe"), OSeq(()), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_rotate_eq_self_iff_eq_replicate"))
        except Exception:
            pass
    return results


def _r0204_rotate_one_eq_self_iff_eq_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_one_eq_self_iff_eq_replicate
    # l.rotate 1 = l ↔ ∃ a : α, l = List.replicate l.length a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("l"), OOp("exists", (OVar("a"), OVar("colon"), OVar("a"), OVar("l"),)))), OOp("replicate", (OVar("l_length"), OVar("a"),))))
            results.append((rhs, "Mathlib: List_rotate_one_eq_self_iff_eq_replicate"))
        except Exception:
            pass
    return results


def _r0205_rotate_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_injective
    # Function.Injective fun l : List α => l.rotate n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("l_rotate"), OVar("n"),))
            results.append((rhs, "Mathlib: List_rotate_injective"))
        except Exception:
            pass
    return results


def _r0206_rotate_eq_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_eq_rotate
    # l.rotate n = l'.rotate n ↔ l = l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("l_prime_rotate", (args[0],)), OVar("l"))), OVar("l_prime")))
            results.append((rhs, "Mathlib: List_rotate_eq_rotate"))
        except Exception:
            pass
    return results


def _r0207_rotate_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_reverse
    # l.reverse.rotate n = (l.rotate (l.length - n % l.length)).reverse
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_reverse_rotate", 1)
    if args is not None:
        try:
            rhs = OVar("l_rotate_l_length_minus_n_l_length_reverse")
            results.append((rhs, "Mathlib: List_rotate_reverse"))
        except Exception:
            pass
    return results


def _r0208_rotate_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.rotate_congr
    # i % l.length = j % l.length
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i", 2)
    if args is not None:
        try:
            rhs = OOp("j", (args[0], args[1],))
            results.append((rhs, "Mathlib: List_Nodup_rotate_congr"))
        except Exception:
            pass
    return results


def _r0209_rotate_congr_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.rotate_congr_iff
    # l.rotate i = l.rotate j ↔ i % l.length = j % l.length ∨ l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("l_rotate", (OVar("j"),)), OOp("i", (OVar("_unknown"), OVar("l_length"),)))), OOp("==", (OOp("or", (OOp("j", (OVar("_unknown"), OVar("l_length"),)), OVar("l"))), OSeq(())))))
            results.append((rhs, "Mathlib: List_Nodup_rotate_congr_iff"))
        except Exception:
            pass
    return results


def _r0210_rotate_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.rotate_eq_self_iff
    # l.rotate n = l ↔ n % l.length = 0 ∨ l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("l"), OOp("n", (OVar("_unknown"), OVar("l_length"),)))), OOp("==", (OOp("or", (OLit(0), OVar("l"))), OSeq(())))))
            results.append((rhs, "Mathlib: List_Nodup_rotate_eq_self_iff"))
        except Exception:
            pass
    return results


def _r0211_length_cyclicPermutations_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_cyclicPermutations_cons
    # length (cyclicPermutations (x :: l)) = length l + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("len", (OVar("l"),)), OLit(1)))
            results.append((rhs, "Mathlib: List_length_cyclicPermutations_cons"))
        except Exception:
            pass
    return results


def _r0212_length_cyclicPermutations_of_ne_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_cyclicPermutations_of_ne_nil
    # length (cyclicPermutations l) = length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("l"),))
            results.append((rhs, "Mathlib: List_length_cyclicPermutations_of_ne_nil"))
        except Exception:
            pass
    return results


def _r0213_length_mem_cyclicPermutations(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_mem_cyclicPermutations
    # length l' = length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("l"),))
            results.append((rhs, "Mathlib: List_length_mem_cyclicPermutations"))
        except Exception:
            pass
    return results


def _r0214_mem_sections_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_sections_length
    # length f = length L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("L"),))
            results.append((rhs, "Mathlib: List_mem_sections_length"))
        except Exception:
            pass
    return results


def _r0215_shortlex_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.shortlex_def
    # Shortlex r s t ↔ s.length < t.length ∨ s.length = t.length ∧ Lex r s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OVar("t_length"), OOp("Lex", (OVar("r"), OVar("s"), OVar("t"),))))
            results.append((rhs, "Mathlib: List_shortlex_def"))
        except Exception:
            pass
    return results


def _r0216_shortlex_nil_or_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.shortlex_nil_or_eq_nil
    # ∀ s : List α, Shortlex r [] s ∨ s = []   | [] => .inr rfl   | _ :: tail => .inl <| .of_length_lt tail.length.succ_pos  @
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OSeq((OOp("pipe_eq_gt_inr_rfl_pipe_colon_colon_tail_eq_gt_inl_lt_pipe_of_length_lt_tail_length_succ_pos_at_simp_theorem_shortlex_singleton_iff_a", (OVar("b"), OVar("colon"), OVar("a_colon_Shortlex_r_a_b"),)),)), OOp("r", (OVar("a"), OVar("b"),))))
            results.append((rhs, "Mathlib: List_shortlex_nil_or_eq_nil"))
        except Exception:
            pass
    return results


def _r0217_eq_of_fst_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.NodupKeys.eq_of_fst_eq
    # s.1 = s'.1 → s = s'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_prime")
            results.append((rhs, "Mathlib: List_NodupKeys_eq_of_fst_eq"))
    except Exception:
        pass
    return results


def _r0218_dlookup_eq_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_eq_none
    # dlookup a l = none ↔ a ∉ l.keys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("none"), OOp("not_in", (args[0], OVar("l_keys")))))
            results.append((rhs, "Mathlib: List_dlookup_eq_none"))
        except Exception:
            pass
    return results


def _r0219_lookupAll_eq_dlookup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookupAll_eq_dlookup
    # lookupAll a l = (dlookup a l).toList
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lookupAll", 2)
    if args is not None:
        try:
            rhs = OVar("dlookup_a_l_toList")
            results.append((rhs, "Mathlib: List_lookupAll_eq_dlookup"))
        except Exception:
            pass
    return results


def _r0220_kreplace_of_forall_not(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kreplace_of_forall_not
    # kreplace a b l = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kreplace", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: List_kreplace_of_forall_not"))
        except Exception:
            pass
    return results


def _r0221_kreplace_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kreplace_self
    # kreplace a b l = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kreplace", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: List_kreplace_self"))
        except Exception:
            pass
    return results


def _r0222_keys_kreplace(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.keys_kreplace
    # ∀ l : List (Sigma β), (kreplace a b l).keys = l.keys
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("kreplace_a_b_l_keys")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_keys")
            results.append((rhs, "Mathlib: List_keys_kreplace"))
    except Exception:
        pass
    return results


def _r0223_exists_of_kerase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_of_kerase
    # ∃ (b : β a) (l₁ l₂ : List (Sigma β)),       a ∉ l₁.keys ∧ l = l₁ ++ ⟨a, b⟩ :: l₂ ∧ kerase a l = l₁ ++ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("l_1"), OOp("concat", (OOp("==", (OOp("and", (OOp("a_b", (OVar("colon_colon"), OVar("l_2"),)), OOp("kerase", (OVar("a"), args[1],)))), OVar("l_1"))), OVar("l_2")))))
            results.append((rhs, "Mathlib: List_exists_of_kerase"))
        except Exception:
            pass
    return results


def _r0224_keys_kerase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.keys_kerase
    # (kerase a l).keys = l.keys.erase a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("kerase_a_l_keys")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_keys_erase", (OVar("a"),))
            results.append((rhs, "Mathlib: List_keys_kerase"))
    except Exception:
        pass
    return results


def _r0225_kerase_kerase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kerase_kerase
    # (kerase a' l).kerase a = (kerase a l).kerase a'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kerase_a_prime_l_kerase", 1)
    if args is not None:
        try:
            rhs = OOp("kerase_a_l_kerase", (OVar("a_prime"),))
            results.append((rhs, "Mathlib: List_kerase_kerase"))
        except Exception:
            pass
    return results


def _r0226_dlookup_kerase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_kerase
    # dlookup a (kerase a l) = none
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OVar("none")
            results.append((rhs, "Mathlib: List_dlookup_kerase"))
        except Exception:
            pass
    return results


def _r0227_dlookup_kerase_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_kerase_ne
    # dlookup a (kerase a' l) = dlookup a l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("dlookup", (args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_dlookup_kerase_ne"))
        except Exception:
            pass
    return results


def _r0228_kerase_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kerase_comm
    # kerase a₂ (kerase a₁ l) = kerase a₁ (kerase a₂ l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kerase", 2)
    if args is not None:
        try:
            rhs = OOp("kerase", (OVar("a_1"), OOp("kerase", (args[0], OVar("l"),)),))
            results.append((rhs, "Mathlib: List_kerase_comm"))
        except Exception:
            pass
    return results


def _r0229_kinsert_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kinsert_def
    # kinsert a b l = ⟨a, b⟩ :: kerase a l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kinsert", 3)
    if args is not None:
        try:
            rhs = OOp("a_b", (OVar("colon_colon"), OVar("kerase"), args[0], args[2],))
            results.append((rhs, "Mathlib: List_kinsert_def"))
        except Exception:
            pass
    return results


def _r0230_dlookup_kinsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_kinsert
    # dlookup a (kinsert a b l) = some b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("some", (OVar("b"),))
            results.append((rhs, "Mathlib: List_dlookup_kinsert"))
        except Exception:
            pass
    return results


def _r0231_dlookup_kinsert_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_kinsert_ne
    # dlookup a (kinsert a' b' l) = dlookup a l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("dlookup", (args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_dlookup_kinsert_ne"))
        except Exception:
            pass
    return results


def _r0232_kextract_eq_dlookup_kerase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kextract_eq_dlookup_kerase
    # ∀ l : List (Sigma β), kextract a l = (dlookup a l, kerase a l)   | [] => rfl   | ⟨a', b⟩ :: l =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kextract", 2)
    if args is not None:
        try:
            rhs = OOp("dlookup_a_l_kerase_a_l", (OVar("pipe"), OSeq(()), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a_prime_b"), OVar("colon_colon"), args[1], OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_kextract_eq_dlookup_kerase"))
        except Exception:
            pass
    return results


def _r0233_dlookup_dedupKeys(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_dedupKeys
    # dlookup a (dedupKeys l) = dlookup a l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("dlookup", (args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_dlookup_dedupKeys"))
        except Exception:
            pass
    return results


def _r0234_kunion_kerase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kunion_kerase
    # ∀ {l₁ l₂ : List (Sigma β)}, kunion (kerase a l₁) (kerase a l₂) = kerase a (kunion l₁ l₂)   | [], _ => rfl   | s :: _, l 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kunion", 2)
    if args is not None:
        try:
            rhs = OOp("kerase", (OVar("a"), OOp("kunion", (OVar("l_1"), OVar("l_2"),)), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("s"), OVar("colon_colon"), OVar("_unknown"), OVar("l"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_kunion_kerase"))
        except Exception:
            pass
    return results


def _r0235_dlookup_kunion_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_kunion_left
    # dlookup a (kunion l₁ l₂) = dlookup a l₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("dlookup", (args[0], OVar("l_1"),))
            results.append((rhs, "Mathlib: List_dlookup_kunion_left"))
        except Exception:
            pass
    return results


def _r0236_dlookup_kunion_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_kunion_right
    # dlookup a (kunion l₁ l₂) = dlookup a l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("dlookup", (args[0], OVar("l_2"),))
            results.append((rhs, "Mathlib: List_dlookup_kunion_right"))
        except Exception:
            pass
    return results


def _r0237_dlookup_kunion_eq_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_kunion_eq_some
    # dlookup a (kunion l₁ l₂) = some b ↔       dlookup a l₁ = some b ∨ a ∉ l₁.keys ∧ dlookup a l₂ = some b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("some", (OVar("b"),)), OOp("dlookup", (args[0], OVar("l_1"),)))), OOp("==", (OOp("and", (OOp("or", (OOp("some", (OVar("b"),)), OOp("not_in", (args[0], OVar("l_1_keys"))))), OOp("dlookup", (args[0], OVar("l_2"),)))), OOp("some", (OVar("b"),))))))
            results.append((rhs, "Mathlib: List_dlookup_kunion_eq_some"))
        except Exception:
            pass
    return results


def _r0238_orderedInsert_of_not_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.orderedInsert_of_not_le
    # orderedInsert r a (b :: l) = b :: orderedInsert r a l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "orderedInsert", 3)
    if args is not None:
        try:
            rhs = OOp("b", (OVar("colon_colon"), OVar("orderedInsert"), args[0], args[1], OVar("l"),))
            results.append((rhs, "Mathlib: List_orderedInsert_of_not_le"))
        except Exception:
            pass
    return results


def _r0239_orderedInsert_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.orderedInsert_length
    # (L.orderedInsert r a).length = L.length + 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L_orderedInsert_r_a_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("L_length"), OLit(1)))
            results.append((rhs, "Mathlib: List_orderedInsert_length"))
    except Exception:
        pass
    return results


def _r0240_erase_orderedInsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.erase_orderedInsert
    # (xs.orderedInsert r x).erase x = xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "xs_orderedInsert_r_x_erase", 1)
    if args is not None:
        try:
            rhs = OVar("xs")
            results.append((rhs, "Mathlib: List_erase_orderedInsert"))
        except Exception:
            pass
    return results


def _r0241_erase_orderedInsert_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.erase_orderedInsert_of_notMem
    # (xs.orderedInsert r x).erase x = xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "xs_orderedInsert_r_x_erase", 1)
    if args is not None:
        try:
            rhs = OVar("xs")
            results.append((rhs, "Mathlib: List_erase_orderedInsert_of_notMem"))
        except Exception:
            pass
    return results


def _r0242_orderedInsert_erase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.orderedInsert_erase
    # (xs.erase x).orderedInsert r x = xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "xs_erase_x_orderedInsert", 2)
    if args is not None:
        try:
            rhs = OVar("xs")
            results.append((rhs, "Mathlib: List_orderedInsert_erase"))
        except Exception:
            pass
    return results


def _r0243_flatten_splitBy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.flatten_splitBy
    # (l.splitBy r).flatten = l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_splitBy_r_flatten")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_flatten_splitBy"))
    except Exception:
        pass
    return results


def _r0244_splitBy_of_isChain(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitBy_of_isChain
    # splitBy r l = [l]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "splitBy", 2)
    if args is not None:
        try:
            rhs = OSeq((args[1],))
            results.append((rhs, "Mathlib: List_splitBy_of_isChain"))
        except Exception:
            pass
    return results


def _r0245_splitBy_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitBy_flatten
    # l.flatten.splitBy r = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_flatten_splitBy", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_splitBy_flatten"))
        except Exception:
            pass
    return results


def _r0246_length_splitLengths(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_splitLengths
    # (sz.splitLengths l).length = sz.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sz_splitLengths_l_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("sz_length")
            results.append((rhs, "Mathlib: List_length_splitLengths"))
    except Exception:
        pass
    return results


def _r0247_take_splitLength(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.take_splitLength
    # (sz.splitLengths l).take i = (sz.take i).splitLengths l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sz_splitLengths_l_take", 1)
    if args is not None:
        try:
            rhs = OOp("sz_take_i_splitLengths", (OVar("l"),))
            results.append((rhs, "Mathlib: List_take_splitLength"))
        except Exception:
            pass
    return results


def _r0248_flatten_splitLengths(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.flatten_splitLengths
    # (sz.splitLengths l).flatten = l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sz_splitLengths_l_flatten")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_flatten_splitLengths"))
    except Exception:
        pass
    return results


def _r0249_map_splitLengths_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.map_splitLengths_length
    # (sz.splitLengths l).map length = sz
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sz_splitLengths_l_map", 1)
    if args is not None:
        try:
            rhs = OVar("sz")
            results.append((rhs, "Mathlib: List_map_splitLengths_length"))
        except Exception:
            pass
    return results


def _r0250_length_splitLengths_getElem_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_splitLengths_getElem_eq
    # ((sz.splitLengths l)[i]'(by simpa)).length = sz[i]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sz_splitLengths_l_i_prime_by_simpa_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("sz_i")
            results.append((rhs, "Mathlib: List_length_splitLengths_getElem_eq"))
    except Exception:
        pass
    return results


def _r0251_splitLengths_length_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitLengths_length_getElem
    # (sz.splitLengths l)[i].length = sz[i]'(by simpa using hi)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sz_splitLengths_l_i_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("sz_i_prime_by_simpa_using_hi")
            results.append((rhs, "Mathlib: List_splitLengths_length_getElem"))
    except Exception:
        pass
    return results


def _r0252_length_sublists(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_sublists
    # length (sublists l) = 2 ^ length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OLit(2), OOp("len", (OVar("l"),))))
            results.append((rhs, "Mathlib: List_length_sublists"))
        except Exception:
            pass
    return results


def _r0253_sublistsLenAux_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsLenAux_zero
    # sublistsLenAux 0 l f r = f [] :: r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublistsLenAux", 4)
    if args is not None:
        try:
            rhs = OOp("f", (OSeq(()), OVar("colon_colon"), args[3],))
            results.append((rhs, "Mathlib: List_sublistsLenAux_zero"))
        except Exception:
            pass
    return results


def _r0254_sublistsLen_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsLen_zero
    # sublistsLen 0 l = [[]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublistsLen", 2)
    if args is not None:
        try:
            rhs = OSeq((OSeq(()),))
            results.append((rhs, "Mathlib: List_sublistsLen_zero"))
        except Exception:
            pass
    return results


def _r0255_length_sublistsLen(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_sublistsLen
    # ∀ (n) (l : List α), length (sublistsLen n l) = Nat.choose (length l) n   | 0, l =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("Nat_choose", (OOp("len", (OVar("l"),)), OVar("n"), OVar("pipe"), OVar("_0"), OVar("l"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_length_sublistsLen"))
        except Exception:
            pass
    return results


def _r0256_length_of_sublistsLen(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_of_sublistsLen
    # ∀ {n} {l l' : List α}, l' ∈ sublistsLen n l → length l' = n   | 0, l, l', h =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("pipe"), OVar("_0"), OVar("l"), args[0], OVar("h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_length_of_sublistsLen"))
        except Exception:
            pass
    return results


def _r0257_mem_sublistsLen(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_sublistsLen
    # l' ∈ sublistsLen n l ↔ l' <+ l ∧ length l' = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: List_mem_sublistsLen"))
        except Exception:
            pass
    return results


def _r0258_sublistsLen_of_length_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsLen_of_length_lt
    # sublistsLen n l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublistsLen", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_sublistsLen_of_length_lt"))
        except Exception:
            pass
    return results


def _r0259_sublistsLen_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsLen_length
    # ∀ l : List α, sublistsLen l.length l = [l]   | [] => rfl   | a :: l =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublistsLen", 2)
    if args is not None:
        try:
            rhs = OOp("l", (OVar("pipe"), OSeq(()), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a"), OVar("colon_colon"), args[1], OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_sublistsLen_length"))
        except Exception:
            pass
    return results


def _r0260_dedup_sym2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_sym2
    # xs.sym2.dedup = xs.dedup.sym2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("xs_sym2_dedup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("xs_dedup_sym2")
            results.append((rhs, "Mathlib: List_dedup_sym2"))
    except Exception:
        pass
    return results


def _r0261_length_sym2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_sym2
    # xs.sym2.length = Nat.choose (xs.length + 1) 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("xs_sym2_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Nat_choose", (OOp("+", (OVar("xs_length"), OLit(1))), OLit(2),))
            results.append((rhs, "Mathlib: List_length_sym2"))
    except Exception:
        pass
    return results


def _r0262_take_one_drop_eq_of_lt_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.take_one_drop_eq_of_lt_length
    # (l.drop n).take 1 = [l.get ⟨n, h⟩]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_drop_n_take", 1)
    if args is not None:
        try:
            rhs = OVar("l_get_n_h")
            results.append((rhs, "Mathlib: List_take_one_drop_eq_of_lt_length"))
        except Exception:
            pass
    return results


def _r0263_take_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.take_eq_self_iff
    # x.take n = x ↔ x.length ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_take", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OVar("x"), OVar("x_length"))), args[0]))
            results.append((rhs, "Mathlib: List_take_eq_self_iff"))
        except Exception:
            pass
    return results


def _r0264_cons_getElem_drop_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cons_getElem_drop_succ
    # l[n] :: l.drop (n + 1) = l.drop n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_n", 3)
    if args is not None:
        try:
            rhs = OOp("l_drop", (OVar("n"),))
            results.append((rhs, "Mathlib: List_cons_getElem_drop_succ"))
        except Exception:
            pass
    return results


def _r0265_drop_length_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.drop_length_sub_one
    # l.drop (l.length - 1) = [l.getLast h]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_drop", 1)
    if args is not None:
        try:
            rhs = OSeq((OOp("l_getLast", (OVar("h"),)),))
            results.append((rhs, "Mathlib: List_drop_length_sub_one"))
        except Exception:
            pass
    return results


def _r0266_takeI_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.takeI_length
    # ∀ n l, length (@takeI α _ n l) = n   | 0, _ => rfl   | _ + 1, _ => congr_arg succ (takeI_length _ _)  @[simp] theorem ta
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "takeI", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("+", (OOp("take", (args[0], args[1], OVar("pipe"), OVar("_0"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"),)), OOp("_1", (OVar("_unknown"), OVar("colon_colon"), OVar("_unknown"), OVar("h"), OVar("eq_gt"), OVar("congr_arg"), OOp("cons", (OVar("_unknown"),)), OVar("lt_pipe"), OVar("takeI_eq_take"), OVar("lt_pipe"), OVar("le_of_succ_le_succ"), OVar("h_at_simp_theorem"), OVar("takeI_left"), OOp("l_1", (OVar("l_2"), OVar("colon"), OVar("List"), OVar("a"),)), OVar("colon"), OVar("takeI"), OOp("len", (OVar("l_1"),)), OOp("concat", (OVar("l_1"), OVar("l_2"))),)))), OVar("l_1")))
            results.append((rhs, "Mathlib: List_takeI_length"))
        except Exception:
            pass
    return results


def _r0267_takeI_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.takeI_nil
    # ∀ n, takeI n (@nil α) = replicate n default   | 0 => rfl   | _ + 1 => congr_arg (cons _) (takeI_nil _)  theorem takeI_eq
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "takeI", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("+", (OOp("take", (args[0], args[1], OVar("pipe"), OVar("_0"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"),)), OOp("_1", (OVar("_unknown"), OVar("colon_colon"), OVar("_unknown"), OVar("h"), OVar("eq_gt"), OVar("congr_arg"), OOp("cons", (OVar("_unknown"),)), OVar("lt_pipe"), OVar("takeI_eq_take"), OVar("lt_pipe"), OVar("le_of_succ_le_succ"), OVar("h_at_simp_theorem"), OVar("takeI_left"), OOp("l_1", (OVar("l_2"), OVar("colon"), OVar("List"), OVar("a"),)), OVar("colon"), OVar("takeI"), OOp("len", (OVar("l_1"),)), OOp("concat", (OVar("l_1"), OVar("l_2"))),)))), OVar("l_1")))
            results.append((rhs, "Mathlib: List_takeI_nil"))
        except Exception:
            pass
    return results


def _r0268_takeI_eq_take(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.takeI_eq_take
    # ∀ {n} {l : List α}, n ≤ length l → takeI n l = take n l   | 0, _, _ => rfl   | _ + 1, _ :: _, h => congr_arg (cons _) <|
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "takeI", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("+", (OOp("take", (args[0], args[1], OVar("pipe"), OVar("_0"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"),)), OOp("_1", (OVar("_unknown"), OVar("colon_colon"), OVar("_unknown"), OVar("h"), OVar("eq_gt"), OVar("congr_arg"), OOp("cons", (OVar("_unknown"),)), OVar("lt_pipe"), OVar("takeI_eq_take"), OVar("lt_pipe"), OVar("le_of_succ_le_succ"), OVar("h_at_simp_theorem"), OVar("takeI_left"), OOp("l_1", (OVar("l_2"), OVar("colon"), OVar("List"), OVar("a"),)), OVar("colon"), OVar("takeI"), OOp("len", (OVar("l_1"),)), OOp("concat", (OVar("l_1"), OVar("l_2"))),)))), OVar("l_1")))
            results.append((rhs, "Mathlib: List_takeI_eq_take"))
        except Exception:
            pass
    return results


def _r0269_takeI_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.takeI_left
    # takeI (length l₁) (l₁ ++ l₂) = l₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "takeI", 2)
    if args is not None:
        try:
            rhs = OVar("l_1")
            results.append((rhs, "Mathlib: List_takeI_left"))
        except Exception:
            pass
    return results


def _r0270_dropWhile_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dropWhile_eq_self_iff
    # dropWhile p l = l ↔ ∀ hl : 0 < l.length, ¬p (l[0]'hl)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dropWhile", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("iff", (args[1], OOp("forall", (OVar("hl"), OVar("colon"), OLit(0),)))), OOp("l_length", (OOp("not", (args[0],)), OVar("l_0_primehl"),))))
            results.append((rhs, "Mathlib: List_dropWhile_eq_self_iff"))
        except Exception:
            pass
    return results


def _r0271_takeWhile_eq_nil_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.takeWhile_eq_nil_iff
    # takeWhile p l = [] ↔ ∀ hl : 0 < l.length, ¬p (l.get ⟨0, hl⟩)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "takeWhile", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("iff", (OSeq(()), OOp("forall", (OVar("hl"), OVar("colon"), OLit(0),)))), OOp("l_length", (OOp("not", (args[0],)), OOp("l_get", (OVar("_0_hl"),)),))))
            results.append((rhs, "Mathlib: List_takeWhile_eq_nil_iff"))
        except Exception:
            pass
    return results


def _r0272_toFinsupp_apply_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_apply_lt
    # l.toFinsupp n = l[n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toFinsupp", 1)
    if args is not None:
        try:
            rhs = OVar("l_n")
            results.append((rhs, "Mathlib: List_toFinsupp_apply_lt"))
        except Exception:
            pass
    return results


def _r0273_toFinsupp_apply_fin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_apply_fin
    # l.toFinsupp n = l[n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toFinsupp", 1)
    if args is not None:
        try:
            rhs = OVar("l_n")
            results.append((rhs, "Mathlib: List_toFinsupp_apply_fin"))
        except Exception:
            pass
    return results


def _r0274_toFinsupp_apply_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_apply_le
    # l.toFinsupp n = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toFinsupp", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: List_toFinsupp_apply_le"))
        except Exception:
            pass
    return results


def _r0275_toFinsupp_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_append
    # toFinsupp (l₁ ++ l₂) =       toFinsupp l₁ + (toFinsupp l₂).embDomain (addLeftEmbedding l₁.length)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("toFinsupp", (OVar("l_1"),)), OOp("toFinsupp_l_2_embDomain", (OOp("addLeftEmbedding", (OVar("l_1_length"),)),))))
            results.append((rhs, "Mathlib: List_toFinsupp_append"))
        except Exception:
            pass
    return results


def _r0276_toFinsupp_concat_eq_toFinsupp_add_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_concat_eq_toFinsupp_add_single
    # toFinsupp (xs ++ [x]) = toFinsupp xs + Finsupp.single xs.length x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("toFinsupp", (OVar("xs"),)), OOp("Finsupp_single", (OVar("xs_length"), OVar("x"),))))
            results.append((rhs, "Mathlib: List_toFinsupp_concat_eq_toFinsupp_add_single"))
        except Exception:
            pass
    return results


def _r0277_length_revzip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_revzip
    # length (revzip l) = length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("l"),))
            results.append((rhs, "Mathlib: List_length_revzip"))
        except Exception:
            pass
    return results


def _r0278_toFinsupp_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_sum
    # l.toFinsupp.sum (fun _ a ↦ a) = l.sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toFinsupp_sum", 1)
    if args is not None:
        try:
            rhs = OVar("l_sum")
            results.append((rhs, "Mathlib: List_toFinsupp_sum"))
        except Exception:
            pass
    return results


def _r0279_mem_fixedLengthDigits_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_fixedLengthDigits_iff
    # L ∈ fixedLengthDigits hb l ↔ L.length = l ∧ ∀ x ∈ L, x < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("and", (OVar("l"), OOp("in", (OOp("forall", (OVar("x"),)), OOp("L", (OVar("x"),)))))), OVar("b")))
            results.append((rhs, "Mathlib: List_mem_fixedLengthDigits_iff"))
        except Exception:
            pass
    return results


def _r0280_fixedLengthDigits_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.fixedLengthDigits_zero
    # fixedLengthDigits hb 0 = {[]}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fixedLengthDigits", 2)
    if args is not None:
        try:
            rhs = OVar("_unknown")
            results.append((rhs, "Mathlib: List_fixedLengthDigits_zero"))
        except Exception:
            pass
    return results


def _r0281_fixedLengthDigits_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.fixedLengthDigits_one
    # fixedLengthDigits hb 1 = Finset.image (fun x : ℕ ↦ [x]) (Finset.range b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fixedLengthDigits", 2)
    if args is not None:
        try:
            rhs = OOp("Finset_image", (OOp("fun", (OVar("x"), OVar("colon"), OVar("_unknown"), OVar("_unknown"), OSeq((OVar("x"),)),)), OOp("range", (OVar("b"),)),))
            results.append((rhs, "Mathlib: List_fixedLengthDigits_one"))
        except Exception:
            pass
    return results


def _r0282_fixedLengthDigits_succ_eq_disjiUnion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.fixedLengthDigits_succ_eq_disjiUnion
    # fixedLengthDigits hb (l + 1) = Finset.disjiUnion (Finset.range b)       (consFixedLengthDigits hb l) (pairwiseDisjoint_c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fixedLengthDigits", 2)
    if args is not None:
        try:
            rhs = OOp("Finset_disjiUnion", (OOp("range", (OVar("b"),)), OOp("consFixedLengthDigits", (args[0], OVar("l"),)), OOp("pairwiseDisjoint_consFixedLengthDigits", (args[0], OVar("l"),)),))
            results.append((rhs, "Mathlib: List_fixedLengthDigits_succ_eq_disjiUnion"))
        except Exception:
            pass
    return results


def _r0283_sum_fixedLengthDigits_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sum_fixedLengthDigits_sum
    # ∑ L ∈ fixedLengthDigits hb l, L.sum = l * b ^ (l - 1) * b.choose 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("l"), OOp("*", (OOp("**", (OVar("b"), OOp("-", (OVar("l"), OLit(1))))), OOp("b_choose", (OLit(2),))))))
            results.append((rhs, "Mathlib: List_sum_fixedLengthDigits_sum"))
        except Exception:
            pass
    return results


def _r0284_fst_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.TProd.fst_mk
    # (TProd.mk (i :: l) f).1 = f i
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("TProd_mk_i_colon_colon_l_f_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("i"),))
            results.append((rhs, "Mathlib: List_TProd_fst_mk"))
    except Exception:
        pass
    return results


def _r0285_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.TProd.ext
    # ∀ {l : List ι} (_ : l.Nodup) {v w : TProd α l}       (_ : ∀ (i) (hi : i ∈ l), v.elim hi = w.elim hi), v = w   | [], _, v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_elim", 1)
    if args is not None:
        try:
            rhs = OOp("w_elim", (OVar("hi_v_eq_w_pipe_v_w_eq_gt_PUnit_ext_v_w_pipe_i_colon_colon_is_hl_v_w_hvw_eq_gt"),))
            results.append((rhs, "Mathlib: List_TProd_ext"))
        except Exception:
            pass
    return results


def _r0286_toList_asString(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toList_asString
    # (ofList l).toList = l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofList_l_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_toList_asString"))
    except Exception:
        pass
    return results


def _r0287_asString_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.asString_eq
    # ofList l = s ↔ l = s.toList
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("s"), args[0])), OVar("s_toList")))
            results.append((rhs, "Mathlib: List_asString_eq"))
        except Exception:
            pass
    return results


def _r0288_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.ext
    # ∀ {v w : Vector α n} (_ : ∀ m : Fin n, Vector.get v m = Vector.get w m), v = w   | ⟨v, hv⟩, ⟨w, hw⟩, h =>     Subtype.ex
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Vector_get", 2)
    if args is not None:
        try:
            rhs = OOp("Vector_get", (OVar("w"), OVar("m_v_eq_w_pipe_v"), OVar("hv_w"), OVar("hw_h_eq_gt_Subtype_ext_List_ext_get"), OOp("by", (OVar("rw"), OVar("hv_hw"),)), OVar("fun"), args[1], OVar("hm"), OVar("_unknown"), OVar("eq_gt"), OVar("h"), OVar("m_hv_hm_instance_zero_subsingleton_colon_Subsingleton_Vector"), OVar("a"), OVar("_0"),))
            results.append((rhs, "Mathlib: List_Vector_ext"))
        except Exception:
            pass
    return results


def _r0289_toList_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.toList_ofFn
    # ∀ {n} (f : Fin n → α), toList (ofFn f) = List.ofFn f   | 0, f =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 1)
    if args is not None:
        try:
            rhs = OOp("List_ofFn", (OVar("f"), OVar("pipe"), OVar("_0"), OVar("f"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_Vector_toList_ofFn"))
        except Exception:
            pass
    return results


def _r0290_mk_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.mk_toList
    # ∀ (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v   | ⟨_, _⟩, _ => rfl   @[simp] theorem length_val (v : Vector α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList_v_h", 4)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("v", (OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl_at_simp"), OVar("theorem"), OVar("length_val"), OOp("v", (args[0], args[1], args[2], args[3],)), args[0], OVar("v_val_length"),)), args[3]))
            results.append((rhs, "Mathlib: List_Vector_mk_toList"))
        except Exception:
            pass
    return results


def _r0291_length_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.length_val
    # v.val.length = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_val_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: List_Vector_length_val"))
    except Exception:
        pass
    return results


def _r0292_getElem_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.getElem_map
    # (v.map f)[i] = f v[i]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_map_f_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("v_i"),))
            results.append((rhs, "Mathlib: List_Vector_getElem_map"))
    except Exception:
        pass
    return results


def _r0293_getElem_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.getElem_pmap
    # (v.pmap f hp)[i] = f v[i] (hp _ (by simp [getElem_def, List.getElem_mem]))
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_pmap_f_hp_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("v_i"), OOp("hp", (OVar("_unknown"), OOp("by", (OVar("simp"), OVar("getElem_def_List_getElem_mem"),)),)),))
            results.append((rhs, "Mathlib: List_Vector_getElem_pmap"))
    except Exception:
        pass
    return results


def _r0294_get_eq_get_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.get_eq_get_toList
    # v.get i = v.toList.get (Fin.cast v.toList_length.symm i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_get", 1)
    if args is not None:
        try:
            rhs = OOp("get", (OOp("Fin_cast", (OVar("v_toList_length_symm"), args[0],)),))
            results.append((rhs, "Mathlib: List_Vector_get_eq_get_toList"))
        except Exception:
            pass
    return results


def _r0295_scanl_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.scanl_val
    # ∀ {v : Vector α n}, (scanl f b v).val = List.scanl f b v.val   | _ => rfl   @[simp] theorem toList_scanl : (scanl f b v)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("scanl_f_b_v_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("List_scanl", (OVar("f"), OVar("b"), OVar("v_val"), OVar("pipe"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl_at_simp_theorem"), OVar("toList_scanl"), OVar("colon"), OVar("scanl_f_b_v_toList"),)), OOp("List_scanl", (OVar("f"), OVar("b"), OVar("v_toList"),))))
            results.append((rhs, "Mathlib: List_Vector_scanl_val"))
    except Exception:
        pass
    return results


def _r0296_toList_scanl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.toList_scanl
    # (scanl f b v).toList = List.scanl f b v.toList
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("scanl_f_b_v_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("List_scanl", (OVar("f"), OVar("b"), OVar("v_toList"),))
            results.append((rhs, "Mathlib: List_Vector_toList_scanl"))
    except Exception:
        pass
    return results


def _r0297_scanl_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.scanl_get
    # (scanl f b v).get i.succ = f ((scanl f b v).get (Fin.castSucc i)) (v.get i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "scanl_f_b_v_get", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("scanl_f_b_v_get", (OOp("Fin_castSucc", (OVar("i"),)),)), OOp("v_get", (OVar("i"),)),))
            results.append((rhs, "Mathlib: List_Vector_scanl_get"))
        except Exception:
            pass
    return results


def _r0298_replicate_succ_to_snoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.replicate_succ_to_snoc
    # replicate (n + 1) val = (replicate n val).snoc val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicate", 2)
    if args is not None:
        try:
            rhs = OOp("replicate_n_val_snoc", (args[1],))
            results.append((rhs, "Mathlib: List_Vector_replicate_succ_to_snoc"))
        except Exception:
            pass
    return results


def _r0299_cycleType_formPerm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cycleType_formPerm
    # cycleType l.attach.formPerm = {l.length}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleType", 1)
    if args is not None:
        try:
            rhs = OVar("l_length")
            results.append((rhs, "Mathlib: List_cycleType_formPerm"))
        except Exception:
            pass
    return results


def _r0300_formPerm_apply_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_apply_of_notMem
    # formPerm l x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: List_formPerm_apply_of_notMem"))
        except Exception:
            pass
    return results


def _r0301_formPerm_apply_getElem_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_apply_getElem_length
    # formPerm (x :: xs) (x :: xs)[xs.length] = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: List_formPerm_apply_getElem_length"))
        except Exception:
            pass
    return results


def _r0302_formPerm_apply_getElem_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_apply_getElem_zero
    # formPerm l l[0] = l[1]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = OVar("l_1")
            results.append((rhs, "Mathlib: List_formPerm_apply_getElem_zero"))
        except Exception:
            pass
    return results


def _r0303_formPerm_apply_lt_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_apply_lt_getElem
    # formPerm xs xs[n] = xs[n + 1]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = OVar("xs_n_plus_1")
            results.append((rhs, "Mathlib: List_formPerm_apply_lt_getElem"))
        except Exception:
            pass
    return results


def _r0304_formPerm_apply_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_apply_getElem
    # formPerm xs xs[i] =       xs[(i + 1) % xs.length]'(Nat.mod_lt _ (i.zero_le.trans_lt h))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = OVar("xs_i_plus_1_xs_length_prime_Nat_mod_lt_i_zero_le_trans_lt_h")
            results.append((rhs, "Mathlib: List_formPerm_apply_getElem"))
        except Exception:
            pass
    return results


def _r0305_formPerm_pow_apply_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_pow_apply_getElem
    # (formPerm l ^ n) l[i] =       l[(i + n) % l.length]'(Nat.mod_lt _ (i.zero_le.trans_lt h))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm_l_pow_n", 1)
    if args is not None:
        try:
            rhs = OVar("l_i_plus_n_l_length_prime_Nat_mod_lt_i_zero_le_trans_lt_h")
            results.append((rhs, "Mathlib: List_formPerm_pow_apply_getElem"))
        except Exception:
            pass
    return results


def _r0306_formPerm_pow_apply_head(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_pow_apply_head
    # (formPerm (x :: l) ^ n) x =       (x :: l)[(n % (x :: l).length)]'(Nat.mod_lt _ (Nat.zero_lt_succ _))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm_x_colon_colon_l_pow_n", 1)
    if args is not None:
        try:
            rhs = OVar("x_colon_colon_l_n_x_colon_colon_l_length_prime_Nat_mod_lt_Nat_zero_lt_succ")
            results.append((rhs, "Mathlib: List_formPerm_pow_apply_head"))
        except Exception:
            pass
    return results


def _r0307_formPerm_apply_mem_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_apply_mem_eq_self_iff
    # formPerm l x = x ↔ length l ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (args[1], OOp("len", (args[0],)))), OLit(1)))
            results.append((rhs, "Mathlib: List_formPerm_apply_mem_eq_self_iff"))
        except Exception:
            pass
    return results


def _r0308_formPerm_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_eq_one_iff
    # formPerm l = 1 ↔ l.length ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OLit(1), OVar("l_length"))), OLit(1)))
            results.append((rhs, "Mathlib: List_formPerm_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0309_formPerm_eq_formPerm_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_eq_formPerm_iff
    # l.formPerm = l'.formPerm ↔ l ~r l' ∨ l.length ≤ 1 ∧ l'.length ≤ 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_formPerm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("or", (OOp("iff", (OVar("l_prime_formPerm"), OOp("l", (OVar("tilde_r"), OVar("l_prime"),)))), OVar("l_length"))), OOp("<=", (OOp("and", (OLit(1), OVar("l_prime_length"))), OLit(1)))))
            results.append((rhs, "Mathlib: List_formPerm_eq_formPerm_iff"))
    except Exception:
        pass
    return results


def _r0310_formPerm_pow_length_eq_one_of_nodup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_pow_length_eq_one_of_nodup
    # formPerm l ^ length l = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: List_formPerm_pow_length_eq_one_of_nodup"))
        except Exception:
            pass
    return results


def _r0311_toFinset_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_range
    # (List.range a).toFinset = Finset.range a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("List_range_a_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("range", (OVar("a"),))
            results.append((rhs, "Mathlib: List_toFinset_range"))
    except Exception:
        pass
    return results


def _r0312_to_ofList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.to_ofList
    # toList (ofList l) = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: Lists_to_ofList"))
        except Exception:
            pass
    return results


def _r0313_to_ofList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.to_ofList
    # toList (ofList l) = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: Lists_to_ofList"))
        except Exception:
            pass
    return results


def _r0314_of_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.of_toList
    # ∀ {l : Lists α}, IsList l → ofList (toList l) = l   | ⟨true, l⟩, _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofList", 1)
    if args is not None:
        try:
            rhs = OOp("l", (OVar("pipe"), OVar("true_l"), OVar("_unknown"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: Lists_of_toList"))
        except Exception:
            pass
    return results


def _r0315_equiv_atom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.equiv_atom
    # atom a ~ l ↔ atom a = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: Lists_equiv_atom"))
        except Exception:
            pass
    return results


def _r0316_mem_of_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.mem_of_subset
    # a ∈ l₁ → a ∈ l₂   | ⟨_, m, e⟩ => (mem_equiv_left e).2 (mem_of_subset' s m)  theorem Subset.trans {l₁ l₂ l₃ : Lists' α tr
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("subset", (OOp("gt", (OVar("mem_equiv_left_e_2"), OVar("mem_of_subset_prime_s_m_theorem"), OVar("Subset_trans"), OVar("l_1_l_2_l_3_colon_Lists_prime_a_true"), OOp("subset", (OOp("h_1", (OVar("colon"), OVar("l_1"),)), OVar("l_2"))), OOp("subset", (OOp("h_2", (OVar("colon"), OVar("l_2"),)), OVar("l_3"))), OVar("colon"), OVar("l_1"),)), OVar("l_3")))
            results.append((rhs, "Mathlib: Lists_mem_of_subset"))
        except Exception:
            pass
    return results


def _r0317_tendsto_nhds(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.tendsto_nhds
    # ∀ l, Tendsto f (𝓝 l) (r l)   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Tendsto", 5)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_tendsto_nhds"))
        except Exception:
            pass
    return results


def _r0318_continuous_insertIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.continuous_insertIdx
    # Continuous fun p : α × List α => p.2.insertIdx n p.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "product", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("p_2_insertIdx"), OVar("n"), OVar("p_1"),))
            results.append((rhs, "Mathlib: List_continuous_insertIdx"))
        except Exception:
            pass
    return results


def _r0319_tendsto_eraseIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.tendsto_eraseIdx
    # ∀ {n : ℕ} {l : List α}, Tendsto (eraseIdx · n) (𝓝 l) (𝓝 (eraseIdx l n))   | _, [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Tendsto", 6)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_tendsto_eraseIdx"))
        except Exception:
            pass
    return results


def _r0320_continuous_eraseIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.continuous_eraseIdx
    # Continuous fun l : List α => eraseIdx l n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Continuous", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("eraseIdx"), args[1], OVar("n"),))
            results.append((rhs, "Mathlib: List_continuous_eraseIdx"))
        except Exception:
            pass
    return results


def _r0321_tendsto_insertIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.tendsto_insertIdx
    # ∀ {l : Vector α n},       Tendsto (fun p : α × Vector α n => insertIdx p.1 i p.2) (𝓝 a ×ˢ 𝓝 l)         (𝓝 (insertIdx a i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Tendsto", 5)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_Vector_tendsto_insertIdx"))
        except Exception:
            pass
    return results


def _r0322_continuous_insertIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.continuous_insertIdx
    # Continuous fun b => Vector.insertIdx (f b) i (g b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Continuous", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("Vector_insertIdx"), OOp("f", (args[1],)), OVar("i"), OOp("g", (args[1],)),))
            results.append((rhs, "Mathlib: List_Vector_continuous_insertIdx"))
        except Exception:
            pass
    return results


def _r0323_continuousAt_eraseIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.continuousAt_eraseIdx
    # ∀ {l : Vector α (n + 1)}, ContinuousAt (Vector.eraseIdx i) l   | ⟨l, hl⟩ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ContinuousAt", 4)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_Vector_continuousAt_eraseIdx"))
        except Exception:
            pass
    return results


def _r0324_sbtw_pair(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sbtw_pair
    # [p₁, p₂].Sbtw R ↔ p₁ ≠ p₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_1_p_2_Sbtw", 1)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("p_1"), OVar("p_2")))
            results.append((rhs, "Mathlib: List_sbtw_pair"))
        except Exception:
            pass
    return results


def _r0325_sbtw_triple(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sbtw_triple
    # [p₁, p₂, p₃].Sbtw R ↔ Sbtw R p₁ p₂ p₃
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_1_p_2_p_3_Sbtw", 1)
    if args is not None:
        try:
            rhs = OOp("Sbtw", (args[0], OVar("p_1"), OVar("p_2"), OVar("p_3"),))
            results.append((rhs, "Mathlib: List_sbtw_triple"))
        except Exception:
            pass
    return results


def _r0326_getElem_fin_surjective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getElem_fin_surjective_iff
    # (fun (n : Fin l.length) ↦ l[n.val]).Surjective ↔ (∀ x, x ∈ l)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fun_n_colon_Fin_l_length_l_n_val_Surjective")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("forall", (OVar("x"), OVar("x"),)), OVar("l")))
            results.append((rhs, "Mathlib: List_getElem_fin_surjective_iff"))
    except Exception:
        pass
    return results


def _r0327_nodupKeys_middle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodupKeys_middle
    # (l₁ ++ s :: l₂).NodupKeys ↔ (s :: (l₁ ++ l₂)).NodupKeys
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_1_plus_plus_s_colon_colon_l_2_NodupKeys")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_colon_colon_l_1_plus_plus_l_2_NodupKeys")
            results.append((rhs, "Mathlib: List_nodupKeys_middle"))
    except Exception:
        pass
    return results


def _r0328_dlookup_isSome(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_isSome
    # (dlookup a l).isSome ↔ a ∈ l.keys
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("dlookup_a_l_isSome")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OVar("a"), OVar("l_keys")))
            results.append((rhs, "Mathlib: List_dlookup_isSome"))
    except Exception:
        pass
    return results


def _r0329_nodup_iff_injective_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.nodup_iff_injective_get
    # v.toList.Nodup ↔ Function.Injective v.get
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_toList_Nodup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("injective", (OVar("v_get"),))
            results.append((rhs, "Mathlib: List_Vector_nodup_iff_injective_get"))
    except Exception:
        pass
    return results


def _r0330_prod_isUnit_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_isUnit_iff
    # IsUnit L.prod ↔ ∀ m ∈ L, IsUnit m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsUnit", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("m"),)), OOp("L", (OVar("IsUnit"), OVar("m"),))))
            results.append((rhs, "Mathlib: List_prod_isUnit_iff"))
        except Exception:
            pass
    return results


def _r0331_mem_mem_ranges_iff_lt_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_mem_ranges_iff_lt_sum
    # (∃ s ∈ l.ranges, n ∈ s) ↔ n < l.sum
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("n"), OVar("l_sum")))
            results.append((rhs, "Mathlib: List_mem_mem_ranges_iff_lt_sum"))
        except Exception:
            pass
    return results


def _r0332_wbtw_triple(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.wbtw_triple
    # [p₁, p₂, p₃].Wbtw R ↔ Wbtw R p₁ p₂ p₃
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_1_p_2_p_3_Wbtw", 1)
    if args is not None:
        try:
            rhs = OOp("Wbtw", (args[0], OVar("p_1"), OVar("p_2"), OVar("p_3"),))
            results.append((rhs, "Mathlib: List_wbtw_triple"))
        except Exception:
            pass
    return results


def _r0333_wbtw_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.wbtw_four
    # [p₁, p₂, p₃, p₄].Wbtw R ↔     Wbtw R p₁ p₂ p₃ ∧ Wbtw R p₁ p₂ p₄ ∧ Wbtw R p₁ p₃ p₄ ∧ Wbtw R p₂ p₃ p₄
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_1_p_2_p_3_p_4_Wbtw", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("Wbtw", (args[0], OVar("p_1"), OVar("p_2"), OVar("p_3"),)), OOp("and", (OOp("Wbtw", (args[0], OVar("p_1"), OVar("p_2"), OVar("p_4"),)), OOp("and", (OOp("Wbtw", (args[0], OVar("p_1"), OVar("p_3"), OVar("p_4"),)), OOp("Wbtw", (args[0], OVar("p_2"), OVar("p_3"), OVar("p_4"),))))))))
            results.append((rhs, "Mathlib: List_wbtw_four"))
        except Exception:
            pass
    return results


def _r0334_sbtw_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sbtw_four
    # [p₁, p₂, p₃, p₄].Sbtw R ↔     Sbtw R p₁ p₂ p₃ ∧ Sbtw R p₁ p₂ p₄ ∧ Sbtw R p₁ p₃ p₄ ∧ Sbtw R p₂ p₃ p₄
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_1_p_2_p_3_p_4_Sbtw", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("Sbtw", (args[0], OVar("p_1"), OVar("p_2"), OVar("p_3"),)), OOp("and", (OOp("Sbtw", (args[0], OVar("p_1"), OVar("p_2"), OVar("p_4"),)), OOp("and", (OOp("Sbtw", (args[0], OVar("p_1"), OVar("p_3"), OVar("p_4"),)), OOp("Sbtw", (args[0], OVar("p_2"), OVar("p_3"), OVar("p_4"),))))))))
            results.append((rhs, "Mathlib: List_sbtw_four"))
        except Exception:
            pass
    return results


def _r0335_sbtw_iff_triplewise_and_ne_pair(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sbtw_iff_triplewise_and_ne_pair
    # l.Sbtw R ↔ l.Triplewise (Sbtw R) ∧ ∀ a, l ≠ [a, a]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_Sbtw", 1)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OOp("l_Triplewise", (OOp("Sbtw", (args[0],)),)), OOp("forall", (OVar("a"), OVar("l"),)))), OVar("a_a")))
            results.append((rhs, "Mathlib: List_sbtw_iff_triplewise_and_ne_pair"))
        except Exception:
            pass
    return results


def _r0336_all_iff_forall_prop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.all_iff_forall_prop
    # (all l fun a => p a) ↔ ∀ a ∈ l, p a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "all", 6)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (args[5],)), OOp("l", (args[4], args[5],))))
            results.append((rhs, "Mathlib: List_all_iff_forall_prop"))
        except Exception:
            pass
    return results


def _r0337_any_iff_exists_prop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.any_iff_exists_prop
    # (any l fun a => p a) ↔ ∃ a ∈ l, p a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "any", 6)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (args[5],)), OOp("l", (args[4], args[5],))))
            results.append((rhs, "Mathlib: List_any_iff_exists_prop"))
        except Exception:
            pass
    return results


def _r0338_disjoint_toFinset_iff_disjoint(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.disjoint_toFinset_iff_disjoint
    # _root_.Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "root_Disjoint", 2)
    if args is not None:
        try:
            rhs = OOp("l_Disjoint", (OVar("l_prime"),))
            results.append((rhs, "Mathlib: List_disjoint_toFinset_iff_disjoint"))
        except Exception:
            pass
    return results


def _r0339_pairwise_iff_coe_toFinset_pairwise(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.pairwise_iff_coe_toFinset_pairwise
    # (l.toFinset : Set α).Pairwise r ↔ l.Pairwise r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toFinset_colon_Set_a_Pairwise", 1)
    if args is not None:
        try:
            rhs = OOp("l_Pairwise", (args[0],))
            results.append((rhs, "Mathlib: List_pairwise_iff_coe_toFinset_pairwise"))
        except Exception:
            pass
    return results


def _r0340_pairwiseDisjoint_iff_coe_toFinset_pairwi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint
    # (l.toFinset : Set ι).PairwiseDisjoint f ↔ l.Pairwise (_root_.Disjoint on f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toFinset_colon_Set_i_PairwiseDisjoint", 1)
    if args is not None:
        try:
            rhs = OOp("l_Pairwise", (OOp("root_Disjoint", (OVar("on"), args[0],)),))
            results.append((rhs, "Mathlib: List_pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint"))
        except Exception:
            pass
    return results


def _r0341_exists_mem_and_apply_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Function.Involutive.exists_mem_and_apply_eq_iff
    # (∃ y : α, y ∈ l ∧ f y = x) ↔ f x ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("f", (args[1],)), OVar("l")))
            results.append((rhs, "Mathlib: Function_Involutive_exists_mem_and_apply_eq_iff"))
        except Exception:
            pass
    return results


def _r0342_length_pos_iff_ne_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_pos_iff_ne_nil
    # 0 < length l ↔ l ≠ []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("l"), OSeq(())))
            results.append((rhs, "Mathlib: List_length_pos_iff_ne_nil"))
        except Exception:
            pass
    return results


def _r0343_length_injective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.length_injective_iff
    # Injective (List.length : List α → ℕ) ↔ Subsingleton α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 1)
    if args is not None:
        try:
            rhs = OOp("Subsingleton", (OVar("a"),))
            results.append((rhs, "Mathlib: List_length_injective_iff"))
        except Exception:
            pass
    return results


def _r0344_exists_mem_iff_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_mem_iff_getElem
    # (∃ x ∈ l, p x) ↔ ∃ (i : ℕ) (_ : i < l.length), p l[i]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("exists", (OOp("i", (OVar("colon"), OVar("_unknown"),)), OVar("colon_i_lt_l_length"), OVar("p"), OVar("l_i"),))
            results.append((rhs, "Mathlib: List_exists_mem_iff_getElem"))
        except Exception:
            pass
    return results


def _r0345_exists_mem_iff_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_mem_iff_get
    # (∃ x ∈ l, p x) ↔ ∃ (i : Fin l.length), p (l.get i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("exists", (OVar("i_colon_Fin_l_length"), OVar("p"), OOp("l_get", (OVar("i"),)),))
            results.append((rhs, "Mathlib: List_exists_mem_iff_get"))
        except Exception:
            pass
    return results


def _r0346_forall_mem_iff_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall_mem_iff_getElem
    # (∀ x ∈ l, p x) ↔ ∀ (i : ℕ) (_ : i < l.length), p l[i]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("forall", (OOp("i", (OVar("colon"), OVar("_unknown"),)), OVar("colon_i_lt_l_length"), OVar("p"), OVar("l_i"),))
            results.append((rhs, "Mathlib: List_forall_mem_iff_getElem"))
        except Exception:
            pass
    return results


def _r0347_forall_mem_iff_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall_mem_iff_get
    # (∀ x ∈ l, p x) ↔ ∀ (i : Fin l.length), p (l.get i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("i_colon_Fin_l_length"), OVar("p"), OOp("l_get", (OVar("i"),)),))
            results.append((rhs, "Mathlib: List_forall_mem_iff_get"))
        except Exception:
            pass
    return results


def _r0348_get_surjective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_surjective_iff
    # l.get.Surjective ↔ (∀ x, x ∈ l)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_get_Surjective")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("forall", (OVar("x"), OVar("x"),)), OVar("l")))
            results.append((rhs, "Mathlib: List_get_surjective_iff"))
    except Exception:
        pass
    return results


def _r0349_mem_iff_idxOf_lt_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsPrefix.mem_iff_idxOf_lt_length
    # a ∈ l₁ ↔ l₂.idxOf a < l₁.length
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("l_2_idxOf", (args[0],)), OVar("l_1_length")))
            results.append((rhs, "Mathlib: List_IsPrefix_mem_iff_idxOf_lt_length"))
        except Exception:
            pass
    return results


def _r0350_mem_dropLast_iff_idxOf_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_dropLast_iff_idxOf_lt
    # a ∈ l.dropLast ↔ l.idxOf a < l.length - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("l_idxOf", (args[0],)), OOp("-", (OVar("l_length"), OLit(1)))))
            results.append((rhs, "Mathlib: List_mem_dropLast_iff_idxOf_lt"))
        except Exception:
            pass
    return results


def _r0351_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.iff
    # IsChain R l ↔ IsChain S l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("IsChain", (OVar("S"), args[1],))
            results.append((rhs, "Mathlib: List_IsChain_iff"))
        except Exception:
            pass
    return results


def _r0352_isChain_pair(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_pair
    # IsChain R [x, y] ↔ R x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("R", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: List_isChain_pair"))
        except Exception:
            pass
    return results


def _r0353_isChain_split(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_split
    # IsChain R (l₁ ++ c :: l₂) ↔ IsChain R (l₁ ++ [c]) ∧ IsChain R (c :: l₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsChain", (args[0], OOp("concat", (OVar("l_1"), OSeq((OVar("c"),)))),)), OOp("IsChain", (args[0], OOp("c", (OVar("colon_colon"), OVar("l_2"),)),))))
            results.append((rhs, "Mathlib: List_isChain_split"))
        except Exception:
            pass
    return results


def _r0354_isChain_iff_forall_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_iff_forall₂
    # IsChain R l ↔ Forall₂ R l.dropLast l.tail
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("Forall_2", (args[0], OVar("l_dropLast"), OVar("l_tail"),))
            results.append((rhs, "Mathlib: List_isChain_iff_forall_2"))
        except Exception:
            pass
    return results


def _r0355_isChain_iff_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_iff_get
    # ∀ {l : List α}, IsChain R l ↔     ∀ (i : Fin (l.length.pred)),     haveI H
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("i_colon_Fin_l_length_pred"), OVar("haveI"), OVar("H"),))
            results.append((rhs, "Mathlib: List_isChain_iff_get"))
        except Exception:
            pass
    return results


def _r0356_isChain_cons_iff_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons_iff_get
    # IsChain R (a :: l) ↔     ∀ (i : Fin l.length), R ((a :: l).get i.castSucc) ((a :: l).get i.succ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("i_colon_Fin_l_length"), args[0], OOp("a_colon_colon_l_get", (OVar("i_castSucc"),)), OOp("a_colon_colon_l_get", (OVar("i_succ"),)),))
            results.append((rhs, "Mathlib: List_isChain_cons_iff_get"))
        except Exception:
            pass
    return results


def _r0357_isChain_attachWith(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_attachWith
    # (l.attachWith p h).IsChain r ↔ l.IsChain fun a b ↦ ∃ ha hb, r ⟨a, ha⟩ ⟨b, hb⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_attachWith_p_h_IsChain", 1)
    if args is not None:
        try:
            rhs = OOp("l_IsChain", (OVar("fun"), OVar("a"), OVar("b"), OVar("_unknown"), OVar("exists"), OVar("ha"), OVar("hb"), args[0], OVar("a_ha"), OVar("b_hb"),))
            results.append((rhs, "Mathlib: List_isChain_attachWith"))
        except Exception:
            pass
    return results


def _r0358_isChain_attach(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_attach
    # l.attach.IsChain r ↔ l.IsChain fun a b ↦ ∃ ha hb, r ⟨a, ha⟩ ⟨b, hb⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_attach_IsChain", 1)
    if args is not None:
        try:
            rhs = OOp("l_IsChain", (OVar("fun"), OVar("a"), OVar("b"), OVar("_unknown"), OVar("exists"), OVar("ha"), OVar("hb"), args[0], OVar("a_ha"), OVar("b_hb"),))
            results.append((rhs, "Mathlib: List_isChain_attach"))
        except Exception:
            pass
    return results


def _r0359_isChain_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_ofFn
    # (ofFn f).IsChain r ↔ ∀ (i) (hi : i + 1 < n), r (f ⟨i, lt_of_succ_lt hi⟩) (f ⟨i + 1, hi⟩)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn_f_IsChain", 1)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("i"), OVar("hi_colon_i_plus_1_lt_n"), args[0], OOp("f", (OVar("i_lt_of_succ_lt_hi"),)), OOp("f", (OVar("i_plus_1_hi"),)),))
            results.append((rhs, "Mathlib: List_isChain_ofFn"))
        except Exception:
            pass
    return results


def _r0360_count_lt_length_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_lt_length_iff
    # l.count a < l.length ↔ ∃ b ∈ l, b ≠ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("in", (OOp("exists", (OVar("b"),)), OOp("l", (OVar("b"),)))), OVar("a")))
            results.append((rhs, "Mathlib: List_count_lt_length_iff"))
        except Exception:
            pass
    return results


def _r0361_duplicate_iff_sublist(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.duplicate_iff_sublist
    # x ∈+ l ↔ [x, x] <+ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("x_x", (OVar("lt_plus"), args[1],))
            results.append((rhs, "Mathlib: List_duplicate_iff_sublist"))
        except Exception:
            pass
    return results


def _r0362_nodup_iff_forall_not_duplicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_iff_forall_not_duplicate
    # Nodup l ↔ ∀ x : α, ¬x ∈+ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("x"), OVar("colon"), OVar("a"), OOp("not", (OVar("x"),)), OVar("in_plus"), args[0],))
            results.append((rhs, "Mathlib: List_nodup_iff_forall_not_duplicate"))
        except Exception:
            pass
    return results


def _r0363_exists_duplicate_iff_not_nodup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_duplicate_iff_not_nodup
    # (∃ x : α, x ∈+ l) ↔ ¬Nodup l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 6)
    if args is not None:
        try:
            rhs = OOp("not_Nodup", (args[5],))
            results.append((rhs, "Mathlib: List_exists_duplicate_iff_not_nodup"))
        except Exception:
            pass
    return results


def _r0364_forall_mem_zipIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall_mem_zipIdx
    # (∀ x ∈ l.zipIdx n, p x) ↔ ∀ (i : ℕ) (_ : i < length l), p (l[i], n + i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("forall", (OOp("i", (OVar("colon"), OVar("_unknown"),)), OVar("colon_i_lt_length_l"), OVar("p"), OOp("+", (OOp("l_i", (OVar("n"),)), OVar("i"))),))
            results.append((rhs, "Mathlib: List_forall_mem_zipIdx"))
        except Exception:
            pass
    return results


def _r0365_exists_mem_zipIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_mem_zipIdx
    # (∃ x ∈ l.zipIdx n, p x) ↔ ∃ (i : ℕ) (_ : i < length l), p (l[i], n + i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("exists", (OOp("i", (OVar("colon"), OVar("_unknown"),)), OVar("colon_i_lt_length_l"), OVar("p"), OOp("+", (OOp("l_i", (OVar("n"),)), OVar("i"))),))
            results.append((rhs, "Mathlib: List_exists_mem_zipIdx"))
        except Exception:
            pass
    return results


def _r0366_nodup_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_ofFn
    # Nodup (ofFn f) ↔ Function.Injective f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("injective", (OVar("f"),))
            results.append((rhs, "Mathlib: List_nodup_ofFn"))
        except Exception:
            pass
    return results


def _r0367_forall_2_reverse_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall₂_reverse_iff
    # Forall₂ R (reverse l₁) (reverse l₂) ↔ Forall₂ R l₁ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2", 3)
    if args is not None:
        try:
            rhs = OOp("Forall_2", (args[0], OVar("l_1"), OVar("l_2"),))
            results.append((rhs, "Mathlib: List_forall_2_reverse_iff"))
        except Exception:
            pass
    return results


def _r0368_sublistForall_2_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistForall₂_iff
    # SublistForall₂ R l₁ l₂ ↔ ∃ l, Forall₂ R l₁ l ∧ l <+ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "SublistForall_2", 3)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("exists", (OVar("l"), OVar("Forall_2"), args[0], args[1], OVar("l"),)), OOp("l", (OVar("lt_plus"), args[2],))))
            results.append((rhs, "Mathlib: List_sublistForall_2_iff"))
        except Exception:
            pass
    return results


def _r0369_sublistForall_2_map_left_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistForall₂_map_left_iff
    # SublistForall₂ R (map f l₁) l₂ ↔ SublistForall₂ (fun c b => R (f c) b) l₁ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "SublistForall_2", 3)
    if args is not None:
        try:
            rhs = OOp("SublistForall_2", (OOp("fun", (OVar("c"), OVar("b"), OVar("eq_gt"), args[0], OOp("f", (OVar("c"),)), OVar("b"),)), OVar("l_1"), args[2],))
            results.append((rhs, "Mathlib: List_sublistForall_2_map_left_iff"))
        except Exception:
            pass
    return results


def _r0370_sublistForall_2_map_right_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistForall₂_map_right_iff
    # SublistForall₂ R l₁ (map f l₂) ↔ SublistForall₂ (fun a c => R a (f c)) l₁ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "SublistForall_2", 3)
    if args is not None:
        try:
            rhs = OOp("SublistForall_2", (OOp("fun", (OVar("a"), OVar("c"), OVar("eq_gt"), args[0], OVar("a"), OOp("f", (OVar("c"),)),)), args[1], OVar("l_2"),))
            results.append((rhs, "Mathlib: List_sublistForall_2_map_right_iff"))
        except Exception:
            pass
    return results


def _r0371_getD_surjective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getD_surjective_iff
    # (l.getD · d).Surjective ↔ (∀ x, x = d ∨ x ∈ l)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_getD_d_Surjective")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("forall", (OVar("x"), OVar("x"),)), OOp("or", (OVar("d"), OOp("in", (OVar("x"), OVar("l")))))))
            results.append((rhs, "Mathlib: List_getD_surjective_iff"))
    except Exception:
        pass
    return results


def _r0372_isPrefix_append_of_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isPrefix_append_of_length
    # l₁ <+: l₂ ++ l₃ ↔ l₁ <+: l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OOp("l_1", (OVar("lt_plus_colon"), OVar("l_2"),))
            results.append((rhs, "Mathlib: List_isPrefix_append_of_length"))
        except Exception:
            pass
    return results


def _r0373_take_isPrefix_take(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.take_isPrefix_take
    # l.take m <+: l.take n ↔ m ≤ n ∨ l.length ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_take", 4)
    if args is not None:
        try:
            rhs = OOp("<=", (args[0], OOp("<=", (OOp("or", (args[3], OVar("l_length"))), args[3]))))
            results.append((rhs, "Mathlib: List_take_isPrefix_take"))
        except Exception:
            pass
    return results


def _r0374_lex_cons_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lex_cons_iff
    # Lex r (a :: l₁) (a :: l₂) ↔ Lex r l₁ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Lex", 3)
    if args is not None:
        try:
            rhs = OOp("Lex", (args[0], OVar("l_1"), OVar("l_2"),))
            results.append((rhs, "Mathlib: List_lex_cons_iff"))
        except Exception:
            pass
    return results


def _r0375_lex_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lex_singleton_iff
    # List.Lex r [a] [b] ↔ r a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_Lex", 3)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: List_lex_singleton_iff"))
        except Exception:
            pass
    return results


def _r0376_ne_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Decidable.List.Lex.ne_iff
    # Lex (· ≠ ·) l₁ l₂ ↔ l₁ ≠ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Lex", 3)
    if args is not None:
        try:
            rhs = OOp("!=", (args[1], args[2]))
            results.append((rhs, "Mathlib: Decidable_List_Lex_ne_iff"))
        except Exception:
            pass
    return results


def _r0377_ne_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Lex.ne_iff
    # Lex (· ≠ ·) l₁ l₂ ↔ l₁ ≠ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Lex", 3)
    if args is not None:
        try:
            rhs = OOp("!=", (args[1], args[2]))
            results.append((rhs, "Mathlib: List_Lex_ne_iff"))
        except Exception:
            pass
    return results


def _r0378_lt_iff_lex_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lt_iff_lex_lt
    # List.lt l l' ↔ Lex (· < ·) l l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_lt", 2)
    if args is not None:
        try:
            rhs = OOp("Lex", (OOp("<", (OVar("_unknown"), OVar("_unknown"))), args[0], args[1],))
            results.append((rhs, "Mathlib: List_lt_iff_lex_lt"))
        except Exception:
            pass
    return results


def _r0379_nodup_iff_sublist(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_iff_sublist
    # Nodup l ↔ ∀ a, ¬[a, a] <+ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("a"), OOp("not", (OVar("a_a"),)), OVar("lt_plus"), args[0],))
            results.append((rhs, "Mathlib: List_nodup_iff_sublist"))
        except Exception:
            pass
    return results


def _r0380_nodup_iff_injective_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_iff_injective_getElem
    # Nodup l ↔ Function.Injective (fun i : Fin l.length => l[i.1])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("injective", (OOp("fun", (OVar("i"), OVar("colon"), OVar("Fin"), OVar("l_length"), OVar("eq_gt"), OVar("l_i_1"),)),))
            results.append((rhs, "Mathlib: List_nodup_iff_injective_getElem"))
        except Exception:
            pass
    return results


def _r0381_nodup_iff_injective_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_iff_injective_get
    # Nodup l ↔ Function.Injective l.get
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("injective", (OVar("l_get"),))
            results.append((rhs, "Mathlib: List_nodup_iff_injective_get"))
        except Exception:
            pass
    return results


def _r0382_nodup_middle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_middle
    # Nodup (l₁ ++ a :: l₂) ↔ Nodup (a :: (l₁ ++ l₂))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("nodup", (OOp("a", (OVar("colon_colon"), OOp("concat", (OVar("l_1"), OVar("l_2"))),)),))
            results.append((rhs, "Mathlib: List_nodup_middle"))
        except Exception:
            pass
    return results


def _r0383_nodup_attach(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_attach
    # Nodup (attach l) ↔ Nodup l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("nodup", (OVar("l"),))
            results.append((rhs, "Mathlib: List_nodup_attach"))
        except Exception:
            pass
    return results


def _r0384_nodup_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_flatten
    # Nodup (flatten L) ↔ (∀ l ∈ L, Nodup l) ∧ Pairwise Disjoint L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (OOp("forall", (OVar("l"),)), OOp("L", (OVar("Nodup"), OVar("l"),)))), OOp("Pairwise", (OVar("Disjoint"), OVar("L"),))))
            results.append((rhs, "Mathlib: List_nodup_flatten"))
        except Exception:
            pass
    return results


def _r0385_pairwise_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.pairwise_ofFn
    # (ofFn f).Pairwise R ↔ ∀ ⦃i j⦄, i < j → R (f i) (f j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn_f_Pairwise", 1)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("forall", (OVar("i"), OVar("j"), OVar("i"),)), OOp("implies", (OVar("j"), OOp("R", (OOp("f", (OVar("i"),)), OOp("f", (OVar("j"),)),))))))
            results.append((rhs, "Mathlib: List_pairwise_ofFn"))
        except Exception:
            pass
    return results


def _r0386_exists_iff_exists_tuple(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_iff_exists_tuple
    # (∃ l : List α, P l) ↔ ∃ (n : _) (f : Fin n → α), P (List.ofFn f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 6)
    if args is not None:
        try:
            rhs = OOp("exists", (OOp("n", (args[1], OVar("_unknown"),)), OVar("f_colon_Fin_n_to_a"), args[4], OOp("List_ofFn", (OVar("f"),)),))
            results.append((rhs, "Mathlib: List_exists_iff_exists_tuple"))
        except Exception:
            pass
    return results


def _r0387_forall_iff_forall_tuple(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall_iff_forall_tuple
    # (∀ l : List α, P l) ↔ ∀ (n) (f : Fin n → α), P (List.ofFn f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forall", 6)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("n"), OVar("f_colon_Fin_n_to_a"), args[4], OOp("List_ofFn", (OVar("f"),)),))
            results.append((rhs, "Mathlib: List_forall_iff_forall_tuple"))
        except Exception:
            pass
    return results


def _r0388_nodup_offDiag(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_offDiag
    # l.offDiag.Nodup ↔ l.Nodup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_offDiag_Nodup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_Nodup")
            results.append((rhs, "Mathlib: List_nodup_offDiag"))
    except Exception:
        pass
    return results


def _r0389_isChain_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_range
    # IsChain r (range n) ↔ ∀ m < n - 1, r m m.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("forall", (OVar("m"),)), OOp("-", (OVar("n"), OOp("_1", (args[0], OVar("m"), OVar("m_succ"),))))))
            results.append((rhs, "Mathlib: List_isChain_range"))
        except Exception:
            pass
    return results


def _r0390_isChain_range_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_range_succ
    # IsChain r (range n.succ) ↔ ∀ m < n, r m m.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("forall", (OVar("m"),)), OOp("n", (args[0], OVar("m"), OVar("m_succ"),))))
            results.append((rhs, "Mathlib: List_isChain_range_succ"))
        except Exception:
            pass
    return results


def _r0391_reduceOption_length_lt_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_length_lt_iff
    # l.reduceOption.length < l.length ↔ none ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("none"), OVar("l")))
            results.append((rhs, "Mathlib: List_reduceOption_length_lt_iff"))
        except Exception:
            pass
    return results


def _r0392_nodup_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_rotate
    # Nodup (l.rotate n) ↔ Nodup l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("nodup", (OVar("l"),))
            results.append((rhs, "Mathlib: List_nodup_rotate"))
        except Exception:
            pass
    return results


def _r0393_isRotated_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isRotated_comm
    # l ~r l' ↔ l' ~r l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = OOp("l_prime", (args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_isRotated_comm"))
        except Exception:
            pass
    return results


def _r0394_nodup_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsRotated.nodup_iff
    # Nodup l ↔ Nodup l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("nodup", (OVar("l_prime"),))
            results.append((rhs, "Mathlib: List_IsRotated_nodup_iff"))
        except Exception:
            pass
    return results


def _r0395_isRotated_iff_mem_map_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isRotated_iff_mem_map_range
    # l ~r l' ↔ l' ∈ (List.range (l.length + 1)).map l.rotate
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[1], OOp("List_range_l_length_plus_1_map", (OVar("l_rotate"),))))
            results.append((rhs, "Mathlib: List_isRotated_iff_mem_map_range"))
        except Exception:
            pass
    return results


def _r0396_shortlex_iff_lex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.shortlex_iff_lex
    # Shortlex r s t ↔ List.Lex r s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Shortlex", 3)
    if args is not None:
        try:
            rhs = OOp("List_Lex", (args[0], args[1], args[2],))
            results.append((rhs, "Mathlib: List_shortlex_iff_lex"))
        except Exception:
            pass
    return results


def _r0397_ne_key(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ne_key
    # a ∉ l.keys ↔ ∀ s : Sigma β, s ∈ l → a ≠ s.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not_in", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("implies", (OOp("in", (OOp("forall", (OVar("s"), OVar("colon"), OVar("Sigma"), OVar("b"), OVar("s"),)), OVar("l"))), args[0])), OVar("s_1")))
            results.append((rhs, "Mathlib: List_ne_key"))
        except Exception:
            pass
    return results


def _r0398_nodupKeys_iff_pairwise(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodupKeys_iff_pairwise
    # NodupKeys l ↔ Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NodupKeys", 1)
    if args is not None:
        try:
            rhs = OOp("Pairwise", (OOp("!=", (OOp("fun", (OVar("s"), OVar("s_prime"), OVar("colon"), OVar("Sigma"), OVar("b"), OVar("eq_gt"), OVar("s_1"),)), OVar("s_prime_1"))), args[0],))
            results.append((rhs, "Mathlib: List_nodupKeys_iff_pairwise"))
        except Exception:
            pass
    return results


def _r0399_kreplace_nodupKeys(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kreplace_nodupKeys
    # (kreplace a b l).NodupKeys ↔ l.NodupKeys
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("kreplace_a_b_l_NodupKeys")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_NodupKeys")
            results.append((rhs, "Mathlib: List_kreplace_nodupKeys"))
    except Exception:
        pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_list rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "**", "+", "-", "<", "<=", "==", "Continuous", "ContinuousAt", "Fin_repeat", "Forall_2", "Ico", "Ico_n_m_filter", "Insert_insert", "IsChain", "IsUnit", "L_flatten_take", "L_flatten_take_L_map_length_take_i_plus_1_sum_drop", "Lex", "List", "List_Lex", "List_lt", "List_nil_colon_List_a_dProd", "List_ofFn", "List_rdrop", "List_traverse", "NodupKeys", "R", "Shortlex", "SublistForall_2", "Tendsto", "Vector", "Vector_eraseIdx", "Vector_get", "_unknown", "a", "a_colon_colon_l_destutter_R_length", "all", "alternatingProd", "and", "antidiagonal", "antidiagonalTuple", "any", "argAux", "at_Finset_mk", "at_List_dProd", "at_ofFnRec", "atom", "attach",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_list axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_list rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_antidiagonalTuple_zero_succ(term, ctx))
    results.extend(_r0001_mem_antidiagonalTuple(term, ctx))
    results.extend(_r0002_toFinset_coe(term, ctx))
    results.extend(_r0003_toFinset_eq(term, ctx))
    results.extend(_r0004_coe_toFinset(term, ctx))
    results.extend(_r0005_toFinset_replicate_of_ne_zero(term, ctx))
    results.extend(_r0006_singleton_injective(term, ctx))
    results.extend(_r0007_length_eq_two(term, ctx))
    results.extend(_r0008_head_eq_getElem_zero(term, ctx))
    results.extend(_r0009_antisymm(term, ctx))
    results.extend(_r0010_idxOf_eq_length_iff(term, ctx))
    results.extend(_r0011_destutter_pair(term, ctx))
    results.extend(_r0012_rdropWhile_eq_self_iff(term, ctx))
    results.extend(_r0013_rtakeWhile_eq_nil_iff(term, ctx))
    results.extend(_r0014_idxOf_finRange(term, ctx))
    results.extend(_r0015_forall_2_nil_right_iff(term, ctx))
    results.extend(_r0016_forall_2_cons_left_iff(term, ctx))
    results.extend(_r0017_mem_offDiag_iff_getElem(term, ctx))
    results.extend(_r0018_rotate_zero(term, ctx))
    results.extend(_r0019_rotate_replicate(term, ctx))
    results.extend(_r0020_rotate_length(term, ctx))
    results.extend(_r0021_rotate_length_mul(term, ctx))
    results.extend(_r0022_rotate_eq_iff(term, ctx))
    results.extend(_r0023_reverse_rotate(term, ctx))
    results.extend(_r0024_trans(term, ctx))
    results.extend(_r0025_isRotated_iff_mod(term, ctx))
    results.extend(_r0026_getElem_cyclicPermutations(term, ctx))
    results.extend(_r0027_length_insertionSort(term, ctx))
    results.extend(_r0028_splitLengths_nil(term, ctx))
    results.extend(_r0029_take_self_eq_iff(term, ctx))
    results.extend(_r0030_take_eq_left_iff(term, ctx))
    results.extend(_r0031_left_eq_take_iff(term, ctx))
    results.extend(_r0032_toFinsupp_support(term, ctx))
    results.extend(_r0033_snd_mk(term, ctx))
    results.extend(_r0034_mk_elim(term, ctx))
    results.extend(_r0035_of_toList(term, ctx))
    results.extend(_r0036_prod_ofFn(term, ctx))
    results.extend(_r0037_prod_eq_one(term, ctx))
    results.extend(_r0038_prod_erase_of_comm(term, ctx))
    results.extend(_r0039_prod_insertIdx(term, ctx))
    results.extend(_r0040_mul_prod_eraseIdx(term, ctx))
    results.extend(_r0041_prod_zpow(term, ctx))
    results.extend(_r0042_take_sum_flatten(term, ctx))
    results.extend(_r0043_prod_isUnit(term, ctx))
    results.extend(_r0044_length_sigma(term, ctx))
    results.extend(_r0045_ranges_flatten(term, ctx))
    results.extend(_r0046_drop_take_succ_flatten_eq_getElem(term, ctx))
    results.extend(_r0047_alternatingProd_append(term, ctx))
    results.extend(_r0048_alternatingProd_reverse(term, ctx))
    results.extend(_r0049_smul_prod(term, ctx))
    results.extend(_r0050_prod_map_neg(term, ctx))
    results.extend(_r0051_dProdIndex_eq_map_sum(term, ctx))
    results.extend(_r0052_dProd_nil(term, ctx))
    results.extend(_r0053_dProd_monoid(term, ctx))
    results.extend(_r0054_trop_sum(term, ctx))
    results.extend(_r0055_untrop_prod(term, ctx))
    results.extend(_r0056_length_splitWrtCompositionAux(term, ctx))
    results.extend(_r0057_length_splitWrtComposition(term, ctx))
    results.extend(_r0058_map_length_splitWrtCompositionAux(term, ctx))
    results.extend(_r0059_map_length_splitWrtComposition(term, ctx))
    results.extend(_r0060_sum_take_map_length_splitWrtComposition(term, ctx))
    results.extend(_r0061_flatten_splitWrtCompositionAux(term, ctx))
    results.extend(_r0062_flatten_splitWrtComposition(term, ctx))
    results.extend(_r0063_splitWrtComposition_flatten(term, ctx))
    results.extend(_r0064_id_traverse(term, ctx))
    results.extend(_r0065_comp_traverse(term, ctx))
    results.extend(_r0066_naturality(term, ctx))
    results.extend(_r0067_antidiagonalTuple_zero_zero(term, ctx))
    results.extend(_r0068_antidiagonalTuple_one(term, ctx))
    results.extend(_r0069_toFinset_union(term, ctx))
    results.extend(_r0070_toFinset_inter(term, ctx))
    results.extend(_r0071_toFinset_val(term, ctx))
    results.extend(_r0072_ext_iff(term, ctx))
    results.extend(_r0073_ext(term, ctx))
    results.extend(_r0074_toFinset_finRange(term, ctx))
    results.extend(_r0075_eq_or_ne_mem_of_mem(term, ctx))
    results.extend(_r0076_exists_of_length_succ(term, ctx))
    results.extend(_r0077_length_eq_three(term, ctx))
    results.extend(_r0078_length_eq_four(term, ctx))
    results.extend(_r0079_insert_neg(term, ctx))
    results.extend(_r0080_insert_pos(term, ctx))
    results.extend(_r0081_doubleton_eq(term, ctx))
    results.extend(_r0082_eq_replicate_length(term, ctx))
    results.extend(_r0083_replicate_add(term, ctx))
    results.extend(_r0084_replicate_right_inj(term, ctx))
    results.extend(_r0085_replicate_left_inj(term, ctx))
    results.extend(_r0086_getLast_replicate_succ(term, ctx))
    results.extend(_r0087_idxOf_of_notMem(term, ctx))
    results.extend(_r0088_idxOf_append_of_notMem(term, ctx))
    results.extend(_r0089_idxOf_eq_of_mem(term, ctx))
    results.extend(_r0090_idxOf_getLast(term, ctx))
    results.extend(_r0091_isChain_cons_iff_forall_2(term, ctx))
    results.extend(_r0092_iterate_eq_of_apply_eq(term, ctx))
    results.extend(_r0093_isChain_eq_iff_eq_replicate(term, ctx))
    results.extend(_r0094_isChain_cons_eq_iff_eq_replicate(term, ctx))
    results.extend(_r0095_countP_lt_length_iff(term, ctx))
    results.extend(_r0096_nextOr_eq_getElem_idxOf_succ_of_mem_drop(term, ctx))
    results.extend(_r0097_nextOr_getLast_of_notMem_dropLast(term, ctx))
    results.extend(_r0098_next_eq_getElem(term, ctx))
    results.extend(_r0099_next_getElem(term, ctx))
    results.extend(_r0100_prev_eq_getElem_idxOf_pred_of_ne_head(term, ctx))
    results.extend(_r0101_prev_eq_getElem(term, ctx))
    results.extend(_r0102_prev_getElem(term, ctx))
    results.extend(_r0103_pmap_prev_eq_rotate_length_sub_one(term, ctx))
    results.extend(_r0104_dedup_eq_self(term, ctx))
    results.extend(_r0105_dedup(term, ctx))
    results.extend(_r0106_dedup_idem(term, ctx))
    results.extend(_r0107_union_eq(term, ctx))
    results.extend(_r0108_replicate_dedup(term, ctx))
    results.extend(_r0109_destutter_eq_self_iff(term, ctx))
    results.extend(_r0110_destutter_idem(term, ctx))
    results.extend(_r0111_length_destutter_le_length_destutter_con(term, ctx))
    results.extend(_r0112_length_le_length_destutter(term, ctx))
    results.extend(_r0113_destutter_eq_dedup(term, ctx))
    results.extend(_r0114_rdrop_append_length(term, ctx))
    results.extend(_r0115_rdrop_append_of_le_length(term, ctx))
    results.extend(_r0116_rdrop_append_length_add(term, ctx))
    results.extend(_r0117_ofFn_id(term, ctx))
    results.extend(_r0118_forall_2_same(term, ctx))
    results.extend(_r0119_forall_2_nil_left_iff(term, ctx))
    results.extend(_r0120_forall_2_cons_right_iff(term, ctx))
    results.extend(_r0121_forall_2_and_left(term, ctx))
    results.extend(_r0122_forall_2_map_left_iff(term, ctx))
    results.extend(_r0123_forall_2_map_right_iff(term, ctx))
    results.extend(_r0124_length_eq(term, ctx))
    results.extend(_r0125_get(term, ctx))
    results.extend(_r0126_forall_2_of_length_eq_of_get(term, ctx))
    results.extend(_r0127_forall_2_iff_get(term, ctx))
    results.extend(_r0128_forall_2_zip(term, ctx))
    results.extend(_r0129_forall_2_iff_zip(term, ctx))
    results.extend(_r0130_forall_2_take(term, ctx))
    results.extend(_r0131_forall_2_drop(term, ctx))
    results.extend(_r0132_getD_eq_getElem(term, ctx))
    results.extend(_r0133_getD_eq_default(term, ctx))
    results.extend(_r0134_getD_reverse(term, ctx))
    results.extend(_r0135_getD_append_right(term, ctx))
    results.extend(_r0136_mapIdx_append_one(term, ctx))
    results.extend(_r0137_mapIdx_eq_ofFn(term, ctx))
    results.extend(_r0138_prefix_append_drop(term, ctx))
    results.extend(_r0139_infix_antisymm(term, ctx))
    results.extend(_r0140_insertIdx_eraseIdx_self(term, ctx))
    results.extend(_r0141_insertIdx_eraseIdx_getElem(term, ctx))
    results.extend(_r0142_eq_or_mem_of_mem_insertIdx(term, ctx))
    results.extend(_r0143_get_insertIdx_of_lt(term, ctx))
    results.extend(_r0144_getElem_insertIdx_add_succ(term, ctx))
    results.extend(_r0145_zero_bot(term, ctx))
    results.extend(_r0146_length(term, ctx))
    results.extend(_r0147_succ_top(term, ctx))
    results.extend(_r0148_filter_lt_of_top_le(term, ctx))
    results.extend(_r0149_filter_lt_of_le_bot(term, ctx))
    results.extend(_r0150_filter_lt_of_ge(term, ctx))
    results.extend(_r0151_filter_le_of_le_bot(term, ctx))
    results.extend(_r0152_filter_le_of_top_le(term, ctx))
    results.extend(_r0153_filter_le_of_le(term, ctx))
    results.extend(_r0154_filter_le(term, ctx))
    results.extend(_r0155_filter_le_of_bot(term, ctx))
    results.extend(_r0156_length_iterate(term, ctx))
    results.extend(_r0157_getElem_iterate(term, ctx))
    results.extend(_r0158_iterate_add(term, ctx))
    results.extend(_r0159_lex_nil_or_eq_nil(term, ctx))
    results.extend(_r0160_append_right(term, ctx))
    results.extend(_r0161_append_left(term, ctx))
    results.extend(_r0162_imp(term, ctx))
    results.extend(_r0163_to_ne(term, ctx))
    results.extend(_r0164_lookmap_of_forall_not(term, ctx))
    results.extend(_r0165_length_lookmap(term, ctx))
    results.extend(_r0166_argAux_self(term, ctx))
    results.extend(_r0167_pure_def(term, ctx))
    results.extend(_r0168_mem_antidiagonal(term, ctx))
    results.extend(_r0169_length_antidiagonal(term, ctx))
    results.extend(_r0170_antidiagonal_zero(term, ctx))
    results.extend(_r0171_getElem_inj_iff(term, ctx))
    results.extend(_r0172_idxOf_getElem(term, ctx))
    results.extend(_r0173_get_bijective_iff(term, ctx))
    results.extend(_r0174_getElem_bijective_iff(term, ctx))
    results.extend(_r0175_erase_getElem(term, ctx))
    results.extend(_r0176_ofFn_congr(term, ctx))
    results.extend(_r0177_ofFn_mul(term, ctx))
    results.extend(_r0178_ofFn_getElem_eq_map(term, ctx))
    results.extend(_r0179_ofFn_fin_repeat(term, ctx))
    results.extend(_r0180_ofFnRec_ofFn(term, ctx))
    results.extend(_r0181_ofFn_inj(term, ctx))
    results.extend(_r0182_length_offDiag(term, ctx))
    results.extend(_r0183_length_permutationsAux2(term, ctx))
    results.extend(_r0184_length_permutationsAux(term, ctx))
    results.extend(_r0185_length_permutations(term, ctx))
    results.extend(_r0186_DecEq_eq(term, ctx))
    results.extend(_r0187_pi_coe(term, ctx))
    results.extend(_r0188_length_product(term, ctx))
    results.extend(_r0189_ranges_length(term, ctx))
    results.extend(_r0190_reduceOption_replicate_none(term, ctx))
    results.extend(_r0191_reduceOption_length_eq(term, ctx))
    results.extend(_r0192_length_eq_reduceOption_length_add_filter(term, ctx))
    results.extend(_r0193_reduceOption_length_eq_iff(term, ctx))
    results.extend(_r0194_rotate_mod(term, ctx))
    results.extend(_r0195_length_rotate(term, ctx))
    results.extend(_r0196_rotate_append_length_eq(term, ctx))
    results.extend(_r0197_rotate_rotate(term, ctx))
    results.extend(_r0198_getElem_rotate(term, ctx))
    results.extend(_r0199_get_rotate(term, ctx))
    results.extend(_r0200_get_rotate_one(term, ctx))
    results.extend(_r0201_getElem_eq_getElem_rotate(term, ctx))
    results.extend(_r0202_get_eq_get_rotate(term, ctx))
    results.extend(_r0203_rotate_eq_self_iff_eq_replicate(term, ctx))
    results.extend(_r0204_rotate_one_eq_self_iff_eq_replicate(term, ctx))
    results.extend(_r0205_rotate_injective(term, ctx))
    results.extend(_r0206_rotate_eq_rotate(term, ctx))
    results.extend(_r0207_rotate_reverse(term, ctx))
    results.extend(_r0208_rotate_congr(term, ctx))
    results.extend(_r0209_rotate_congr_iff(term, ctx))
    results.extend(_r0210_rotate_eq_self_iff(term, ctx))
    results.extend(_r0211_length_cyclicPermutations_cons(term, ctx))
    results.extend(_r0212_length_cyclicPermutations_of_ne_nil(term, ctx))
    results.extend(_r0213_length_mem_cyclicPermutations(term, ctx))
    results.extend(_r0214_mem_sections_length(term, ctx))
    results.extend(_r0215_shortlex_def(term, ctx))
    results.extend(_r0216_shortlex_nil_or_eq_nil(term, ctx))
    results.extend(_r0217_eq_of_fst_eq(term, ctx))
    results.extend(_r0218_dlookup_eq_none(term, ctx))
    results.extend(_r0219_lookupAll_eq_dlookup(term, ctx))
    results.extend(_r0220_kreplace_of_forall_not(term, ctx))
    results.extend(_r0221_kreplace_self(term, ctx))
    results.extend(_r0222_keys_kreplace(term, ctx))
    results.extend(_r0223_exists_of_kerase(term, ctx))
    results.extend(_r0224_keys_kerase(term, ctx))
    results.extend(_r0225_kerase_kerase(term, ctx))
    results.extend(_r0226_dlookup_kerase(term, ctx))
    results.extend(_r0227_dlookup_kerase_ne(term, ctx))
    results.extend(_r0228_kerase_comm(term, ctx))
    results.extend(_r0229_kinsert_def(term, ctx))
    results.extend(_r0230_dlookup_kinsert(term, ctx))
    results.extend(_r0231_dlookup_kinsert_ne(term, ctx))
    results.extend(_r0232_kextract_eq_dlookup_kerase(term, ctx))
    results.extend(_r0233_dlookup_dedupKeys(term, ctx))
    results.extend(_r0234_kunion_kerase(term, ctx))
    results.extend(_r0235_dlookup_kunion_left(term, ctx))
    results.extend(_r0236_dlookup_kunion_right(term, ctx))
    results.extend(_r0237_dlookup_kunion_eq_some(term, ctx))
    results.extend(_r0238_orderedInsert_of_not_le(term, ctx))
    results.extend(_r0239_orderedInsert_length(term, ctx))
    results.extend(_r0240_erase_orderedInsert(term, ctx))
    results.extend(_r0241_erase_orderedInsert_of_notMem(term, ctx))
    results.extend(_r0242_orderedInsert_erase(term, ctx))
    results.extend(_r0243_flatten_splitBy(term, ctx))
    results.extend(_r0244_splitBy_of_isChain(term, ctx))
    results.extend(_r0245_splitBy_flatten(term, ctx))
    results.extend(_r0246_length_splitLengths(term, ctx))
    results.extend(_r0247_take_splitLength(term, ctx))
    results.extend(_r0248_flatten_splitLengths(term, ctx))
    results.extend(_r0249_map_splitLengths_length(term, ctx))
    results.extend(_r0250_length_splitLengths_getElem_eq(term, ctx))
    results.extend(_r0251_splitLengths_length_getElem(term, ctx))
    results.extend(_r0252_length_sublists(term, ctx))
    results.extend(_r0253_sublistsLenAux_zero(term, ctx))
    results.extend(_r0254_sublistsLen_zero(term, ctx))
    results.extend(_r0255_length_sublistsLen(term, ctx))
    results.extend(_r0256_length_of_sublistsLen(term, ctx))
    results.extend(_r0257_mem_sublistsLen(term, ctx))
    results.extend(_r0258_sublistsLen_of_length_lt(term, ctx))
    results.extend(_r0259_sublistsLen_length(term, ctx))
    results.extend(_r0260_dedup_sym2(term, ctx))
    results.extend(_r0261_length_sym2(term, ctx))
    results.extend(_r0262_take_one_drop_eq_of_lt_length(term, ctx))
    results.extend(_r0263_take_eq_self_iff(term, ctx))
    results.extend(_r0264_cons_getElem_drop_succ(term, ctx))
    results.extend(_r0265_drop_length_sub_one(term, ctx))
    results.extend(_r0266_takeI_length(term, ctx))
    results.extend(_r0267_takeI_nil(term, ctx))
    results.extend(_r0268_takeI_eq_take(term, ctx))
    results.extend(_r0269_takeI_left(term, ctx))
    results.extend(_r0270_dropWhile_eq_self_iff(term, ctx))
    results.extend(_r0271_takeWhile_eq_nil_iff(term, ctx))
    results.extend(_r0272_toFinsupp_apply_lt(term, ctx))
    results.extend(_r0273_toFinsupp_apply_fin(term, ctx))
    results.extend(_r0274_toFinsupp_apply_le(term, ctx))
    results.extend(_r0275_toFinsupp_append(term, ctx))
    results.extend(_r0276_toFinsupp_concat_eq_toFinsupp_add_single(term, ctx))
    results.extend(_r0277_length_revzip(term, ctx))
    results.extend(_r0278_toFinsupp_sum(term, ctx))
    results.extend(_r0279_mem_fixedLengthDigits_iff(term, ctx))
    results.extend(_r0280_fixedLengthDigits_zero(term, ctx))
    results.extend(_r0281_fixedLengthDigits_one(term, ctx))
    results.extend(_r0282_fixedLengthDigits_succ_eq_disjiUnion(term, ctx))
    results.extend(_r0283_sum_fixedLengthDigits_sum(term, ctx))
    results.extend(_r0284_fst_mk(term, ctx))
    results.extend(_r0285_ext(term, ctx))
    results.extend(_r0286_toList_asString(term, ctx))
    results.extend(_r0287_asString_eq(term, ctx))
    results.extend(_r0288_ext(term, ctx))
    results.extend(_r0289_toList_ofFn(term, ctx))
    results.extend(_r0290_mk_toList(term, ctx))
    results.extend(_r0291_length_val(term, ctx))
    results.extend(_r0292_getElem_map(term, ctx))
    results.extend(_r0293_getElem_pmap(term, ctx))
    results.extend(_r0294_get_eq_get_toList(term, ctx))
    results.extend(_r0295_scanl_val(term, ctx))
    results.extend(_r0296_toList_scanl(term, ctx))
    results.extend(_r0297_scanl_get(term, ctx))
    results.extend(_r0298_replicate_succ_to_snoc(term, ctx))
    results.extend(_r0299_cycleType_formPerm(term, ctx))
    results.extend(_r0300_formPerm_apply_of_notMem(term, ctx))
    results.extend(_r0301_formPerm_apply_getElem_length(term, ctx))
    results.extend(_r0302_formPerm_apply_getElem_zero(term, ctx))
    results.extend(_r0303_formPerm_apply_lt_getElem(term, ctx))
    results.extend(_r0304_formPerm_apply_getElem(term, ctx))
    results.extend(_r0305_formPerm_pow_apply_getElem(term, ctx))
    results.extend(_r0306_formPerm_pow_apply_head(term, ctx))
    results.extend(_r0307_formPerm_apply_mem_eq_self_iff(term, ctx))
    results.extend(_r0308_formPerm_eq_one_iff(term, ctx))
    results.extend(_r0309_formPerm_eq_formPerm_iff(term, ctx))
    results.extend(_r0310_formPerm_pow_length_eq_one_of_nodup(term, ctx))
    results.extend(_r0311_toFinset_range(term, ctx))
    results.extend(_r0312_to_ofList(term, ctx))
    results.extend(_r0313_to_ofList(term, ctx))
    results.extend(_r0314_of_toList(term, ctx))
    results.extend(_r0315_equiv_atom(term, ctx))
    results.extend(_r0316_mem_of_subset(term, ctx))
    results.extend(_r0317_tendsto_nhds(term, ctx))
    results.extend(_r0318_continuous_insertIdx(term, ctx))
    results.extend(_r0319_tendsto_eraseIdx(term, ctx))
    results.extend(_r0320_continuous_eraseIdx(term, ctx))
    results.extend(_r0321_tendsto_insertIdx(term, ctx))
    results.extend(_r0322_continuous_insertIdx(term, ctx))
    results.extend(_r0323_continuousAt_eraseIdx(term, ctx))
    results.extend(_r0324_sbtw_pair(term, ctx))
    results.extend(_r0325_sbtw_triple(term, ctx))
    results.extend(_r0326_getElem_fin_surjective_iff(term, ctx))
    results.extend(_r0327_nodupKeys_middle(term, ctx))
    results.extend(_r0328_dlookup_isSome(term, ctx))
    results.extend(_r0329_nodup_iff_injective_get(term, ctx))
    results.extend(_r0330_prod_isUnit_iff(term, ctx))
    results.extend(_r0331_mem_mem_ranges_iff_lt_sum(term, ctx))
    results.extend(_r0332_wbtw_triple(term, ctx))
    results.extend(_r0333_wbtw_four(term, ctx))
    results.extend(_r0334_sbtw_four(term, ctx))
    results.extend(_r0335_sbtw_iff_triplewise_and_ne_pair(term, ctx))
    results.extend(_r0336_all_iff_forall_prop(term, ctx))
    results.extend(_r0337_any_iff_exists_prop(term, ctx))
    results.extend(_r0338_disjoint_toFinset_iff_disjoint(term, ctx))
    results.extend(_r0339_pairwise_iff_coe_toFinset_pairwise(term, ctx))
    results.extend(_r0340_pairwiseDisjoint_iff_coe_toFinset_pairwi(term, ctx))
    results.extend(_r0341_exists_mem_and_apply_eq_iff(term, ctx))
    results.extend(_r0342_length_pos_iff_ne_nil(term, ctx))
    results.extend(_r0343_length_injective_iff(term, ctx))
    results.extend(_r0344_exists_mem_iff_getElem(term, ctx))
    results.extend(_r0345_exists_mem_iff_get(term, ctx))
    results.extend(_r0346_forall_mem_iff_getElem(term, ctx))
    results.extend(_r0347_forall_mem_iff_get(term, ctx))
    results.extend(_r0348_get_surjective_iff(term, ctx))
    results.extend(_r0349_mem_iff_idxOf_lt_length(term, ctx))
    results.extend(_r0350_mem_dropLast_iff_idxOf_lt(term, ctx))
    results.extend(_r0351_iff(term, ctx))
    results.extend(_r0352_isChain_pair(term, ctx))
    results.extend(_r0353_isChain_split(term, ctx))
    results.extend(_r0354_isChain_iff_forall_2(term, ctx))
    results.extend(_r0355_isChain_iff_get(term, ctx))
    results.extend(_r0356_isChain_cons_iff_get(term, ctx))
    results.extend(_r0357_isChain_attachWith(term, ctx))
    results.extend(_r0358_isChain_attach(term, ctx))
    results.extend(_r0359_isChain_ofFn(term, ctx))
    results.extend(_r0360_count_lt_length_iff(term, ctx))
    results.extend(_r0361_duplicate_iff_sublist(term, ctx))
    results.extend(_r0362_nodup_iff_forall_not_duplicate(term, ctx))
    results.extend(_r0363_exists_duplicate_iff_not_nodup(term, ctx))
    results.extend(_r0364_forall_mem_zipIdx(term, ctx))
    results.extend(_r0365_exists_mem_zipIdx(term, ctx))
    results.extend(_r0366_nodup_ofFn(term, ctx))
    results.extend(_r0367_forall_2_reverse_iff(term, ctx))
    results.extend(_r0368_sublistForall_2_iff(term, ctx))
    results.extend(_r0369_sublistForall_2_map_left_iff(term, ctx))
    results.extend(_r0370_sublistForall_2_map_right_iff(term, ctx))
    results.extend(_r0371_getD_surjective_iff(term, ctx))
    results.extend(_r0372_isPrefix_append_of_length(term, ctx))
    results.extend(_r0373_take_isPrefix_take(term, ctx))
    results.extend(_r0374_lex_cons_iff(term, ctx))
    results.extend(_r0375_lex_singleton_iff(term, ctx))
    results.extend(_r0376_ne_iff(term, ctx))
    results.extend(_r0377_ne_iff(term, ctx))
    results.extend(_r0378_lt_iff_lex_lt(term, ctx))
    results.extend(_r0379_nodup_iff_sublist(term, ctx))
    results.extend(_r0380_nodup_iff_injective_getElem(term, ctx))
    results.extend(_r0381_nodup_iff_injective_get(term, ctx))
    results.extend(_r0382_nodup_middle(term, ctx))
    results.extend(_r0383_nodup_attach(term, ctx))
    results.extend(_r0384_nodup_flatten(term, ctx))
    results.extend(_r0385_pairwise_ofFn(term, ctx))
    results.extend(_r0386_exists_iff_exists_tuple(term, ctx))
    results.extend(_r0387_forall_iff_forall_tuple(term, ctx))
    results.extend(_r0388_nodup_offDiag(term, ctx))
    results.extend(_r0389_isChain_range(term, ctx))
    results.extend(_r0390_isChain_range_succ(term, ctx))
    results.extend(_r0391_reduceOption_length_lt_iff(term, ctx))
    results.extend(_r0392_nodup_rotate(term, ctx))
    results.extend(_r0393_isRotated_comm(term, ctx))
    results.extend(_r0394_nodup_iff(term, ctx))
    results.extend(_r0395_isRotated_iff_mem_map_range(term, ctx))
    results.extend(_r0396_shortlex_iff_lex(term, ctx))
    results.extend(_r0397_ne_key(term, ctx))
    results.extend(_r0398_nodupKeys_iff_pairwise(term, ctx))
    results.extend(_r0399_kreplace_nodupKeys(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_list rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("List_rel_prod", "Forall_2_R_R_prod_prod", "Not an equality or iff proposition"),
    ("List_length_pos_of_prod_ne_one", "_0_lt_L_length", "Not an equality or iff proposition"),
    ("List_length_pos_of_one_lt_prod", "_0_lt_L_length", "Not an equality or iff proposition"),
    ("List_length_pos_of_prod_lt_one", "_0_lt_L_length", "Not an equality or iff proposition"),
    ("List_getElem", "_unknown", "Empty proposition"),
    ("Commute_list_prod_right", "Commute_y_l_prod", "Not an equality or iff proposition"),
    ("Commute_list_prod_left", "Commute_l_prod_y", "Not an equality or iff proposition"),
    ("List_prod_range_succ", "_unknown", "Empty proposition"),
    ("List_exists_mem_ne_one_of_prod_ne_one", "exists_x_in_l_x_ne_1_colon_M", "Not an equality or iff proposition"),
    ("List_length_le_sum_of_one_le", "L_length_le_L_sum", "Not an equality or iff proposition"),
    ("List_ranges_nodup", "s_Nodup", "Not an equality or iff proposition"),
    ("List_neg_one_mem_of_prod_eq_neg_one", "minus_1_colon_in_l", "Not an equality or iff proposition"),
    ("List_dvd_prod", "a_l_prod", "Not an equality or iff proposition"),
    ("List_Sublist_prod_dvd_prod", "l_1_prod_l_2_prod", "Not an equality or iff proposition"),
    ("List_smul_prod", "_unknown", "Empty proposition"),
    ("List_Forall_2_prod_le_prod", "_unknown", "Empty proposition"),
    ("List_Sublist_prod_le_prod", "_unknown", "Empty proposition"),
    ("List_SublistForall_2_prod_le_prod", "_unknown", "Empty proposition"),
    ("List_prod_le_prod", "_unknown", "Empty proposition"),
    ("List_prod_lt_prod", "_unknown", "Empty proposition"),
    ("List_exists_lt_of_prod_lt", "_unknown", "Empty proposition"),
    ("List_exists_le_of_prod_le", "_unknown", "Empty proposition"),
    ("List_one_le_prod_of_one_le", "_1_le_l_prod", "Not an equality or iff proposition"),
    ("List_monotone_prod_take", "Monotone_fun_i_L_take_i_prod", "Not an equality or iff proposition"),
    ("List_prod_nonneg", "_0_le_s_prod", "Not an equality or iff proposition"),
    ("List_one_le_prod", "_1_le_s_prod", "Not an equality or iff proposition"),
    ("List_prod_map_le_pow_length_0", "map_f_t_prod_le_r_pow_length_t", "Not an equality or iff proposition"),
    ("List_prod_pos", "_0_lt_s_prod", "Not an equality or iff proposition"),
    ("List_wbtw_pair", "p_1_p_2_Wbtw_R", "Not an equality or iff proposition"),
    ("List_Sbtw_wbtw", "l_Wbtw_R", "Not an equality or iff proposition"),
    ("List_Sbtw_pairwise_ne", "l_Pairwise_ne", "Not an equality or iff proposition"),
    ("List_norm_prod_le", "_unknown", "Empty proposition"),
    ("List_nnnorm_prod_le", "_unknown", "Empty proposition"),
    ("List_length_pos_of_mem_splitWrtComposition", "_0_lt_length_l_prime", "Not an equality or iff proposition"),
    ("List_getElem_splitWrtComposition", "_unknown", "Empty proposition"),
    ("Turing_ListBlank_induction_on", "p_q", "Not an equality or iff proposition"),
    ("List_traverse_eq_map_id", "List_traverse_pure_colon_to_Id_comp_f_x_eq_pure_colon_to_Id_f_lt_gt_x", "Not an equality or iff proposition"),
    ("List_Nat_nodup_antidiagonalTuple", "List_Nodup_antidiagonalTuple_k_n", "Not an equality or iff proposition"),
    ("List_toFinset_surj_on", "Set_SurjOn_toFinset_l_colon_List_a_pipe_l_Nodup_Set_univ", "Not an equality or iff proposition"),
    ("List_toFinset_surjective", "Surjective_toFinset_colon_List_a_to_Finset_a", "Not an equality or iff proposition"),
    ("List_pairwise_of_coe_toFinset_pairwise", "l_Pairwise_r", "Not an equality or iff proposition"),
    ("List_pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint", "l_Pairwise_root_Disjoint_on_f", "Not an equality or iff proposition"),
    ("List_cons_injective", "Injective_cons_a", "Not an equality or iff proposition"),
    ("List_length_injective", "Injective_length_colon_List_a_to", "Not an equality or iff proposition"),
    ("List_length_eq_two", "_unknown", "Empty proposition"),
    ("List_append_right_injective", "Injective_fun_t_s_plus_plus_t", "Not an equality or iff proposition"),
    ("List_append_left_injective", "Injective_fun_s_s_plus_plus_t", "Not an equality or iff proposition"),
    ("List_replicate_right_injective", "Injective_at_replicate_a_n", "Not an equality or iff proposition"),
    ("List_replicate_right_inj", "_unknown", "Empty proposition"),
    ("List_replicate_left_injective", "Injective_replicate_a", "Not an equality or iff proposition"),
    ("List_reverse_involutive", "Involutive_at_reverse_a", "Not an equality or iff proposition"),
    ("List_reverse_injective", "Injective_at_reverse_a", "Not an equality or iff proposition"),
    ("List_reverse_surjective", "Surjective_at_reverse_a", "Not an equality or iff proposition"),
    ("List_reverse_bijective", "Bijective_at_reverse_a", "Not an equality or iff proposition"),
    ("List_getLast_singleton", "_unknown", "Empty proposition"),
    ("List_get_eq_getElem", "_unknown", "Empty proposition"),
    ("List_getElem", "_unknown", "Empty proposition"),
    ("List_IsPrefix_idxOf_le", "l_1_idxOf_a_le_l_2_idxOf_a", "Not an equality or iff proposition"),
    ("List_IsSuffix_idxOf_le", "l_2_idxOf_a_le_l_2_length_minus_l_1_length_plus_l_1_idxOf_a", "Not an equality or iff proposition"),
    ("List_IsSuffix_idxOf_add_length_le", "l_2_idxOf_a_plus_l_1_length_le_l_1_idxOf_a_plus_l_2_length", "Not an equality or iff proposition"),
    ("List_succ_idxOf_lt_length_of_mem_dropLast", "l_idxOf_a_plus_1_lt_l_length", "Not an equality or iff proposition"),
    ("List_IsChain_sublist", "l_1_IsChain_R", "Not an equality or iff proposition"),
    ("List_IsChain_infix", "IsChain_R_l_1", "Not an equality or iff proposition"),
    ("List_IsChain_suffix", "IsChain_R_l_1", "Not an equality or iff proposition"),
    ("List_IsChain_prefix", "IsChain_R_l_1", "Not an equality or iff proposition"),
    ("List_exists_not_getElem_of_not_isChain", "exists_n_colon_exists_h_colon_n_plus_1_lt_l_length_not_R_l_n_l_n_plus_1", "Not an equality or iff proposition"),
    ("List_IsChain_induction", "forall_i_in_l_p_i", "Not an equality or iff proposition"),
    ("List_IsChain_backwards_induction", "forall_i_in_l_p_i", "Not an equality or iff proposition"),
    ("List_isChain_replicate_of_rel", "IsChain_r_replicate_n_a", "Not an equality or iff proposition"),
    ("List_nextOr_eq_getElem", "_unknown", "Empty proposition"),
    ("List_prev_eq_getElem", "_unknown", "Empty proposition"),
    ("List_dedup_sublist", "forall_l_colon_List_a_dedup_l_lt_plus_l", "Not an equality or iff proposition"),
    ("List_dedup_subset", "forall_l_colon_List_a_dedup_l_sub_l", "Not an equality or iff proposition"),
    ("List_subset_dedup", "l_sub_dedup_l", "Not an equality or iff proposition"),
    ("List_nodup_dedup", "forall_l_colon_List_a_Nodup_dedup_l", "Not an equality or iff proposition"),
    ("List_destutter", "_unknown", "Empty proposition"),
    ("List_destutter", "_unknown", "Empty proposition"),
    ("List_destutter", "_unknown", "Empty proposition"),
    ("List_destutter", "_unknown", "Empty proposition"),
    ("List_destutter", "_unknown", "Empty proposition"),
    ("List_destutter", "_unknown", "Empty proposition"),
    ("List_isChain_destutter", "_unknown", "Empty proposition"),
    ("List_destutter", "_unknown", "Empty proposition"),
    ("List_destutter", "_unknown", "Empty proposition"),
    ("List_destutter", "_unknown", "Empty proposition"),
    ("List_length_destutter", "_unknown", "Empty proposition"),
    ("List_length_destutter", "_unknown", "Empty proposition"),
    ("List_le_length_destutter", "_unknown", "Empty proposition"),
    ("List_length_destutter_ne_le_length_destutter_cons", "l_destutter_ne_length_le_a_colon_colon_l_destutter_ne_length", "Not an equality or iff proposition"),
    ("List_IsChain_length_le_length_destutter_ne", "l_1_length_le_l_2_destutter_ne_length", "Not an equality or iff proposition"),
    ("List_Duplicate_mono_sublist", "x_in_plus_l_prime", "Not an equality or iff proposition"),
    ("List_Duplicate_not_nodup", "not_Nodup_l", "Not an equality or iff proposition"),
    ("List_nodup_ofFn_ofInjective", "Nodup_ofFn_f", "Not an equality or iff proposition"),
    ("List_Sublist_flatten", "l_1_flatten_lt_plus_l_2_flatten", "Not an equality or iff proposition"),
    ("List_Forall_2_imp", "Forall_2_S_l_1_l_2", "Not an equality or iff proposition"),
    ("List_forall_2_refl", "Forall_2_R_l_l", "Not an equality or iff proposition"),
    ("List_forall_2_eq_eq_eq", "Forall_2_eq_colon_a_to_a_to_Prop_eq_Eq", "Not an equality or iff proposition"),
    ("List_left_unique_forall_2", "_unknown", "Empty proposition"),
    ("Relator_LeftUnique_forall_2", "LeftUnique_Forall_2_R", "Not an equality or iff proposition"),
    ("List_right_unique_forall_2", "_unknown", "Empty proposition"),
    ("Relator_RightUnique_forall_2", "RightUnique_Forall_2_R", "Not an equality or iff proposition"),
    ("Relator_BiUnique_forall_2", "BiUnique_Forall_2_R", "Not an equality or iff proposition"),
    ("List_forall_2_take_append", "Forall_2_R_List_take_length_l_1_l_l_1", "Not an equality or iff proposition"),
    ("List_forall_2_drop_append", "Forall_2_R_List_drop_length_l_1_l_l_2", "Not an equality or iff proposition"),
    ("List_Sublist_sublistForall_2", "SublistForall_2_R_l_1_l_2", "Not an equality or iff proposition"),
    ("List_tail_sublistForall_2_self", "SublistForall_2_R_l_tail_l", "Not an equality or iff proposition"),
    ("List_getD_eq_getElem", "_unknown", "Empty proposition"),
    ("List_getElem", "_unknown", "Empty proposition"),
    ("List_getElem", "_unknown", "Empty proposition"),
    ("List_getD_surjective", "l_getD_d_Surjective", "Not an equality or iff proposition"),
    ("List_IsPrefix_flatten", "l_1_flatten_lt_plus_colon_l_2_flatten", "Not an equality or iff proposition"),
    ("List_IsSuffix_flatten", "l_1_flatten_lt_colon_plus_l_2_flatten", "Not an equality or iff proposition"),
    ("List_IsInfix_flatten", "l_1_flatten_lt_colon_plus_colon_l_2_flatten", "Not an equality or iff proposition"),
    ("List_concat_get_prefix", "x_plus_plus_y_get_x_length_hl_lt_plus_colon_y", "Not an equality or iff proposition"),
    ("List_IsPrefix_reduceOption", "l_1_reduceOption_lt_plus_colon_l_2_reduceOption", "Not an equality or iff proposition"),
    ("List_IsPrefix_nodup", "l_1_Nodup", "Not an equality or iff proposition"),
    ("List_IsInfix_nodup", "l_1_Nodup", "Not an equality or iff proposition"),
    ("List_IsSuffix_nodup", "l_1_Nodup", "Not an equality or iff proposition"),
    ("List_sublist_insertIdx", "l_lt_plus_l_insertIdx_n_a", "Not an equality or iff proposition"),
    ("List_subset_insertIdx", "l_sub_l_insertIdx_n_a", "Not an equality or iff proposition"),
    ("List_insertIdx_injective", "Function_Injective_fun_l_colon_List_a_eq_gt_l_insertIdx_n_x", "Not an equality or iff proposition"),
    ("List_Ico_pairwise_lt", "Pairwise_lt_Ico_n_m", "Not an equality or iff proposition"),
    ("List_Ico_nodup", "Nodup_Ico_n_m", "Not an equality or iff proposition"),
    ("List_Ico_isChain_succ", "IsChain_fun_a_b_eq_gt_b_eq_succ_a_Ico_n_m", "Not an equality or iff proposition"),
    ("List_Ico_trichotomy", "n_lt_a_or_b_le_n_or_n_in_Ico_a_b", "Not an equality or iff proposition"),
    ("List_getElem", "_unknown", "Empty proposition"),
    ("List_Disjoint_symm", "Disjoint_l_2_l_1", "Not an equality or iff proposition"),
    ("List_injOn_insertIdx_index_of_notMem", "Set_InjOn_fun_k_eq_gt_l_insertIdx_k_x_n_pipe_n_le_l_length", "Not an equality or iff proposition"),
    ("List_head_le_of_lt", "a_prime_le_a", "Not an equality or iff proposition"),
    ("List_Nat_nodup_antidiagonal", "Nodup_antidiagonal_n", "Not an equality or iff proposition"),
    ("List_Nat_antidiagonal_succ", "_unknown", "Empty proposition"),
    ("List_Nat_antidiagonal_succ_succ", "_unknown", "Empty proposition"),
    ("List_Pairwise_nodup", "Nodup_l", "Not an equality or iff proposition"),
    ("List_not_nodup_pair", "not_Nodup_a_a", "Not an equality or iff proposition"),
    ("List_Nodup_injective_get", "Function_Injective_l_get", "Not an equality or iff proposition"),
    ("Function_Injective_nodup", "l_Nodup", "Not an equality or iff proposition"),
    ("List_nodup_iff_getElem", "_unknown", "Empty proposition"),
    ("List_Nodup_diff", "l_1_Nodup_to_l_1_diff_l_2_Nodup", "Not an equality or iff proposition"),
    ("List_Nodup_product", "l_1_times_l_2_Nodup", "Not an equality or iff proposition"),
    ("List_Nodup_sigma", "l_1_sigma_l_2_Nodup", "Not an equality or iff proposition"),
    ("List_Nodup_insert", "l_insert_a_Nodup", "Not an equality or iff proposition"),
    ("List_Nodup_union", "l_1_union_l_2_Nodup", "Not an equality or iff proposition"),
    ("List_Nodup_inter", "Nodup_l_1_to_Nodup_l_1_inter_l_2", "Not an equality or iff proposition"),
    ("List_Nodup_pairwise_of_forall_ne", "l_Pairwise_r", "Not an equality or iff proposition"),
    ("List_ofFn_comp", "_unknown", "Empty proposition"),
    ("List_ofFn_succ", "_unknown", "Empty proposition"),
    ("List_ofFn_mul", "_unknown", "Empty proposition"),
    ("List_find", "_unknown", "Empty proposition"),
    ("List_find", "_unknown", "Empty proposition"),
    ("List_ofFn_inj", "_unknown", "Empty proposition"),
    ("List_ofFn_injective", "Function_Injective_ofFn_colon_Fin_n_to_a_to_List_a", "Not an equality or iff proposition"),
    ("List_length_offDiag", "_unknown", "Empty proposition"),
    ("List_Nodup_offDiag", "l_offDiag_Nodup", "Not an equality or iff proposition"),
    ("List_Nodup_of_offDiag", "l_Nodup", "Not an equality or iff proposition"),
    ("List_Pairwise_forall_of_forall", "forall_x_x_in_l_to_forall_y_y_in_l_to_R_x_y", "Not an equality or iff proposition"),
    ("List_Pairwise_forall", "forall_a_a_in_l_to_forall_b_b_in_l_to_a_ne_b_to_R_a_b", "Not an equality or iff proposition"),
    ("List_Pairwise_set_pairwise", "x_pipe_x_in_l_Pairwise_R", "Not an equality or iff proposition"),
    ("List_pairwise_of_reflexive_of_forall_ne", "l_Pairwise_R", "Not an equality or iff proposition"),
    ("List_pairwise_replicate_of_refl", "replicate_n_a_Pairwise_R", "Not an equality or iff proposition"),
    ("List_Pairwise_rel_get_of_lt", "R_l_get_a_l_get_b", "Not an equality or iff proposition"),
    ("List_Pairwise_rel_get_of_le", "R_l_get_a_l_get_b", "Not an equality or iff proposition"),
    ("List_Pairwise_decide", "Pairwise_fun_a_b_eq_gt_decide_R_a_b_eq_true_l", "Not an equality or iff proposition"),
    ("List_hasPeriod_iff_getElem", "_unknown", "Empty proposition"),
    ("List_hasPeriod_zero", "HasPeriod_w_0", "Not an equality or iff proposition"),
    ("List_hasPeriod_of_length_le", "HasPeriod_w_p", "Not an equality or iff proposition"),
    ("List_HasPeriod_getElem", "_unknown", "Empty proposition"),
    ("List_hasPeriod_iff_forall_getElem", "_unknown", "Empty proposition"),
    ("List_HasPeriod_factor", "HasPeriod_v_p", "Not an equality or iff proposition"),
    ("List_HasPeriod_infix", "HasPeriod_u_p", "Not an equality or iff proposition"),
    ("List_HasPeriod_gcd", "HasPeriod_w_p_gcd_q", "Not an equality or iff proposition"),
    ("List_getElem_cons_eraseIdx_perm", "l_n_colon_colon_l_eraseIdx_n_tilde_l", "Not an equality or iff proposition"),
    ("List_perm_eraseIdx_of_getElem", "_unknown", "Empty proposition"),
    ("List_getElem_permutations", "_unknown", "Empty proposition"),
    ("List_length_permutations", "_unknown", "Empty proposition"),
    ("List_getElem_range", "_unknown", "Empty proposition"),
    ("List_ranges_disjoint", "Pairwise_Disjoint_ranges_l", "Not an equality or iff proposition"),
    ("List_reduceOption_length_le", "l_reduceOption_length_le_l_length", "Not an equality or iff proposition"),
    ("List_reduceOption_getElem", "_unknown", "Empty proposition"),
    ("List_rotate", "_unknown", "Empty proposition"),
    ("List_rotate", "_unknown", "Empty proposition"),
    ("List_rotate", "_unknown", "Empty proposition"),
    ("List_length_rotate", "_unknown", "Empty proposition"),
    ("List_rotate", "_unknown", "Empty proposition"),
    ("List_rotate", "_unknown", "Empty proposition"),
    ("List_rotate", "_unknown", "Empty proposition"),
    ("List_rotate", "_unknown", "Empty proposition"),
    ("List_rotate", "_unknown", "Empty proposition"),
    ("List_rotate_eq_rotate", "_unknown", "Empty proposition"),
    ("List_getElem", "_unknown", "Empty proposition"),
    ("List_IsRotated_refl", "l_tilde_r_l", "Not an equality or iff proposition"),
    ("List_IsRotated_symm", "l_prime_tilde_r_l", "Not an equality or iff proposition"),
    ("List_IsRotated_forall", "l_rotate_n_tilde_r_l", "Not an equality or iff proposition"),
    ("List_IsRotated_eqv", "Equivalence_at_IsRotated_a", "Not an equality or iff proposition"),
    ("List_cyclicPermutations_injective", "Function_Injective_at_cyclicPermutations_a", "Not an equality or iff proposition"),
    ("List_Shortlex_of_length_lt", "Shortlex_r_s_t", "Not an equality or iff proposition"),
    ("List_Shortlex_of_lex", "Shortlex_r_s_t", "Not an equality or iff proposition"),
    ("List_not_shortlex_nil_right", "not_Shortlex_r_s", "Not an equality or iff proposition"),
    ("Acc_shortlex", "Acc_Shortlex_r_a_colon_colon_b", "Not an equality or iff proposition"),
    ("List_Shortlex_wf", "WellFounded_Shortlex_r", "Not an equality or iff proposition"),
    ("List_NodupKeys_pairwise_ne", "Pairwise_fun_s_s_prime_colon_Sigma_b_eq_gt_s_1_ne_s_prime_1_l", "Not an equality or iff proposition"),
]
