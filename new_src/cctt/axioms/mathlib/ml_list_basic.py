"""Mathlib: List Basic — auto-generated from Mathlib4.

Contains 292 rewrite rules derived from Mathlib theorems.
Plus 137 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_list_basic"
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
# Rewrite rules (292 total)
# ════════════════════════════════════════════════════════════

def _r0000_dProdIndex_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dProdIndex_cons
    # (a :: l).dProdIndex fι = fι a + l.dProdIndex fι
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_dProdIndex", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("fi", (OVar("a"),)), OOp("l_dProdIndex", (args[0],))))
            results.append((rhs, "Mathlib: List_dProdIndex_cons"))
        except Exception:
            pass
    return results


def _r0001_count_false_add_count_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_false_add_count_true
    # count false l + count true l = length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("l"),))
            results.append((rhs, "Mathlib: List_count_false_add_count_true"))
        except Exception:
            pass
    return results


def _r0002_count_not_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.count_not_cons
    # ∀ {b : Bool} {l : List Bool}, IsChain (· ≠ ·) (b :: l) →     count (!b) l = count b l + length l % 2   | _, [], _h => rf
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("count", (OVar("b"), args[1],)), OOp("len", (args[1], OVar("_unknown"), OLit(2), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("h"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("b"), OVar("x"), OVar("colon_colon"), args[1], OVar("h"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_IsChain_count_not_cons"))
        except Exception:
            pass
    return results


def _r0003_toFinset_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_cons
    # toFinset (a :: l) = insert a (toFinset l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinset", 1)
    if args is not None:
        try:
            rhs = OOp("insert", (OVar("a"), OOp("toFinset", (OVar("l"),)),))
            results.append((rhs, "Mathlib: List_toFinset_cons"))
        except Exception:
            pass
    return results


def _r0004_set_of_mem_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.set_of_mem_cons
    # { x | x ∈ a :: l } = insert a { x | x ∈ l }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pipe_x_in_a_colon_colon_l")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("insert", (OVar("a"), OVar("x_pipe_x_in_l"),))
            results.append((rhs, "Mathlib: List_set_of_mem_cons"))
    except Exception:
        pass
    return results


def _r0005_dropLast_append_getLast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dropLast_append_getLast
    # ∀ {l : List α} (h : l ≠ []), dropLast l ++ [getLast l h] = l   | [], h => absurd rfl h   | [_], _ => rfl   | a :: b :: l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OOp("l", (OVar("pipe"), OVar("_unknown"), OVar("h"), OVar("eq_gt"), OVar("absurd"), OVar("rfl"), OVar("h"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("a"), OVar("colon_colon"), OVar("b"), OVar("colon_colon"), OVar("l"), OVar("h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_dropLast_append_getLast"))
        except Exception:
            pass
    return results


def _r0006_countP_erase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.countP_erase
    # countP p (l.erase a) = countP p l - if a ∈ l ∧ p a then 1 else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("-", (OOp("countP", (args[0], OVar("l"),)), OOp("in", (OOp("if", (OVar("a"),)), OVar("l"))))), OOp("p", (OVar("a"), OVar("then"), OLit(1), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: List_countP_erase"))
        except Exception:
            pass
    return results


def _r0007_nextOr_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nextOr_singleton
    # nextOr [y] x d = d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: List_nextOr_singleton"))
        except Exception:
            pass
    return results


def _r0008_nextOr_self_cons_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nextOr_self_cons_cons
    # nextOr (x :: y :: xs) x d = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 3)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_nextOr_self_cons_cons"))
        except Exception:
            pass
    return results


def _r0009_nextOr_cons_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nextOr_cons_of_ne
    # nextOr (y :: xs) x d = nextOr xs x d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 3)
    if args is not None:
        try:
            rhs = OOp("or", (OVar("xs"), args[1], args[2],))
            results.append((rhs, "Mathlib: List_nextOr_cons_of_ne"))
        except Exception:
            pass
    return results


def _r0010_prev_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_singleton
    # prev [y] x h = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prev", 3)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_prev_singleton"))
        except Exception:
            pass
    return results


def _r0011_dedup_cons_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_cons_of_notMem
    # dedup (a :: l) = a :: dedup l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("dedup"), OVar("l"),))
            results.append((rhs, "Mathlib: List_dedup_cons_of_notMem"))
        except Exception:
            pass
    return results


def _r0012_dedup_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_cons
    # dedup (a :: l) = if a ∈ l then dedup l else a :: dedup l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("if", (OVar("a"),)), OOp("l", (OVar("then"), OVar("dedup"), OVar("l"), OVar("else"), OVar("a"), OVar("colon_colon"), OVar("dedup"), OVar("l"),))))
            results.append((rhs, "Mathlib: List_dedup_cons"))
        except Exception:
            pass
    return results


def _r0013_dedup_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_append
    # dedup (l₁ ++ l₂) = l₁ ∪ dedup l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("union", (OVar("l_1"), OOp("dedup", (OVar("l_2"),))))
            results.append((rhs, "Mathlib: List_dedup_append"))
        except Exception:
            pass
    return results


def _r0014_destutter_sublist(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.destutter_sublist
    # ∀ l : List α, l.destutter R <+ l   | [] => Sublist.slnil   | h :: l => l.destutter'_sublist R h  theorem isChain_destutt
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_destutter", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("l", (OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), OVar("l"), OVar("h"), OVar("eq_gt"), OVar("l_destutter_prime_of_isChain_cons"), OVar("_unknown"), OVar("h_at_simp_theorem"), OVar("destutter_eq_self_iff"), OVar("colon"), OVar("forall"), OVar("l"), OVar("colon"), OVar("List"), OVar("a"), OVar("l_destutter"), args[0],)), OOp("iff", (OVar("l"), OOp("l_IsChain", (args[0], OVar("pipe"), OSeq(()), OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: List_destutter_sublist"))
        except Exception:
            pass
    return results


def _r0015_rdropWhile_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdropWhile_concat
    # rdropWhile p (l ++ [x]) = if p x then rdropWhile p l else l ++ [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdropWhile", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("if", (args[0], OVar("x"), OVar("then"), OVar("rdropWhile"), args[0], OVar("l"), OVar("else"), OVar("l"),)), OSeq((OVar("x"),))))
            results.append((rhs, "Mathlib: List_rdropWhile_concat"))
        except Exception:
            pass
    return results


def _r0016_rdropWhile_concat_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdropWhile_concat_neg
    # rdropWhile p (l ++ [x]) = l ++ [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdropWhile", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("l"), OSeq((OVar("x"),))))
            results.append((rhs, "Mathlib: List_rdropWhile_concat_neg"))
        except Exception:
            pass
    return results


def _r0017_rtakeWhile_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtakeWhile_concat
    # rtakeWhile p (l ++ [x]) = if p x then rtakeWhile p l ++ [x] else []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rtakeWhile", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("if", (args[0], OVar("x"), OVar("then"), OVar("rtakeWhile"), args[0], OVar("l"),)), OSeq((OVar("x_else"),))))
            results.append((rhs, "Mathlib: List_rtakeWhile_concat"))
        except Exception:
            pass
    return results


def _r0018_rtakeWhile_concat_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtakeWhile_concat_neg
    # rtakeWhile p (l ++ [x]) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rtakeWhile", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_rtakeWhile_concat_neg"))
        except Exception:
            pass
    return results


def _r0019_eq_empty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.eq_empty_iff
    # Ico n m = [] ↔ m ≤ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OSeq(()), args[1])), args[0]))
            results.append((rhs, "Mathlib: List_Ico_eq_empty_iff"))
        except Exception:
            pass
    return results


def _r0020_append_consecutive(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.append_consecutive
    # Ico n m ++ Ico m l = Ico n l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OOp("Ico", (OVar("n"), OVar("l"),))
            results.append((rhs, "Mathlib: List_Ico_append_consecutive"))
        except Exception:
            pass
    return results


def _r0021_iterate_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.iterate_eq_nil
    # iterate f a n = [] ↔ n = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iterate", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OSeq(()), args[2])), OLit(0)))
            results.append((rhs, "Mathlib: List_iterate_eq_nil"))
        except Exception:
            pass
    return results


def _r0022_reduceOption_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_nil
    # @reduceOption α [] = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_reduceOption", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_reduceOption_nil"))
        except Exception:
            pass
    return results


def _r0023_rotate_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_nil
    # ([] : List α).rotate n = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "colon_List_a_rotate", 1)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_rotate_nil"))
        except Exception:
            pass
    return results


def _r0024_mem_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_rotate
    # ∀ {l : List α} {a : α} {n : ℕ}, a ∈ l.rotate n ↔ a ∈ l   | [], _, n =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_mem_rotate"))
        except Exception:
            pass
    return results


def _r0025_rotate_eq_nil_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_eq_nil_iff
    # l.rotate n = [] ↔ l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OSeq((OVar("iff_l_eq"),))
            results.append((rhs, "Mathlib: List_rotate_eq_nil_iff"))
        except Exception:
            pass
    return results


def _r0026_singleton_eq_rotate_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.singleton_eq_rotate_iff
    # [x] = l.rotate n ↔ [x] = l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OSeq((OVar("x"),))
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("l_rotate", (OVar("n"),)), OSeq((OVar("x"),)))), OVar("l")))
            results.append((rhs, "Mathlib: List_singleton_eq_rotate_iff"))
    except Exception:
        pass
    return results


def _r0027_isRotated_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isRotated_singleton_iff
    # l ~r [x] ↔ l = [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OSeq((OVar("x"),))
            results.append((rhs, "Mathlib: List_isRotated_singleton_iff"))
        except Exception:
            pass
    return results


def _r0028_keys_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.keys_cons
    # (s :: l).keys = s.1 :: l.keys
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_colon_colon_l_keys")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s_1", (OVar("colon_colon"), OVar("l_keys"),))
            results.append((rhs, "Mathlib: List_keys_cons"))
    except Exception:
        pass
    return results


def _r0029_keys_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.keys_append
    # (l₁ ++ l₂).keys = l₁.keys ++ l₂.keys
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_1_plus_plus_l_2_keys")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OVar("l_1_keys"), OVar("l_2_keys")))
            results.append((rhs, "Mathlib: List_keys_append"))
    except Exception:
        pass
    return results


def _r0030_dlookup_cons_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_cons_eq
    # dlookup a (⟨a, b⟩ :: l) = some b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("some", (OVar("b"),))
            results.append((rhs, "Mathlib: List_dlookup_cons_eq"))
        except Exception:
            pass
    return results


def _r0031_dlookup_cons_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_cons_ne
    # ∀ s : Sigma β, a ≠ s.1 → dlookup a (s :: l) = dlookup a l   | ⟨_, _⟩, h => dif_neg h.symm  @[grind =] theorem dlookup_is
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("dlookup", (args[0], OVar("l"), OVar("pipe"), OVar("_unknown"), OVar("h"), OVar("eq_gt"), OVar("dif_neg"), OVar("h_symm_at_grind_eq_theorem"), OVar("dlookup_isSome"), OVar("a_colon_a"), OVar("l_colon_List_Sigma_b"), OVar("colon"), OVar("dlookup_a_l_isSome"),)), OOp("in", (args[0], OVar("l_keys")))))
            results.append((rhs, "Mathlib: List_dlookup_cons_ne"))
        except Exception:
            pass
    return results


def _r0032_lookupAll_cons_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookupAll_cons_eq
    # lookupAll a (⟨a, b⟩ :: l) = b :: lookupAll a l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lookupAll", 2)
    if args is not None:
        try:
            rhs = OOp("b", (OVar("colon_colon"), OVar("lookupAll"), args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_lookupAll_cons_eq"))
        except Exception:
            pass
    return results


def _r0033_lookupAll_cons_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookupAll_cons_ne
    # ∀ s : Sigma β, a ≠ s.1 → lookupAll a (s :: l) = lookupAll a l   | ⟨_, _⟩, h => dif_neg h.symm  theorem lookupAll_eq_nil 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lookupAll", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("lookupAll", (args[0], OVar("l"), OVar("pipe"), OVar("_unknown"), OVar("h"), OVar("eq_gt"), OVar("dif_neg"), OVar("h_symm_theorem"), OVar("lookupAll_eq_nil"), OVar("a_colon_a"), OVar("colon"), OVar("forall"), OVar("l_colon_List_Sigma_b"), OVar("lookupAll"), args[0], OVar("l"),)), OOp("iff", (OSeq(()), OOp("not_in", (OOp("forall", (OVar("b"), OVar("colon"), OVar("b"), args[0], OVar("Sigma_mk"), args[0], OVar("b"),)), OOp("l", (OVar("pipe"), OSeq(()), OVar("eq_gt"),))))))))
            results.append((rhs, "Mathlib: List_lookupAll_cons_ne"))
        except Exception:
            pass
    return results


def _r0034_lookupAll_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookupAll_eq_nil
    # ∀ {l : List (Sigma β)}, lookupAll a l = [] ↔ ∀ b : β a, Sigma.mk a b ∉ l   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lookupAll", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OSeq(()), OOp("not_in", (OOp("forall", (OVar("b"), OVar("colon"), OVar("b"), args[0], OVar("Sigma_mk"), args[0], OVar("b"),)), OOp("l", (OVar("pipe"), OSeq(()), OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: List_lookupAll_eq_nil"))
        except Exception:
            pass
    return results


def _r0035_kerase_cons_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kerase_cons_eq
    # kerase a (s :: l) = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kerase", 2)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_kerase_cons_eq"))
        except Exception:
            pass
    return results


def _r0036_kerase_cons_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kerase_cons_ne
    # kerase a (s :: l) = s :: kerase a l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kerase", 2)
    if args is not None:
        try:
            rhs = OOp("s", (OVar("colon_colon"), OVar("kerase"), args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_kerase_cons_ne"))
        except Exception:
            pass
    return results


def _r0037_kerase_of_notMem_keys(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kerase_of_notMem_keys
    # kerase a l = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kerase", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: List_kerase_of_notMem_keys"))
        except Exception:
            pass
    return results


def _r0038_mem_keys_kinsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_keys_kinsert
    # a ∈ (kinsert a' b' l).keys ↔ a = a' ∨ a ∈ l.keys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OVar("a_prime"), OOp("in", (args[1], OVar("l_keys")))))
            results.append((rhs, "Mathlib: List_mem_keys_kinsert"))
        except Exception:
            pass
    return results


def _r0039_kunion_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kunion_nil
    # ∀ {l : List (Sigma β)}, kunion l [] = l   | [] => rfl   | _ :: l =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kunion", 2)
    if args is not None:
        try:
            rhs = OOp("l", (OVar("pipe"), OSeq(()), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), args[0], OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_kunion_nil"))
        except Exception:
            pass
    return results


def _r0040_orderedInsert_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.orderedInsert_cons
    # (b :: l).orderedInsert r a = if r a b then a :: b :: l else b :: l.orderedInsert r a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b_colon_colon_l_orderedInsert", 2)
    if args is not None:
        try:
            rhs = OOp("if", (args[0], args[1], OVar("b"), OVar("then"), args[1], OVar("colon_colon"), OVar("b"), OVar("colon_colon"), OVar("l"), OVar("else"), OVar("b"), OVar("colon_colon"), OVar("l_orderedInsert"), args[0], args[1],))
            results.append((rhs, "Mathlib: List_orderedInsert_cons"))
        except Exception:
            pass
    return results


def _r0041_orderedInsert_cons_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.orderedInsert_cons_of_le
    # orderedInsert r a (b :: l) = a :: b :: l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "orderedInsert", 3)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("b"), OVar("colon_colon"), OVar("l"),))
            results.append((rhs, "Mathlib: List_orderedInsert_cons_of_le"))
        except Exception:
            pass
    return results


def _r0042_splitByLoop_eq_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitByLoop_eq_append
    # splitBy.loop r l a g gs = gs.reverse ++ splitBy.loop r l a g []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "splitBy_loop", 5)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("gs_reverse"), OOp("splitBy_loop", (args[0], args[1], args[2], args[3], OSeq(()),))))
            results.append((rhs, "Mathlib: List_splitByLoop_eq_append"))
        except Exception:
            pass
    return results


def _r0043_sublists_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublists_singleton
    # sublists [a] = [[], [a]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublists", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: List_sublists_singleton"))
        except Exception:
            pass
    return results


def _r0044_sublistsLen_succ_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublistsLen_succ_nil
    # sublistsLen (n + 1) (@nil α) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublistsLen", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_sublistsLen_succ_nil"))
        except Exception:
            pass
    return results


def _r0045_elim_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.TProd.elim_of_ne
    # v.elim hj = TProd.elim v.2 ((List.mem_cons.mp hj).resolve_left hji)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_elim", 1)
    if args is not None:
        try:
            rhs = OOp("TProd_elim", (OVar("v_2"), OOp("List_mem_cons_mp_hj_resolve_left", (OVar("hji"),)),))
            results.append((rhs, "Mathlib: List_TProd_elim_of_ne"))
        except Exception:
            pass
    return results


def _r0046_elim_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.TProd.elim_of_mem
    # v.elim (mem_cons_of_mem _ hj) = TProd.elim v.2 hj
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_elim", 1)
    if args is not None:
        try:
            rhs = OOp("TProd_elim", (OVar("v_2"), OVar("hj"),))
            results.append((rhs, "Mathlib: List_TProd_elim_of_mem"))
        except Exception:
            pass
    return results


def _r0047_snoc_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.snoc_nil
    # (nil.snoc x) = x ::ᵥ nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nil_snoc", 1)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("colon_colon"), OVar("nil"),))
            results.append((rhs, "Mathlib: List_Vector_snoc_nil"))
        except Exception:
            pass
    return results


def _r0048_sum_toFinset_count_eq_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sum_toFinset_count_eq_length
    # ∑ a ∈ l.toFinset, l.count a = l.length
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OVar("l_length")
            results.append((rhs, "Mathlib: List_sum_toFinset_count_eq_length"))
        except Exception:
            pass
    return results


def _r0049_prod_eq_pow_single(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_eq_pow_single
    # l.prod = a ^ l.count a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("a"), OOp("l_count", (OVar("a"),))))
            results.append((rhs, "Mathlib: List_prod_eq_pow_single"))
    except Exception:
        pass
    return results


def _r0050_dProdIndex_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dProdIndex_nil
    # ([] : List α).dProdIndex fι = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "colon_List_a_dProdIndex", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: List_dProdIndex_nil"))
        except Exception:
            pass
    return results


def _r0051_dProd_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dProd_cons
    # (a :: l).dProd fι fA = (GradedMonoid.GMul.mul (fA a) (l.dProd fι fA) :)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_dProd", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("fA", (OVar("a"),)), OOp("l_dProd", (args[0], args[1],)), OVar("colon"),))
            results.append((rhs, "Mathlib: List_dProd_cons"))
        except Exception:
            pass
    return results


def _r0052_cons_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.cons_mk
    # ListBlank.cons a (ListBlank.mk l) = ListBlank.mk (a :: l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ListBlank_cons", 2)
    if args is not None:
        try:
            rhs = OOp("ListBlank_mk", (OOp("a", (OVar("colon_colon"), OVar("l"),)),))
            results.append((rhs, "Mathlib: Turing_ListBlank_cons_mk"))
        except Exception:
            pass
    return results


def _r0053_exists_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.exists_cons
    # ∃ a l', l = ListBlank.cons a l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = OOp("ListBlank_cons", (args[0], args[1],))
            results.append((rhs, "Mathlib: Turing_ListBlank_exists_cons"))
        except Exception:
            pass
    return results


def _r0054_append_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.append_mk
    # ListBlank.append l₁ (ListBlank.mk l₂) = ListBlank.mk (l₁ ++ l₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ListBlank_append", 2)
    if args is not None:
        try:
            rhs = OOp("ListBlank_mk", (OOp("concat", (args[0], OVar("l_2"))),))
            results.append((rhs, "Mathlib: Turing_ListBlank_append_mk"))
        except Exception:
            pass
    return results


def _r0055_append_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.append_assoc
    # ListBlank.append (l₁ ++ l₂) l₃ = ListBlank.append l₁ (ListBlank.append l₂ l₃)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ListBlank_append", 2)
    if args is not None:
        try:
            rhs = OOp("ListBlank_append", (OVar("l_1"), OOp("ListBlank_append", (OVar("l_2"), args[1],)),))
            results.append((rhs, "Mathlib: Turing_ListBlank_append_assoc"))
        except Exception:
            pass
    return results


def _r0056_count_not_add_count(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_not_add_count
    # count (!b) l + count b l = length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("l"),))
            results.append((rhs, "Mathlib: List_count_not_add_count"))
        except Exception:
            pass
    return results


def _r0057_count_add_count_not(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_add_count_not
    # count b l + count (!b) l = length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("l"),))
            results.append((rhs, "Mathlib: List_count_add_count_not"))
        except Exception:
            pass
    return results


def _r0058_count_true_add_count_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_true_add_count_false
    # count true l + count false l = length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("l"),))
            results.append((rhs, "Mathlib: List_count_true_add_count_false"))
        except Exception:
            pass
    return results


def _r0059_count_not_eq_count(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.count_not_eq_count
    # count (!b) l = count b l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("count", (OVar("b"), args[1],))
            results.append((rhs, "Mathlib: List_IsChain_count_not_eq_count"))
        except Exception:
            pass
    return results


def _r0060_count_false_eq_count_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.count_false_eq_count_true
    # count false l = count true l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("count", (OLit(True), args[1],))
            results.append((rhs, "Mathlib: List_IsChain_count_false_eq_count_true"))
        except Exception:
            pass
    return results


def _r0061_two_mul_count_bool_of_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.two_mul_count_bool_of_even
    # 2 * count b l = length l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("l"),))
            results.append((rhs, "Mathlib: List_IsChain_two_mul_count_bool_of_even"))
        except Exception:
            pass
    return results


def _r0062_two_mul_count_bool_eq_ite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.two_mul_count_bool_eq_ite
    # 2 * count b l =       if Even (length l) then length l else       if Option.some b == l.head? then length l + 1 else len
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("if", (OVar("Even"), OOp("len", (OVar("l"),)), OVar("then"), OVar("length"), OVar("l"), OVar("else"), OVar("if"), OVar("Option_some"), OVar("b"), OVar("eq_eq"), OVar("l_head_q"), OVar("then"), OVar("length"), OVar("l"),)), OOp("-", (OOp("_1", (OVar("else"), OVar("length"), OVar("l"),)), OLit(1)))))
            results.append((rhs, "Mathlib: List_IsChain_two_mul_count_bool_eq_ite"))
        except Exception:
            pass
    return results


def _r0063_antidiagonalTuple_zero_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.antidiagonalTuple_zero_right
    # ∀ k, antidiagonalTuple k 0 = [0]   | 0 => (congr_arg fun x => [x]) <| Subsingleton.elim _ _   | k + 1 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("_0", (OVar("pipe"), OLit(0), OVar("eq_gt"), OOp("congr_arg", (OVar("fun"), OVar("x"), OVar("eq_gt"), OSeq((OVar("x"),)),)), OVar("lt_pipe"), OVar("Subsingleton_elim"), OVar("_unknown"), OVar("_unknown"), OVar("pipe"), args[0],)), OOp("_1", (OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_Nat_antidiagonalTuple_zero_right"))
        except Exception:
            pass
    return results


def _r0064_antidiagonalTuple_pairwise_pi_lex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nat.antidiagonalTuple_pairwise_pi_lex
    # ∀ k n, (antidiagonalTuple k n).Pairwise (Pi.Lex (· < ·) @fun _ => (· < ·))   | 0, 0 => List.pairwise_singleton _ _   | 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "antidiagonalTuple_k_n_Pairwise", 4)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("gt", (OVar("List_pairwise_singleton"), OVar("_unknown"), OVar("_unknown"), args[1], args[2], OVar("_unknown"),)), OOp("+", (OOp("_1", (OVar("eq_gt"), OVar("List_Pairwise_nil"), args[1], OVar("k"),)), OOp("_1", (OVar("n"), OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: List_Nat_antidiagonalTuple_pairwise_pi_lex"))
        except Exception:
            pass
    return results


def _r0065_mem_pi_toList(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_pi_toList
    # f ∈ pi xs fun x => toList (β x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("toList"), OOp("b", (OVar("x"),)),))
            results.append((rhs, "Mathlib: List_mem_pi_toList"))
        except Exception:
            pass
    return results


def _r0066_card_toFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.card_toFinset
    # #l.toFinset = l.dedup.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_l_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_dedup_length")
            results.append((rhs, "Mathlib: List_card_toFinset"))
    except Exception:
        pass
    return results


def _r0067_toFinset_card_of_nodup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_card_of_nodup
    # #l.toFinset = l.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_l_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l_length")
            results.append((rhs, "Mathlib: List_toFinset_card_of_nodup"))
    except Exception:
        pass
    return results


def _r0068_toFinset_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_nil
    # toFinset (@nil α) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinset", 1)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: List_toFinset_nil"))
        except Exception:
            pass
    return results


def _r0069_toFinset_eq_empty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_eq_empty_iff
    # l.toFinset = ∅ ↔ l = nil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("l"))), OVar("nil")))
            results.append((rhs, "Mathlib: List_toFinset_eq_empty_iff"))
    except Exception:
        pass
    return results


def _r0070_toFinset_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_append
    # toFinset (l ++ l') = l.toFinset ∪ l'.toFinset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinset", 1)
    if args is not None:
        try:
            rhs = OOp("union", (OVar("l_toFinset"), OVar("l_prime_toFinset")))
            results.append((rhs, "Mathlib: List_toFinset_append"))
        except Exception:
            pass
    return results


def _r0071_mem_pair(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_pair
    # a ∈ [b, c] ↔ a = b ∨ a = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OVar("b"), args[1])), OVar("c")))
            results.append((rhs, "Mathlib: List_mem_pair"))
        except Exception:
            pass
    return results


def _r0072_singleton_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.singleton_eq
    # ({x} : List α) = [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 3)
    if args is not None:
        try:
            rhs = OSeq((OVar("x"),))
            results.append((rhs, "Mathlib: List_singleton_eq"))
        except Exception:
            pass
    return results


def _r0073_append_eq_has_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.append_eq_has_append
    # List.append L₁ L₂ = L₁ ++ L₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (args[0], args[1]))
            results.append((rhs, "Mathlib: List_append_eq_has_append"))
        except Exception:
            pass
    return results


def _r0074_subset_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.subset_singleton_iff
    # L ⊆ [a] ↔ ∃ n, L = replicate n a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("replicate", (OVar("n"), OVar("a"),))
            results.append((rhs, "Mathlib: List_subset_singleton_iff"))
        except Exception:
            pass
    return results


def _r0075_mem_pure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_pure
    # x ∈ (pure y : List α) ↔ x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_mem_pure"))
        except Exception:
            pass
    return results


def _r0076_concat_eq_reverse_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.concat_eq_reverse_cons
    # concat l a = reverse (a :: reverse l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OOp("reverse", (OOp("a", (OVar("colon_colon"), OVar("reverse"), args[0],)),))
            results.append((rhs, "Mathlib: List_concat_eq_reverse_cons"))
        except Exception:
            pass
    return results


def _r0077_getLast_append_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getLast_append_singleton
    # getLast (l ++ [a]) (append_ne_nil_of_right_ne_nil l (cons_ne_nil a _)) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "last", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: List_getLast_append_singleton"))
        except Exception:
            pass
    return results


def _r0078_getLast_append_of_right_ne_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getLast_append_of_right_ne_nil
    # getLast (l₁ ++ l₂) (append_ne_nil_of_right_ne_nil l₁ h) = getLast l₂ h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "last", 2)
    if args is not None:
        try:
            rhs = OOp("last", (OVar("l_2"), OVar("h"),))
            results.append((rhs, "Mathlib: List_getLast_append_of_right_ne_nil"))
        except Exception:
            pass
    return results


def _r0079_tail_append_singleton_of_ne_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.tail_append_singleton_of_ne_nil
    # tail (l ++ [a]) = tail l ++ [a]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tail", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("tail", (OVar("l"),)), OSeq((OVar("a"),))))
            results.append((rhs, "Mathlib: List_tail_append_singleton_of_ne_nil"))
        except Exception:
            pass
    return results


def _r0080_sublist_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublist_singleton
    # l <+ [a] ↔ l = [] ∨ l = [a]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OSeq((OVar("or_l_eq_a"),))
            results.append((rhs, "Mathlib: List_sublist_singleton"))
        except Exception:
            pass
    return results


def _r0081_idxOf_cons_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_cons_eq
    # b = a → idxOf a (b :: l) = 0   | e =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "idxOf", 2)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("pipe"), OVar("e"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_idxOf_cons_eq"))
        except Exception:
            pass
    return results


def _r0082_idxOf_cons_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_cons_ne
    # idxOf a (b :: l) = succ (idxOf a l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "idxOf", 2)
    if args is not None:
        try:
            rhs = OOp("succ", (OOp("idxOf", (args[0], OVar("l"),)),))
            results.append((rhs, "Mathlib: List_idxOf_cons_ne"))
        except Exception:
            pass
    return results


def _r0083_idxOf_append_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_append_of_mem
    # idxOf a (l₁ ++ l₂) = idxOf a l₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "idxOf", 2)
    if args is not None:
        try:
            rhs = OOp("idxOf", (args[0], OVar("l_1"),))
            results.append((rhs, "Mathlib: List_idxOf_append_of_mem"))
        except Exception:
            pass
    return results


def _r0084_isChain_cons_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons_iff
    # IsChain R (a :: l) ↔ l = [] ∨       ∃ (b : α) (l' : List α), R a b ∧ IsChain R (b :: l') ∧ l = b :: l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("or", (OSeq(()), OOp("exists", (OOp("b", (OVar("colon"), OVar("a"),)), OVar("l_prime_colon_List_a"), OVar("R"), OVar("a"), OVar("b"),)))), OOp("and", (OOp("IsChain", (OVar("R"), OOp("b", (OVar("colon_colon"), OVar("l_prime"),)),)), args[1])))), OOp("b", (OVar("colon_colon"), OVar("l_prime"),))))
            results.append((rhs, "Mathlib: List_isChain_cons_iff"))
        except Exception:
            pass
    return results


def _r0085_isChain_isInfix(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_isInfix
    # ∀ l : List α, IsChain (fun x y => [x, y] <:+: l) l   | [] => .nil   | [_] => .singleton _   | a :: b :: l => .cons_cons 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 4)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("nil"), args[2], OSeq((OVar("_unknown"),)), OVar("eq_gt"), OVar("singleton"), OVar("_unknown"), args[2], OVar("a"), OVar("colon_colon"), OVar("b"), OVar("colon_colon"), args[1], OVar("eq_gt"), OVar("cons_cons"), args[1],))
            results.append((rhs, "Mathlib: List_isChain_isInfix"))
        except Exception:
            pass
    return results


def _r0086_isChain_iff_forall_rel_of_append_cons_co(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_iff_forall_rel_of_append_cons_cons
    # IsChain R l ↔ ∀ ⦃a b l₁ l₂⦄, l = l₁ ++ a :: b :: l₂ → R a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("l_1"), OOp("implies", (OOp("a", (OVar("colon_colon"), OVar("b"), OVar("colon_colon"), OVar("l_2"),)), OOp("R", (OVar("a"), OVar("b"),))))))
            results.append((rhs, "Mathlib: List_isChain_iff_forall_rel_of_append_cons_cons"))
        except Exception:
            pass
    return results


def _r0087_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.cons
    # ∀ {l : List α}, IsChain R l → (∀ y ∈ l.head?, R x y) →     IsChain R (x :: l)   | [], _, _ => .singleton x   | _ :: _, h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 6)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("singleton"), OVar("x"), args[2], args[5], OVar("colon_colon"), args[5], OVar("hl"), OVar("H"), OVar("eq_gt"), OVar("hl_cons_cons"), OVar("lt_pipe"), OVar("H"), args[5], OVar("rfl_at_deprecated_since_colon_eq_2025minus_10minus_16"), OVar("alias"), OVar("IsChain_cons_prime"),))
            results.append((rhs, "Mathlib: List_IsChain_cons"))
        except Exception:
            pass
    return results


def _r0088_exists_isChain_cons_of_relationReflTrans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_isChain_cons_of_relationReflTransGen
    # ∃ l, IsChain r (a :: l) ∧ getLast (a :: l) (cons_ne_nil _ _) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: List_exists_isChain_cons_of_relationReflTransGen"))
        except Exception:
            pass
    return results


def _r0089_count_diff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_diff
    # ∀ l₂, count a (l₁.diff l₂) = count a l₁ - count a l₂   | [] => rfl   | b :: l₂ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("count", (args[0], OVar("l_1"),)), OOp("count", (args[0], OVar("l_2"), OVar("pipe"), OSeq(()), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("b"), OVar("colon_colon"), OVar("l_2"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_count_diff"))
        except Exception:
            pass
    return results


def _r0090_countP_diff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.countP_diff
    # countP p (l₁.diff l₂) = countP p l₁ - countP p l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "countP", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("countP", (args[0], OVar("l_1"),)), OOp("countP", (args[0], OVar("l_2"),))))
            results.append((rhs, "Mathlib: List_countP_diff"))
        except Exception:
            pass
    return results


def _r0091_nextOr_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nextOr_nil
    # nextOr [] x d = d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: List_nextOr_nil"))
        except Exception:
            pass
    return results


def _r0092_nextOr_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nextOr_concat
    # nextOr (xs ++ [x]) x d = d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: List_nextOr_concat"))
        except Exception:
            pass
    return results


def _r0093_next_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_singleton
    # next [y] x h = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "next", 3)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_next_singleton"))
        except Exception:
            pass
    return results


def _r0094_next_cons_cons_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_cons_cons_eq
    # next (x :: z :: l) x h = z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "next", 3)
    if args is not None:
        try:
            rhs = OVar("z")
            results.append((rhs, "Mathlib: List_next_cons_cons_eq"))
        except Exception:
            pass
    return results


def _r0095_next_cons_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_cons_concat
    # next (y :: l ++ [x]) x h = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "next", 3)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_next_cons_concat"))
        except Exception:
            pass
    return results


def _r0096_prev_getLast_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_getLast_cons
    # prev (x :: l) x h = getLast (x :: l) (cons_ne_nil _ _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prev", 3)
    if args is not None:
        try:
            rhs = OOp("last", (OOp("x", (OVar("colon_colon"), OVar("l"),)), OOp("cons_ne_nil", (OVar("_unknown"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: List_prev_getLast_cons"))
        except Exception:
            pass
    return results


def _r0097_prev_cons_cons_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_cons_cons_eq
    # prev (x :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prev", 3)
    if args is not None:
        try:
            rhs = OOp("last", (OOp("z", (OVar("colon_colon"), OVar("l"),)), OOp("cons_ne_nil", (OVar("_unknown"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: List_prev_cons_cons_eq"))
        except Exception:
            pass
    return results


def _r0098_prev_cons_cons_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_cons_cons_of_ne
    # prev (y :: x :: l) x h = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prev", 3)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_prev_cons_cons_of_ne"))
        except Exception:
            pass
    return results


def _r0099_prev_ne_cons_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_ne_cons_cons
    # prev (y :: z :: l) x h = prev (z :: l) x (by simpa [hy] using h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prev", 3)
    if args is not None:
        try:
            rhs = OOp("prev", (OOp("z", (OVar("colon_colon"), OVar("l"),)), args[1], OOp("by", (OVar("simpa"), OSeq((OVar("hy"),)), OVar("using"), args[2],)),))
            results.append((rhs, "Mathlib: List_prev_ne_cons_cons"))
        except Exception:
            pass
    return results


def _r0100_prev_next(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_next
    # prev l (next l x hx) (next_mem _ _ _) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prev", 3)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: List_prev_next"))
        except Exception:
            pass
    return results


def _r0101_next_prev(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_prev
    # next l (prev l x hx) (prev_mem _ _ _) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "next", 3)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: List_next_prev"))
        except Exception:
            pass
    return results


def _r0102_isRotated_next_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isRotated_next_eq
    # l.next x hx = l'.next x (h.mem_iff.mp hx)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_next", 2)
    if args is not None:
        try:
            rhs = OOp("l_prime_next", (args[0], OOp("h_mem_iff_mp", (args[1],)),))
            results.append((rhs, "Mathlib: List_isRotated_next_eq"))
        except Exception:
            pass
    return results


def _r0103_isRotated_prev_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isRotated_prev_eq
    # l.prev x hx = l'.prev x (h.mem_iff.mp hx)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_prev", 2)
    if args is not None:
        try:
            rhs = OOp("l_prime_prev", (args[0], OOp("h_mem_iff_mp", (args[1],)),))
            results.append((rhs, "Mathlib: List_isRotated_prev_eq"))
        except Exception:
            pass
    return results


def _r0104_dedup_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_nil
    # dedup [] = ([] : List α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("colon"), OVar("List"), OVar("a"),))
            results.append((rhs, "Mathlib: List_dedup_nil"))
        except Exception:
            pass
    return results


def _r0105_dedup_cons_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_cons_of_mem
    # dedup (a :: l) = dedup l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("dedup", (OVar("l"),))
            results.append((rhs, "Mathlib: List_dedup_cons_of_mem"))
        except Exception:
            pass
    return results


def _r0106_dedup_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_eq_nil
    # l.dedup = [] ↔ l = []
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_dedup")
        if term.canon() == lhs_pattern.canon():
            rhs = OSeq((OVar("iff_l_eq"),))
            results.append((rhs, "Mathlib: List_dedup_eq_nil"))
    except Exception:
        pass
    return results


def _r0107_dedup_append_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Subset.dedup_append_right
    # dedup (xs ++ ys) = dedup ys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("dedup", (OVar("ys"),))
            results.append((rhs, "Mathlib: List_Subset_dedup_append_right"))
        except Exception:
            pass
    return results


def _r0108_dedup_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Disjoint.dedup_append
    # dedup (xs ++ ys) = dedup xs ++ dedup ys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedup", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("dedup", (OVar("xs"),)), OOp("dedup", (OVar("ys"),))))
            results.append((rhs, "Mathlib: List_Disjoint_dedup_append"))
        except Exception:
            pass
    return results


def _r0109_count_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_dedup
    # l.dedup.count a = if a ∈ l then 1 else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_dedup_count", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("if", (args[0],)), OOp("l", (OVar("then"), OLit(1), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: List_count_dedup"))
        except Exception:
            pass
    return results


def _r0110_destutter_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.destutter_nil
    # ([] : List α).destutter R = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "colon_List_a_destutter", 1)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_destutter_nil"))
        except Exception:
            pass
    return results


def _r0111_destutter_cons_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.destutter_cons_cons
    # (a :: b :: l).destutter R = if R a b then a :: destutter' R b l else destutter' R a l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_b_colon_colon_l_destutter", 1)
    if args is not None:
        try:
            rhs = OOp("if", (args[0], OVar("a"), OVar("b"), OVar("then"), OVar("a"), OVar("colon_colon"), OVar("destutter_prime"), args[0], OVar("b"), OVar("l"), OVar("else"), OVar("destutter_prime"), args[0], OVar("a"), OVar("l"),))
            results.append((rhs, "Mathlib: List_destutter_cons_cons"))
        except Exception:
            pass
    return results


def _r0112_destutter_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.destutter_singleton
    # destutter R [a] = [a]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "destutter", 2)
    if args is not None:
        try:
            rhs = OSeq((OVar("a"),))
            results.append((rhs, "Mathlib: List_destutter_singleton"))
        except Exception:
            pass
    return results


def _r0113_isChain_destutter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_destutter
    # ∀ l : List α, (l.destutter R).IsChain R   | [] => .nil   | h :: l => l.isChain_destutter' R h  theorem destutter_of_isCh
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_destutter", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("l", (OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), OVar("l"), OVar("h"), OVar("eq_gt"), OVar("l_destutter_prime_of_isChain_cons"), OVar("_unknown"), OVar("h_at_simp_theorem"), OVar("destutter_eq_self_iff"), OVar("colon"), OVar("forall"), OVar("l"), OVar("colon"), OVar("List"), OVar("a"), OVar("l_destutter"), args[0],)), OOp("iff", (OVar("l"), OOp("l_IsChain", (args[0], OVar("pipe"), OSeq(()), OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: List_isChain_destutter"))
        except Exception:
            pass
    return results


def _r0114_destutter_of_isChain(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.destutter_of_isChain
    # ∀ l : List α, l.IsChain R → l.destutter R = l   | [], _ => rfl   | _ :: l, h => l.destutter'_of_isChain_cons _ h  @[simp
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_destutter", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("l", (OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), OVar("l"), OVar("h"), OVar("eq_gt"), OVar("l_destutter_prime_of_isChain_cons"), OVar("_unknown"), OVar("h_at_simp_theorem"), OVar("destutter_eq_self_iff"), OVar("colon"), OVar("forall"), OVar("l"), OVar("colon"), OVar("List"), OVar("a"), OVar("l_destutter"), args[0],)), OOp("iff", (OVar("l"), OOp("l_IsChain", (args[0], OVar("pipe"), OSeq(()), OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: List_destutter_of_isChain"))
        except Exception:
            pass
    return results


def _r0115_rdrop_concat_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdrop_concat_succ
    # rdrop (l ++ [x]) (n + 1) = rdrop l n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdrop", 2)
    if args is not None:
        try:
            rhs = OOp("rdrop", (OVar("l"), OVar("n"),))
            results.append((rhs, "Mathlib: List_rdrop_concat_succ"))
        except Exception:
            pass
    return results


def _r0116_rtake_concat_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtake_concat_succ
    # rtake (l ++ [x]) (n + 1) = rtake l n ++ [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rtake", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("rtake", (OVar("l"), OVar("n"),)), OSeq((OVar("x"),))))
            results.append((rhs, "Mathlib: List_rtake_concat_succ"))
        except Exception:
            pass
    return results


def _r0117_rdropWhile_concat_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdropWhile_concat_pos
    # rdropWhile p (l ++ [x]) = rdropWhile p l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdropWhile", 2)
    if args is not None:
        try:
            rhs = OOp("rdropWhile", (args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_rdropWhile_concat_pos"))
        except Exception:
            pass
    return results


def _r0118_rtakeWhile_concat_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtakeWhile_concat_pos
    # rtakeWhile p (l ++ [x]) = rtakeWhile p l ++ [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rtakeWhile", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("rtakeWhile", (args[0], OVar("l"),)), OSeq((OVar("x"),))))
            results.append((rhs, "Mathlib: List_rtakeWhile_concat_pos"))
        except Exception:
            pass
    return results


def _r0119_duplicate_cons_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.duplicate_cons_iff
    # x ∈+ y :: l ↔ y = x ∧ x ∈ l ∨ x ∈+ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OVar("x"), OOp("or", (OOp("in", (OVar("x"), OVar("l"))), OOp("x", (OVar("in_plus"), OVar("l"),))))))
            results.append((rhs, "Mathlib: List_duplicate_cons_iff"))
        except Exception:
            pass
    return results


def _r0120_count_finRange(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_finRange
    # count a (finRange n) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: List_count_finRange"))
        except Exception:
            pass
    return results


def _r0121_mp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Forall₂.mp
    # ∀ {l₁ l₂}, Forall₂ Q l₁ l₂ → Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂   | [], [], Forall₂.nil, Forall₂.nil => Forall₂.nil   | a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2", 7)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("gt", (args[6], args[3], args[5], OVar("colon_colon"), args[5], args[5], OVar("colon_colon"), args[5], OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), OVar("eq_gt"), OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2_flip_at_simp_theorem"), OVar("forall_2_same"), OVar("colon"), OVar("forall"), OVar("l_colon_List_a"), OVar("Forall_2"), args[0], OVar("l"), OVar("l"),)), OOp("in", (OOp("forall", (OVar("x"),)), OOp("l", (args[0], OVar("x"), OVar("x"), args[3], OSeq(()), OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: List_Forall_2_mp"))
        except Exception:
            pass
    return results


def _r0122_flip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Forall₂.flip
    # ∀ {a b}, Forall₂ (flip R) b a → Forall₂ R a b   | _, _, Forall₂.nil => Forall₂.nil   | _ :: _, _ :: _, Forall₂.cons h₁ h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2", 7)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("gt", (args[6], args[3], args[5], OVar("colon_colon"), args[5], args[5], OVar("colon_colon"), args[5], OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), OVar("eq_gt"), OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2_flip_at_simp_theorem"), OVar("forall_2_same"), OVar("colon"), OVar("forall"), OVar("l_colon_List_a"), OVar("Forall_2"), args[0], OVar("l"), OVar("l"),)), OOp("in", (OOp("forall", (OVar("x"),)), OOp("l", (args[0], OVar("x"), OVar("x"), args[3], OSeq(()), OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: List_Forall_2_flip"))
        except Exception:
            pass
    return results


def _r0123_rel_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rel_mem
    # (R ⇒ Forall₂ R ⇒ Iff) (· ∈ ·) (· ∈ ·)   | a, b, _, [], [], Forall₂.nil =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R_Forall_2_R_Iff", 9)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_rel_mem"))
        except Exception:
            pass
    return results


def _r0124_rel_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rel_map
    # ((R ⇒ P) ⇒ Forall₂ R ⇒ Forall₂ P) map map   | _, _, _, [], [], Forall₂.nil => Forall₂.nil   | _, _, h, _ :: _, _ :: _, F
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R_P_Forall_2_R_Forall_2_P", 9)
    if args is not None:
        try:
            rhs = OOp("gt", (args[8], args[2], args[7], args[7], OVar("h"), args[7], OVar("colon_colon"), args[7], args[7], OVar("colon_colon"), args[7], OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), OVar("eq_gt"), OVar("Forall_2_cons"), OOp("h", (OVar("h_1"),)), OVar("rel_map_at_h_h_2_theorem"), OVar("rel_append"), OVar("colon"), OOp("Forall_2", (OVar("R"), args[7], OVar("Forall_2"), OVar("R"), args[7], OVar("Forall_2"), OVar("R"),)), OOp("concat", (args[7], args[7])), OOp("concat", (args[7], args[7])), args[2], args[7], args[7], args[7], args[7], args[7], OVar("hl"), OVar("eq_gt"), OVar("hl"), args[2], args[7], args[7], OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), args[7], args[7], OVar("hl"), OVar("eq_gt"), OVar("Forall_2_cons"), OVar("h_1"), OVar("rel_append_h_2_hl_theorem"), OVar("rel_reverse"), OVar("colon"), OOp("Forall_2", (OVar("R"), args[7], OVar("Forall_2"), OVar("R"),)), OVar("reverse"), OVar("reverse"), args[2], args[7], args[7], args[8], OVar("eq_gt"), args[8], args[2], args[7], args[7], OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_rel_map"))
        except Exception:
            pass
    return results


def _r0125_rel_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rel_append
    # (Forall₂ R ⇒ Forall₂ R ⇒ Forall₂ R) (· ++ ·) (· ++ ·)   | [], [], _, _, _, hl => hl   | _, _, Forall₂.cons h₁ h₂, _, _, 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2_R_Forall_2_R_Forall_2_R", 9)
    if args is not None:
        try:
            rhs = OOp("gt", (args[8], args[2], args[7], args[7], OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), args[7], args[7], args[8], OVar("eq_gt"), OVar("Forall_2_cons"), OVar("h_1"), OVar("rel_append_h_2_hl_theorem"), OVar("rel_reverse"), OVar("colon"), OOp("Forall_2", (OVar("R"), args[7], OVar("Forall_2"), OVar("R"),)), OVar("reverse"), OVar("reverse"), args[2], args[7], args[7], OVar("Forall_2_nil"), OVar("eq_gt"), OVar("Forall_2_nil"), args[2], args[7], args[7], OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_rel_append"))
        except Exception:
            pass
    return results


def _r0126_rel_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rel_reverse
    # (Forall₂ R ⇒ Forall₂ R) reverse reverse   | [], [], Forall₂.nil => Forall₂.nil   | _, _, Forall₂.cons h₁ h₂ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2_R_Forall_2_R", 6)
    if args is not None:
        try:
            rhs = OOp("gt", (args[5], args[2], args[4], args[4], OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_rel_reverse"))
        except Exception:
            pass
    return results


def _r0127_rel_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rel_flatten
    # (Forall₂ (Forall₂ R) ⇒ Forall₂ R) flatten flatten   | [], [], Forall₂.nil => Forall₂.nil   | _, _, Forall₂.cons h₁ h₂ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2_Forall_2_R_Forall_2_R", 6)
    if args is not None:
        try:
            rhs = OOp("gt", (args[5], args[2], args[4], args[4], OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), OVar("eq_gt"), OVar("rel_append"), OVar("h_1"), OVar("rel_flatten_h_2_theorem"), OVar("rel_flatMap"), OVar("colon"), OOp("Forall_2", (OVar("R"), args[4], OOp("R", (args[4], OVar("Forall_2"), OVar("P"),)), args[4], OVar("Forall_2"), OVar("P"),)), OOp("Function_swap", (OVar("List_flatMap"),)), OOp("Function_swap", (OVar("List_flatMap"),)),))
            results.append((rhs, "Mathlib: List_rel_flatten"))
        except Exception:
            pass
    return results


def _r0128_rel_filter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rel_filter
    # (Forall₂ R ⇒ Forall₂ R) (filter p) (filter q)   | _, _, Forall₂.nil => Forall₂.nil   | a :: as, b :: bs, Forall₂.cons h₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2_R_Forall_2_R", 6)
    if args is not None:
        try:
            rhs = OOp("gt", (args[5], args[2], OVar("a"), OVar("colon_colon"), OVar("as"), OVar("b"), OVar("colon_colon"), OVar("bs"), OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_rel_filter"))
        except Exception:
            pass
    return results


def _r0129_rel_filterMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rel_filterMap
    # ((R ⇒ Option.Rel P) ⇒ Forall₂ R ⇒ Forall₂ P) filterMap filterMap   | _, _, _, _, _, Forall₂.nil => Forall₂.nil   | f, g,
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R_Option_Rel_P_Forall_2_R_Forall_2_P", 9)
    if args is not None:
        try:
            rhs = OOp("gt", (args[8], args[2], OVar("f"), OVar("g"), OVar("hfg"), OVar("a"), OVar("colon_colon"), OVar("as"), OVar("b"), OVar("colon_colon"), OVar("bs"), OVar("Forall_2_cons"), OVar("h_1"), OVar("h_2"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_rel_filterMap"))
        except Exception:
            pass
    return results


def _r0130_getD_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getD_append
    # (l ++ l').getD n d = l.getD n d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_plus_plus_l_prime_getD", 2)
    if args is not None:
        try:
            rhs = OOp("l_getD", (args[0], args[1],))
            results.append((rhs, "Mathlib: List_getD_append"))
        except Exception:
            pass
    return results


def _r0131_reverseRec_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reverseRec_nil
    # [].reverseRec nil append_singleton = nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reverseRec", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: List_reverseRec_nil"))
        except Exception:
            pass
    return results


def _r0132_reverseRec_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reverseRec_concat
    # (xs ++ [x]).reverseRec nil append_singleton =     append_singleton xs x (xs.reverseRec nil append_singleton)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "xs_plus_plus_x_reverseRec", 2)
    if args is not None:
        try:
            rhs = OOp("append_singleton", (OVar("xs"), OVar("x"), OOp("xs_reverseRec", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: List_reverseRec_concat"))
        except Exception:
            pass
    return results


def _r0133_reverseRecOn_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reverseRecOn_nil
    # reverseRecOn [] nil append_singleton = nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reverseRecOn", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: List_reverseRecOn_nil"))
        except Exception:
            pass
    return results


def _r0134_reverseRecOn_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reverseRecOn_concat
    # (xs ++ [x]).reverseRecOn nil append_singleton =       append_singleton xs x (reverseRecOn xs nil append_singleton)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "xs_plus_plus_x_reverseRecOn", 2)
    if args is not None:
        try:
            rhs = OOp("append_singleton", (OVar("xs"), OVar("x"), OOp("reverseRecOn", (OVar("xs"), args[0], args[1],)),))
            results.append((rhs, "Mathlib: List_reverseRecOn_concat"))
        except Exception:
            pass
    return results


def _r0135_bidirectionalRec_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.bidirectionalRec_nil
    # bidirectionalRec nil singleton cons_append [] = nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bidirectionalRec", 4)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: List_bidirectionalRec_nil"))
        except Exception:
            pass
    return results


def _r0136_bidirectionalRec_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.bidirectionalRec_singleton
    # bidirectionalRec nil singleton cons_append [a] = singleton a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bidirectionalRec", 4)
    if args is not None:
        try:
            rhs = OOp("singleton", (OVar("a"),))
            results.append((rhs, "Mathlib: List_bidirectionalRec_singleton"))
        except Exception:
            pass
    return results


def _r0137_bidirectionalRec_cons_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.bidirectionalRec_cons_append
    # bidirectionalRec nil singleton cons_append (a :: (l ++ [b])) =       cons_append a l b (bidirectionalRec nil singleton c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bidirectionalRec", 4)
    if args is not None:
        try:
            rhs = OOp("cons_append", (OVar("a"), OVar("l"), OVar("b"), OOp("bidirectionalRec", (args[0], args[1], args[2], OVar("l"),)),))
            results.append((rhs, "Mathlib: List_bidirectionalRec_cons_append"))
        except Exception:
            pass
    return results


def _r0138_recNeNil_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.recNeNil_singleton
    # recNeNil singleton cons [x] (cons_ne_nil x []) = singleton x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "recNeNil", 4)
    if args is not None:
        try:
            rhs = OOp("singleton", (OVar("x"),))
            results.append((rhs, "Mathlib: List_recNeNil_singleton"))
        except Exception:
            pass
    return results


def _r0139_recNeNil_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.recNeNil_cons
    # recNeNil singleton cons (x :: xs) (cons_ne_nil x xs) =       cons x xs h (recNeNil singleton cons xs h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "recNeNil", 4)
    if args is not None:
        try:
            rhs = OOp("cons", (OVar("x"), OVar("xs"), OVar("h"), OOp("recNeNil", (args[0], args[1], OVar("xs"), OVar("h"),)),))
            results.append((rhs, "Mathlib: List_recNeNil_cons"))
        except Exception:
            pass
    return results


def _r0140_twoStepInduction_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.twoStepInduction_nil
    # twoStepInduction nil singleton cons_cons [] = nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "twoStepInduction", 4)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: List_twoStepInduction_nil"))
        except Exception:
            pass
    return results


def _r0141_twoStepInduction_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.twoStepInduction_singleton
    # twoStepInduction nil singleton cons_cons [x] = singleton x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "twoStepInduction", 4)
    if args is not None:
        try:
            rhs = OOp("singleton", (OVar("x"),))
            results.append((rhs, "Mathlib: List_twoStepInduction_singleton"))
        except Exception:
            pass
    return results


def _r0142_twoStepInduction_cons_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.twoStepInduction_cons_cons
    # twoStepInduction nil singleton cons_cons (x :: y :: xs) =     cons_cons x y xs     (twoStepInduction nil singleton cons_
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "twoStepInduction", 4)
    if args is not None:
        try:
            rhs = OOp("cons_cons", (OVar("x"), OVar("y"), OVar("xs"), OOp("twoStepInduction", (args[0], args[1], args[2], OVar("xs"),)), OOp("fun", (OVar("y"), OVar("eq_gt"), OVar("twoStepInduction"), args[0], args[1], args[2], OOp("y", (OVar("colon_colon"), OVar("xs"),)),)),))
            results.append((rhs, "Mathlib: List_twoStepInduction_cons_cons"))
        except Exception:
            pass
    return results


def _r0143_singleton_infix_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.singleton_infix_singleton_iff
    # [x] <:+: [y] ↔ x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_singleton_infix_singleton_iff"))
        except Exception:
            pass
    return results


def _r0144_infix_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.infix_singleton_iff
    # xs <:+: [x] ↔ xs = [] ∨ xs = [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OSeq((OVar("or_xs_eq_x"),))
            results.append((rhs, "Mathlib: List_infix_singleton_iff"))
        except Exception:
            pass
    return results


def _r0145_eq_nil_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.eq_nil_of_le
    # Ico n m = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_Ico_eq_nil_of_le"))
        except Exception:
            pass
    return results


def _r0146_self_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.self_empty
    # Ico n n = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_Ico_self_empty"))
        except Exception:
            pass
    return results


def _r0147_inter_consecutive(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.inter_consecutive
    # Ico n m ∩ Ico m l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_Ico_inter_consecutive"))
        except Exception:
            pass
    return results


def _r0148_bagInter_consecutive(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.bagInter_consecutive
    # @List.bagInter ℕ instBEqOfDecidableEq (Ico n m) (Ico m l) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_List_bagInter", 4)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_Ico_bagInter_consecutive"))
        except Exception:
            pass
    return results


def _r0149_succ_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.succ_singleton
    # Ico n (n + 1) = [n]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OSeq((args[0],))
            results.append((rhs, "Mathlib: List_Ico_succ_singleton"))
        except Exception:
            pass
    return results


def _r0150_eq_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.eq_cons
    # Ico n m = n :: Ico (n + 1) m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("colon_colon"), OVar("Ico"), OOp("+", (args[0], OLit(1))), args[1],))
            results.append((rhs, "Mathlib: List_Ico_eq_cons"))
        except Exception:
            pass
    return results


def _r0151_pred_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.pred_singleton
    # Ico (m - 1) m = [m - 1]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Ico", 2)
    if args is not None:
        try:
            rhs = OSeq((OOp("-", (args[1], OLit(1))),))
            results.append((rhs, "Mathlib: List_Ico_pred_singleton"))
        except Exception:
            pass
    return results


def _r0152_mem_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_iterate
    # b ∈ iterate f a n ↔ ∃ m < n, b = f^[m] a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("fpow_m", (OVar("a"),))
            results.append((rhs, "Mathlib: List_mem_iterate"))
        except Exception:
            pass
    return results


def _r0153_setOf_mem_eq_empty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.setOf_mem_eq_empty_iff
    # { x | x ∈ l } = ∅ ↔ l = []
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pipe_x_in_l")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("l"))), OSeq(())))
            results.append((rhs, "Mathlib: List_setOf_mem_eq_empty_iff"))
    except Exception:
        pass
    return results


def _r0154_go_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookmap.go_append
    # lookmap.go f l acc = acc.toListAppend (lookmap f l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lookmap_go", 3)
    if args is not None:
        try:
            rhs = OOp("acc_toListAppend", (OOp("lookmap", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: List_lookmap_go_append"))
        except Exception:
            pass
    return results


def _r0155_go_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.modifyLast.go_concat
    # modifyLast.go f (tl ++ [a]) r = (r.toListAppend <| modifyLast.go f (tl ++ [a]) #[])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "modifyLast_go", 3)
    if args is not None:
        try:
            rhs = OOp("r_toListAppend", (OVar("lt_pipe"), OVar("modifyLast_go"), args[0], OOp("concat", (OVar("tl"), OSeq((OVar("a"),)))), OVar("hash"),))
            results.append((rhs, "Mathlib: List_modifyLast_go_concat"))
        except Exception:
            pass
    return results


def _r0156_modifyLast_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.modifyLast_concat
    # modifyLast f (l ++ [a]) = l ++ [f a]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "modifyLast", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("l"), OSeq((OOp("f", (OVar("a"),)),))))
            results.append((rhs, "Mathlib: List_modifyLast_concat"))
        except Exception:
            pass
    return results


def _r0157_modifyLast_append_of_right_ne_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.modifyLast_append_of_right_ne_nil
    # modifyLast f (l₁ ++ l₂) = l₁ ++ modifyLast f l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "modifyLast", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("l_1"), OOp("modifyLast", (args[0], OVar("l_2"),))))
            results.append((rhs, "Mathlib: List_modifyLast_append_of_right_ne_nil"))
        except Exception:
            pass
    return results


def _r0158_rel_nodup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rel_nodup
    # (Forall₂ r ⇒ (· ↔ ·)) Nodup Nodup   | _, _, Forall₂.nil =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Forall_2_r_iff", 6)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_rel_nodup"))
        except Exception:
            pass
    return results


def _r0159_ne_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.ne_singleton_iff
    # l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("or", (OSeq(()), OOp("in", (OOp("exists", (OVar("y"),)), OOp("l", (OVar("y"),)))))), OVar("x")))
            results.append((rhs, "Mathlib: List_Nodup_ne_singleton_iff"))
        except Exception:
            pass
    return results


def _r0160_nodup_iff_count_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_iff_count_eq_one
    # Nodup l ↔ ∀ a ∈ l, count a l = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: List_nodup_iff_count_eq_one"))
        except Exception:
            pass
    return results


def _r0161_count_eq_one_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_eq_one_of_mem
    # count a l = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: List_count_eq_one_of_mem"))
        except Exception:
            pass
    return results


def _r0162_take_eq_filter_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.take_eq_filter_mem
    # ∀ {l : List α} {n : ℕ} (_ : l.Nodup), l.take n = l.filter (l.take n).elem   | [], n, _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_take", 1)
    if args is not None:
        try:
            rhs = OOp("l_filter", (OVar("l_take_n_elem"), OVar("pipe"), OVar("_unknown"), args[0], OVar("_unknown"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_Nodup_take_eq_filter_mem"))
        except Exception:
            pass
    return results


def _r0163_ofFn_fin_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_fin_append
    # List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_ofFn", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("List_ofFn", (OVar("a"),)), OOp("List_ofFn", (OVar("b"),))))
            results.append((rhs, "Mathlib: List_ofFn_fin_append"))
        except Exception:
            pass
    return results


def _r0164_ofFn_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_const
    # ∀ (n : ℕ) (c : α), (ofFn fun _ : Fin n => c) = replicate n c   | 0, c =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn", 7)
    if args is not None:
        try:
            rhs = OOp("replicate", (args[4], args[6], OVar("pipe"), OVar("_0"), args[6], args[5],))
            results.append((rhs, "Mathlib: List_ofFn_const"))
        except Exception:
            pass
    return results


def _r0165_ofFn_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_cons
    # ofFn (Fin.cons a f) = a :: ofFn f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("ofFn"), OVar("f"),))
            results.append((rhs, "Mathlib: List_ofFn_cons"))
        except Exception:
            pass
    return results


def _r0166_offDiag_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.offDiag_nil
    # offDiag ([] : List α) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "offDiag", 1)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_offDiag_nil"))
        except Exception:
            pass
    return results


def _r0167_offDiag_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.offDiag_singleton
    # offDiag [a] = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "offDiag", 1)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_offDiag_singleton"))
        except Exception:
            pass
    return results


def _r0168_count_offDiag_eq_mul_sub_ite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.count_offDiag_eq_mul_sub_ite
    # count (a, b) l.offDiag = count a l * count b l - if a = b then count a l else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("*", (OOp("count", (OVar("a"), OVar("l"),)), OOp("-", (OOp("count", (OVar("b"), OVar("l"),)), OOp("if", (OVar("a"),)))))), OOp("b", (OVar("then"), OVar("count"), OVar("a"), OVar("l"), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: List_count_offDiag_eq_mul_sub_ite"))
        except Exception:
            pass
    return results


def _r0169_cons_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Pi.cons_def
    # cons _ _ a f =     fun j hj ↦ if h : j = i then h.symm.rec a else f j <| (mem_cons.1 hj).resolve_left h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons", 4)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("fun", (OVar("j"), OVar("hj"), args[1], OVar("if"), OVar("h"), OVar("colon"), OVar("j"),)), OOp("i", (OVar("then"), OVar("h_symm_rec"), args[2], OVar("else"), args[3], OVar("j"), OVar("lt_pipe"), OVar("mem_cons_1_hj_resolve_left"), OVar("h"),))))
            results.append((rhs, "Mathlib: List_Pi_cons_def"))
        except Exception:
            pass
    return results


def _r0170_cons_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Multiset.Pi.cons_coe
    # Multiset.Pi.cons l _ a f = cons _ _ a f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Multiset_Pi_cons", 4)
    if args is not None:
        try:
            rhs = OOp("cons", (args[1], args[1], args[2], args[3],))
            results.append((rhs, "Mathlib: Multiset_Pi_cons_coe"))
        except Exception:
            pass
    return results


def _r0171_pi_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.pi_nil
    # pi [] t = [Pi.nil α]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pi", 2)
    if args is not None:
        try:
            rhs = OSeq((OOp("Pi_nil", (OVar("a"),)),))
            results.append((rhs, "Mathlib: List_pi_nil"))
        except Exception:
            pass
    return results


def _r0172_nil_product(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nil_product
    # (@nil α) ×ˢ l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_nil_a", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_nil_product"))
        except Exception:
            pass
    return results


def _r0173_product_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.product_nil
    # ∀ l : List α, l ×ˢ (@nil β) = []   | [] => rfl   | _ :: l =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("pipe"), OSeq(()), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), OVar("l"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_product_nil"))
        except Exception:
            pass
    return results


def _r0174_nil_sigma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nil_sigma
    # (@nil α).sigma l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_nil_a_sigma", 1)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_nil_sigma"))
        except Exception:
            pass
    return results


def _r0175_sigma_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sigma_nil
    # ∀ l : List α, (l.sigma fun a => @nil (σ a)) = []   | [] => rfl   | _ :: l =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_sigma", 5)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("pipe"), OSeq(()), args[2], OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), OVar("l"), args[2],))
            results.append((rhs, "Mathlib: List_sigma_nil"))
        except Exception:
            pass
    return results


def _r0176_reduceOption_cons_of_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_cons_of_some
    # reduceOption (some x :: l) = x :: l.reduceOption
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reduceOption", 1)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("colon_colon"), OVar("l_reduceOption"),))
            results.append((rhs, "Mathlib: List_reduceOption_cons_of_some"))
        except Exception:
            pass
    return results


def _r0177_reduceOption_cons_of_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_cons_of_none
    # reduceOption (none :: l) = l.reduceOption
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reduceOption", 1)
    if args is not None:
        try:
            rhs = OVar("l_reduceOption")
            results.append((rhs, "Mathlib: List_reduceOption_cons_of_none"))
        except Exception:
            pass
    return results


def _r0178_reduceOption_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_append
    # (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_plus_plus_l_prime_reduceOption")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OVar("l_reduceOption"), OVar("l_prime_reduceOption")))
            results.append((rhs, "Mathlib: List_reduceOption_append"))
    except Exception:
        pass
    return results


def _r0179_reduceOption_eq_nil_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_eq_nil_iff
    # l.reduceOption = [] ↔ ∃ n, l = replicate n none
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_reduceOption")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OSeq(()), OOp("exists", (OVar("n"), OVar("l"),)))), OOp("replicate", (OVar("n"), OVar("none"),))))
            results.append((rhs, "Mathlib: List_reduceOption_eq_nil_iff"))
    except Exception:
        pass
    return results


def _r0180_reduceOption_eq_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_eq_singleton_iff
    # l.reduceOption = [a] ↔ ∃ m n, l = replicate m none ++ some a :: replicate n none
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_reduceOption")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OOp("==", (OOp("iff", (OSeq((OVar("a"),)), OOp("exists", (OVar("m"), OVar("n"), OVar("l"),)))), OOp("replicate", (OVar("m"), OVar("none"),)))), OOp("some", (OVar("a"), OVar("colon_colon"), OVar("replicate"), OVar("n"), OVar("none"),))))
            results.append((rhs, "Mathlib: List_reduceOption_eq_singleton_iff"))
    except Exception:
        pass
    return results


def _r0181_reduceOption_eq_append_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_eq_append_iff
    # l.reduceOption = l'₁ ++ l'₂ ↔       ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.reduceOption = l'₁ ∧ l₂.reduceOption = l'₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_reduceOption")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OVar("l_prime_1"), OOp("concat", (OOp("==", (OOp("iff", (OVar("l_prime_2"), OOp("exists", (OVar("l_1"), OVar("l_2"), OVar("l"),)))), OVar("l_1"))), OOp("==", (OOp("and", (OVar("l_2"), OVar("l_1_reduceOption"))), OOp("==", (OOp("and", (OVar("l_prime_1"), OVar("l_2_reduceOption"))), OVar("l_prime_2")))))))))
            results.append((rhs, "Mathlib: List_reduceOption_eq_append_iff"))
    except Exception:
        pass
    return results


def _r0182_reduceOption_eq_concat_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_eq_concat_iff
    # l.reduceOption = l'.concat a ↔       ∃ l₁ l₂, l = l₁ ++ some a :: l₂ ∧ l₁.reduceOption = l' ∧ l₂.reduceOption = []
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_reduceOption")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OOp("==", (OOp("iff", (OOp("l_prime_concat", (OVar("a"),)), OOp("exists", (OVar("l_1"), OVar("l_2"), OVar("l"),)))), OVar("l_1"))), OOp("==", (OOp("and", (OOp("some", (OVar("a"), OVar("colon_colon"), OVar("l_2"),)), OVar("l_1_reduceOption"))), OOp("==", (OOp("and", (OVar("l_prime"), OVar("l_2_reduceOption"))), OSeq(())))))))
            results.append((rhs, "Mathlib: List_reduceOption_eq_concat_iff"))
    except Exception:
        pass
    return results


def _r0183_reduceOption_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_singleton
    # [x].reduceOption = x.toList
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_reduceOption")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_toList")
            results.append((rhs, "Mathlib: List_reduceOption_singleton"))
    except Exception:
        pass
    return results


def _r0184_reduceOption_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_concat
    # (l.concat x).reduceOption = l.reduceOption ++ x.toList
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_concat_x_reduceOption")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OVar("l_reduceOption"), OVar("x_toList")))
            results.append((rhs, "Mathlib: List_reduceOption_concat"))
    except Exception:
        pass
    return results


def _r0185_reduceOption_concat_of_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_concat_of_some
    # (l.concat (some x)).reduceOption = l.reduceOption.concat x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_concat_some_x_reduceOption")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_reduceOption_concat", (OVar("x"),))
            results.append((rhs, "Mathlib: List_reduceOption_concat_of_some"))
    except Exception:
        pass
    return results


def _r0186_rotate_cons_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_cons_succ
    # (a :: l : List α).rotate (n + 1) = (l ++ [a]).rotate n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_colon_List_a_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("l_plus_plus_a_rotate", (OVar("n"),))
            results.append((rhs, "Mathlib: List_rotate_cons_succ"))
        except Exception:
            pass
    return results


def _r0187_nil_eq_rotate_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nil_eq_rotate_iff
    # [] = l.rotate n ↔ [] = l
    results: List[Tuple[OTerm, str]] = []
    if _is_empty_seq(term):
        try:
            rhs = OOp("==", (OOp("iff", (OOp("l_rotate", (OVar("n"),)), OSeq(()))), OVar("l")))
            results.append((rhs, "Mathlib: List_nil_eq_rotate_iff"))
        except Exception:
            pass
    return results


def _r0188_rotate_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_singleton
    # [x].rotate n = [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_rotate", 1)
    if args is not None:
        try:
            rhs = OSeq((OVar("x"),))
            results.append((rhs, "Mathlib: List_rotate_singleton"))
        except Exception:
            pass
    return results


def _r0189_rotate_eq_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_eq_singleton_iff
    # l.rotate n = [x] ↔ l = [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OSeq((OVar("x_iff_l_eq_x"),))
            results.append((rhs, "Mathlib: List_rotate_eq_singleton_iff"))
        except Exception:
            pass
    return results


def _r0190_isRotated_nil_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isRotated_nil_iff
    # l ~r [] ↔ l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_isRotated_nil_iff"))
        except Exception:
            pass
    return results


def _r0191_keys_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.keys_nil
    # @keys α β [] = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_keys", 3)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_keys_nil"))
        except Exception:
            pass
    return results


def _r0192_eq_of_mk_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.NodupKeys.eq_of_mk_mem
    # b = b'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b_prime")
            results.append((rhs, "Mathlib: List_NodupKeys_eq_of_mk_mem"))
    except Exception:
        pass
    return results


def _r0193_dlookup_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_nil
    # dlookup a [] = @none (β a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dlookup", 2)
    if args is not None:
        try:
            rhs = OOp("at_none", (OOp("b", (args[0],)),))
            results.append((rhs, "Mathlib: List_dlookup_nil"))
        except Exception:
            pass
    return results


def _r0194_dlookup_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dlookup_append
    # (l₁ ++ l₂).dlookup a = (l₁.dlookup a).or (l₂.dlookup a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_1_plus_plus_l_2_dlookup", 1)
    if args is not None:
        try:
            rhs = OOp("l_1_dlookup_a_or", (OOp("l_2_dlookup", (args[0],)),))
            results.append((rhs, "Mathlib: List_dlookup_append"))
        except Exception:
            pass
    return results


def _r0195_lookupAll_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.lookupAll_nil
    # lookupAll a [] = @nil (β a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lookupAll", 2)
    if args is not None:
        try:
            rhs = OOp("at_nil", (OOp("b", (args[0],)),))
            results.append((rhs, "Mathlib: List_lookupAll_nil"))
        except Exception:
            pass
    return results


def _r0196_mem_lookupAll(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_lookupAll
    # ∀ {l : List (Sigma β)}, b ∈ lookupAll a l ↔ Sigma.mk a b ∈ l   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_mem_lookupAll"))
        except Exception:
            pass
    return results


def _r0197_kerase_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kerase_nil
    # @kerase _ β _ a [] = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_kerase", 5)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_kerase_nil"))
        except Exception:
            pass
    return results


def _r0198_kerase_append_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kerase_append_left
    # ∀ {l₁ l₂ : List (Sigma β)}, a ∈ l₁.keys → kerase a (l₁ ++ l₂) = kerase a l₁ ++ l₂   | [], _, h =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kerase", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("kerase", (args[0], OVar("l_1"),)), OOp("l_2", (OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("h"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_kerase_append_left"))
        except Exception:
            pass
    return results


def _r0199_kerase_append_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kerase_append_right
    # ∀ {l₁ l₂ : List (Sigma β)}, a ∉ l₁.keys → kerase a (l₁ ++ l₂) = l₁ ++ kerase a l₂   | [], _, _ => rfl   | _ :: l₁, l₂, h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kerase", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OVar("l_1"), OOp("kerase", (args[0], OVar("l_2"), OVar("pipe"), OVar("_unknown"), OVar("_unknown"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("_unknown"), OVar("colon_colon"), OVar("l_1"), OVar("l_2"), OVar("h"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_kerase_append_right"))
        except Exception:
            pass
    return results


def _r0200_dedupKeys_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedupKeys_cons
    # dedupKeys (x :: l) = kinsert x.1 x.2 (dedupKeys l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dedupKeys", 1)
    if args is not None:
        try:
            rhs = OOp("kinsert", (OVar("x_1"), OVar("x_2"), OOp("dedupKeys", (OVar("l"),)),))
            results.append((rhs, "Mathlib: List_dedupKeys_cons"))
        except Exception:
            pass
    return results


def _r0201_nil_kunion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nil_kunion
    # kunion [] l = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kunion", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: List_nil_kunion"))
        except Exception:
            pass
    return results


def _r0202_kunion_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.kunion_cons
    # kunion (s :: l₁) l₂ = s :: kunion l₁ (kerase s.1 l₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kunion", 2)
    if args is not None:
        try:
            rhs = OOp("s", (OVar("colon_colon"), OVar("kunion"), OVar("l_1"), OOp("kerase", (OVar("s_1"), args[1],)),))
            results.append((rhs, "Mathlib: List_kunion_cons"))
        except Exception:
            pass
    return results


def _r0203_orderedInsert_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.orderedInsert_nil
    # [].orderedInsert r a = [a]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "orderedInsert", 2)
    if args is not None:
        try:
            rhs = OSeq((args[1],))
            results.append((rhs, "Mathlib: List_orderedInsert_nil"))
        except Exception:
            pass
    return results


def _r0204_mem_orderedInsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_orderedInsert
    # a ∈ orderedInsert r b l ↔ a = b ∨ a ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OVar("b"), OOp("in", (args[1], OVar("l")))))
            results.append((rhs, "Mathlib: List_mem_orderedInsert"))
        except Exception:
            pass
    return results


def _r0205_orderedInsert_count(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.orderedInsert_count
    # count a (L.orderedInsert r b) = count a L + if b = a then 1 else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "count", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("+", (OOp("count", (args[0], OVar("L"),)), OOp("if", (OVar("b"),)))), OOp("a", (OVar("then"), OLit(1), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: List_orderedInsert_count"))
        except Exception:
            pass
    return results


def _r0206_orderedInsert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Pairwise.orderedInsert
    # ∀ l, Pairwise r l → Pairwise r (orderedInsert r a l)   | [], _ => pairwise_singleton _ a   | b :: l, h =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Pairwise", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("pairwise_singleton"), args[4], OVar("a"), args[2], OVar("b"), OVar("colon_colon"), OVar("l"), OVar("h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_Pairwise_orderedInsert"))
        except Exception:
            pass
    return results


def _r0207_splitBy_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitBy_nil
    # splitBy r [] = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "splitBy", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_splitBy_nil"))
        except Exception:
            pass
    return results


def _r0208_splitBy_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitBy_eq_nil
    # l.splitBy r = [] ↔ l = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_splitBy", 1)
    if args is not None:
        try:
            rhs = OSeq((OVar("iff_l_eq"),))
            results.append((rhs, "Mathlib: List_splitBy_eq_nil"))
        except Exception:
            pass
    return results


def _r0209_splitByLoop_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitByLoop_append
    # splitBy.loop r (l ++ m) a g [] = (g.reverse ++ a :: l) :: m.splitBy r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "splitBy_loop", 5)
    if args is not None:
        try:
            rhs = OOp("g_reverse_plus_plus_a_colon_colon_l", (OVar("colon_colon"), OVar("m_splitBy"), args[0],))
            results.append((rhs, "Mathlib: List_splitByLoop_append"))
        except Exception:
            pass
    return results


def _r0210_splitBy_append_of_isChain(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitBy_append_of_isChain
    # (l ++ m).splitBy r = l :: m.splitBy r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_plus_plus_m_splitBy", 1)
    if args is not None:
        try:
            rhs = OOp("l", (OVar("colon_colon"), OVar("m_splitBy"), args[0],))
            results.append((rhs, "Mathlib: List_splitBy_append_of_isChain"))
        except Exception:
            pass
    return results


def _r0211_splitBy_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitBy_append
    # (l ++ m).splitBy r = l.splitBy r ++ m.splitBy r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_plus_plus_m_splitBy", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("l_splitBy", (args[0],)), OOp("m_splitBy", (args[0],))))
            results.append((rhs, "Mathlib: List_splitBy_append"))
        except Exception:
            pass
    return results


def _r0212_splitBy_append_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitBy_append_cons
    # (l ++ a :: m).splitBy r = l.splitBy r ++ (a :: m).splitBy r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_plus_plus_a_colon_colon_m_splitBy", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("l_splitBy", (args[0],)), OOp("a_colon_colon_m_splitBy", (args[0],))))
            results.append((rhs, "Mathlib: List_splitBy_append_cons"))
        except Exception:
            pass
    return results


def _r0213_sublists_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublists_nil
    # sublists (@nil α) = [[]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublists", 1)
    if args is not None:
        try:
            rhs = OSeq((OSeq(()),))
            results.append((rhs, "Mathlib: List_sublists_nil"))
        except Exception:
            pass
    return results


def _r0214_sublists_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sublists_cons
    # sublists (a :: l) = sublists l >>= (fun x => [x, a :: x])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sublists", 1)
    if args is not None:
        try:
            rhs = OOp("sublists", (OVar("l"), OVar("gt_gt_eq"), OOp("fun", (OVar("x"), OVar("eq_gt"), OVar("x_a_colon_colon_x"),)),))
            results.append((rhs, "Mathlib: List_sublists_cons"))
        except Exception:
            pass
    return results


def _r0215_mem_sym2_cons_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_sym2_cons_iff
    # z ∈ (x :: xs).sym2 ↔ z = s(x, x) ∨ (∃ y, y ∈ xs ∧ z = s(x, y)) ∨ z ∈ xs.sym2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OVar("s_x_x"), OOp("or", (OOp("==", (OOp("and", (OOp("in", (OOp("exists", (OVar("y"), OVar("y"),)), OVar("xs"))), args[1])), OVar("s_x_y"))), OOp("in", (args[1], OVar("xs_sym2")))))))
            results.append((rhs, "Mathlib: List_mem_sym2_cons_iff"))
        except Exception:
            pass
    return results


def _r0216_sym2_eq_nil_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sym2_eq_nil_iff
    # xs.sym2 = [] ↔ xs = []
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("xs_sym2")
        if term.canon() == lhs_pattern.canon():
            rhs = OSeq((OVar("iff_xs_eq"),))
            results.append((rhs, "Mathlib: List_sym2_eq_nil_iff"))
    except Exception:
        pass
    return results


def _r0217_setOf_mem_sym2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.setOf_mem_sym2
    # {z : Sym2 α | z ∈ xs.sym2} = {x : α | x ∈ xs}.sym2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_colon_Sym2_a_pipe_z_in_xs_sym2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_colon_a_pipe_x_in_xs_sym2")
            results.append((rhs, "Mathlib: List_setOf_mem_sym2"))
    except Exception:
        pass
    return results


def _r0218_toFinsupp_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_nil
    # toFinsupp ([] : List M) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: List_toFinsupp_nil"))
        except Exception:
            pass
    return results


def _r0219_toFinsupp_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_singleton
    # toFinsupp [x] = Finsupp.single 0 x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("Finsupp_single", (OLit(0), OVar("x"),))
            results.append((rhs, "Mathlib: List_toFinsupp_singleton"))
        except Exception:
            pass
    return results


def _r0220_toFinsupp_cons_eq_single_add_embDomain(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinsupp_cons_eq_single_add_embDomain
    # toFinsupp (x::xs) =       Finsupp.single 0 x + (toFinsupp xs).embDomain ⟨Nat.succ, Nat.succ_injective⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinsupp", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("Finsupp_single", (OLit(0), OVar("x"),)), OOp("toFinsupp_xs_embDomain", (OVar("Nat_succ_Nat_succ_injective"),))))
            results.append((rhs, "Mathlib: List_toFinsupp_cons_eq_single_add_embDomain"))
        except Exception:
            pass
    return results


def _r0221_multinomial_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.multinomial_cons
    # (x :: l).multinomial = Nat.choose (x + l.sum) x * l.multinomial
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_colon_colon_l_multinomial")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OOp("Nat_choose", (OOp("+", (OVar("x"), OVar("l_sum"))), OVar("x"),)), OVar("l_multinomial")))
            results.append((rhs, "Mathlib: List_multinomial_cons"))
    except Exception:
        pass
    return results


def _r0222_card_fixedLengthDigits(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.card_fixedLengthDigits
    # Finset.card (fixedLengthDigits hb l) = b ^ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "len", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("b"), OVar("l")))
            results.append((rhs, "Mathlib: List_card_fixedLengthDigits"))
        except Exception:
            pass
    return results


def _r0223_consFixedLengthDigits_head(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.consFixedLengthDigits_head
    # List.head L (ne_empty_of_mem_consFixedLengthDigits hb hL) = d
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "head", 2)
    if args is not None:
        try:
            rhs = OVar("d")
            results.append((rhs, "Mathlib: List_consFixedLengthDigits_head"))
        except Exception:
            pass
    return results


def _r0224_elim_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.TProd.elim_self
    # v.elim mem_cons_self = v.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "v_elim", 1)
    if args is not None:
        try:
            rhs = OVar("v_1")
            results.append((rhs, "Mathlib: List_TProd_elim_self"))
        except Exception:
            pass
    return results


def _r0225_exists_eq_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.exists_eq_cons
    # ∃ (a : α) (as : Vector α n), v = a ::ᵥ as
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("as"),))
            results.append((rhs, "Mathlib: List_Vector_exists_eq_cons"))
        except Exception:
            pass
    return results


def _r0226_toList_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.toList_empty
    # v.toList = []
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_Vector_toList_empty"))
    except Exception:
        pass
    return results


def _r0227_empty_toList_eq_ff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.empty_toList_eq_ff
    # v.toList.isEmpty = false
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_toList_isEmpty")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(False)
            results.append((rhs, "Mathlib: List_Vector_empty_toList_eq_ff"))
    except Exception:
        pass
    return results


def _r0228_get_cons_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.get_cons_nil
    # ∀ {ix : Fin 1} (x : α), get (x ::ᵥ nil) ix = x   | ⟨0, _⟩, _ => rfl  set_option backward.isDefEq.respectTransparency fal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "get", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("x", (OVar("pipe"), OVar("_0"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl_set_option"), OVar("backward_isDefEq_respectTransparency"), OLit(False), OVar("in_at_simp_theorem"), OVar("get_cons_succ"), OOp("a", (OVar("colon"), OVar("a"),)), OOp("v", (OVar("colon"), OVar("Vector"), OVar("a"), OVar("n"),)), OOp("i", (OVar("colon"), OVar("Fin"), OVar("n"),)), OVar("colon"), OVar("get"), OOp("a", (OVar("colon_colon"), OVar("v"),)), OVar("i_succ"),)), OOp("get", (OVar("v"), OVar("i"),))))
            results.append((rhs, "Mathlib: List_Vector_get_cons_nil"))
        except Exception:
            pass
    return results


def _r0229_scanl_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.scanl_nil
    # scanl f b nil = b ::ᵥ nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "scanl", 3)
    if args is not None:
        try:
            rhs = OOp("b", (OVar("colon_colon"), args[2],))
            results.append((rhs, "Mathlib: List_Vector_scanl_nil"))
        except Exception:
            pass
    return results


def _r0230_scanl_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.scanl_cons
    # scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "scanl", 3)
    if args is not None:
        try:
            rhs = OOp("b", (OVar("colon_colon"), OVar("scanl"), args[0], OOp("f", (args[1], OVar("x"),)), OVar("v"),))
            results.append((rhs, "Mathlib: List_Vector_scanl_cons"))
        except Exception:
            pass
    return results


def _r0231_scanl_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.scanl_singleton
    # scanl f b v = b ::ᵥ f b v.head ::ᵥ nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "scanl", 3)
    if args is not None:
        try:
            rhs = OOp("b", (OVar("colon_colon"), args[0], args[1], OVar("v_head"), OVar("colon_colon"), OVar("nil"),))
            results.append((rhs, "Mathlib: List_Vector_scanl_singleton"))
        except Exception:
            pass
    return results


def _r0232_mem_cons_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.mem_cons_iff
    # a' ∈ (a ::ᵥ v).toList ↔ a' = a ∨ a' ∈ v.toList
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OVar("a"), OOp("in", (args[1], OVar("v_toList")))))
            results.append((rhs, "Mathlib: List_Vector_mem_cons_iff"))
        except Exception:
            pass
    return results


def _r0233_snoc_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.snoc_cons
    # (x ::ᵥ xs).snoc y = x ::ᵥ (xs.snoc y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_colon_colon_xs_snoc", 1)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("colon_colon"), OOp("xs_snoc", (args[0],)),))
            results.append((rhs, "Mathlib: List_Vector_snoc_cons"))
        except Exception:
            pass
    return results


def _r0234_exists_pw_disjoint_with_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_pw_disjoint_with_card
    # ∃ o : List (List α),       o.map length = c ∧ (∀ s ∈ o, s.Nodup) ∧ Pairwise List.Disjoint o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 6)
    if args is not None:
        try:
            rhs = OOp("and", (OVar("c"), OOp("and", (OOp("in", (OOp("forall", (OVar("s"),)), OOp("o", (OVar("s_Nodup"),)))), OOp("Pairwise", (OVar("List_Disjoint"), args[0],))))))
            results.append((rhs, "Mathlib: List_exists_pw_disjoint_with_card"))
        except Exception:
            pass
    return results


def _r0235_formPerm_apply_getLast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_apply_getLast
    # formPerm (x :: xs) ((x :: xs).getLast (cons_ne_nil x xs)) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: List_formPerm_apply_getLast"))
        except Exception:
            pass
    return results


def _r0236_toList_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.toList_cons
    # toList (cons a l) = a :: l.toList
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toList", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("colon_colon"), OVar("l_toList"),))
            results.append((rhs, "Mathlib: Lists_toList_cons"))
        except Exception:
            pass
    return results


def _r0237_subset_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.subset_nil
    # l ⊆ Lists'.nil → l = Lists'.nil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Lists_prime_nil")
            results.append((rhs, "Mathlib: Lists_subset_nil"))
    except Exception:
        pass
    return results


def _r0238_isList_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.isList_of_mem
    # ∀ {l : Lists α}, a ∈ l → IsList l   | ⟨_, Lists'.nil⟩, _ => rfl   | ⟨_, Lists'.cons' _ _⟩, _ => rfl  theorem Equiv.antis
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsList", 4)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("iff", (OOp("gt", (OVar("rfl"), args[1], OVar("Lists_prime_cons_prime"), args[3], OVar("eq_gt"), OVar("rfl_theorem"), OVar("Equiv_antisymm_iff"), OVar("l_1_l_2_colon_Lists_prime_a_true"), OVar("colon"), OVar("of_prime"), OVar("l_1"), OVar("tilde"), OVar("of_prime"), OVar("l_2"),)), OOp("subset", (OVar("l_1"), OVar("l_2"))))), OOp("subset", (OVar("l_2"), OVar("l_1")))))
            results.append((rhs, "Mathlib: Lists_isList_of_mem"))
        except Exception:
            pass
    return results


def _r0239_continuous_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.continuous_cons
    # Continuous fun x : α × List α => (x.1::x.2 : List α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "product", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OOp("x_1colon_colon_x_2", (OVar("colon"), OVar("List"), OVar("a"),)),))
            results.append((rhs, "Mathlib: List_continuous_cons"))
        except Exception:
            pass
    return results


def _r0240_toFinset_nonempty_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_nonempty_iff
    # l.toFinset.Nonempty ↔ l ≠ []
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_toFinset_Nonempty")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("!=", (OVar("l"), OSeq(())))
            results.append((rhs, "Mathlib: List_toFinset_nonempty_iff"))
    except Exception:
        pass
    return results


def _r0241_nodup_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_concat
    # (l.concat u).Nodup ↔ u ∉ l ∧ l.Nodup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_concat_u_Nodup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("and", (OOp("not_in", (OVar("u"), OVar("l"))), OVar("l_Nodup")))
            results.append((rhs, "Mathlib: List_nodup_concat"))
    except Exception:
        pass
    return results


def _r0242_mem_offDiag(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.mem_offDiag
    # x ∈ l.offDiag ↔ x.1 ∈ l ∧ x.2 ∈ l ∧ x.1 ≠ x.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OOp("in", (OVar("x_1"), OVar("l"))), OOp("and", (OOp("in", (OVar("x_2"), OVar("l"))), OVar("x_1"))))), OVar("x_2")))
            results.append((rhs, "Mathlib: List_Nodup_mem_offDiag"))
        except Exception:
            pass
    return results


def _r0243_nodupKeys_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodupKeys_cons
    # NodupKeys (s :: l) ↔ s.1 ∉ l.keys ∧ NodupKeys l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NodupKeys", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("not_in", (OVar("s_1"), OVar("l_keys"))), OOp("NodupKeys", (OVar("l"),))))
            results.append((rhs, "Mathlib: List_nodupKeys_cons"))
        except Exception:
            pass
    return results


def _r0244_tfae_cons_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.tfae_cons_of_mem
    # TFAE (a :: l) ↔ (a ↔ b) ∧ TFAE l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "TFAE", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("iff", (OVar("a"), OVar("b"))), OOp("TFAE", (OVar("l"),))))
            results.append((rhs, "Mathlib: List_tfae_cons_of_mem"))
        except Exception:
            pass
    return results


def _r0245_cons_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.cons_subset
    # Lists'.cons a l₁ ⊆ l₂ ↔ a ∈ l₂ ∧ l₁ ⊆ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (OVar("a"), args[1])), OOp("subset", (OVar("l_1"), args[1]))))
            results.append((rhs, "Mathlib: Lists_cons_subset"))
        except Exception:
            pass
    return results


def _r0246_wbtw_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.wbtw_cons
    # (p :: l).Wbtw R ↔ l.Pairwise (Wbtw R p) ∧ l.Wbtw R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_colon_colon_l_Wbtw", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("l_Pairwise", (OOp("Wbtw", (args[0], OVar("p"),)),)), OOp("l_Wbtw", (args[0],))))
            results.append((rhs, "Mathlib: List_wbtw_cons"))
        except Exception:
            pass
    return results


def _r0247_sbtw_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.sbtw_cons
    # (p :: l).Sbtw R ↔ l.Pairwise (Sbtw R p) ∧ l.Sbtw R ∧ l ≠ [p]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_colon_colon_l_Sbtw", 1)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OOp("l_Pairwise", (OOp("Sbtw", (args[0], OVar("p"),)),)), OOp("and", (OOp("l_Sbtw", (args[0],)), OVar("l"))))), OSeq((OVar("p"),))))
            results.append((rhs, "Mathlib: List_sbtw_cons"))
        except Exception:
            pass
    return results


def _r0248_mem_toFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_toFinset
    # a ∈ l.toFinset ↔ a ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("l")))
            results.append((rhs, "Mathlib: List_mem_toFinset"))
        except Exception:
            pass
    return results


def _r0249_exists_mem_cons_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_mem_cons_iff
    # (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OOp("p", (OVar("a"),)), OOp("in", (OOp("exists", (OVar("x"),)), OOp("l", (OVar("p"), OVar("x"),))))))
            results.append((rhs, "Mathlib: List_exists_mem_cons_iff"))
        except Exception:
            pass
    return results


def _r0250_iff_of_mem_imp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.iff_of_mem_imp
    # IsChain R l ↔ IsChain S l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("IsChain", (OVar("S"), args[1],))
            results.append((rhs, "Mathlib: List_IsChain_iff_of_mem_imp"))
        except Exception:
            pass
    return results


def _r0251_iff_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.iff_mem
    # IsChain R l ↔ IsChain (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("IsChain", (OOp("and", (OOp("in", (OOp("fun", (OVar("x"), OVar("y"), OVar("eq_gt"), OVar("x"),)), args[1])), OOp("and", (OOp("in", (OVar("y"), args[1])), OOp("R", (OVar("x"), OVar("y"),)))))), args[1],))
            results.append((rhs, "Mathlib: List_IsChain_iff_mem"))
        except Exception:
            pass
    return results


def _r0252_isChain_cons_split(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons_split
    # IsChain R (a :: (l₁ ++ c :: l₂)) ↔ IsChain R (a :: (l₁ ++ [c])) ∧ IsChain R (c :: l₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsChain", (args[0], OOp("a", (OVar("colon_colon"), OOp("concat", (OVar("l_1"), OSeq((OVar("c"),)))),)),)), OOp("IsChain", (args[0], OOp("c", (OVar("colon_colon"), OVar("l_2"),)),))))
            results.append((rhs, "Mathlib: List_isChain_cons_split"))
        except Exception:
            pass
    return results


def _r0253_isChain_append_cons_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_append_cons_cons
    # IsChain R (l₁ ++ b :: c :: l₂) ↔ IsChain R (l₁ ++ [b]) ∧ R b c ∧ IsChain R (c :: l₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsChain", (args[0], OOp("concat", (OVar("l_1"), OSeq((OVar("b"),)))),)), OOp("and", (OOp("R", (OVar("b"), OVar("c"),)), OOp("IsChain", (args[0], OOp("c", (OVar("colon_colon"), OVar("l_2"),)),))))))
            results.append((rhs, "Mathlib: List_isChain_append_cons_cons"))
        except Exception:
            pass
    return results


def _r0254_isChain_cons_append_cons_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons_append_cons_cons
    # IsChain R (a :: (l₁ ++ b :: c :: l₂)) ↔     IsChain R (a :: (l₁ ++ [b])) ∧ R b c ∧ IsChain R (c :: l₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("IsChain", (args[0], OOp("a", (OVar("colon_colon"), OOp("concat", (OVar("l_1"), OSeq((OVar("b"),)))),)),)), OOp("and", (OOp("R", (OVar("b"), OVar("c"),)), OOp("IsChain", (args[0], OOp("c", (OVar("colon_colon"), OVar("l_2"),)),))))))
            results.append((rhs, "Mathlib: List_isChain_cons_append_cons_cons"))
        except Exception:
            pass
    return results


def _r0255_isChain_cons_append_singleton_iff_forall(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons_append_singleton_iff_forall₂
    # IsChain R (a :: l ++ [b]) ↔ Forall₂ R (a :: l) (l ++ [b])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("Forall_2", (args[0], OOp("a", (OVar("colon_colon"), OVar("l"),)), OOp("concat", (OVar("l"), OSeq((OVar("b"),)))),))
            results.append((rhs, "Mathlib: List_isChain_cons_append_singleton_iff_forall_2"))
        except Exception:
            pass
    return results


def _r0256_mem_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_dedup
    # a ∈ dedup l ↔ a ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("l")))
            results.append((rhs, "Mathlib: List_mem_dedup"))
        except Exception:
            pass
    return results


def _r0257_duplicate_cons_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.duplicate_cons_self_iff
    # x ∈+ x :: l ↔ x ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 4)
    if args is not None:
        try:
            rhs = OOp("in", (args[1], args[3]))
            results.append((rhs, "Mathlib: List_duplicate_cons_self_iff"))
        except Exception:
            pass
    return results


def _r0258_duplicate_cons_iff_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.duplicate_cons_iff_of_ne
    # x ∈+ y :: l ↔ x ∈+ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 4)
    if args is not None:
        try:
            rhs = OOp("x", (args[0], args[3],))
            results.append((rhs, "Mathlib: List_duplicate_cons_iff_of_ne"))
        except Exception:
            pass
    return results


def _r0259_duplicate_iff_two_le_count(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.duplicate_iff_two_le_count
    # x ∈+ l ↔ 2 ≤ count x l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OLit(2), OOp("count", (OVar("x"), args[1],))))
            results.append((rhs, "Mathlib: List_duplicate_iff_two_le_count"))
        except Exception:
            pass
    return results


def _r0260_singleton_infix_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.singleton_infix_iff
    # [x] <:+: xs ↔ x ∈ xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("x"), args[1]))
            results.append((rhs, "Mathlib: List_singleton_infix_iff"))
        except Exception:
            pass
    return results


def _r0261_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Ico.mem
    # l ∈ Ico n m ↔ n ≤ l ∧ l < m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("n"), OOp("<", (OOp("and", (args[0], args[0])), OVar("m")))))
            results.append((rhs, "Mathlib: List_Ico_mem"))
        except Exception:
            pass
    return results


def _r0262_nodup_iff_count_le_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_iff_count_le_one
    # Nodup l ↔ ∀ a, count a l ≤ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("forall", (OVar("a"), OVar("count"), OVar("a"), args[0],)), OLit(1)))
            results.append((rhs, "Mathlib: List_nodup_iff_count_le_one"))
        except Exception:
            pass
    return results


def _r0263_nodup_append_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_append_comm
    # Nodup (l₁ ++ l₂) ↔ Nodup (l₂ ++ l₁)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("nodup", (OOp("concat", (OVar("l_2"), OVar("l_1"))),))
            results.append((rhs, "Mathlib: List_nodup_append_comm"))
        except Exception:
            pass
    return results


def _r0264_mem_diff_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.mem_diff_iff
    # a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (args[0], OVar("l_1"))), OOp("not_in", (args[0], OVar("l_2")))))
            results.append((rhs, "Mathlib: List_Nodup_mem_diff_iff"))
        except Exception:
            pass
    return results


def _r0265_forall_mem_ofFn_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.forall_mem_ofFn_iff
    # (∀ i ∈ ofFn f, P i) ↔ ∀ j : Fin n, P (f j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("forall", (OVar("j"), OVar("colon"), OVar("Fin"), OVar("n"), OVar("P"), OOp("f", (OVar("j"),)),))
            results.append((rhs, "Mathlib: List_forall_mem_ofFn_iff"))
        except Exception:
            pass
    return results


def _r0266_pairwise_cons_cons_iff_of_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.pairwise_cons_cons_iff_of_trans
    # Pairwise R (a :: b :: l) ↔ R a b ∧ Pairwise R (b :: l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Pairwise", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("R", (OVar("a"), OVar("b"),)), OOp("Pairwise", (args[0], OOp("b", (OVar("colon_colon"), OVar("l"),)),))))
            results.append((rhs, "Mathlib: List_pairwise_cons_cons_iff_of_trans"))
        except Exception:
            pass
    return results


def _r0267_mem_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_pi
    # (f ∈ pi l fs) ↔ (∀ i (hi : i ∈ l), f i hi ∈ fs i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("i"), OVar("hi_colon_i_in_l"), args[0], OVar("i"), OVar("hi"),)), OOp("fs", (OVar("i"),))))
            results.append((rhs, "Mathlib: List_mem_pi"))
        except Exception:
            pass
    return results


def _r0268_mem_product(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_product
    # (a, b) ∈ l₁ ×ˢ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (OVar("a"), OVar("l_1"))), OOp("in", (OVar("b"), OVar("l_2")))))
            results.append((rhs, "Mathlib: List_mem_product"))
        except Exception:
            pass
    return results


def _r0269_mem_sigma(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_sigma
    # Sigma.mk a b ∈ l₁.sigma l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (OVar("a"), OVar("l_1"))), OOp("in", (OVar("b"), OOp("l_2", (OVar("a"),))))))
            results.append((rhs, "Mathlib: List_mem_sigma"))
        except Exception:
            pass
    return results


def _r0270_isChain_cons_range_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons_range_succ
    # IsChain r (a :: range n.succ) ↔ r a 0 ∧ ∀ m < n, r m m.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("and", (OOp("r", (OVar("a"), OLit(0),)), OOp("forall", (OVar("m"),)))), OOp("n", (args[0], OVar("m"), OVar("m_succ"),))))
            results.append((rhs, "Mathlib: List_isChain_cons_range_succ"))
        except Exception:
            pass
    return results


def _r0271_reduceOption_mem_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.reduceOption_mem_iff
    # x ∈ l.reduceOption ↔ some x ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("some", (args[0],)), OVar("l")))
            results.append((rhs, "Mathlib: List_reduceOption_mem_iff"))
        except Exception:
            pass
    return results


def _r0272_mem_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsRotated.mem_iff
    # a ∈ l ↔ a ∈ l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("l_prime")))
            results.append((rhs, "Mathlib: List_IsRotated_mem_iff"))
        except Exception:
            pass
    return results


def _r0273_mem_sections(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_sections
    # f ∈ sections L ↔ Forall₂ (· ∈ ·) f L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("Forall_2", (OOp("in", (OVar("_unknown"), OVar("_unknown"))), args[0], OVar("L"),))
            results.append((rhs, "Mathlib: List_mem_sections"))
        except Exception:
            pass
    return results


def _r0274_shortlex_cons_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.shortlex_cons_iff
    # Shortlex r (a :: s) (a :: t) ↔ Shortlex r s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Shortlex", 3)
    if args is not None:
        try:
            rhs = OOp("Shortlex", (args[0], OVar("s"), OVar("t"),))
            results.append((rhs, "Mathlib: List_shortlex_cons_iff"))
        except Exception:
            pass
    return results


def _r0275_shortlex_singleton_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.shortlex_singleton_iff
    # Shortlex r [a] [b] ↔ r a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Shortlex", 3)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: List_shortlex_singleton_iff"))
        except Exception:
            pass
    return results


def _r0276_mem_keys(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_keys
    # a ∈ l.keys ↔ ∃ b : β a, Sigma.mk a b ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("b"), OVar("colon"), OVar("b"), args[0], OVar("Sigma_mk"), args[0], OVar("b"),)), OVar("l")))
            results.append((rhs, "Mathlib: List_mem_keys"))
        except Exception:
            pass
    return results


def _r0277_notMem_keys(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.notMem_keys
    # a ∉ l.keys ↔ ∀ b : β a, Sigma.mk a b ∉ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not_in", 2)
    if args is not None:
        try:
            rhs = OOp("not_in", (OOp("forall", (OVar("b"), OVar("colon"), OVar("b"), args[0], OVar("Sigma_mk"), args[0], OVar("b"),)), OVar("l")))
            results.append((rhs, "Mathlib: List_notMem_keys"))
        except Exception:
            pass
    return results


def _r0278_mem_dlookup_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_dlookup_iff
    # b ∈ dlookup a l ↔ Sigma.mk a b ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("Sigma_mk", (OVar("a"), args[0],)), OVar("l")))
            results.append((rhs, "Mathlib: List_mem_dlookup_iff"))
        except Exception:
            pass
    return results


def _r0279_mem_keys_kerase_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_keys_kerase_of_ne
    # a₁ ∈ (kerase a₂ l).keys ↔ a₁ ∈ l.keys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("l_keys")))
            results.append((rhs, "Mathlib: List_mem_keys_kerase_of_ne"))
        except Exception:
            pass
    return results


def _r0280_mem_keys_kunion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_keys_kunion
    # a ∈ (kunion l₁ l₂).keys ↔ a ∈ l₁.keys ∨ a ∈ l₂.keys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OOp("in", (args[0], OVar("l_1_keys"))), OOp("in", (args[0], OVar("l_2_keys")))))
            results.append((rhs, "Mathlib: List_mem_keys_kunion"))
        except Exception:
            pass
    return results


def _r0281_mem_dlookup_kunion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_dlookup_kunion
    # b ∈ dlookup a (kunion l₁ l₂) ↔ b ∈ dlookup a l₁ ∨ a ∉ l₁.keys ∧ b ∈ dlookup a l₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("or", (OOp("in", (args[0], OOp("dlookup", (OVar("a"), OVar("l_1"),)))), OOp("not_in", (OVar("a"), OVar("l_1_keys"))))), OOp("in", (args[0], OOp("dlookup", (OVar("a"), OVar("l_2"),))))))
            results.append((rhs, "Mathlib: List_mem_dlookup_kunion"))
        except Exception:
            pass
    return results


def _r0282_splitBy_ne_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitBy_ne_nil
    # l.splitBy r ≠ [] ↔ l ≠ []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("l"), OSeq(())))
            results.append((rhs, "Mathlib: List_splitBy_ne_nil"))
        except Exception:
            pass
    return results


def _r0283_mk_mem_sym2_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mk_mem_sym2_iff
    # s(a, b) ∈ xs.sym2 ↔ a ∈ xs ∧ b ∈ xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (OVar("a"), OVar("xs"))), OOp("in", (OVar("b"), OVar("xs")))))
            results.append((rhs, "Mathlib: List_mk_mem_sym2_iff"))
        except Exception:
            pass
    return results


def _r0284_mem_sym2_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_sym2_iff
    # z ∈ xs.sym2 ↔ ∀ y ∈ z, y ∈ xs
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("y"),)), OOp("in", (OOp("z", (OVar("y"),)), OVar("xs")))))
            results.append((rhs, "Mathlib: List_mem_sym2_iff"))
        except Exception:
            pass
    return results


def _r0285_tfae_cons_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.tfae_cons_cons
    # TFAE (a :: b :: l) ↔ (a ↔ b) ∧ TFAE (b :: l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "TFAE", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("iff", (OVar("a"), OVar("b"))), OOp("TFAE", (OOp("b", (OVar("colon_colon"), OVar("l"),)),))))
            results.append((rhs, "Mathlib: List_tfae_cons_cons"))
        except Exception:
            pass
    return results


def _r0286_tfae_cons_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.tfae_cons_self
    # TFAE (a :: a :: l) ↔ TFAE (a :: l)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "TFAE", 1)
    if args is not None:
        try:
            rhs = OOp("TFAE", (OOp("a", (OVar("colon_colon"), OVar("l"),)),))
            results.append((rhs, "Mathlib: List_tfae_cons_self"))
        except Exception:
            pass
    return results


def _r0287_triplewise_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.triplewise_cons
    # (a :: l).Triplewise p ↔ l.Pairwise (p a) ∧ l.Triplewise p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_colon_colon_l_Triplewise", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("l_Pairwise", (OOp("p", (OVar("a"),)),)), OOp("l_Triplewise", (args[0],))))
            results.append((rhs, "Mathlib: List_triplewise_cons"))
        except Exception:
            pass
    return results


def _r0288_triplewise_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.triplewise_append
    # (l₁ ++ l₂).Triplewise p ↔ l₁.Triplewise p ∧ l₂.Triplewise p ∧     (∀ a ∈ l₁, l₂.Pairwise (p a)) ∧ ∀ a ∈ l₂, l₁.Pairwise 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_1_plus_plus_l_2_Triplewise", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("l_1_Triplewise", (args[0],)), OOp("and", (OOp("l_2_Triplewise", (args[0],)), OOp("and", (OOp("in", (OOp("forall", (OVar("a"),)), OOp("l_1", (OVar("l_2_Pairwise"), OOp("p", (OVar("a"),)),)))), OOp("in", (OOp("forall", (OVar("a"),)), OOp("l_2", (OVar("l_1_Pairwise"), OVar("fun"), OVar("x"), OVar("y"), OVar("_unknown"), args[0], OVar("x"), OVar("y"), OVar("a"),))))))))))
            results.append((rhs, "Mathlib: List_triplewise_append"))
        except Exception:
            pass
    return results


def _r0289_mem_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.mem_def
    # a ∈ l ↔ ∃ a' ∈ l.toList, a ~ a'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("a_prime"),)), OOp("l_toList", (args[0], OVar("tilde"), OVar("a_prime"),))))
            results.append((rhs, "Mathlib: Lists_mem_def"))
        except Exception:
            pass
    return results


def _r0290_mem_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Lists.mem_cons
    # a ∈ @cons α y l ↔ a ~ y ∨ a ∈ l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OOp("a", (OVar("tilde"), OVar("y"),)), OOp("in", (args[0], OVar("l")))))
            results.append((rhs, "Mathlib: Lists_mem_cons"))
        except Exception:
            pass
    return results


def _r0291_tendsto_cons_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.tendsto_cons_iff
    # Tendsto f (𝓝 (a::l)) b ↔ Tendsto (fun p : α × List α => f (p.1::p.2)) (𝓝 a ×ˢ 𝓝 l) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Tendsto", 3)
    if args is not None:
        try:
            rhs = OOp("Tendsto", (OOp("product", (OOp("fun", (OVar("p"), OVar("colon"), OVar("a"),)), OOp("List", (OVar("a"), OVar("eq_gt"), args[0], OVar("p_1colon_colon_p_2"),)))), OOp("_unknown", (OVar("a"), OVar("times"), OVar("_unknown"), OVar("l"),)), args[2],))
            results.append((rhs, "Mathlib: List_tendsto_cons_iff"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_list_basic rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "+", "-", "<", "Continuous", "Fin_append", "Fin_cons", "Forall_2", "Forall_2_Forall_2_R_Forall_2_R", "Forall_2_R_Forall_2_R", "Forall_2_R_Forall_2_R_Forall_2_R", "Forall_2_r_iff", "Ico", "IsChain", "IsList", "L_orderedInsert", "List", "ListBlank_append", "ListBlank_cons", "ListBlank_mk", "List_ofFn", "Lists_prime_cons", "Multiset_Pi_cons", "NodupKeys", "Pairwise", "Pi_Lex", "R_Forall_2_R_Iff", "R_Option_Rel_P_Forall_2_R_Forall_2_P", "R_P_Forall_2_R_Forall_2_P", "Shortlex", "Sigma_mk", "TFAE", "Tendsto", "_unknown", "a", "a_b", "a_colon_colon_b_colon_colon_l_destutter", "a_colon_colon_l_Triplewise", "a_colon_colon_l_colon_List_a_rotate", "a_colon_colon_l_dProd", "a_colon_colon_l_dProdIndex", "and", "antidiagonalTuple", "antidiagonalTuple_k_n_Pairwise", "append_ne_nil_of_right_ne_nil", "at_List_bagInter", "at_cons", "at_kerase", "at_keys",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_list_basic axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_list_basic rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_dProdIndex_cons(term, ctx))
    results.extend(_r0001_count_false_add_count_true(term, ctx))
    results.extend(_r0002_count_not_cons(term, ctx))
    results.extend(_r0003_toFinset_cons(term, ctx))
    results.extend(_r0004_set_of_mem_cons(term, ctx))
    results.extend(_r0005_dropLast_append_getLast(term, ctx))
    results.extend(_r0006_countP_erase(term, ctx))
    results.extend(_r0007_nextOr_singleton(term, ctx))
    results.extend(_r0008_nextOr_self_cons_cons(term, ctx))
    results.extend(_r0009_nextOr_cons_of_ne(term, ctx))
    results.extend(_r0010_prev_singleton(term, ctx))
    results.extend(_r0011_dedup_cons_of_notMem(term, ctx))
    results.extend(_r0012_dedup_cons(term, ctx))
    results.extend(_r0013_dedup_append(term, ctx))
    results.extend(_r0014_destutter_sublist(term, ctx))
    results.extend(_r0015_rdropWhile_concat(term, ctx))
    results.extend(_r0016_rdropWhile_concat_neg(term, ctx))
    results.extend(_r0017_rtakeWhile_concat(term, ctx))
    results.extend(_r0018_rtakeWhile_concat_neg(term, ctx))
    results.extend(_r0019_eq_empty_iff(term, ctx))
    results.extend(_r0020_append_consecutive(term, ctx))
    results.extend(_r0021_iterate_eq_nil(term, ctx))
    results.extend(_r0022_reduceOption_nil(term, ctx))
    results.extend(_r0023_rotate_nil(term, ctx))
    results.extend(_r0024_mem_rotate(term, ctx))
    results.extend(_r0025_rotate_eq_nil_iff(term, ctx))
    results.extend(_r0026_singleton_eq_rotate_iff(term, ctx))
    results.extend(_r0027_isRotated_singleton_iff(term, ctx))
    results.extend(_r0028_keys_cons(term, ctx))
    results.extend(_r0029_keys_append(term, ctx))
    results.extend(_r0030_dlookup_cons_eq(term, ctx))
    results.extend(_r0031_dlookup_cons_ne(term, ctx))
    results.extend(_r0032_lookupAll_cons_eq(term, ctx))
    results.extend(_r0033_lookupAll_cons_ne(term, ctx))
    results.extend(_r0034_lookupAll_eq_nil(term, ctx))
    results.extend(_r0035_kerase_cons_eq(term, ctx))
    results.extend(_r0036_kerase_cons_ne(term, ctx))
    results.extend(_r0037_kerase_of_notMem_keys(term, ctx))
    results.extend(_r0038_mem_keys_kinsert(term, ctx))
    results.extend(_r0039_kunion_nil(term, ctx))
    results.extend(_r0040_orderedInsert_cons(term, ctx))
    results.extend(_r0041_orderedInsert_cons_of_le(term, ctx))
    results.extend(_r0042_splitByLoop_eq_append(term, ctx))
    results.extend(_r0043_sublists_singleton(term, ctx))
    results.extend(_r0044_sublistsLen_succ_nil(term, ctx))
    results.extend(_r0045_elim_of_ne(term, ctx))
    results.extend(_r0046_elim_of_mem(term, ctx))
    results.extend(_r0047_snoc_nil(term, ctx))
    results.extend(_r0048_sum_toFinset_count_eq_length(term, ctx))
    results.extend(_r0049_prod_eq_pow_single(term, ctx))
    results.extend(_r0050_dProdIndex_nil(term, ctx))
    results.extend(_r0051_dProd_cons(term, ctx))
    results.extend(_r0052_cons_mk(term, ctx))
    results.extend(_r0053_exists_cons(term, ctx))
    results.extend(_r0054_append_mk(term, ctx))
    results.extend(_r0055_append_assoc(term, ctx))
    results.extend(_r0056_count_not_add_count(term, ctx))
    results.extend(_r0057_count_add_count_not(term, ctx))
    results.extend(_r0058_count_true_add_count_false(term, ctx))
    results.extend(_r0059_count_not_eq_count(term, ctx))
    results.extend(_r0060_count_false_eq_count_true(term, ctx))
    results.extend(_r0061_two_mul_count_bool_of_even(term, ctx))
    results.extend(_r0062_two_mul_count_bool_eq_ite(term, ctx))
    results.extend(_r0063_antidiagonalTuple_zero_right(term, ctx))
    results.extend(_r0064_antidiagonalTuple_pairwise_pi_lex(term, ctx))
    results.extend(_r0065_mem_pi_toList(term, ctx))
    results.extend(_r0066_card_toFinset(term, ctx))
    results.extend(_r0067_toFinset_card_of_nodup(term, ctx))
    results.extend(_r0068_toFinset_nil(term, ctx))
    results.extend(_r0069_toFinset_eq_empty_iff(term, ctx))
    results.extend(_r0070_toFinset_append(term, ctx))
    results.extend(_r0071_mem_pair(term, ctx))
    results.extend(_r0072_singleton_eq(term, ctx))
    results.extend(_r0073_append_eq_has_append(term, ctx))
    results.extend(_r0074_subset_singleton_iff(term, ctx))
    results.extend(_r0075_mem_pure(term, ctx))
    results.extend(_r0076_concat_eq_reverse_cons(term, ctx))
    results.extend(_r0077_getLast_append_singleton(term, ctx))
    results.extend(_r0078_getLast_append_of_right_ne_nil(term, ctx))
    results.extend(_r0079_tail_append_singleton_of_ne_nil(term, ctx))
    results.extend(_r0080_sublist_singleton(term, ctx))
    results.extend(_r0081_idxOf_cons_eq(term, ctx))
    results.extend(_r0082_idxOf_cons_ne(term, ctx))
    results.extend(_r0083_idxOf_append_of_mem(term, ctx))
    results.extend(_r0084_isChain_cons_iff(term, ctx))
    results.extend(_r0085_isChain_isInfix(term, ctx))
    results.extend(_r0086_isChain_iff_forall_rel_of_append_cons_co(term, ctx))
    results.extend(_r0087_cons(term, ctx))
    results.extend(_r0088_exists_isChain_cons_of_relationReflTrans(term, ctx))
    results.extend(_r0089_count_diff(term, ctx))
    results.extend(_r0090_countP_diff(term, ctx))
    results.extend(_r0091_nextOr_nil(term, ctx))
    results.extend(_r0092_nextOr_concat(term, ctx))
    results.extend(_r0093_next_singleton(term, ctx))
    results.extend(_r0094_next_cons_cons_eq(term, ctx))
    results.extend(_r0095_next_cons_concat(term, ctx))
    results.extend(_r0096_prev_getLast_cons(term, ctx))
    results.extend(_r0097_prev_cons_cons_eq(term, ctx))
    results.extend(_r0098_prev_cons_cons_of_ne(term, ctx))
    results.extend(_r0099_prev_ne_cons_cons(term, ctx))
    results.extend(_r0100_prev_next(term, ctx))
    results.extend(_r0101_next_prev(term, ctx))
    results.extend(_r0102_isRotated_next_eq(term, ctx))
    results.extend(_r0103_isRotated_prev_eq(term, ctx))
    results.extend(_r0104_dedup_nil(term, ctx))
    results.extend(_r0105_dedup_cons_of_mem(term, ctx))
    results.extend(_r0106_dedup_eq_nil(term, ctx))
    results.extend(_r0107_dedup_append_right(term, ctx))
    results.extend(_r0108_dedup_append(term, ctx))
    results.extend(_r0109_count_dedup(term, ctx))
    results.extend(_r0110_destutter_nil(term, ctx))
    results.extend(_r0111_destutter_cons_cons(term, ctx))
    results.extend(_r0112_destutter_singleton(term, ctx))
    results.extend(_r0113_isChain_destutter(term, ctx))
    results.extend(_r0114_destutter_of_isChain(term, ctx))
    results.extend(_r0115_rdrop_concat_succ(term, ctx))
    results.extend(_r0116_rtake_concat_succ(term, ctx))
    results.extend(_r0117_rdropWhile_concat_pos(term, ctx))
    results.extend(_r0118_rtakeWhile_concat_pos(term, ctx))
    results.extend(_r0119_duplicate_cons_iff(term, ctx))
    results.extend(_r0120_count_finRange(term, ctx))
    results.extend(_r0121_mp(term, ctx))
    results.extend(_r0122_flip(term, ctx))
    results.extend(_r0123_rel_mem(term, ctx))
    results.extend(_r0124_rel_map(term, ctx))
    results.extend(_r0125_rel_append(term, ctx))
    results.extend(_r0126_rel_reverse(term, ctx))
    results.extend(_r0127_rel_flatten(term, ctx))
    results.extend(_r0128_rel_filter(term, ctx))
    results.extend(_r0129_rel_filterMap(term, ctx))
    results.extend(_r0130_getD_append(term, ctx))
    results.extend(_r0131_reverseRec_nil(term, ctx))
    results.extend(_r0132_reverseRec_concat(term, ctx))
    results.extend(_r0133_reverseRecOn_nil(term, ctx))
    results.extend(_r0134_reverseRecOn_concat(term, ctx))
    results.extend(_r0135_bidirectionalRec_nil(term, ctx))
    results.extend(_r0136_bidirectionalRec_singleton(term, ctx))
    results.extend(_r0137_bidirectionalRec_cons_append(term, ctx))
    results.extend(_r0138_recNeNil_singleton(term, ctx))
    results.extend(_r0139_recNeNil_cons(term, ctx))
    results.extend(_r0140_twoStepInduction_nil(term, ctx))
    results.extend(_r0141_twoStepInduction_singleton(term, ctx))
    results.extend(_r0142_twoStepInduction_cons_cons(term, ctx))
    results.extend(_r0143_singleton_infix_singleton_iff(term, ctx))
    results.extend(_r0144_infix_singleton_iff(term, ctx))
    results.extend(_r0145_eq_nil_of_le(term, ctx))
    results.extend(_r0146_self_empty(term, ctx))
    results.extend(_r0147_inter_consecutive(term, ctx))
    results.extend(_r0148_bagInter_consecutive(term, ctx))
    results.extend(_r0149_succ_singleton(term, ctx))
    results.extend(_r0150_eq_cons(term, ctx))
    results.extend(_r0151_pred_singleton(term, ctx))
    results.extend(_r0152_mem_iterate(term, ctx))
    results.extend(_r0153_setOf_mem_eq_empty_iff(term, ctx))
    results.extend(_r0154_go_append(term, ctx))
    results.extend(_r0155_go_concat(term, ctx))
    results.extend(_r0156_modifyLast_concat(term, ctx))
    results.extend(_r0157_modifyLast_append_of_right_ne_nil(term, ctx))
    results.extend(_r0158_rel_nodup(term, ctx))
    results.extend(_r0159_ne_singleton_iff(term, ctx))
    results.extend(_r0160_nodup_iff_count_eq_one(term, ctx))
    results.extend(_r0161_count_eq_one_of_mem(term, ctx))
    results.extend(_r0162_take_eq_filter_mem(term, ctx))
    results.extend(_r0163_ofFn_fin_append(term, ctx))
    results.extend(_r0164_ofFn_const(term, ctx))
    results.extend(_r0165_ofFn_cons(term, ctx))
    results.extend(_r0166_offDiag_nil(term, ctx))
    results.extend(_r0167_offDiag_singleton(term, ctx))
    results.extend(_r0168_count_offDiag_eq_mul_sub_ite(term, ctx))
    results.extend(_r0169_cons_def(term, ctx))
    results.extend(_r0170_cons_coe(term, ctx))
    results.extend(_r0171_pi_nil(term, ctx))
    results.extend(_r0172_nil_product(term, ctx))
    results.extend(_r0173_product_nil(term, ctx))
    results.extend(_r0174_nil_sigma(term, ctx))
    results.extend(_r0175_sigma_nil(term, ctx))
    results.extend(_r0176_reduceOption_cons_of_some(term, ctx))
    results.extend(_r0177_reduceOption_cons_of_none(term, ctx))
    results.extend(_r0178_reduceOption_append(term, ctx))
    results.extend(_r0179_reduceOption_eq_nil_iff(term, ctx))
    results.extend(_r0180_reduceOption_eq_singleton_iff(term, ctx))
    results.extend(_r0181_reduceOption_eq_append_iff(term, ctx))
    results.extend(_r0182_reduceOption_eq_concat_iff(term, ctx))
    results.extend(_r0183_reduceOption_singleton(term, ctx))
    results.extend(_r0184_reduceOption_concat(term, ctx))
    results.extend(_r0185_reduceOption_concat_of_some(term, ctx))
    results.extend(_r0186_rotate_cons_succ(term, ctx))
    results.extend(_r0187_nil_eq_rotate_iff(term, ctx))
    results.extend(_r0188_rotate_singleton(term, ctx))
    results.extend(_r0189_rotate_eq_singleton_iff(term, ctx))
    results.extend(_r0190_isRotated_nil_iff(term, ctx))
    results.extend(_r0191_keys_nil(term, ctx))
    results.extend(_r0192_eq_of_mk_mem(term, ctx))
    results.extend(_r0193_dlookup_nil(term, ctx))
    results.extend(_r0194_dlookup_append(term, ctx))
    results.extend(_r0195_lookupAll_nil(term, ctx))
    results.extend(_r0196_mem_lookupAll(term, ctx))
    results.extend(_r0197_kerase_nil(term, ctx))
    results.extend(_r0198_kerase_append_left(term, ctx))
    results.extend(_r0199_kerase_append_right(term, ctx))
    results.extend(_r0200_dedupKeys_cons(term, ctx))
    results.extend(_r0201_nil_kunion(term, ctx))
    results.extend(_r0202_kunion_cons(term, ctx))
    results.extend(_r0203_orderedInsert_nil(term, ctx))
    results.extend(_r0204_mem_orderedInsert(term, ctx))
    results.extend(_r0205_orderedInsert_count(term, ctx))
    results.extend(_r0206_orderedInsert(term, ctx))
    results.extend(_r0207_splitBy_nil(term, ctx))
    results.extend(_r0208_splitBy_eq_nil(term, ctx))
    results.extend(_r0209_splitByLoop_append(term, ctx))
    results.extend(_r0210_splitBy_append_of_isChain(term, ctx))
    results.extend(_r0211_splitBy_append(term, ctx))
    results.extend(_r0212_splitBy_append_cons(term, ctx))
    results.extend(_r0213_sublists_nil(term, ctx))
    results.extend(_r0214_sublists_cons(term, ctx))
    results.extend(_r0215_mem_sym2_cons_iff(term, ctx))
    results.extend(_r0216_sym2_eq_nil_iff(term, ctx))
    results.extend(_r0217_setOf_mem_sym2(term, ctx))
    results.extend(_r0218_toFinsupp_nil(term, ctx))
    results.extend(_r0219_toFinsupp_singleton(term, ctx))
    results.extend(_r0220_toFinsupp_cons_eq_single_add_embDomain(term, ctx))
    results.extend(_r0221_multinomial_cons(term, ctx))
    results.extend(_r0222_card_fixedLengthDigits(term, ctx))
    results.extend(_r0223_consFixedLengthDigits_head(term, ctx))
    results.extend(_r0224_elim_self(term, ctx))
    results.extend(_r0225_exists_eq_cons(term, ctx))
    results.extend(_r0226_toList_empty(term, ctx))
    results.extend(_r0227_empty_toList_eq_ff(term, ctx))
    results.extend(_r0228_get_cons_nil(term, ctx))
    results.extend(_r0229_scanl_nil(term, ctx))
    results.extend(_r0230_scanl_cons(term, ctx))
    results.extend(_r0231_scanl_singleton(term, ctx))
    results.extend(_r0232_mem_cons_iff(term, ctx))
    results.extend(_r0233_snoc_cons(term, ctx))
    results.extend(_r0234_exists_pw_disjoint_with_card(term, ctx))
    results.extend(_r0235_formPerm_apply_getLast(term, ctx))
    results.extend(_r0236_toList_cons(term, ctx))
    results.extend(_r0237_subset_nil(term, ctx))
    results.extend(_r0238_isList_of_mem(term, ctx))
    results.extend(_r0239_continuous_cons(term, ctx))
    results.extend(_r0240_toFinset_nonempty_iff(term, ctx))
    results.extend(_r0241_nodup_concat(term, ctx))
    results.extend(_r0242_mem_offDiag(term, ctx))
    results.extend(_r0243_nodupKeys_cons(term, ctx))
    results.extend(_r0244_tfae_cons_of_mem(term, ctx))
    results.extend(_r0245_cons_subset(term, ctx))
    results.extend(_r0246_wbtw_cons(term, ctx))
    results.extend(_r0247_sbtw_cons(term, ctx))
    results.extend(_r0248_mem_toFinset(term, ctx))
    results.extend(_r0249_exists_mem_cons_iff(term, ctx))
    results.extend(_r0250_iff_of_mem_imp(term, ctx))
    results.extend(_r0251_iff_mem(term, ctx))
    results.extend(_r0252_isChain_cons_split(term, ctx))
    results.extend(_r0253_isChain_append_cons_cons(term, ctx))
    results.extend(_r0254_isChain_cons_append_cons_cons(term, ctx))
    results.extend(_r0255_isChain_cons_append_singleton_iff_forall(term, ctx))
    results.extend(_r0256_mem_dedup(term, ctx))
    results.extend(_r0257_duplicate_cons_self_iff(term, ctx))
    results.extend(_r0258_duplicate_cons_iff_of_ne(term, ctx))
    results.extend(_r0259_duplicate_iff_two_le_count(term, ctx))
    results.extend(_r0260_singleton_infix_iff(term, ctx))
    results.extend(_r0261_mem(term, ctx))
    results.extend(_r0262_nodup_iff_count_le_one(term, ctx))
    results.extend(_r0263_nodup_append_comm(term, ctx))
    results.extend(_r0264_mem_diff_iff(term, ctx))
    results.extend(_r0265_forall_mem_ofFn_iff(term, ctx))
    results.extend(_r0266_pairwise_cons_cons_iff_of_trans(term, ctx))
    results.extend(_r0267_mem_pi(term, ctx))
    results.extend(_r0268_mem_product(term, ctx))
    results.extend(_r0269_mem_sigma(term, ctx))
    results.extend(_r0270_isChain_cons_range_succ(term, ctx))
    results.extend(_r0271_reduceOption_mem_iff(term, ctx))
    results.extend(_r0272_mem_iff(term, ctx))
    results.extend(_r0273_mem_sections(term, ctx))
    results.extend(_r0274_shortlex_cons_iff(term, ctx))
    results.extend(_r0275_shortlex_singleton_iff(term, ctx))
    results.extend(_r0276_mem_keys(term, ctx))
    results.extend(_r0277_notMem_keys(term, ctx))
    results.extend(_r0278_mem_dlookup_iff(term, ctx))
    results.extend(_r0279_mem_keys_kerase_of_ne(term, ctx))
    results.extend(_r0280_mem_keys_kunion(term, ctx))
    results.extend(_r0281_mem_dlookup_kunion(term, ctx))
    results.extend(_r0282_splitBy_ne_nil(term, ctx))
    results.extend(_r0283_mk_mem_sym2_iff(term, ctx))
    results.extend(_r0284_mem_sym2_iff(term, ctx))
    results.extend(_r0285_tfae_cons_cons(term, ctx))
    results.extend(_r0286_tfae_cons_self(term, ctx))
    results.extend(_r0287_triplewise_cons(term, ctx))
    results.extend(_r0288_triplewise_append(term, ctx))
    results.extend(_r0289_mem_def(term, ctx))
    results.extend(_r0290_mem_cons(term, ctx))
    results.extend(_r0291_tendsto_cons_iff(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_list_basic rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("List_prod_le_pow_card", "l_prod_le_n_pow_l_length", "Not an equality or iff proposition"),
    ("List_pow_card_le_prod", "n_pow_l_length_le_l_prod", "Not an equality or iff proposition"),
    ("List_le_prod_of_mem", "x_le_xs_prod", "Not an equality or iff proposition"),
    ("List_wbtw_nil", "colon_List_P_Wbtw_R", "Not an equality or iff proposition"),
    ("List_sbtw_nil", "colon_List_P_Sbtw_R", "Not an equality or iff proposition"),
    ("List_wbtw_singleton", "p_1_Wbtw_R", "Not an equality or iff proposition"),
    ("List_sbtw_singleton", "p_1_Sbtw_R", "Not an equality or iff proposition"),
    ("List_any_of_mem", "any_l_p", "Not an equality or iff proposition"),
    ("List_IsChain_count_not_le_count_add_one", "count_bangb_l_le_count_b_l_plus_1", "Not an equality or iff proposition"),
    ("List_IsChain_count_false_le_count_true_add_one", "count_false_l_le_count_true_l_plus_1", "Not an equality or iff proposition"),
    ("List_IsChain_count_true_le_count_false_add_one", "count_true_l_le_count_false_l_plus_1", "Not an equality or iff proposition"),
    ("List_IsChain_length_sub_one_le_two_mul_count_bool", "length_l_minus_1_le_2_star_count_b_l", "Not an equality or iff proposition"),
    ("List_IsChain_length_div_two_le_count_bool", "length_l_slash_2_le_count_b_l", "Not an equality or iff proposition"),
    ("List_IsChain_two_mul_count_bool_le_length_add_one", "_2_star_count_b_l_le_length_l_plus_1", "Not an equality or iff proposition"),
    ("List_Pi_mem_enum", "f_in_Pi_enum_b", "Not an equality or iff proposition"),
    ("List_Nodup_length_le_natCard", "l_length_le_Nat_card_a", "Not an equality or iff proposition"),
    ("List_Nodup_length_le_enatCard", "l_length_le_ENat_card_a", "Not an equality or iff proposition"),
    ("List_toFinset_card_le", "hash_l_toFinset_le_l_length", "Not an equality or iff proposition"),
    ("List_Nodup_length_le_card", "l_length_le_Fintype_card_a", "Not an equality or iff proposition"),
    ("List_forall_mem_of_forall_mem_cons", "forall_x_in_l_p_x", "Not an equality or iff proposition"),
    ("List_exists_mem_cons_of", "exists_x_in_a_colon_colon_l_p_x", "Not an equality or iff proposition"),
    ("List_exists_mem_cons_of_exists", "exists_x_in_l_p_x_to_exists_x_in_a_colon_colon_l_p_x", "Not an equality or iff proposition"),
    ("List_or_exists_of_exists_mem_cons", "exists_x_in_a_colon_colon_l_p_x_to_p_a_or_exists_x_in_l_p_x", "Not an equality or iff proposition"),
    ("List_cons_subset_of_subset_of_mem", "acolon_colon_l_sub_m", "Not an equality or iff proposition"),
    ("List_append_subset_of_subset_of_subset", "l_1_plus_plus_l_2_sub_l", "Not an equality or iff proposition"),
    ("List_replicate_subset_singleton", "replicate_n_a_sub_a", "Not an equality or iff proposition"),
    ("List_reverse_concat", "_unknown", "Empty proposition"),
    ("List_getLast_concat", "_unknown", "Empty proposition"),
    ("List_dropLast_append_getLast", "_unknown", "Empty proposition"),
    ("List_cons_sublist_cons", "_unknown", "Empty proposition"),
    ("List_sublist_cons_of_sublist", "l_1_lt_plus_a_colon_colon_l_2", "Not an equality or iff proposition"),
    ("List_Sublist_of_cons_of_ne", "a_colon_colon_l_1_lt_plus_l_2", "Not an equality or iff proposition"),
    ("List_isChain_nil", "IsChain_R", "Not an equality or iff proposition"),
    ("List_isChain_singleton", "IsChain_R_a", "Not an equality or iff proposition"),
    ("List_IsChain_imp_of_mem_imp", "IsChain_S_l", "Not an equality or iff proposition"),
    ("List_IsChain_rel_cons", "R_a_b", "Not an equality or iff proposition"),
    ("List_IsChain_cons_of_ne_nil", "IsChain_R_x_colon_colon_l", "Not an equality or iff proposition"),
    ("List_IsChain_append", "IsChain_R_l_1_plus_plus_l_2", "Not an equality or iff proposition"),
    ("List_IsChain_left_of_append", "IsChain_R_l_1", "Not an equality or iff proposition"),
    ("List_IsChain_right_of_append", "IsChain_R_l_2", "Not an equality or iff proposition"),
    ("List_IsChain_append_overlap", "IsChain_R_l_1_plus_plus_l_2_plus_plus_l_3", "Not an equality or iff proposition"),
    ("List_IsChain_cons_induction", "forall_i_in_l_p_i", "Not an equality or iff proposition"),
    ("List_IsChain_concat_induction", "forall_i_in_l_plus_plus_b_p_i", "Not an equality or iff proposition"),
    ("List_IsChain_concat_induction_head", "p_b", "Not an equality or iff proposition"),
    ("List_IsChain_backwards_concat_induction", "forall_i_in_l_p_i", "Not an equality or iff proposition"),
    ("List_IsChain_backwards_cons_induction", "forall_i_in_a_colon_colon_l_p_i", "Not an equality or iff proposition"),
    ("List_relationReflTransGen_of_exists_isChain_cons", "Relation_ReflTransGen_r_a_b", "Not an equality or iff proposition"),
    ("List_IsChain_cons_of_le", "List_IsChain_gt_a_colon_colon_m", "Not an equality or iff proposition"),
    ("List_IsChain_isChain_cons", "v_colon_colon_l_IsChain_R", "Not an equality or iff proposition"),
    ("List_mem_of_nextOr_ne", "x_in_xs", "Not an equality or iff proposition"),
    ("List_nextOr_mem", "nextOr_xs_x_d_in_xs", "Not an equality or iff proposition"),
    ("List_next_cons_cons_eq", "_unknown", "Empty proposition"),
    ("List_prev_cons_cons_eq", "_unknown", "Empty proposition"),
    ("List_prev_cons_cons_of_ne", "_unknown", "Empty proposition"),
    ("List_next_mem", "l_next_x_h_in_l", "Not an equality or iff proposition"),
    ("List_prev_mem", "l_prev_x_h_in_l", "Not an equality or iff proposition"),
    ("List_dedup_cons_of_mem", "_unknown", "Empty proposition"),
    ("List_dedup_cons_of_notMem", "_unknown", "Empty proposition"),
    ("List_dedup_cons", "_unknown", "Empty proposition"),
    ("List_mem_destutter", "_unknown", "Empty proposition"),
    ("List_isChain_cons_destutter", "_unknown", "Empty proposition"),
    ("List_destutter_cons", "_unknown", "Empty proposition"),
    ("List_Mem_duplicate_cons_self", "x_in_plus_x_colon_colon_l", "Not an equality or iff proposition"),
    ("List_Duplicate_duplicate_cons", "x_in_plus_y_colon_colon_l", "Not an equality or iff proposition"),
    ("List_Duplicate_mem", "x_in_l", "Not an equality or iff proposition"),
    ("List_Duplicate_mem_cons_self", "x_in_l", "Not an equality or iff proposition"),
    ("List_Duplicate_ne_nil", "l_ne", "Not an equality or iff proposition"),
    ("List_not_duplicate_nil", "not_x_in_plus", "Not an equality or iff proposition"),
    ("List_Duplicate_ne_singleton", "l_ne_y", "Not an equality or iff proposition"),
    ("List_not_duplicate_singleton", "not_x_in_plus_y", "Not an equality or iff proposition"),
    ("List_Duplicate_elim_nil", "False", "Not an equality or iff proposition"),
    ("List_Duplicate_elim_singleton", "False", "Not an equality or iff proposition"),
    ("List_Duplicate_of_duplicate_cons", "x_in_plus_l", "Not an equality or iff proposition"),
    ("List_insertIdx_subset_cons", "l_insertIdx_n_a_sub_a_colon_colon_l", "Not an equality or iff proposition"),
    ("List_Ico_notMem_top", "m_notin_Ico_n_m", "Not an equality or iff proposition"),
    ("List_cons_le_cons", "a_colon_colon_l_prime_le_a_colon_colon_l", "Not an equality or iff proposition"),
    ("List_Nodup_cons", "Nodup_a_colon_colon_l", "Not an equality or iff proposition"),
    ("List_nodup_singleton", "Nodup_a", "Not an equality or iff proposition"),
    ("List_Nodup_of_cons", "Nodup_l", "Not an equality or iff proposition"),
    ("List_Nodup_notMem", "a_notin_l", "Not an equality or iff proposition"),
    ("List_not_nodup_cons_of_mem", "a_in_l_to_not_Nodup_a_colon_colon_l", "Not an equality or iff proposition"),
    ("List_Nodup_of_append_left", "Nodup_l_1_plus_plus_l_2_to_Nodup_l_1", "Not an equality or iff proposition"),
    ("List_Nodup_of_append_right", "Nodup_l_1_plus_plus_l_2_to_Nodup_l_2", "Not an equality or iff proposition"),
    ("List_nodup_append", "_unknown", "Empty proposition"),
    ("List_disjoint_of_nodup_append", "Disjoint_l_1_l_2", "Not an equality or iff proposition"),
    ("List_Nodup_append", "Nodup_l_1_plus_plus_l_2", "Not an equality or iff proposition"),
    ("List_Nodup_concat", "l_concat_a_Nodup", "Not an equality or iff proposition"),
    ("List_Nodup_set", "forall_l_colon_List_a_n_colon_a_colon_a_colon_l_Nodup_colon_a_notin_l_l_set_n_a_Nodup_pipe", "Not an equality or iff proposition"),
    ("List_mem_ofFn", "_unknown", "Empty proposition"),
    ("List_Pairwise_cons_cons_of_trans", "R_a_b_to_Pairwise_R_b_colon_colon_l_to_Pairwise_R_a_colon_colon_b_colon_colon_l", "Not an equality or iff proposition"),
    ("List_Palindrome_append_reverse", "Palindrome_l_plus_plus_reverse_l", "Not an equality or iff proposition"),
    ("List_hasPeriod_empty", "HasPeriod_colon_List_a_p", "Not an equality or iff proposition"),
    ("List_HasPeriod_take_append", "HasPeriod_take_n_w_plus_plus_w_p", "Not an equality or iff proposition"),
    ("List_Pi_forall_rel_cons_ext", "forall_j_hj_r_cons_a_1_f_1_j_hj_cons_a_2_f_2_j_hj", "Not an equality or iff proposition"),
    ("List_isRotated_nil_iff", "_unknown", "Empty proposition"),
    ("List_isRotated_singleton_iff", "_unknown", "Empty proposition"),
    ("List_isRotated_concat", "tl_plus_plus_hd_tilde_r_hd_colon_colon_tl", "Not an equality or iff proposition"),
    ("List_isRotated_append", "l_plus_plus_l_prime_tilde_r_l_prime_plus_plus_l", "Not an equality or iff proposition"),
    ("List_IsRotated_cons_append_singleton", "a_colon_colon_l_tilde_r_l_plus_plus_a", "Not an equality or iff proposition"),
    ("List_Shortlex_append_right", "Shortlex_r_s_1_s_2_plus_plus_t", "Not an equality or iff proposition"),
    ("List_Shortlex_append_left", "Shortlex_r_s_plus_plus_t_1_s_plus_plus_t_2", "Not an equality or iff proposition"),
    ("List_mem_keys_of_mem", "s_in_l_to_s_1_in_l_keys", "Not an equality or iff proposition"),
    ("List_exists_of_mem_keys", "exists_b_colon_b_a_Sigma_mk_a_b_in_l", "Not an equality or iff proposition"),
    ("List_nodupKeys_nil", "at_NodupKeys_a_b", "Not an equality or iff proposition"),
    ("List_notMem_keys_of_nodupKeys_cons", "s_1_notin_l_keys", "Not an equality or iff proposition"),
    ("List_nodupKeys_of_nodupKeys_cons", "NodupKeys_l", "Not an equality or iff proposition"),
    ("List_nodupKeys_singleton", "NodupKeys_s", "Not an equality or iff proposition"),
    ("List_mem_ext", "l_0_tilde_l_1", "Not an equality or iff proposition"),
    ("List_of_mem_dlookup", "b_in_dlookup_a_l_to_Sigma_mk_a_b_in_l", "Not an equality or iff proposition"),
    ("List_mem_dlookup", "b_in_dlookup_a_l", "Not an equality or iff proposition"),
    ("List_mem_keys_of_mem_keys_kerase", "a_1_in_kerase_a_2_l_keys_to_a_1_in_l_keys", "Not an equality or iff proposition"),
    ("List_notMem_keys_kerase", "a_notin_kerase_a_l_keys", "Not an equality or iff proposition"),
    ("List_cons_sublist_orderedInsert", "a_colon_colon_c_lt_plus_orderedInsert_r_a_l", "Not an equality or iff proposition"),
    ("List_nil_notMem_splitByLoop", "notin_splitBy_loop_r_l_a_g", "Not an equality or iff proposition"),
    ("List_nil_notMem_splitBy", "notin_l_splitBy_r", "Not an equality or iff proposition"),
    ("List_ne_nil_of_mem_splitBy", "m_ne", "Not an equality or iff proposition"),
    ("List_isChain_of_mem_splitByLoop", "m_IsChain_fun_x_y_r_x_y", "Not an equality or iff proposition"),
    ("List_isChain_of_mem_splitBy", "m_IsChain_fun_x_y_r_x_y", "Not an equality or iff proposition"),
    ("List_left_mem_of_mk_mem_sym2", "a_in_xs", "Not an equality or iff proposition"),
    ("List_right_mem_of_mk_mem_sym2", "b_in_xs", "Not an equality or iff proposition"),
    ("List_mk_mem_sym2", "s_a_b_in_xs_sym2", "Not an equality or iff proposition"),
    ("List_tfae_nil", "TFAE", "Not an equality or iff proposition"),
    ("List_tfae_singleton", "TFAE_p", "Not an equality or iff proposition"),
    ("List_take_concat_get", "_unknown", "Empty proposition"),
    ("List_triplewise_singleton", "a_Triplewise_p", "Not an equality or iff proposition"),
    ("Nat_bijOn_digitsAppend", "_unknown", "Empty proposition"),
    ("List_ne_empty_of_mem_consFixedLengthDigits", "L_ne", "Not an equality or iff proposition"),
    ("List_IsZeckendorfRep_nil", "IsZeckendorfRep", "Not an equality or iff proposition"),
    ("List_Vector_singleton_tail", "forall_v_colon_Vector_a_1_v_tail_eq_Vector_nil_pipe_eq_gt_rfl_at_simp_theorem_tai", "Not an equality or iff proposition"),
    ("List_Vector_not_empty_toList", "not_v_toList_isEmpty", "Not an equality or iff proposition"),
    ("List_Vector_append_def", "HAppend_hAppend_colon_Vector_a_n_to_Vector_a_m_to_Vector_a_n_plus_m_eq_fun_pipe_l_1", "Not an equality or iff proposition"),
    ("List_Vector_mem_cons_self", "a_in_a_colon_colon_v_toList", "Not an equality or iff proposition"),
    ("List_Vector_mem_cons_of_mem", "a_prime_in_a_colon_colon_v_toList", "Not an equality or iff proposition"),
    ("Lists_lt_sizeof_cons", "_unknown", "Empty proposition"),
    ("Lists_mem_equiv_left", "forall_a_a_prime_a_tilde_a_prime_to_a_in_l_iff_a_prime_in_l", "Not an equality or iff proposition"),
    ("List_tendsto_cons", "Tendsto_fun_p_colon_a_times_List_a_eq_gt_List_cons_p_1_p_2_a_times_l_acolon_colon_l", "Not an equality or iff proposition"),
    ("List_Vector_tendsto_cons", "Tendsto_fun_p_colon_a_times_Vector_a_n_eq_gt_p_1_colon_colon_p_2_a_times_l_a_colon_colon_l", "Not an equality or iff proposition"),
]
