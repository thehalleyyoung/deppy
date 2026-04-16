"""Mathlib: List Misc — auto-generated from Mathlib4.

Contains 139 rewrite rules derived from Mathlib theorems.
Plus 82 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_list_misc"
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
# Rewrite rules (139 total)
# ════════════════════════════════════════════════════════════

def _r0000_tail_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.tail_cons
    # ∀ l : ListBlank Γ, (l.cons a).tail = l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_cons_a_tail")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("l")
            results.append((rhs, "Mathlib: Turing_ListBlank_tail_cons"))
    except Exception:
        pass
    return results


def _r0001_idxOf_eq_zero_iff_eq_nil_or_head_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_eq_zero_iff_eq_nil_or_head_eq
    # l.idxOf a = 0 ↔ l = [] ∨ l.head? = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_idxOf", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("l"))), OOp("==", (OOp("or", (OSeq(()), OVar("l_head_q"))), args[0]))))
            results.append((rhs, "Mathlib: List_idxOf_eq_zero_iff_eq_nil_or_head_eq"))
        except Exception:
            pass
    return results


def _r0002_next_cons_eq_next_of_mem_dropLast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_cons_eq_next_of_mem_dropLast
    # next (y :: l) x (mem_cons_of_mem _ <| mem_of_mem_dropLast h) =       next l x (mem_of_mem_dropLast h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "next", 3)
    if args is not None:
        try:
            rhs = OOp("next", (OVar("l"), args[1], OOp("mem_of_mem_dropLast", (OVar("h"),)),))
            results.append((rhs, "Mathlib: List_next_cons_eq_next_of_mem_dropLast"))
        except Exception:
            pass
    return results


def _r0003_headI_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.headI_cons
    # (h :: t).headI = h
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h_colon_colon_t_headI")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("h")
            results.append((rhs, "Mathlib: List_headI_cons"))
    except Exception:
        pass
    return results


def _r0004_rdrop_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdrop_zero
    # rdrop l 0 = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdrop", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: List_rdrop_zero"))
        except Exception:
            pass
    return results


def _r0005_rdrop_eq_reverse_drop_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdrop_eq_reverse_drop_reverse
    # l.rdrop n = reverse (l.reverse.drop n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rdrop", 1)
    if args is not None:
        try:
            rhs = OOp("reverse", (OOp("l_reverse_drop", (args[0],)),))
            results.append((rhs, "Mathlib: List_rdrop_eq_reverse_drop_reverse"))
        except Exception:
            pass
    return results


def _r0006_rtake_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtake_zero
    # rtake l 0 = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rtake", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_rtake_zero"))
        except Exception:
            pass
    return results


def _r0007_rtake_eq_reverse_take_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtake_eq_reverse_take_reverse
    # l.rtake n = reverse (l.reverse.take n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rtake", 1)
    if args is not None:
        try:
            rhs = OOp("reverse", (OOp("l_reverse_take", (args[0],)),))
            results.append((rhs, "Mathlib: List_rtake_eq_reverse_take_reverse"))
        except Exception:
            pass
    return results


def _r0008_rdropWhile_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdropWhile_singleton
    # rdropWhile p [x] = if p x then [] else [x]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdropWhile", 2)
    if args is not None:
        try:
            rhs = OOp("if", (args[0], OVar("x"), OVar("then"), OSeq(()), OVar("else"), OSeq((OVar("x"),)),))
            results.append((rhs, "Mathlib: List_rdropWhile_singleton"))
        except Exception:
            pass
    return results


def _r0009_getD_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getD_replicate
    # getD (replicate n x) i y = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "option_get_or", 3)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: List_getD_replicate"))
        except Exception:
            pass
    return results


def _r0010_cons_eta(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Pi.cons_eta
    # cons _ _ (head f) (tail f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons", 4)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: List_Pi_cons_eta"))
        except Exception:
            pass
    return results


def _r0011_splitLengths_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitLengths_cons
    # (n :: sz).splitLengths l = l.take n :: sz.splitLengths (l.drop n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_colon_colon_sz_splitLengths", 1)
    if args is not None:
        try:
            rhs = OOp("l_take", (OVar("n"), OVar("colon_colon"), OVar("sz_splitLengths"), OOp("l_drop", (OVar("n"),)),))
            results.append((rhs, "Mathlib: List_splitLengths_cons"))
        except Exception:
            pass
    return results


def _r0012_drop_take_append_drop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.drop_take_append_drop
    # (x.drop m).take n ++ x.drop (m + n) = x.drop m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OOp("x_drop", (OVar("m"),))
            results.append((rhs, "Mathlib: List_drop_take_append_drop"))
        except Exception:
            pass
    return results


def _r0013_ofFn_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.ofFn_get
    # ofFn (get v) = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn", 1)
    if args is not None:
        try:
            rhs = OVar("v")
            results.append((rhs, "Mathlib: List_Vector_ofFn_get"))
        except Exception:
            pass
    return results


def _r0014_tail_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.tail_val
    # ∀ v : Vector α n.succ, v.tail.val = v.val.tail   | ⟨_ :: _, _⟩ => rfl   @[simp] theorem tail_nil : (@nil α).tail = nil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_tail_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("v_val_tail", (OVar("pipe"), OVar("colon_colon"), OVar("eq_gt"), OVar("rfl_at_simp_theorem"), OVar("tail_nil"), OVar("colon"), OVar("at_nil_a_tail"),)), OVar("nil")))
            results.append((rhs, "Mathlib: List_Vector_tail_val"))
    except Exception:
        pass
    return results


def _r0015_tail_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.tail_ofFn
    # tail (ofFn f) = ofFn fun i => f i.succ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tail", 1)
    if args is not None:
        try:
            rhs = OOp("ofFn", (OVar("fun"), OVar("i"), OVar("eq_gt"), OVar("f"), OVar("i_succ"),))
            results.append((rhs, "Mathlib: List_Vector_tail_ofFn"))
        except Exception:
            pass
    return results


def _r0016_head_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.head_ofFn
    # head (ofFn f) = f 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "head", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OLit(0),))
            results.append((rhs, "Mathlib: List_Vector_head_ofFn"))
        except Exception:
            pass
    return results


def _r0017_get_cons_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.get_cons_zero
    # get (a ::ᵥ v) 0 = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "get", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: List_Vector_get_cons_zero"))
        except Exception:
            pass
    return results


def _r0018_mem_iff_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.mem_iff_get
    # a ∈ v.toList ↔ ∃ i, v.get i = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: List_Vector_mem_iff_get"))
        except Exception:
            pass
    return results


def _r0019_reverse_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.reverse_cons
    # reverse (x ::ᵥ xs) = (reverse xs).snoc x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reverse", 1)
    if args is not None:
        try:
            rhs = OOp("reverse_xs_snoc", (OVar("x"),))
            results.append((rhs, "Mathlib: List_Vector_reverse_cons"))
        except Exception:
            pass
    return results


def _r0020_prod_take_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_take_ofFn
    # ((ofFn f).take i).prod = ∏ j with j.val < i, f j
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofFn_f_take_i_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<", (OOp("_unknown", (OVar("j"), OVar("with"), OVar("j_val"),)), OOp("i", (OVar("f"), OVar("j"),))))
            results.append((rhs, "Mathlib: List_prod_take_ofFn"))
    except Exception:
        pass
    return results


def _r0021_prod_take_mul_prod_drop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_take_mul_prod_drop
    # (L.take i).prod * (L.drop i).prod = L.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("L_prod")
            results.append((rhs, "Mathlib: List_prod_take_mul_prod_drop"))
        except Exception:
            pass
    return results


def _r0022_prod_take_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_take_succ
    # (L.take (i + 1)).prod = (L.take i).prod * L[i]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L_take_i_plus_1_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("L_take_i_prod"), OVar("L_i")))
            results.append((rhs, "Mathlib: List_prod_take_succ"))
    except Exception:
        pass
    return results


def _r0023_prod_set(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prod_set
    # ∀ (L : List M) (n : ℕ) (a : M),       (L.set n a).prod =         ((L.take n).prod * if n < L.length then a else 1) * (L.
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L_set_n_a_prod")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OOp("<", (OOp("*", (OVar("L_take_n_prod"), OOp("if", (OVar("n"),)))), OOp("L_length", (OVar("then"), OVar("a"), OVar("else"), OLit(1),)))), OOp("L_drop_n_plus_1_prod", (OVar("pipe"), OVar("x"), OVar("colon_colon"), OVar("xs"), OVar("_0"), OVar("a"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_prod_set"))
    except Exception:
        pass
    return results


def _r0024_headI_mul_tail_prod_of_ne_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.headI_mul_tail_prod_of_ne_nil
    # l.headI * l.tail.prod = l.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("l_prod")
            results.append((rhs, "Mathlib: List_headI_mul_tail_prod_of_ne_nil"))
        except Exception:
            pass
    return results


def _r0025_drop_sum_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.drop_sum_flatten
    # L.flatten.drop ((L.map length).take i).sum = (L.drop i).flatten
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_flatten_drop", 1)
    if args is not None:
        try:
            rhs = OVar("L_drop_i_flatten")
            results.append((rhs, "Mathlib: List_drop_sum_flatten"))
        except Exception:
            pass
    return results


def _r0026_splitWrtCompositionAux_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitWrtCompositionAux_cons
    # l.splitWrtCompositionAux (n::ns) = take n l::(drop n l).splitWrtCompositionAux ns
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_splitWrtCompositionAux", 1)
    if args is not None:
        try:
            rhs = OOp("take", (OVar("n"), OVar("lcolon_colon_drop_n_l_splitWrtCompositionAux"), OVar("ns"),))
            results.append((rhs, "Mathlib: List_splitWrtCompositionAux_cons"))
        except Exception:
            pass
    return results


def _r0027_getElem_splitWrtCompositionAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getElem_splitWrtCompositionAux
    # (l.splitWrtCompositionAux ns)[i] =       (l.take (ns.take (i + 1)).sum).drop (ns.take i).sum
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_splitWrtCompositionAux_ns_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_take_ns_take_i_plus_1_sum_drop", (OVar("ns_take_i_sum"),))
            results.append((rhs, "Mathlib: List_getElem_splitWrtCompositionAux"))
    except Exception:
        pass
    return results


def _r0028_getElem_splitWrtComposition(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getElem_splitWrtComposition
    # (l.splitWrtComposition c)[i] = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_splitWrtComposition_c_i")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("l_take_c_sizeUpTo_i_plus_1_drop", (OOp("c_sizeUpTo", (OVar("i"),)),))
            results.append((rhs, "Mathlib: List_getElem_splitWrtComposition"))
    except Exception:
        pass
    return results


def _r0029_head_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.head_mk
    # ListBlank.head (ListBlank.mk l) = l.headI
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ListBlank_head", 1)
    if args is not None:
        try:
            rhs = OVar("l_headI")
            results.append((rhs, "Mathlib: Turing_ListBlank_head_mk"))
        except Exception:
            pass
    return results


def _r0030_tail_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.tail_mk
    # ListBlank.tail (ListBlank.mk l) = ListBlank.mk l.tail
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ListBlank_tail", 1)
    if args is not None:
        try:
            rhs = OOp("ListBlank_mk", (OVar("l_tail"),))
            results.append((rhs, "Mathlib: Turing_ListBlank_tail_mk"))
        except Exception:
            pass
    return results


def _r0031_head_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.head_cons
    # ∀ l : ListBlank Γ, (l.cons a).head = a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_cons_a_head")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Turing_ListBlank_head_cons"))
    except Exception:
        pass
    return results


def _r0032_cons_head_tail(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.cons_head_tail
    # ∀ l : ListBlank Γ, l.tail.cons l.head = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_tail_cons", 1)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: Turing_ListBlank_cons_head_tail"))
        except Exception:
            pass
    return results


def _r0033_nth_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.nth_mk
    # (ListBlank.mk l).nth n = l.getI n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ListBlank_mk_l_nth", 1)
    if args is not None:
        try:
            rhs = OOp("l_getI", (args[0],))
            results.append((rhs, "Mathlib: Turing_ListBlank_nth_mk"))
        except Exception:
            pass
    return results


def _r0034_nth_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.nth_zero
    # l.nth 0 = l.head
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_nth", 1)
    if args is not None:
        try:
            rhs = OVar("l_head")
            results.append((rhs, "Mathlib: Turing_ListBlank_nth_zero"))
        except Exception:
            pass
    return results


def _r0035_nth_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.nth_succ
    # l.nth (n + 1) = l.tail.nth n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_nth", 1)
    if args is not None:
        try:
            rhs = OOp("l_tail_nth", (OVar("n"),))
            results.append((rhs, "Mathlib: Turing_ListBlank_nth_succ"))
        except Exception:
            pass
    return results


def _r0036_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.ext
    # (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("L_2")
            results.append((rhs, "Mathlib: Turing_ListBlank_ext"))
    except Exception:
        pass
    return results


def _r0037_nth_modifyNth(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Turing.ListBlank.nth_modifyNth
    # (L.modifyNth f n).nth i = if i = n then f (L.nth i) else L.nth i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_modifyNth_f_n_nth", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0],)), OOp("n", (OVar("then"), OVar("f"), OOp("L_nth", (args[0],)), OVar("else"), OVar("L_nth"), args[0],))))
            results.append((rhs, "Mathlib: Turing_ListBlank_nth_modifyNth"))
        except Exception:
            pass
    return results


def _r0038_toFinset_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.toFinset_reverse
    # toFinset l.reverse = l.toFinset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toFinset", 1)
    if args is not None:
        try:
            rhs = OVar("l_toFinset")
            results.append((rhs, "Mathlib: List_toFinset_reverse"))
        except Exception:
            pass
    return results


def _r0039_getLast_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getLast_congr
    # getLast l₁ h₁ = getLast l₂ h₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "last", 2)
    if args is not None:
        try:
            rhs = OOp("last", (OVar("l_2"), OVar("h_2"),))
            results.append((rhs, "Mathlib: List_getLast_congr"))
        except Exception:
            pass
    return results


def _r0040_surjective_tail(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.surjective_tail
    # Surjective (@tail α)   | [] => ⟨[], rfl⟩   | a :: l => ⟨a :: a :: l, rfl⟩  theorem eq_cons_of_mem_head? {x : α} : ∀ {l :
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("x", (OVar("colon_colon"), OVar("tail"), OVar("l"), OVar("pipe"), OVar("_unknown"), OVar("h"), OVar("eq_gt"), OVar("Option_not_mem_none_h_elim"), OVar("pipe"), OVar("a"), OVar("colon_colon"), OVar("l"), OVar("h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_surjective_tail"))
    except Exception:
        pass
    return results


def _r0041_get_tail(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_tail
    # l.tail.get ⟨i, h⟩ = l.get ⟨i + 1, h'⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_tail_get", 1)
    if args is not None:
        try:
            rhs = OOp("l_get", (OVar("i_plus_1_h_prime"),))
            results.append((rhs, "Mathlib: List_get_tail"))
        except Exception:
            pass
    return results


def _r0042_idxOf_eq_zero_iff_head_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.idxOf_eq_zero_iff_head_eq
    # l.idxOf a = 0 ↔ l.head hl = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_idxOf", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("l_head", (OVar("hl"),)))), args[0]))
            results.append((rhs, "Mathlib: List_idxOf_eq_zero_iff_head_eq"))
        except Exception:
            pass
    return results


def _r0043_isChain_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_append
    # ∀ {l₁ l₂ : List α},       IsChain R (l₁ ++ l₂) ↔ IsChain R l₁ ∧ IsChain R l₂ ∧ ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_isChain_append"))
        except Exception:
            pass
    return results


def _r0044_isChain_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_flatten
    # ∀ {L : List (List α)}, [] ∉ L →     (IsChain R L.flatten ↔ (∀ l ∈ L, IsChain R l) ∧     L.IsChain (fun l₁ l₂ => ∀ᵉ (x ∈ 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain_R_L_flatten_iff_forall_l_in_L_IsChain_R_l_and_L_IsChain_fun_l_1_l_2_eq_gt_forall_x_in_l_1_getLast_q_y_in_l_2_head_q_R_x_y_pipe", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: List_isChain_flatten"))
        except Exception:
            pass
    return results


def _r0045_exists_isChain_ne_nil_of_relationReflTra(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.exists_isChain_ne_nil_of_relationReflTransGen
    # ∃ l, ∃ (hl : l ≠ []), IsChain r l ∧ l.head hl = a ∧ getLast l hl = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OVar("a"), OOp("last", (OVar("l"), OVar("hl"),)))), OVar("b")))
            results.append((rhs, "Mathlib: List_exists_isChain_ne_nil_of_relationReflTransGen"))
        except Exception:
            pass
    return results


def _r0046_nextOr_eq_nextOr_of_mem_dropLast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nextOr_eq_nextOr_of_mem_dropLast
    # nextOr xs x d = nextOr xs x d'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "or", 3)
    if args is not None:
        try:
            rhs = OOp("or", (args[0], args[1], OVar("d_prime"),))
            results.append((rhs, "Mathlib: List_nextOr_eq_nextOr_of_mem_dropLast"))
        except Exception:
            pass
    return results


def _r0047_next_getLast_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_getLast_cons
    # next (y :: l) x h = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "next", 3)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: List_next_getLast_cons"))
        except Exception:
            pass
    return results


def _r0048_prev_head_eq_getLast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_head_eq_getLast
    # l.prev (l.head hl) (head_mem hl) = l.getLast hl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_prev", 2)
    if args is not None:
        try:
            rhs = OOp("l_getLast", (OVar("hl"),))
            results.append((rhs, "Mathlib: List_prev_head_eq_getLast"))
        except Exception:
            pass
    return results


def _r0049_next_getLast_eq_head_of_notMem_dropLast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_getLast_eq_head_of_notMem_dropLast
    # l.next (l.getLast hl) (getLast_mem hl) = l.head hl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_next", 2)
    if args is not None:
        try:
            rhs = OOp("l_head", (OVar("hl"),))
            results.append((rhs, "Mathlib: List_next_getLast_eq_head_of_notMem_dropLast"))
        except Exception:
            pass
    return results


def _r0050_next_getLast_eq_head(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_getLast_eq_head
    # l.next (l.getLast h) (getLast_mem h) = l.head h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_next", 2)
    if args is not None:
        try:
            rhs = OOp("l_head", (OVar("h"),))
            results.append((rhs, "Mathlib: List_next_getLast_eq_head"))
        except Exception:
            pass
    return results


def _r0051_prev_reverse_eq_next(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.prev_reverse_eq_next
    # prev l.reverse x (mem_reverse.mpr hx) = next l x hx
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prev", 3)
    if args is not None:
        try:
            rhs = OOp("next", (OVar("l"), args[1], OVar("hx"),))
            results.append((rhs, "Mathlib: List_prev_reverse_eq_next"))
        except Exception:
            pass
    return results


def _r0052_next_reverse_eq_prev(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.next_reverse_eq_prev
    # next l.reverse x (mem_reverse.mpr hx) = prev l x hx
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "next", 3)
    if args is not None:
        try:
            rhs = OOp("prev", (OVar("l"), args[1], OVar("hx"),))
            results.append((rhs, "Mathlib: List_next_reverse_eq_prev"))
        except Exception:
            pass
    return results


def _r0053_headI_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.headI_dedup
    # l.dedup.headI = if l.headI ∈ l.tail then l.tail.dedup.headI else l.headI
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_dedup_headI")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("if", (OVar("l_headI"),)), OOp("l_tail", (OVar("then"), OVar("l_tail_dedup_headI"), OVar("else"), OVar("l_headI"),))))
            results.append((rhs, "Mathlib: List_headI_dedup"))
    except Exception:
        pass
    return results


def _r0054_tail_dedup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.tail_dedup
    # l.dedup.tail = if l.headI ∈ l.tail then l.tail.dedup.tail else l.tail.dedup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_dedup_tail")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("if", (OVar("l_headI"),)), OOp("l_tail", (OVar("then"), OVar("l_tail_dedup_tail"), OVar("else"), OVar("l_tail_dedup"),))))
            results.append((rhs, "Mathlib: List_tail_dedup"))
    except Exception:
        pass
    return results


def _r0055_dedup_eq_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dedup_eq_cons
    # l.dedup = a :: l' ↔ a ∈ l ∧ a ∉ l' ∧ l.dedup.tail = l'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l_dedup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("and", (OOp("iff", (OOp("a", (OVar("colon_colon"), OVar("l_prime"),)), OOp("in", (OVar("a"), OVar("l"))))), OOp("and", (OOp("not_in", (OVar("a"), OVar("l_prime"))), OVar("l_dedup_tail"))))), OVar("l_prime")))
            results.append((rhs, "Mathlib: List_dedup_eq_cons"))
    except Exception:
        pass
    return results


def _r0056_headI_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.headI_nil
    # ([] : List α).headI = default
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("colon_List_a_headI")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("default")
            results.append((rhs, "Mathlib: List_headI_nil"))
    except Exception:
        pass
    return results


def _r0057_rdrop_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdrop_nil
    # rdrop ([] : List α) n = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdrop", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_rdrop_nil"))
        except Exception:
            pass
    return results


def _r0058_rtake_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtake_nil
    # rtake ([] : List α) n = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rtake", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_rtake_nil"))
        except Exception:
            pass
    return results


def _r0059_rdropWhile_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdropWhile_nil
    # rdropWhile p ([] : List α) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdropWhile", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_rdropWhile_nil"))
        except Exception:
            pass
    return results


def _r0060_rdropWhile_eq_nil_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdropWhile_eq_nil_iff
    # rdropWhile p l = [] ↔ ∀ x ∈ l, p x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdropWhile", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OSeq(()), OOp("in", (OOp("forall", (OVar("x"),)), OOp("l", (args[0], OVar("x"),))))))
            results.append((rhs, "Mathlib: List_rdropWhile_eq_nil_iff"))
        except Exception:
            pass
    return results


def _r0061_dropWhile_idempotent(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dropWhile_idempotent
    # dropWhile p (dropWhile p l) = dropWhile p l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dropWhile", 2)
    if args is not None:
        try:
            rhs = OOp("dropWhile", (args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_dropWhile_idempotent"))
        except Exception:
            pass
    return results


def _r0062_rdropWhile_idempotent(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdropWhile_idempotent
    # rdropWhile p (rdropWhile p l) = rdropWhile p l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rdropWhile", 2)
    if args is not None:
        try:
            rhs = OOp("rdropWhile", (args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_rdropWhile_idempotent"))
        except Exception:
            pass
    return results


def _r0063_rdropWhile_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdropWhile_reverse
    # l.reverse.rdropWhile p = (l.dropWhile p).reverse
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_reverse_rdropWhile", 1)
    if args is not None:
        try:
            rhs = OVar("l_dropWhile_p_reverse")
            results.append((rhs, "Mathlib: List_rdropWhile_reverse"))
        except Exception:
            pass
    return results


def _r0064_rtakeWhile_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtakeWhile_nil
    # rtakeWhile p ([] : List α) = []
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rtakeWhile", 2)
    if args is not None:
        try:
            rhs = OSeq(())
            results.append((rhs, "Mathlib: List_rtakeWhile_nil"))
        except Exception:
            pass
    return results


def _r0065_rtakeWhile_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtakeWhile_eq_self_iff
    # rtakeWhile p l = l ↔ ∀ x ∈ l, p x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rtakeWhile", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (args[1], OOp("in", (OOp("forall", (OVar("x"),)), OOp("l", (args[0], OVar("x"),))))))
            results.append((rhs, "Mathlib: List_rtakeWhile_eq_self_iff"))
        except Exception:
            pass
    return results


def _r0066_rtakeWhile_idempotent(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtakeWhile_idempotent
    # rtakeWhile p (rtakeWhile p l) = rtakeWhile p l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rtakeWhile", 2)
    if args is not None:
        try:
            rhs = OOp("rtakeWhile", (args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_rtakeWhile_idempotent"))
        except Exception:
            pass
    return results


def _r0067_rtakeWhile_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rtakeWhile_reverse
    # l.reverse.rtakeWhile p = (l.takeWhile p).reverse
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_reverse_rtakeWhile", 1)
    if args is not None:
        try:
            rhs = OVar("l_takeWhile_p_reverse")
            results.append((rhs, "Mathlib: List_rtakeWhile_reverse"))
        except Exception:
            pass
    return results


def _r0068_rdropWhile_append_rtakeWhile(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdropWhile_append_rtakeWhile
    # l.rdropWhile p ++ l.rtakeWhile p = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_rdropWhile_append_rtakeWhile"))
        except Exception:
            pass
    return results


def _r0069_rdrop_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rdrop_add
    # (l.rdrop i).rdrop j = l.rdrop (i + j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rdrop_i_rdrop", 1)
    if args is not None:
        try:
            rhs = OOp("l_rdrop", (OOp("+", (OVar("i"), args[0])),))
            results.append((rhs, "Mathlib: List_rdrop_add"))
        except Exception:
            pass
    return results


def _r0070_drop_take_succ_eq_cons_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.drop_take_succ_eq_cons_getElem
    # (L.take (i + 1)).drop i = [L[i]]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_take_i_plus_1_drop", 1)
    if args is not None:
        try:
            rhs = OSeq((OVar("L_i"),))
            results.append((rhs, "Mathlib: List_drop_take_succ_eq_cons_getElem"))
        except Exception:
            pass
    return results


def _r0071_head_head_eq_head_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.head_head_eq_head_flatten
    # (l.head hl).head hl' = l.flatten.head (flatten_ne_nil_iff.2 ⟨_, head_mem hl, hl'⟩)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_head_hl_head", 1)
    if args is not None:
        try:
            rhs = OOp("l_flatten_head", (OOp("flatten_ne_nil_iff_2", (OVar("head_mem_hl_hl_prime"),)),))
            results.append((rhs, "Mathlib: List_head_head_eq_head_flatten"))
        except Exception:
            pass
    return results


def _r0072_head_flatten_eq_head_head(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.head_flatten_eq_head_head
    # l.flatten.head hl = (l.head (by grind)).head hl'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_flatten_head", 1)
    if args is not None:
        try:
            rhs = OOp("l_head_by_grind_head", (OVar("hl_prime"),))
            results.append((rhs, "Mathlib: List_head_flatten_eq_head_head"))
        except Exception:
            pass
    return results


def _r0073_getLast_getLast_eq_getLast_flatten(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getLast_getLast_eq_getLast_flatten
    # (l.getLast hl).getLast hl' =       l.flatten.getLast (flatten_ne_nil_iff.2 ⟨_, getLast_mem hl, hl'⟩)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_getLast_hl_getLast", 1)
    if args is not None:
        try:
            rhs = OOp("l_flatten_getLast", (OOp("flatten_ne_nil_iff_2", (OVar("getLast_mem_hl_hl_prime"),)),))
            results.append((rhs, "Mathlib: List_getLast_getLast_eq_getLast_flatten"))
        except Exception:
            pass
    return results


def _r0074_getLast_flatten_eq_getLast_getLast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getLast_flatten_eq_getLast_getLast
    # l.flatten.getLast hl = (l.getLast (by grind)).getLast hl'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_flatten_getLast", 1)
    if args is not None:
        try:
            rhs = OOp("l_getLast_by_grind_getLast", (OVar("hl_prime"),))
            results.append((rhs, "Mathlib: List_getLast_flatten_eq_getLast_getLast"))
        except Exception:
            pass
    return results


def _r0075_getD_eq_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getD_eq_get
    # l.getD i d = l.get i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_getD", 2)
    if args is not None:
        try:
            rhs = OOp("l_get", (args[0],))
            results.append((rhs, "Mathlib: List_getD_eq_get"))
        except Exception:
            pass
    return results


def _r0076_get_insertIdx_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_insertIdx_self
    # (l.insertIdx n x).get ⟨n, hn'⟩ = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_insertIdx_n_x_get", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: List_get_insertIdx_self"))
        except Exception:
            pass
    return results


def _r0077_get_insertIdx_add_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_insertIdx_add_succ
    # (l.insertIdx n x).get ⟨n + k + 1, hk⟩ = get l ⟨n + k, hk'⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_insertIdx_n_x_get", 1)
    if args is not None:
        try:
            rhs = OOp("get", (OVar("l"), OVar("n_plus_k_hk_prime"),))
            results.append((rhs, "Mathlib: List_get_insertIdx_add_succ"))
        except Exception:
            pass
    return results


def _r0078_take_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.take_iterate
    # take m (iterate f a n) = iterate f a (min m n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "take", 2)
    if args is not None:
        try:
            rhs = OOp("iterate", (OVar("f"), OVar("a"), OOp("min", (args[0], OVar("n"),)),))
            results.append((rhs, "Mathlib: List_take_iterate"))
        except Exception:
            pass
    return results


def _r0079_get_inj_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.get_inj_iff
    # l.get i = l.get j ↔ i = j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_get", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("l_get", (OVar("j"),)), args[0])), OVar("j")))
            results.append((rhs, "Mathlib: List_Nodup_get_inj_iff"))
        except Exception:
            pass
    return results


def _r0080_get_idxOf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_idxOf
    # idxOf (get l i) l = i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "idxOf", 2)
    if args is not None:
        try:
            rhs = OVar("i")
            results.append((rhs, "Mathlib: List_get_idxOf"))
        except Exception:
            pass
    return results


def _r0081_erase_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Nodup.erase_get
    # l.erase (l.get i) = l.eraseIdx ↑i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_erase", 1)
    if args is not None:
        try:
            rhs = OOp("l_eraseIdx", (OVar("i"),))
            results.append((rhs, "Mathlib: List_Nodup_erase_get"))
        except Exception:
            pass
    return results


def _r0082_get_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.get_ofFn
    # get (ofFn f) i = f (Fin.cast (by simp) i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "get", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("Fin_cast", (OOp("by", (OVar("simp"),)), args[1],)),))
            results.append((rhs, "Mathlib: List_get_ofFn"))
        except Exception:
            pass
    return results


def _r0083_ofFn_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.ofFn_get
    # ∀ l : List α, (ofFn (get l)) = l   | [] =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn", 1)
    if args is not None:
        try:
            rhs = OOp("l", (OVar("pipe"), OSeq(()), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_ofFn_get"))
        except Exception:
            pass
    return results


def _r0084_getLast_ofFn_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getLast_ofFn_succ
    # (ofFn f).getLast (mt ofFn_eq_nil_iff.1 (Nat.succ_ne_zero _)) = f (Fin.last _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofFn_f_getLast", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("Fin_last", (OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: List_getLast_ofFn_succ"))
        except Exception:
            pass
    return results


def _r0085_reverse_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Palindrome.reverse_eq
    # reverse l = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reverse", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: List_Palindrome_reverse_eq"))
        except Exception:
            pass
    return results


def _r0086_of_reverse_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Palindrome.of_reverse_eq
    # reverse l = l → Palindrome l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reverse", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (args[0], OOp("Palindrome", (args[0],))))
            results.append((rhs, "Mathlib: List_Palindrome_of_reverse_eq"))
        except Exception:
            pass
    return results


def _r0087_iff_reverse_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Palindrome.iff_reverse_eq
    # Palindrome l ↔ reverse l = l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("l")
            results.append((rhs, "Mathlib: List_Palindrome_iff_reverse_eq"))
        except Exception:
            pass
    return results


def _r0088_rotate_eq_drop_append_take(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_eq_drop_append_take
    # n ≤ l.length → l.rotate n = l.drop n ++ l.take n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("l_drop", (args[0],)), OOp("l_take", (args[0],))))
            results.append((rhs, "Mathlib: List_rotate_eq_drop_append_take"))
        except Exception:
            pass
    return results


def _r0089_rotate_eq_drop_append_take_mod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.rotate_eq_drop_append_take_mod
    # l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_rotate", 1)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("l_drop", (OOp("n", (OVar("_unknown"), OVar("l_length"),)),)), OOp("l_take", (OOp("n", (OVar("_unknown"), OVar("l_length"),)),))))
            results.append((rhs, "Mathlib: List_rotate_eq_drop_append_take_mod"))
        except Exception:
            pass
    return results


def _r0090_orderedInsert_eq_take_drop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.orderedInsert_eq_take_drop
    # l.orderedInsert r a = (l.takeWhile fun b => ¬a ≼ b) ++ a :: l.dropWhile fun b => ¬a ≼ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_orderedInsert", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("l_takeWhile", (OVar("fun"), OVar("b"), OVar("eq_gt"), OOp("not", (args[1],)), OVar("_unknown"), OVar("b"),)), OOp("a", (OVar("colon_colon"), OVar("l_dropWhile"), OVar("fun"), OVar("b"), OVar("eq_gt"), OOp("not", (args[1],)), OVar("_unknown"), OVar("b"),))))
            results.append((rhs, "Mathlib: List_orderedInsert_eq_take_drop"))
        except Exception:
            pass
    return results


def _r0091_insertionSort_cons_eq_take_drop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.insertionSort_cons_eq_take_drop
    # insertionSort r (a :: l) =       ((insertionSort r l).takeWhile fun b => ¬a ≼ b) ++         a :: (insertionSort r l).dro
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "insertionSort", 2)
    if args is not None:
        try:
            rhs = OOp("concat", (OOp("insertionSort_r_l_takeWhile", (OVar("fun"), OVar("b"), OVar("eq_gt"), OOp("not", (OVar("a"),)), OVar("_unknown"), OVar("b"),)), OOp("a", (OVar("colon_colon"), OVar("insertionSort_r_l_dropWhile"), OVar("fun"), OVar("b"), OVar("eq_gt"), OOp("not", (OVar("a"),)), OVar("_unknown"), OVar("b"),))))
            results.append((rhs, "Mathlib: List_insertionSort_cons_eq_take_drop"))
        except Exception:
            pass
    return results


def _r0092_flatten_splitByLoop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.flatten_splitByLoop
    # (splitBy.loop r l a g []).flatten = g.reverse ++ a :: l
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("splitBy_loop_r_l_a_g_flatten")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OVar("g_reverse"), OOp("a", (OVar("colon_colon"), OVar("l"),))))
            results.append((rhs, "Mathlib: List_flatten_splitByLoop"))
    except Exception:
        pass
    return results


def _r0093_head_head_splitBy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.head_head_splitBy
    # ((l.splitBy r).head (splitBy_ne_nil.2 hn)).head       (ne_nil_of_mem_splitBy (head_mem _)) = l.head hn
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_splitBy_r_head_splitBy_ne_nil_2_hn_head", 1)
    if args is not None:
        try:
            rhs = OOp("l_head", (OVar("hn"),))
            results.append((rhs, "Mathlib: List_head_head_splitBy"))
        except Exception:
            pass
    return results


def _r0094_getLast_getLast_splitBy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.getLast_getLast_splitBy
    # ((l.splitBy r).getLast (splitBy_ne_nil.2 hn)).getLast       (ne_nil_of_mem_splitBy (getLast_mem _)) = l.getLast hn
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_splitBy_r_getLast_splitBy_ne_nil_2_hn_getLast", 1)
    if args is not None:
        try:
            rhs = OOp("l_getLast", (OVar("hn"),))
            results.append((rhs, "Mathlib: List_getLast_getLast_splitBy"))
        except Exception:
            pass
    return results


def _r0095_isChain_getLast_head_splitByLoop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_getLast_head_splitByLoop
    # (splitBy.loop r l a g gs).IsChain fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "splitBy_loop_r_l_a_g_gs_IsChain", 10)
    if args is not None:
        try:
            rhs = OLit(False)
            results.append((rhs, "Mathlib: List_isChain_getLast_head_splitByLoop"))
        except Exception:
            pass
    return results


def _r0096_isChain_getLast_head_splitBy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_getLast_head_splitBy
    # (l.splitBy r).IsChain fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_splitBy_r_IsChain", 10)
    if args is not None:
        try:
            rhs = OLit(False)
            results.append((rhs, "Mathlib: List_isChain_getLast_head_splitBy"))
        except Exception:
            pass
    return results


def _r0097_splitBy_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.splitBy_eq_iff
    # m.splitBy r = l ↔ m = l.flatten ∧ [] ∉ l ∧ (∀ m ∈ l, m.IsChain fun x y ↦ r x y) ∧       l.IsChain fun a b ↦ ∃ ha hb, r (
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_splitBy", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("l"), OVar("m"))), OOp("==", (OOp("and", (OVar("l_flatten"), OOp("and", (OOp("not_in", (OSeq(()), OVar("l"))), OOp("and", (OOp("in", (OOp("forall", (OVar("m"),)), OOp("l", (OVar("m_IsChain"), OVar("fun"), OVar("x"), OVar("y"), OVar("_unknown"), args[0], OVar("x"), OVar("y"),)))), OOp("l_IsChain", (OVar("fun"), OVar("a"), OVar("b"), OVar("_unknown"), OVar("exists"), OVar("ha"), OVar("hb"), args[0], OOp("a_getLast", (OVar("ha"),)), OOp("b_head", (OVar("hb"),)),)))))))), OLit(False)))))
            results.append((rhs, "Mathlib: List_splitBy_eq_iff"))
        except Exception:
            pass
    return results


def _r0098_cons_get_drop_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.cons_get_drop_succ
    # l.get n :: l.drop (n.1 + 1) = l.drop n.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_get", 4)
    if args is not None:
        try:
            rhs = OOp("l_drop", (OVar("n_1"),))
            results.append((rhs, "Mathlib: List_cons_get_drop_succ"))
        except Exception:
            pass
    return results


def _r0099_tail_iterate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.tail_iterate
    # (List.tail^[n]) l = l.drop n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "List_tailpow_n", 1)
    if args is not None:
        try:
            rhs = OOp("l_drop", (OVar("n"),))
            results.append((rhs, "Mathlib: List_tail_iterate"))
        except Exception:
            pass
    return results


def _r0100_dropWhile_eq_nil_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.dropWhile_eq_nil_iff
    # dropWhile p l = [] ↔ ∀ x ∈ l, p x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dropWhile", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OSeq(()), OOp("in", (OOp("forall", (OVar("x"),)), OOp("l", (args[0], OVar("x"),))))))
            results.append((rhs, "Mathlib: List_dropWhile_eq_nil_iff"))
        except Exception:
            pass
    return results


def _r0101_takeWhile_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.takeWhile_eq_self_iff
    # takeWhile p l = l ↔ ∀ x ∈ l, p x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "takeWhile", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (args[1], OOp("in", (OOp("forall", (OVar("x"),)), OOp("l", (args[0], OVar("x"),))))))
            results.append((rhs, "Mathlib: List_takeWhile_eq_self_iff"))
        except Exception:
            pass
    return results


def _r0102_takeWhile_takeWhile(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.takeWhile_takeWhile
    # takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "takeWhile", 2)
    if args is not None:
        try:
            rhs = OOp("takeWhile", (OOp("and", (OOp("fun", (OVar("a"), OVar("eq_gt"), args[0], OVar("a"),)), OOp("q", (OVar("a"),)))), OVar("l"),))
            results.append((rhs, "Mathlib: List_takeWhile_takeWhile"))
        except Exception:
            pass
    return results


def _r0103_takeWhile_idem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.takeWhile_idem
    # takeWhile p (takeWhile p l) = takeWhile p l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "takeWhile", 2)
    if args is not None:
        try:
            rhs = OOp("takeWhile", (args[0], OVar("l"),))
            results.append((rhs, "Mathlib: List_takeWhile_idem"))
        except Exception:
            pass
    return results


def _r0104_cons_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.cons_val
    # ∀ v : Vector α n, (a ::ᵥ v).val = a :: v.val   | ⟨_, _⟩ => rfl  set_option backward.isDefEq.respectTransparency false in
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_colon_v_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("a", (OVar("colon_colon"), OVar("v_val"), OVar("pipe"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl_set_option"), OVar("backward_isDefEq_respectTransparency"), OLit(False), OVar("in_theorem"), OVar("eq_cons_iff"), OOp("a", (OVar("colon"), OVar("a"),)), OOp("v", (OVar("colon"), OVar("Vector"), OVar("a"), OVar("n_succ"),)), OOp("v_prime", (OVar("colon"), OVar("Vector"), OVar("a"), OVar("n"),)), OVar("colon"), OVar("v"),)), OOp("==", (OOp("iff", (OOp("a", (OVar("colon_colon"), OVar("v_prime"),)), OVar("v_head"))), OOp("==", (OOp("and", (OVar("a"), OVar("v_tail"))), OVar("v_prime")))))))
            results.append((rhs, "Mathlib: List_Vector_cons_val"))
    except Exception:
        pass
    return results


def _r0105_eq_cons_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.eq_cons_iff
    # v = a ::ᵥ v' ↔ v.head = a ∧ v.tail = v'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("a", (OVar("colon_colon"), OVar("v_prime"),)), OVar("v_head"))), OOp("==", (OOp("and", (OVar("a"), OVar("v_tail"))), OVar("v_prime")))))
            results.append((rhs, "Mathlib: List_Vector_eq_cons_iff"))
    except Exception:
        pass
    return results


def _r0106_head_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.head_pmap
    # (v.pmap f hp).head = f v.head (hp _ <| by       rw [← cons_head_tail v, toList_cons, head_cons, List.mem_cons]; exact .i
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_pmap_f_hp_head")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f", (OVar("v_head"), OOp("hp", (OVar("_unknown"), OVar("lt_pipe"), OVar("by"), OVar("rw"), OVar("from_cons_head_tail_v_toList_cons_head_cons_List_mem_cons"), OVar("exact"), OVar("inl"), OVar("rfl"),)),))
            results.append((rhs, "Mathlib: List_Vector_head_pmap"))
    except Exception:
        pass
    return results


def _r0107_tail_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.tail_pmap
    # (v.pmap f hp).tail = v.tail.pmap f (fun x hx ↦ hp _ <| by       rw [← cons_head_tail v, toList_cons, List.mem_cons]; exa
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_pmap_f_hp_tail")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("v_tail_pmap", (OVar("f"), OOp("fun", (OVar("x"), OVar("hx"), OVar("_unknown"), OVar("hp"), OVar("_unknown"), OVar("lt_pipe"), OVar("by"), OVar("rw"), OVar("from_cons_head_tail_v_toList_cons_List_mem_cons"), OVar("exact"), OVar("inr"), OVar("hx"),)),))
            results.append((rhs, "Mathlib: List_Vector_tail_pmap"))
    except Exception:
        pass
    return results


def _r0108_get_replicate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.get_replicate
    # (Vector.replicate n a).get i = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Vector_replicate_n_a_get", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: List_Vector_get_replicate"))
        except Exception:
            pass
    return results


def _r0109_get_ofFn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.get_ofFn
    # get (ofFn f) i = f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "get", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: List_Vector_get_ofFn"))
        except Exception:
            pass
    return results


def _r0110_get_tail(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.get_tail
    # x.tail.get i = x.get ⟨i.1 + 1,
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_tail_get", 1)
    if args is not None:
        try:
            rhs = OOp("x_get", (OVar("i_1_plus_1"),))
            results.append((rhs, "Mathlib: List_Vector_get_tail"))
        except Exception:
            pass
    return results


def _r0111_get_tail_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.get_tail_succ
    # ∀ (v : Vector α n.succ) (i : Fin n), get (tail v) i = get v i.succ   | ⟨a :: l, e⟩, ⟨i, h⟩ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "get", 2)
    if args is not None:
        try:
            rhs = OOp("get", (OVar("v"), OVar("i_succ"), OVar("pipe"), OVar("a_colon_colon_l_e"), OVar("i_h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_Vector_get_tail_succ"))
        except Exception:
            pass
    return results


def _r0112_tail_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.tail_nil
    # (@nil α).tail = nil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("at_nil_a_tail")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("nil")
            results.append((rhs, "Mathlib: List_Vector_tail_nil"))
    except Exception:
        pass
    return results


def _r0113_toList_tail(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.toList_tail
    # ∀ (v : Vector α n), v.tail.toList = v.toList.tail   | ⟨[], _⟩     =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_tail_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("tail", (OVar("pipe"), OVar("_unknown"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_Vector_toList_tail"))
    except Exception:
        pass
    return results


def _r0114_toList_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.toList_singleton
    # v.toList = [v.head]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OSeq((OVar("v_head"),))
            results.append((rhs, "Mathlib: List_Vector_toList_singleton"))
    except Exception:
        pass
    return results


def _r0115_toList_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.toList_reverse
    # v.reverse.toList = v.toList.reverse
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_reverse_toList")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("v_toList_reverse")
            results.append((rhs, "Mathlib: List_Vector_toList_reverse"))
    except Exception:
        pass
    return results


def _r0116_reverse_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.reverse_reverse
    # v.reverse.reverse = v
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_reverse_reverse")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("v")
            results.append((rhs, "Mathlib: List_Vector_reverse_reverse"))
    except Exception:
        pass
    return results


def _r0117_get_cons_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.get_cons_succ
    # get (a ::ᵥ v) i.succ = get v i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "get", 2)
    if args is not None:
        try:
            rhs = OOp("get", (OVar("v"), OVar("i"),))
            results.append((rhs, "Mathlib: List_Vector_get_cons_succ"))
        except Exception:
            pass
    return results


def _r0118_last_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.last_def
    # v.last = v.get (Fin.last n)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_last")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("v_get", (OOp("Fin_last", (OVar("n"),)),))
            results.append((rhs, "Mathlib: List_Vector_last_def"))
    except Exception:
        pass
    return results


def _r0119_reverse_get_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.reverse_get_zero
    # v.reverse.head = v.last
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("v_reverse_head")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("v_last")
            results.append((rhs, "Mathlib: List_Vector_reverse_get_zero"))
    except Exception:
        pass
    return results


def _r0120_scanl_head(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.scanl_head
    # (scanl f b v).head = b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("scanl_f_b_v_head")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b")
            results.append((rhs, "Mathlib: List_Vector_scanl_head"))
    except Exception:
        pass
    return results


def _r0121_head_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.head_cons
    # ∀ v : Vector α n, head (cons a v) = a   | ⟨_, _⟩ => rfl   def tail : Vector α n → Vector α (n - 1)   | ⟨[], h⟩ => ⟨[], c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Vector", 4)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("gt", (OVar("congrArg_pred_h"), args[2], OVar("colon_colon_v_h"), OVar("eq_gt"), OVar("v_congrArg_pred_h_theorem"), OVar("tail_cons"), OOp("a", (OVar("colon"), args[0],)), OVar("colon"), OVar("forall"), OVar("v"), OVar("colon"), OVar("Vector"), args[0], OVar("n"), OVar("tail"), OOp("cons", (args[0], OVar("v"),)),)), OOp("==", (OOp("v", (args[2], OVar("_unknown"), OVar("eq_gt"), OVar("rfl_at_simp_theorem"), OVar("cons_head_tail"), OVar("colon"), OVar("forall"), OVar("v"), OVar("colon"), OVar("Vector"), args[0], OVar("succ_n"), OVar("cons"), OOp("head", (OVar("v"),)), OOp("tail", (OVar("v"),)),)), OOp("v", (args[2], args[3], OVar("eq_gt"),))))))
            results.append((rhs, "Mathlib: List_Vector_head_cons"))
        except Exception:
            pass
    return results


def _r0122_tail_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.tail_cons
    # ∀ v : Vector α n, tail (cons a v) = v   | ⟨_, _⟩ => rfl   @[simp] theorem cons_head_tail : ∀ v : Vector α (succ n), cons
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tail", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("v", (OVar("pipe"), OVar("_unknown"), OVar("eq_gt"), OVar("rfl_at_simp_theorem"), OVar("cons_head_tail"), OVar("colon"), OVar("forall"), OVar("v"), OVar("colon"), OVar("Vector"), OVar("a"), OVar("succ_n"), OVar("cons"), OOp("head", (OVar("v"),)), OOp("tail", (OVar("v"),)),)), OOp("v", (OVar("pipe"), OVar("h"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: List_Vector_tail_cons"))
        except Exception:
            pass
    return results


def _r0123_cons_head_tail(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.cons_head_tail
    # ∀ v : Vector α (succ n), cons (head v) (tail v) = v   | ⟨[], h⟩ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons", 2)
    if args is not None:
        try:
            rhs = OOp("v", (OVar("pipe"), OVar("h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: List_Vector_cons_head_tail"))
        except Exception:
            pass
    return results


def _r0124_mem_succ_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.mem_succ_iff
    # a ∈ v.toList ↔ a = v.head ∨ a ∈ v.tail.toList
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OVar("v_head"), OOp("in", (args[1], OVar("v_tail_toList")))))
            results.append((rhs, "Mathlib: List_Vector_mem_succ_iff"))
        except Exception:
            pass
    return results


def _r0125_mem_map_succ_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.mem_map_succ_iff
    # b ∈ (v.map f).toList ↔ f v.head = b ∨ ∃ a : α, a ∈ v.tail.toList ∧ f a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("or", (OVar("b"), OOp("in", (OOp("exists", (OVar("a"), OVar("colon"), OVar("a"), OVar("a"),)), OVar("v_tail_toList"))))), OOp("f", (OVar("a"),)))), OVar("b")))
            results.append((rhs, "Mathlib: List_Vector_mem_map_succ_iff"))
        except Exception:
            pass
    return results


def _r0126_reverse_snoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.reverse_snoc
    # reverse (xs.snoc x) = x ::ᵥ (reverse xs)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reverse", 1)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("colon_colon"), OOp("reverse", (OVar("xs"),)),))
            results.append((rhs, "Mathlib: List_Vector_reverse_snoc"))
        except Exception:
            pass
    return results


def _r0127_formPerm_eq_head_iff_eq_getLast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.formPerm_eq_head_iff_eq_getLast
    # formPerm (y :: l) x = y ↔ x = getLast (y :: l) (cons_ne_nil _ _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "formPerm", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("y"), args[1])), OOp("last", (OOp("y", (OVar("colon_colon"), OVar("l"),)), OOp("cons_ne_nil", (OVar("_unknown"), OVar("_unknown"),)),))))
            results.append((rhs, "Mathlib: List_formPerm_eq_head_iff_eq_getLast"))
        except Exception:
            pass
    return results


def _r0128_mem_take_iff_idxOf_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.mem_take_iff_idxOf_lt
    # a ∈ l.take n ↔ l.idxOf a < n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("l_idxOf", (args[0],)), OVar("n")))
            results.append((rhs, "Mathlib: List_mem_take_iff_idxOf_lt"))
        except Exception:
            pass
    return results


def _r0129_iff_of_mem_tail_imp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.iff_of_mem_tail_imp
    # IsChain R l ↔ IsChain S l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("IsChain", (OVar("S"), args[1],))
            results.append((rhs, "Mathlib: List_IsChain_iff_of_mem_tail_imp"))
        except Exception:
            pass
    return results


def _r0130_iff_mem_mem_tail(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.IsChain.iff_mem_mem_tail
    # IsChain R l ↔ IsChain (fun x y => x ∈ l ∧ y ∈ l.tail ∧ R x y) l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("IsChain", (OOp("and", (OOp("in", (OOp("fun", (OVar("x"), OVar("y"), OVar("eq_gt"), OVar("x"),)), args[1])), OOp("and", (OOp("in", (OVar("y"), OVar("l_tail"))), OOp("R", (OVar("x"), OVar("y"),)))))), args[1],))
            results.append((rhs, "Mathlib: List_IsChain_iff_mem_mem_tail"))
        except Exception:
            pass
    return results


def _r0131_isChain_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_cons
    # IsChain R (x :: l) ↔ (∀ y ∈ head? l, R x y) ∧ IsChain R l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsChain", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (OOp("forall", (OVar("y"),)), OOp("head_q", (OVar("l"), args[0], OVar("x"), OVar("y"),)))), OOp("IsChain", (args[0], OVar("l"),))))
            results.append((rhs, "Mathlib: List_isChain_cons"))
        except Exception:
            pass
    return results


def _r0132_isChain_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isChain_reverse
    # l.reverse.IsChain R ↔ l.IsChain (fun a b => R b a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_reverse_IsChain", 1)
    if args is not None:
        try:
            rhs = OOp("l_IsChain", (OOp("fun", (OVar("a"), OVar("b"), OVar("eq_gt"), args[0], OVar("b"), OVar("a"),)),))
            results.append((rhs, "Mathlib: List_isChain_reverse"))
        except Exception:
            pass
    return results


def _r0133_nodup_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_reverse
    # Nodup (reverse l) ↔ Nodup l
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("nodup", (OVar("l"),))
            results.append((rhs, "Mathlib: List_nodup_reverse"))
        except Exception:
            pass
    return results


def _r0134_nodup_tail_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.nodup_tail_reverse
    # Nodup l.reverse.tail ↔ Nodup l.tail
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 1)
    if args is not None:
        try:
            rhs = OOp("nodup", (OVar("l_tail"),))
            results.append((rhs, "Mathlib: List_nodup_tail_reverse"))
        except Exception:
            pass
    return results


def _r0135_isRotated_reverse_comm_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isRotated_reverse_comm_iff
    # l.reverse ~r l' ↔ l ~r l'.reverse
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_reverse", 2)
    if args is not None:
        try:
            rhs = OOp("l", (args[0], OVar("l_prime_reverse"),))
            results.append((rhs, "Mathlib: List_isRotated_reverse_comm_iff"))
        except Exception:
            pass
    return results


def _r0136_isRotated_reverse_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.isRotated_reverse_iff
    # l.reverse ~r l'.reverse ↔ l ~r l'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_reverse", 2)
    if args is not None:
        try:
            rhs = OOp("l", (args[0], OVar("l_prime"),))
            results.append((rhs, "Mathlib: List_isRotated_reverse_iff"))
        except Exception:
            pass
    return results


def _r0137_triplewise_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.triplewise_reverse
    # l.reverse.Triplewise p ↔ l.Triplewise fun a b c ↦ p c b a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_reverse_Triplewise", 1)
    if args is not None:
        try:
            rhs = OOp("l_Triplewise", (OVar("fun"), OVar("a"), OVar("b"), OVar("c"), OVar("_unknown"), args[0], OVar("c"), OVar("b"), OVar("a"),))
            results.append((rhs, "Mathlib: List_triplewise_reverse"))
        except Exception:
            pass
    return results


def _r0138_ne_cons_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: List.Vector.ne_cons_iff
    # v ≠ a ::ᵥ v' ↔ v.head ≠ a ∨ v.tail ≠ v'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OVar("v_head"), OOp("!=", (OOp("or", (OVar("a"), OVar("v_tail"))), OVar("v_prime")))))
            results.append((rhs, "Mathlib: List_Vector_ne_cons_iff"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_list_misc rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "+", "-", "IsChain", "IsChain_R_L_flatten_iff_forall_l_in_L_IsChain_R_l_and_L_IsChain_fun_l_1_l_2_eq_gt_forall_x_in_l_1_getLast_q_y_in_l_2_head_q_R_x_y_pipe", "L_flatten_drop", "L_modifyNth_f_n_nth", "L_take_i_plus_1_drop", "ListBlank_head", "ListBlank_mk", "ListBlank_mk_l_nth", "ListBlank_tail", "List_tailpow_n", "Nat_succ_ne_zero", "Palindrome", "Vector", "Vector_replicate_n_a_get", "_unknown", "a", "a_getLast", "and", "b_head", "concat", "cons", "dropWhile", "exists", "f", "forall", "formPerm", "get", "getLast_mem", "head", "head_mem", "idxOf", "iff", "in", "insertionSort", "iterate", "l_1_getLast_q", "l_2_head_q", "l_erase", "l_flatten_getLast", "l_flatten_head", "l_get", "l_getD", "l_getLast", "l_getLast_hl_getLast", "l_head", "l_head_hl_head",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_list_misc axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_list_misc rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_tail_cons(term, ctx))
    results.extend(_r0001_idxOf_eq_zero_iff_eq_nil_or_head_eq(term, ctx))
    results.extend(_r0002_next_cons_eq_next_of_mem_dropLast(term, ctx))
    results.extend(_r0003_headI_cons(term, ctx))
    results.extend(_r0004_rdrop_zero(term, ctx))
    results.extend(_r0005_rdrop_eq_reverse_drop_reverse(term, ctx))
    results.extend(_r0006_rtake_zero(term, ctx))
    results.extend(_r0007_rtake_eq_reverse_take_reverse(term, ctx))
    results.extend(_r0008_rdropWhile_singleton(term, ctx))
    results.extend(_r0009_getD_replicate(term, ctx))
    results.extend(_r0010_cons_eta(term, ctx))
    results.extend(_r0011_splitLengths_cons(term, ctx))
    results.extend(_r0012_drop_take_append_drop(term, ctx))
    results.extend(_r0013_ofFn_get(term, ctx))
    results.extend(_r0014_tail_val(term, ctx))
    results.extend(_r0015_tail_ofFn(term, ctx))
    results.extend(_r0016_head_ofFn(term, ctx))
    results.extend(_r0017_get_cons_zero(term, ctx))
    results.extend(_r0018_mem_iff_get(term, ctx))
    results.extend(_r0019_reverse_cons(term, ctx))
    results.extend(_r0020_prod_take_ofFn(term, ctx))
    results.extend(_r0021_prod_take_mul_prod_drop(term, ctx))
    results.extend(_r0022_prod_take_succ(term, ctx))
    results.extend(_r0023_prod_set(term, ctx))
    results.extend(_r0024_headI_mul_tail_prod_of_ne_nil(term, ctx))
    results.extend(_r0025_drop_sum_flatten(term, ctx))
    results.extend(_r0026_splitWrtCompositionAux_cons(term, ctx))
    results.extend(_r0027_getElem_splitWrtCompositionAux(term, ctx))
    results.extend(_r0028_getElem_splitWrtComposition(term, ctx))
    results.extend(_r0029_head_mk(term, ctx))
    results.extend(_r0030_tail_mk(term, ctx))
    results.extend(_r0031_head_cons(term, ctx))
    results.extend(_r0032_cons_head_tail(term, ctx))
    results.extend(_r0033_nth_mk(term, ctx))
    results.extend(_r0034_nth_zero(term, ctx))
    results.extend(_r0035_nth_succ(term, ctx))
    results.extend(_r0036_ext(term, ctx))
    results.extend(_r0037_nth_modifyNth(term, ctx))
    results.extend(_r0038_toFinset_reverse(term, ctx))
    results.extend(_r0039_getLast_congr(term, ctx))
    results.extend(_r0040_surjective_tail(term, ctx))
    results.extend(_r0041_get_tail(term, ctx))
    results.extend(_r0042_idxOf_eq_zero_iff_head_eq(term, ctx))
    results.extend(_r0043_isChain_append(term, ctx))
    results.extend(_r0044_isChain_flatten(term, ctx))
    results.extend(_r0045_exists_isChain_ne_nil_of_relationReflTra(term, ctx))
    results.extend(_r0046_nextOr_eq_nextOr_of_mem_dropLast(term, ctx))
    results.extend(_r0047_next_getLast_cons(term, ctx))
    results.extend(_r0048_prev_head_eq_getLast(term, ctx))
    results.extend(_r0049_next_getLast_eq_head_of_notMem_dropLast(term, ctx))
    results.extend(_r0050_next_getLast_eq_head(term, ctx))
    results.extend(_r0051_prev_reverse_eq_next(term, ctx))
    results.extend(_r0052_next_reverse_eq_prev(term, ctx))
    results.extend(_r0053_headI_dedup(term, ctx))
    results.extend(_r0054_tail_dedup(term, ctx))
    results.extend(_r0055_dedup_eq_cons(term, ctx))
    results.extend(_r0056_headI_nil(term, ctx))
    results.extend(_r0057_rdrop_nil(term, ctx))
    results.extend(_r0058_rtake_nil(term, ctx))
    results.extend(_r0059_rdropWhile_nil(term, ctx))
    results.extend(_r0060_rdropWhile_eq_nil_iff(term, ctx))
    results.extend(_r0061_dropWhile_idempotent(term, ctx))
    results.extend(_r0062_rdropWhile_idempotent(term, ctx))
    results.extend(_r0063_rdropWhile_reverse(term, ctx))
    results.extend(_r0064_rtakeWhile_nil(term, ctx))
    results.extend(_r0065_rtakeWhile_eq_self_iff(term, ctx))
    results.extend(_r0066_rtakeWhile_idempotent(term, ctx))
    results.extend(_r0067_rtakeWhile_reverse(term, ctx))
    results.extend(_r0068_rdropWhile_append_rtakeWhile(term, ctx))
    results.extend(_r0069_rdrop_add(term, ctx))
    results.extend(_r0070_drop_take_succ_eq_cons_getElem(term, ctx))
    results.extend(_r0071_head_head_eq_head_flatten(term, ctx))
    results.extend(_r0072_head_flatten_eq_head_head(term, ctx))
    results.extend(_r0073_getLast_getLast_eq_getLast_flatten(term, ctx))
    results.extend(_r0074_getLast_flatten_eq_getLast_getLast(term, ctx))
    results.extend(_r0075_getD_eq_get(term, ctx))
    results.extend(_r0076_get_insertIdx_self(term, ctx))
    results.extend(_r0077_get_insertIdx_add_succ(term, ctx))
    results.extend(_r0078_take_iterate(term, ctx))
    results.extend(_r0079_get_inj_iff(term, ctx))
    results.extend(_r0080_get_idxOf(term, ctx))
    results.extend(_r0081_erase_get(term, ctx))
    results.extend(_r0082_get_ofFn(term, ctx))
    results.extend(_r0083_ofFn_get(term, ctx))
    results.extend(_r0084_getLast_ofFn_succ(term, ctx))
    results.extend(_r0085_reverse_eq(term, ctx))
    results.extend(_r0086_of_reverse_eq(term, ctx))
    results.extend(_r0087_iff_reverse_eq(term, ctx))
    results.extend(_r0088_rotate_eq_drop_append_take(term, ctx))
    results.extend(_r0089_rotate_eq_drop_append_take_mod(term, ctx))
    results.extend(_r0090_orderedInsert_eq_take_drop(term, ctx))
    results.extend(_r0091_insertionSort_cons_eq_take_drop(term, ctx))
    results.extend(_r0092_flatten_splitByLoop(term, ctx))
    results.extend(_r0093_head_head_splitBy(term, ctx))
    results.extend(_r0094_getLast_getLast_splitBy(term, ctx))
    results.extend(_r0095_isChain_getLast_head_splitByLoop(term, ctx))
    results.extend(_r0096_isChain_getLast_head_splitBy(term, ctx))
    results.extend(_r0097_splitBy_eq_iff(term, ctx))
    results.extend(_r0098_cons_get_drop_succ(term, ctx))
    results.extend(_r0099_tail_iterate(term, ctx))
    results.extend(_r0100_dropWhile_eq_nil_iff(term, ctx))
    results.extend(_r0101_takeWhile_eq_self_iff(term, ctx))
    results.extend(_r0102_takeWhile_takeWhile(term, ctx))
    results.extend(_r0103_takeWhile_idem(term, ctx))
    results.extend(_r0104_cons_val(term, ctx))
    results.extend(_r0105_eq_cons_iff(term, ctx))
    results.extend(_r0106_head_pmap(term, ctx))
    results.extend(_r0107_tail_pmap(term, ctx))
    results.extend(_r0108_get_replicate(term, ctx))
    results.extend(_r0109_get_ofFn(term, ctx))
    results.extend(_r0110_get_tail(term, ctx))
    results.extend(_r0111_get_tail_succ(term, ctx))
    results.extend(_r0112_tail_nil(term, ctx))
    results.extend(_r0113_toList_tail(term, ctx))
    results.extend(_r0114_toList_singleton(term, ctx))
    results.extend(_r0115_toList_reverse(term, ctx))
    results.extend(_r0116_reverse_reverse(term, ctx))
    results.extend(_r0117_get_cons_succ(term, ctx))
    results.extend(_r0118_last_def(term, ctx))
    results.extend(_r0119_reverse_get_zero(term, ctx))
    results.extend(_r0120_scanl_head(term, ctx))
    results.extend(_r0121_head_cons(term, ctx))
    results.extend(_r0122_tail_cons(term, ctx))
    results.extend(_r0123_cons_head_tail(term, ctx))
    results.extend(_r0124_mem_succ_iff(term, ctx))
    results.extend(_r0125_mem_map_succ_iff(term, ctx))
    results.extend(_r0126_reverse_snoc(term, ctx))
    results.extend(_r0127_formPerm_eq_head_iff_eq_getLast(term, ctx))
    results.extend(_r0128_mem_take_iff_idxOf_lt(term, ctx))
    results.extend(_r0129_iff_of_mem_tail_imp(term, ctx))
    results.extend(_r0130_iff_mem_mem_tail(term, ctx))
    results.extend(_r0131_isChain_cons(term, ctx))
    results.extend(_r0132_isChain_reverse(term, ctx))
    results.extend(_r0133_nodup_reverse(term, ctx))
    results.extend(_r0134_nodup_tail_reverse(term, ctx))
    results.extend(_r0135_isRotated_reverse_comm_iff(term, ctx))
    results.extend(_r0136_isRotated_reverse_iff(term, ctx))
    results.extend(_r0137_triplewise_reverse(term, ctx))
    results.extend(_r0138_ne_cons_iff(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_list_misc rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("List_head", "_unknown", "Empty proposition"),
    ("List_getLast", "_unknown", "Empty proposition"),
    ("List_reverse_cons", "_unknown", "Empty proposition"),
    ("List_mem_getLast", "_unknown", "Empty proposition"),
    ("List_getLast", "_unknown", "Empty proposition"),
    ("List_mem_getLast", "_unknown", "Empty proposition"),
    ("List_getLastI_eq_getLast", "_unknown", "Empty proposition"),
    ("List_getLastI_eq_getLast", "_unknown", "Empty proposition"),
    ("List_getLast", "_unknown", "Empty proposition"),
    ("List_getLast", "_unknown", "Empty proposition"),
    ("List_mem_getLast", "_unknown", "Empty proposition"),
    ("List_mem_dropLast_of_mem_of_ne_getLast", "a_in_l_dropLast", "Not an equality or iff proposition"),
    ("List_mem_dropLast_of_mem_of_ne_getLastD", "a_in_l_dropLast", "Not an equality or iff proposition"),
    ("List_mem_dropLast_of_mem_of_ne_getLast", "_unknown", "Empty proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_surjective_head", "_unknown", "Empty proposition"),
    ("List_surjective_head", "_unknown", "Empty proposition"),
    ("List_eq_cons_of_mem_head", "_unknown", "Empty proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_mem_head", "_unknown", "Empty proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_cons_head", "_unknown", "Empty proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_cons_head", "_unknown", "Empty proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_IsChain_imp_of_mem_tail_imp", "IsChain_S_l", "Not an equality or iff proposition"),
    ("List_IsChain_tail", "IsChain_R_l_tail", "Not an equality or iff proposition"),
    ("List_IsChain_rel_head", "R_x_y", "Not an equality or iff proposition"),
    ("List_IsChain_rel_head", "_unknown", "Empty proposition"),
    ("List_IsChain_drop", "IsChain_R_drop_n_l", "Not an equality or iff proposition"),
    ("List_IsChain_dropLast", "IsChain_R_l_dropLast", "Not an equality or iff proposition"),
    ("List_IsChain_take", "IsChain_R_take_n_l", "Not an equality or iff proposition"),
    ("List_IsChain_imp_head", "IsChain_R_y_colon_colon_l", "Not an equality or iff proposition"),
    ("List_IsChain_backwards_cons_induction_head", "p_a", "Not an equality or iff proposition"),
    ("List_relationReflTransGen_of_exists_isChain", "Relation_ReflTransGen_r_head_l_hne_getLast_l_hne", "Not an equality or iff proposition"),
    ("List_prev_getLast_cons", "_unknown", "Empty proposition"),
    ("List_nextOr_infix_of_mem_dropLast", "a_l_nextOr_a_d_lt_colon_plus_colon_l", "Not an equality or iff proposition"),
    ("List_prev_infix_of_mem_tail", "l_prev_a_ha_a_lt_colon_plus_colon_l", "Not an equality or iff proposition"),
    ("List_rdropWhile_last_not", "not_p_rdropWhile_p_l_getLast_hl", "Not an equality or iff proposition"),
    ("List_rdropWhile_prefix", "l_rdropWhile_p_lt_plus_colon_l", "Not an equality or iff proposition"),
    ("List_rtakeWhile_suffix", "l_rtakeWhile_p_lt_colon_plus_l", "Not an equality or iff proposition"),
    ("List_mem_rtakeWhile_imp", "p_x", "Not an equality or iff proposition"),
    ("List_IsPrefix_take", "l_1_take_n_lt_plus_colon_l_2_take_n", "Not an equality or iff proposition"),
    ("List_IsPrefix_drop", "l_1_drop_n_lt_plus_colon_l_2_drop_n", "Not an equality or iff proposition"),
    ("List_dropSlice_sublist", "l_dropSlice_n_m_lt_plus_l", "Not an equality or iff proposition"),
    ("List_dropSlice_subset", "l_dropSlice_n_m_sub_l", "Not an equality or iff proposition"),
    ("List_mem_of_mem_dropSlice", "a_in_l", "Not an equality or iff proposition"),
    ("List_tail_subset", "tail_l_sub_l", "Not an equality or iff proposition"),
    ("List_mem_of_mem_dropLast", "a_in_l", "Not an equality or iff proposition"),
    ("List_take_insertIdx_eq_take_of_le", "_unknown", "Empty proposition"),
    ("List_take_eraseIdx_eq_take_of_le", "_unknown", "Empty proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_not_nodup_of_get_eq_of_ne", "not_Nodup_xs", "Not an equality or iff proposition"),
    ("List_Pairwise_rel_head_tail", "R_l_head_lt_pipe_ne_nil_of_mem_lt_pipe_mem_of_mem_tail_ha_a", "Not an equality or iff proposition"),
    ("List_Pairwise_rel_head_of_rel_head_head", "R_l_head_lt_pipe_ne_nil_of_mem_ha_a", "Not an equality or iff proposition"),
    ("List_Pairwise_rel_head", "R_l_head_lt_pipe_ne_nil_of_mem_ha_a", "Not an equality or iff proposition"),
    ("List_Pairwise_rel_dropLast_getLast", "R_a_l_getLast_lt_pipe_ne_nil_of_mem_lt_pipe_dropLast_subset_ha", "Not an equality or iff proposition"),
    ("List_Pairwise_rel_getLast_of_rel_getLast_getLast", "R_a_l_getLast_lt_pipe_ne_nil_of_mem_ha", "Not an equality or iff proposition"),
    ("List_Pairwise_rel_getLast", "R_a_l_getLast_lt_pipe_ne_nil_of_mem_ha", "Not an equality or iff proposition"),
    ("List_Pairwise_head", "_unknown", "Empty proposition"),
    ("List_HasPeriod_drop_prefix", "drop_p_w_lt_plus_colon_w", "Not an equality or iff proposition"),
    ("List_HasPeriod_drop_of_hasPeriod_add", "HasPeriod_drop_q_w_k", "Not an equality or iff proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_IsRotated_reverse", "l_reverse_tilde_r_l_prime_reverse", "Not an equality or iff proposition"),
    ("List_IsRotated_cons_getLast_dropLast", "L_getLast_hL_colon_colon_L_dropLast_tilde_r_L", "Not an equality or iff proposition"),
    ("List_IsRotated_dropLast_tail", "L_dropLast_tilde_r_L_tail", "Not an equality or iff proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_head", "_unknown", "Empty proposition"),
    ("List_pairwise_sublists", "Pairwise_Lex_R_on_reverse_sublists_l", "Not an equality or iff proposition"),
    ("List_drop_take_append_drop", "_unknown", "Empty proposition"),
    ("List_takeI_left", "_unknown", "Empty proposition"),
    ("List_mem_takeWhile_imp", "p_x", "Not an equality or iff proposition"),
    ("List_coe_toFinsupp", "l_toFinsupp_colon_to_M_eq_l_getD_0", "Not an equality or iff proposition"),
    ("List_toFinsupp_apply", "l_toFinsupp_colon_to_M_i_eq_l_getD_i_0", "Not an equality or iff proposition"),
    ("List_Vector_head", "_unknown", "Empty proposition"),
    ("List_Vector_get_zero", "forall_v_colon_Vector_a_n_succ_get_v_0_eq_head_v_pipe_colon_colon_eq_gt_rfl_at_simp_theorem", "Not an equality or iff proposition"),
    ("List_Vector_get_mem", "v_get_i_in_v_toList", "Not an equality or iff proposition"),
    ("List_Vector_head_mem", "v_head_in_v_toList", "Not an equality or iff proposition"),
    ("List_Vector_mem_of_mem_tail", "a_in_v_toList", "Not an equality or iff proposition"),
]
