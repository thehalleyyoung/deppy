"""Mathlib: Option — auto-generated from Mathlib4.

Contains 67 rewrite rules derived from Mathlib theorems.
Plus 14 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_option"
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
# Rewrite rules (67 total)
# ════════════════════════════════════════════════════════════

def _r0000_smul_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.smul_some
    # a • some b = some (a • b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OOp("some", (OOp("a", (args[0], args[2],)),))
            results.append((rhs, "Mathlib: Option_smul_some"))
        except Exception:
            pass
    return results


def _r0001_toFinset_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.toFinset_some
    # (some a).toFinset = {a}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("some_a_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Option_toFinset_some"))
    except Exception:
        pass
    return results


def _r0002_card_toFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.card_toFinset
    # o.toFinset.card = o.elim 0 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("o_toFinset_card")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("o_elim", (OLit(0), OLit(1),))
            results.append((rhs, "Mathlib: Option_card_toFinset"))
    except Exception:
        pass
    return results


def _r0003_map_eq_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_eq_id
    # Option.map f = id ↔ f = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "option_map", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("id"), args[0])), OVar("id")))
            results.append((rhs, "Mathlib: Option_map_eq_id"))
        except Exception:
            pass
    return results


def _r0004_map_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_comm
    # (Option.map f₁ a).map g₁ = (Option.map f₂ a).map g₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Option_map_f_1_a_map", 1)
    if args is not None:
        try:
            rhs = OOp("Option_map_f_2_a_map", (OVar("g_2"),))
            results.append((rhs, "Mathlib: Option_map_comm"))
        except Exception:
            pass
    return results


def _r0005_map_2_coe_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_coe_coe
    # map₂ f a b = f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[1], args[2],))
            results.append((rhs, "Mathlib: Option_map_2_coe_coe"))
        except Exception:
            pass
    return results


def _r0006_map_2_none_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_none_right
    # map₂ f a none = none
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Option_map_2_none_right"))
        except Exception:
            pass
    return results


def _r0007_map_2_coe_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_coe_left
    # map₂ f a b = b.map fun b => f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("b_map", (OVar("fun"), args[2], OVar("eq_gt"), args[0], args[1], args[2],))
            results.append((rhs, "Mathlib: Option_map_2_coe_left"))
        except Exception:
            pass
    return results


def _r0008_map_2_coe_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_coe_right
    # map₂ f a b = a.map fun a => f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("a_map", (OVar("fun"), args[1], OVar("eq_gt"), args[0], args[1], args[2],))
            results.append((rhs, "Mathlib: Option_map_2_coe_right"))
        except Exception:
            pass
    return results


def _r0009_mem_map_2_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.mem_map₂_iff
    # c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("c")
            results.append((rhs, "Mathlib: Option_mem_map_2_iff"))
        except Exception:
            pass
    return results


def _r0010_map_2_swap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_swap
    # map₂ f a b = map₂ (fun a b => f b a) b a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2", (OOp("fun", (args[1], args[2], OVar("eq_gt"), args[0], args[2], args[1],)), args[2], args[1],))
            results.append((rhs, "Mathlib: Option_map_2_swap"))
        except Exception:
            pass
    return results


def _r0011_map_uncurry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_uncurry
    # x.map (uncurry f) = map₂ f (x.map Prod.fst) (x.map Prod.snd)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_map", 1)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("f"), OOp("x_map", (OVar("Prod_fst"),)), OOp("x_map", (OVar("Prod_snd"),)),))
            results.append((rhs, "Mathlib: Option_map_uncurry"))
        except Exception:
            pass
    return results


def _r0012_mem_toFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.mem_toFinset
    # a ∈ o.toFinset ↔ a ∈ o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("o")))
            results.append((rhs, "Mathlib: Option_mem_toFinset"))
        except Exception:
            pass
    return results


def _r0013_smul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.smul_def
    # a • x = x.map (a • ·)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("x_map", (OOp("a", (args[0], args[0],)),))
            results.append((rhs, "Mathlib: Option_smul_def"))
        except Exception:
            pass
    return results


def _r0014_smul_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.smul_none
    # a • (none : Option α) = none
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OVar("none")
            results.append((rhs, "Mathlib: Option_smul_none"))
        except Exception:
            pass
    return results


def _r0015_goto_mkLabel(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OptionT.goto_mkLabel
    # goto (OptionT.mkLabel x) i = OptionT.mk (goto x (some i) >>= fun a => pure (some a))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "goto", 2)
    if args is not None:
        try:
            rhs = OOp("OptionT_mk", (OOp("goto", (OVar("x"), OOp("some", (args[1],)), OVar("gt_gt_eq"), OVar("fun"), OVar("a"), OVar("eq_gt"), OVar("pure"), OOp("some", (OVar("a"),)),)),))
            results.append((rhs, "Mathlib: OptionT_goto_mkLabel"))
        except Exception:
            pass
    return results


def _r0016_comp_traverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.comp_traverse
    # Option.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =       Comp.mk (Option.traverse f <$> Option.traverse g x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Option_traverse", 2)
    if args is not None:
        try:
            rhs = OOp("Comp_mk", (OOp("Option_traverse", (OVar("f"), OVar("lt_gt"), OVar("Option_traverse"), OVar("g"), args[1],)),))
            results.append((rhs, "Mathlib: Option_comp_traverse"))
        except Exception:
            pass
    return results


def _r0017_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.naturality
    # η (Option.traverse f x) = Option.traverse (@η _ ∘ f) x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eta", 1)
    if args is not None:
        try:
            rhs = OOp("Option_traverse", (OOp("comp", (OOp("at_eta", (OVar("_unknown"),)), OVar("f"))), OVar("x"),))
            results.append((rhs, "Mathlib: Option_naturality"))
        except Exception:
            pass
    return results


def _r0018_toFinset_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.toFinset_none
    # none.toFinset = (∅ : Finset α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("none_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("empty", (OVar("colon"), OVar("Finset"), OVar("a"),))
            results.append((rhs, "Mathlib: Option_toFinset_none"))
    except Exception:
        pass
    return results


def _r0019_toList_nodup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.toList_nodup
    # ∀ o : Option α, o.toList.Nodup   | none => List.nodup_nil   | some x => List.nodup_singleton x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nodup", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("List_nodup_nil"), args[0], OVar("some"), OVar("x"), OVar("eq_gt"), OVar("List_nodup_singleton"), OVar("x"),))
            results.append((rhs, "Mathlib: Option_toList_nodup"))
        except Exception:
            pass
    return results


def _r0020_mem_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.mem_map
    # y ∈ o.map f ↔ ∃ x ∈ o, f x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: Option_mem_map"))
        except Exception:
            pass
    return results


def _r0021_coe_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.coe_get
    # ((Option.get _ h : α) : Option α) = o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Option_get_h_colon_a", 3)
    if args is not None:
        try:
            rhs = OVar("o")
            results.append((rhs, "Mathlib: Option_coe_get"))
        except Exception:
            pass
    return results


def _r0022_eq_of_mem_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.eq_of_mem_of_mem
    # o1 = o2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("o1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("o2")
            results.append((rhs, "Mathlib: Option_eq_of_mem_of_mem"))
    except Exception:
        pass
    return results


def _r0023_map_comp_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_comp_some
    # Option.map f ∘ some = some ∘ f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (args[1], OVar("f")))
            results.append((rhs, "Mathlib: Option_map_comp_some"))
        except Exception:
            pass
    return results


def _r0024_joinM_eq_join(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.joinM_eq_join
    # joinM = @join α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("joinM")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("at_join", (OVar("a"),))
            results.append((rhs, "Mathlib: Option_joinM_eq_join"))
    except Exception:
        pass
    return results


def _r0025_map_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_coe
    # f <$> (a : Option α) = ↑(f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OVar("f_a")
            results.append((rhs, "Mathlib: Option_map_coe"))
        except Exception:
            pass
    return results


def _r0026_map_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_inj
    # Option.map f = Option.map g ↔ f = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "option_map", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("option_map", (OVar("g"),)), args[0])), OVar("g")))
            results.append((rhs, "Mathlib: Option_map_inj"))
        except Exception:
            pass
    return results


def _r0027_pmap_bind(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.pmap_bind
    # pmap f (x >>= g) H = x >>= fun a ↦ pmap f (g a) fun _ h ↦ H _ (H' a _ h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pmap", 3)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("gt_gt_eq"), OVar("fun"), OVar("a"), OVar("_unknown"), OVar("pmap"), args[0], OOp("g", (OVar("a"),)), OVar("fun"), OVar("_unknown"), OVar("h"), OVar("_unknown"), args[2], OVar("_unknown"), OOp("H_prime", (OVar("a"), OVar("_unknown"), OVar("h"),)),))
            results.append((rhs, "Mathlib: Option_pmap_bind"))
        except Exception:
            pass
    return results


def _r0028_bind_pmap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.bind_pmap
    # pmap f x H >>= g = x.pbind fun a h ↦ g (f a (H _ h))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pmap", 5)
    if args is not None:
        try:
            rhs = OOp("x_pbind", (OVar("fun"), OVar("a"), OVar("h"), OVar("_unknown"), args[4], OOp("f", (OVar("a"), OOp("H", (OVar("_unknown"), OVar("h"),)),)),))
            results.append((rhs, "Mathlib: Option_bind_pmap"))
        except Exception:
            pass
    return results


def _r0029_pbind_eq_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.pbind_eq_none
    # x.pbind f = none ↔ x = none
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_pbind", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("none"), OVar("x"))), OVar("none")))
            results.append((rhs, "Mathlib: Option_pbind_eq_none"))
        except Exception:
            pass
    return results


def _r0030_join_pmap_eq_pmap_join(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.join_pmap_eq_pmap_join
    # (pmap (pmap f) x H).join = pmap f x.join fun a h ↦ H (some a) (mem_of_mem_join h) _ rfl
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pmap_pmap_f_x_H_join")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("pmap", (OVar("f"), OVar("x_join"), OVar("fun"), OVar("a"), OVar("h"), OVar("_unknown"), OVar("H"), OOp("some", (OVar("a"),)), OOp("mem_of_mem_join", (OVar("h"),)), OVar("_unknown"), OVar("rfl"),))
            results.append((rhs, "Mathlib: Option_join_pmap_eq_pmap_join"))
    except Exception:
        pass
    return results


def _r0031_pmap_bind_id_eq_pmap_join(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.pmap_bind_id_eq_pmap_join
    # ((pmap (pmap f) x H).bind fun a ↦ a) =       pmap f x.join fun a h ↦ H (some a) (mem_of_mem_join h) _ rfl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pmap_pmap_f_x_H_bind", 4)
    if args is not None:
        try:
            rhs = OOp("pmap", (OVar("f"), OVar("x_join"), args[0], args[3], OVar("h"), args[2], OVar("H"), OOp("some", (args[3],)), OOp("mem_of_mem_join", (OVar("h"),)), args[2], OVar("rfl"),))
            results.append((rhs, "Mathlib: Option_pmap_bind_id_eq_pmap_join"))
        except Exception:
            pass
    return results


def _r0032_iget_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.iget_some
    # (some a).iget = a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("some_a_iget")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Option_iget_some"))
    except Exception:
        pass
    return results


def _r0033_map_2_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_def
    # map₂ f a b = f <$> a <*> b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("lt_gt"), args[1], OVar("lt_star_gt"), args[2],))
            results.append((rhs, "Mathlib: Option_map_2_def"))
        except Exception:
            pass
    return results


def _r0034_map_2_some_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_some_some
    # map₂ f (some a) (some b) = f a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Option_map_2_some_some"))
        except Exception:
            pass
    return results


def _r0035_map_2_none_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_none_left
    # map₂ f none b = none
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Option_map_2_none_left"))
        except Exception:
            pass
    return results


def _r0036_map_2_eq_some_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_eq_some_iff
    # map₂ f a b = some c ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OOp("iff", (OOp("some", (OVar("c"),)), OOp("in", (OOp("exists", (OVar("a_prime"), OVar("b_prime"), OVar("a_prime"),)), args[1])))), OOp("and", (OOp("in", (OVar("b_prime"), args[2])), OOp("f", (OVar("a_prime"), OVar("b_prime"),)))))), OVar("c")))
            results.append((rhs, "Mathlib: Option_map_2_eq_some_iff"))
        except Exception:
            pass
    return results


def _r0037_map_2_eq_none_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_eq_none_iff
    # map₂ f a b = none ↔ a = none ∨ b = none
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("none"), args[1])), OOp("==", (OOp("or", (OVar("none"), args[2])), OVar("none")))))
            results.append((rhs, "Mathlib: Option_map_2_eq_none_iff"))
        except Exception:
            pass
    return results


def _r0038_map_map_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_map₂
    # (map₂ f a b).map g = map₂ (fun a b => g (f a b)) a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2_f_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("map_2", (OOp("fun", (OVar("a"), OVar("b"), OVar("eq_gt"), args[0], OOp("f", (OVar("a"), OVar("b"),)),)), OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Option_map_map_2"))
        except Exception:
            pass
    return results


def _r0039_map_2_map_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_map_left
    # map₂ f (a.map g) b = map₂ (fun a b => f (g a) b) a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2", (OOp("fun", (OVar("a"), args[2], OVar("eq_gt"), args[0], OOp("g", (OVar("a"),)), args[2],)), OVar("a"), args[2],))
            results.append((rhs, "Mathlib: Option_map_2_map_left"))
        except Exception:
            pass
    return results


def _r0040_map_2_map_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_map_right
    # map₂ f a (b.map g) = map₂ (fun a b => f a (g b)) a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2", (OOp("fun", (args[1], OVar("b"), OVar("eq_gt"), args[0], args[1], OOp("g", (OVar("b"),)),)), args[1], OVar("b"),))
            results.append((rhs, "Mathlib: Option_map_2_map_right"))
        except Exception:
            pass
    return results


def _r0041_map_2_curry(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_curry
    # map₂ (curry f) a b = Option.map f (map₂ Prod.mk a b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("option_map", (OVar("f"), OOp("map_2", (OVar("Prod_mk"), args[1], args[2],)),))
            results.append((rhs, "Mathlib: Option_map_2_curry"))
        except Exception:
            pass
    return results


def _r0042_map_2_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_assoc
    # map₂ f (map₂ g a b) c = map₂ f' a (map₂ g' b c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("f_prime"), OVar("a"), OOp("map_2", (OVar("g_prime"), OVar("b"), args[2],)),))
            results.append((rhs, "Mathlib: Option_map_2_assoc"))
        except Exception:
            pass
    return results


def _r0043_map_2_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_comm
    # map₂ f a b = map₂ g b a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("g"), args[2], args[1],))
            results.append((rhs, "Mathlib: Option_map_2_comm"))
        except Exception:
            pass
    return results


def _r0044_map_2_left_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_left_comm
    # map₂ f a (map₂ g b c) = map₂ g' b (map₂ f' a c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("g_prime"), OVar("b"), OOp("map_2", (OVar("f_prime"), args[1], OVar("c"),)),))
            results.append((rhs, "Mathlib: Option_map_2_left_comm"))
        except Exception:
            pass
    return results


def _r0045_map_2_right_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_right_comm
    # map₂ f (map₂ g a b) c = map₂ g' (map₂ f' a c) b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("g_prime"), OOp("map_2", (OVar("f_prime"), OVar("a"), args[2],)), OVar("b"),))
            results.append((rhs, "Mathlib: Option_map_2_right_comm"))
        except Exception:
            pass
    return results


def _r0046_map_map_2_distrib(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_map₂_distrib
    # (map₂ f a b).map g = map₂ f' (a.map g₁) (b.map g₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2_f_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("f_prime"), OOp("a_map", (OVar("g_1"),)), OOp("b_map", (OVar("g_2"),)),))
            results.append((rhs, "Mathlib: Option_map_map_2_distrib"))
        except Exception:
            pass
    return results


def _r0047_map_map_2_distrib_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_map₂_distrib_left
    # (map₂ f a b).map g = map₂ f' (a.map g') b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2_f_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("f_prime"), OOp("a_map", (OVar("g_prime"),)), OVar("b"),))
            results.append((rhs, "Mathlib: Option_map_map_2_distrib_left"))
        except Exception:
            pass
    return results


def _r0048_map_map_2_distrib_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_map₂_distrib_right
    # (map₂ f a b).map g = map₂ f' a (b.map g')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2_f_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("f_prime"), OVar("a"), OOp("b_map", (OVar("g_prime"),)),))
            results.append((rhs, "Mathlib: Option_map_map_2_distrib_right"))
        except Exception:
            pass
    return results


def _r0049_map_2_map_left_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_map_left_comm
    # map₂ f (a.map g) b = (map₂ f' a b).map g'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2_f_prime_a_b_map", (OVar("g_prime"),))
            results.append((rhs, "Mathlib: Option_map_2_map_left_comm"))
        except Exception:
            pass
    return results


def _r0050_map_map_2_right_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_map₂_right_comm
    # map₂ f a (b.map g) = (map₂ f' a b).map g'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2_f_prime_a_b_map", (OVar("g_prime"),))
            results.append((rhs, "Mathlib: Option_map_map_2_right_comm"))
        except Exception:
            pass
    return results


def _r0051_map_map_2_antidistrib(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_map₂_antidistrib
    # (map₂ f a b).map g = map₂ f' (b.map g₁) (a.map g₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2_f_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("f_prime"), OOp("b_map", (OVar("g_1"),)), OOp("a_map", (OVar("g_2"),)),))
            results.append((rhs, "Mathlib: Option_map_map_2_antidistrib"))
        except Exception:
            pass
    return results


def _r0052_map_map_2_antidistrib_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_map₂_antidistrib_left
    # (map₂ f a b).map g = map₂ f' (b.map g') a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2_f_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("f_prime"), OOp("b_map", (OVar("g_prime"),)), OVar("a"),))
            results.append((rhs, "Mathlib: Option_map_map_2_antidistrib_left"))
        except Exception:
            pass
    return results


def _r0053_map_map_2_antidistrib_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_map₂_antidistrib_right
    # (map₂ f a b).map g = map₂ f' b (a.map g')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2_f_a_b_map", 1)
    if args is not None:
        try:
            rhs = OOp("map_2", (OVar("f_prime"), OVar("b"), OOp("a_map", (OVar("g_prime"),)),))
            results.append((rhs, "Mathlib: Option_map_map_2_antidistrib_right"))
        except Exception:
            pass
    return results


def _r0054_map_2_map_left_anticomm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_map_left_anticomm
    # map₂ f (a.map g) b = (map₂ f' b a).map g'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2_f_prime_b_a_map", (OVar("g_prime"),))
            results.append((rhs, "Mathlib: Option_map_2_map_left_anticomm"))
        except Exception:
            pass
    return results


def _r0055_map_map_2_right_anticomm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map_map₂_right_anticomm
    # map₂ f a (b.map g) = (map₂ f' b a).map g'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = OOp("map_2_f_prime_b_a_map", (OVar("g_prime"),))
            results.append((rhs, "Mathlib: Option_map_map_2_right_anticomm"))
        except Exception:
            pass
    return results


def _r0056_map_2_left_identity(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_left_identity
    # map₂ f (some a) o = o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Option_map_2_left_identity"))
        except Exception:
            pass
    return results


def _r0057_map_2_right_identity(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.map₂_right_identity
    # map₂ f o (some b) = o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_2", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Option_map_2_right_identity"))
        except Exception:
            pass
    return results


def _r0058_range_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.range_eq
    # range f = insert (f none) (range (f ∘ some))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("insert", (OOp("f", (OVar("none"),)), OOp("range", (OOp("comp", (args[0], OVar("some"))),)),))
            results.append((rhs, "Mathlib: Option_range_eq"))
        except Exception:
            pass
    return results


def _r0059_range_elim(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.range_elim
    # range (fun o : Option α => o.elim b f) = insert b (range f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OOp("insert", (OVar("b"), OOp("range", (OVar("f"),)),))
            results.append((rhs, "Mathlib: Option_range_elim"))
        except Exception:
            pass
    return results


def _r0060_image_elim_range_some_eq_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.image_elim_range_some_eq_range
    # (fun o : Option α => o.elim b f) '' range some = range f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fun_o_colon_Option_a_eq_gt_o_elim_b_f", 3)
    if args is not None:
        try:
            rhs = OOp("range", (OVar("f"),))
            results.append((rhs, "Mathlib: Option_image_elim_range_some_eq_range"))
        except Exception:
            pass
    return results


def _r0061_rec_update(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.rec_update
    # Option.rec f (update g a x) = update (Option.rec f g) (.some a) x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Option_rec", 2)
    if args is not None:
        try:
            rhs = OOp("update", (OOp("Option_rec", (args[0], OVar("g"),)), OOp("some", (OVar("a"),)), OVar("x"),))
            results.append((rhs, "Mathlib: Option_rec_update"))
        except Exception:
            pass
    return results


def _r0062_mem_map_of_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.mem_map_of_injective
    # f a ∈ o.map f ↔ a ∈ o
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("a"), OVar("o")))
            results.append((rhs, "Mathlib: Option_mem_map_of_injective"))
        except Exception:
            pass
    return results


def _r0063_forall_mem_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.forall_mem_map
    # (∀ y ∈ o.map f, p y) ↔ ∀ x ∈ o, p (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("x"),)), OOp("o", (OVar("p"), OOp("f", (OVar("x"),)),))))
            results.append((rhs, "Mathlib: Option_forall_mem_map"))
        except Exception:
            pass
    return results


def _r0064_exists_mem_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.exists_mem_map
    # (∃ y ∈ o.map f, p y) ↔ ∃ x ∈ o, p (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("x"),)), OOp("o", (OVar("p"), OOp("f", (OVar("x"),)),))))
            results.append((rhs, "Mathlib: Option_exists_mem_map"))
        except Exception:
            pass
    return results


def _r0065_injective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.injective_iff
    # Injective f ↔ Injective (f ∘ some) ∧ f none ∉ range (f ∘ some)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("injective", (OOp("comp", (args[0], OVar("some"))),)), OOp("not_in", (OOp("f", (OVar("none"),)), OOp("range", (OOp("comp", (args[0], OVar("some"))),))))))
            results.append((rhs, "Mathlib: Option_injective_iff"))
        except Exception:
            pass
    return results


def _r0066_subsingleton_iff_isEmpty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Option.subsingleton_iff_isEmpty
    # Subsingleton (Option α) ↔ IsEmpty α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subsingleton", 1)
    if args is not None:
        try:
            rhs = OOp("IsEmpty", (OVar("a"),))
            results.append((rhs, "Mathlib: Option_subsingleton_iff_isEmpty"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_option rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("Option", "OptionT_mkLabel", "Option_get_h_colon_a", "Option_map_f_1_a_map", "Option_rec", "Option_traverse", "Subsingleton", "a", "a_map", "and", "b_map", "comp", "curry", "eta", "exists", "f", "forall", "fun", "fun_o_colon_Option_a_eq_gt_o_elim_b_f", "goto", "iff", "in", "injective", "map_2", "map_2_f_a_b_map", "nodup", "none", "o", "o_map", "option_map", "pmap", "pmap_pmap_f_x_H_bind", "range", "some", "uncurry", "update", "x", "x_map", "x_pbind",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_option axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_option rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_smul_some(term, ctx))
    results.extend(_r0001_toFinset_some(term, ctx))
    results.extend(_r0002_card_toFinset(term, ctx))
    results.extend(_r0003_map_eq_id(term, ctx))
    results.extend(_r0004_map_comm(term, ctx))
    results.extend(_r0005_map_2_coe_coe(term, ctx))
    results.extend(_r0006_map_2_none_right(term, ctx))
    results.extend(_r0007_map_2_coe_left(term, ctx))
    results.extend(_r0008_map_2_coe_right(term, ctx))
    results.extend(_r0009_mem_map_2_iff(term, ctx))
    results.extend(_r0010_map_2_swap(term, ctx))
    results.extend(_r0011_map_uncurry(term, ctx))
    results.extend(_r0012_mem_toFinset(term, ctx))
    results.extend(_r0013_smul_def(term, ctx))
    results.extend(_r0014_smul_none(term, ctx))
    results.extend(_r0015_goto_mkLabel(term, ctx))
    results.extend(_r0016_comp_traverse(term, ctx))
    results.extend(_r0017_naturality(term, ctx))
    results.extend(_r0018_toFinset_none(term, ctx))
    results.extend(_r0019_toList_nodup(term, ctx))
    results.extend(_r0020_mem_map(term, ctx))
    results.extend(_r0021_coe_get(term, ctx))
    results.extend(_r0022_eq_of_mem_of_mem(term, ctx))
    results.extend(_r0023_map_comp_some(term, ctx))
    results.extend(_r0024_joinM_eq_join(term, ctx))
    results.extend(_r0025_map_coe(term, ctx))
    results.extend(_r0026_map_inj(term, ctx))
    results.extend(_r0027_pmap_bind(term, ctx))
    results.extend(_r0028_bind_pmap(term, ctx))
    results.extend(_r0029_pbind_eq_none(term, ctx))
    results.extend(_r0030_join_pmap_eq_pmap_join(term, ctx))
    results.extend(_r0031_pmap_bind_id_eq_pmap_join(term, ctx))
    results.extend(_r0032_iget_some(term, ctx))
    results.extend(_r0033_map_2_def(term, ctx))
    results.extend(_r0034_map_2_some_some(term, ctx))
    results.extend(_r0035_map_2_none_left(term, ctx))
    results.extend(_r0036_map_2_eq_some_iff(term, ctx))
    results.extend(_r0037_map_2_eq_none_iff(term, ctx))
    results.extend(_r0038_map_map_2(term, ctx))
    results.extend(_r0039_map_2_map_left(term, ctx))
    results.extend(_r0040_map_2_map_right(term, ctx))
    results.extend(_r0041_map_2_curry(term, ctx))
    results.extend(_r0042_map_2_assoc(term, ctx))
    results.extend(_r0043_map_2_comm(term, ctx))
    results.extend(_r0044_map_2_left_comm(term, ctx))
    results.extend(_r0045_map_2_right_comm(term, ctx))
    results.extend(_r0046_map_map_2_distrib(term, ctx))
    results.extend(_r0047_map_map_2_distrib_left(term, ctx))
    results.extend(_r0048_map_map_2_distrib_right(term, ctx))
    results.extend(_r0049_map_2_map_left_comm(term, ctx))
    results.extend(_r0050_map_map_2_right_comm(term, ctx))
    results.extend(_r0051_map_map_2_antidistrib(term, ctx))
    results.extend(_r0052_map_map_2_antidistrib_left(term, ctx))
    results.extend(_r0053_map_map_2_antidistrib_right(term, ctx))
    results.extend(_r0054_map_2_map_left_anticomm(term, ctx))
    results.extend(_r0055_map_map_2_right_anticomm(term, ctx))
    results.extend(_r0056_map_2_left_identity(term, ctx))
    results.extend(_r0057_map_2_right_identity(term, ctx))
    results.extend(_r0058_range_eq(term, ctx))
    results.extend(_r0059_range_elim(term, ctx))
    results.extend(_r0060_image_elim_range_some_eq_range(term, ctx))
    results.extend(_r0061_rec_update(term, ctx))
    results.extend(_r0062_mem_map_of_injective(term, ctx))
    results.extend(_r0063_forall_mem_map(term, ctx))
    results.extend(_r0064_exists_mem_map(term, ctx))
    results.extend(_r0065_injective_iff(term, ctx))
    results.extend(_r0066_subsingleton_iff_isEmpty(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_option rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Option_id_traverse", "Option_traverse_pure_colon_a_to_Id_a_x_eq_pure_x", "Not an equality or iff proposition"),
    ("Option_traverse_eq_map_id", "Option_traverse_pure_colon_to_Id_comp_f_x_eq_pure_colon_to_Id_f_lt_gt_x", "Not an equality or iff proposition"),
    ("Option_coe_def", "fun_a_a_colon_a_to_Option_a_eq_some", "Not an equality or iff proposition"),
    ("Option_Mem_leftUnique", "Relator_LeftUnique_in_colon_a_to_Option_a_to_Prop", "Not an equality or iff proposition"),
    ("Option_some_injective", "Function_Injective_at_some_a", "Not an equality or iff proposition"),
    ("Option_bind_congr", "_unknown", "Empty proposition"),
    ("Option_bind_eq_bind", "_unknown", "Empty proposition"),
    ("Option_map_coe", "_unknown", "Empty proposition"),
    ("Option_map_injective", "_unknown", "Empty proposition"),
    ("Option_mem_pmem", "f_a_h_a_ha_in_pmap_f_x_h", "Not an equality or iff proposition"),
    ("Option_elim", "_unknown", "Empty proposition"),
    ("Option_elim", "_unknown", "Empty proposition"),
    ("Option_elim", "_unknown", "Empty proposition"),
    ("Option_elim", "_unknown", "Empty proposition"),
]
