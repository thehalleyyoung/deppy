"""Mathlib: Bool — auto-generated from Mathlib4.

Contains 158 rewrite rules derived from Mathlib theorems.
Plus 48 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_bool"
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
# Rewrite rules (158 total)
# ════════════════════════════════════════════════════════════

def _r0000_mul_one_add_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.mul_one_add_self
    # a * (1 + a) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: BooleanRing_mul_one_add_self"))
        except Exception:
            pass
    return results


def _r0001_range_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.range_eq
    # range f = {f false, f true}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OVar("f_false_f_true")
            results.append((rhs, "Mathlib: Bool_range_eq"))
        except Exception:
            pass
    return results


def _r0002_compl_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.compl_singleton
    # ({b}ᶜ : Set Bool) = {!b}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "b", 3)
    if args is not None:
        try:
            rhs = OVar("bangb")
            results.append((rhs, "Mathlib: Bool_compl_singleton"))
        except Exception:
            pass
    return results


def _r0003_coe_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_mk
    # (mk L h_compl h_bot : Set α) = L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 6)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_mk"))
        except Exception:
            pass
    return results


def _r0004_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.copy_eq
    # L.copy s hs = L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_copy", 2)
    if args is not None:
        try:
            rhs = OVar("L")
            results.append((rhs, "Mathlib: BooleanSubalgebra_copy_eq"))
        except Exception:
            pass
    return results


def _r0005_val_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.val_top
    # (⊤ : L) = (⊤ : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top", 2)
    if args is not None:
        try:
            rhs = OOp("top", (args[0], OVar("a"),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_val_top"))
        except Exception:
            pass
    return results


def _r0006_val_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.val_sup
    # a ⊔ b = (a : α) ⊔ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("a_colon_a", (args[0], args[1],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_val_sup"))
        except Exception:
            pass
    return results


def _r0007_val_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.val_inf
    # a ⊓ b = (a : α) ⊓ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("a_colon_a", (args[0], args[1],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_val_inf"))
        except Exception:
            pass
    return results


def _r0008_val_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.val_compl
    # aᶜ = (a : α)ᶜ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a_colon_a")
            results.append((rhs, "Mathlib: BooleanSubalgebra_val_compl"))
    except Exception:
        pass
    return results


def _r0009_val_sdiff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.val_sdiff
    # a \\ b = (a : α) \\ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("a_colon_a", (args[0], args[1],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_val_sdiff"))
        except Exception:
            pass
    return results


def _r0010_val_himp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.val_himp
    # a ⇨ b = (a : α) ⇨ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("a_colon_a", (args[0], args[1],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_val_himp"))
        except Exception:
            pass
    return results


def _r0011_mk_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mk_bot
    # (⟨⊥, bot_mem⟩ : L) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_bot_mem", 2)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: BooleanSubalgebra_mk_bot"))
        except Exception:
            pass
    return results


def _r0012_mk_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mk_top
    # (⟨⊤, top_mem⟩ : L) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_top_mem", 2)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: BooleanSubalgebra_mk_top"))
        except Exception:
            pass
    return results


def _r0013_mk_sup_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mk_sup_mk
    # (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_ha", 4)
    if args is not None:
        try:
            rhs = OVar("a_b_L_supClosed_ha_hb")
            results.append((rhs, "Mathlib: BooleanSubalgebra_mk_sup_mk"))
        except Exception:
            pass
    return results


def _r0014_mk_inf_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mk_inf_mk
    # (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_ha", 4)
    if args is not None:
        try:
            rhs = OVar("a_b_L_infClosed_ha_hb")
            results.append((rhs, "Mathlib: BooleanSubalgebra_mk_inf_mk"))
        except Exception:
            pass
    return results


def _r0015_compl_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.compl_mk
    # (⟨a, ha⟩ : L)ᶜ = ⟨aᶜ, compl_mem ha⟩
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_ha_colon_L")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a_compl_mem_ha")
            results.append((rhs, "Mathlib: BooleanSubalgebra_compl_mk"))
    except Exception:
        pass
    return results


def _r0016_mk_sdiff_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mk_sdiff_mk
    # (⟨a, ha⟩ \\ ⟨b, hb⟩ : L) = ⟨a \\ b, sdiff_mem ha hb⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_ha", 4)
    if args is not None:
        try:
            rhs = OVar("a_bsl_b_sdiff_mem_ha_hb")
            results.append((rhs, "Mathlib: BooleanSubalgebra_mk_sdiff_mk"))
        except Exception:
            pass
    return results


def _r0017_mk_himp_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mk_himp_mk
    # (⟨a, ha⟩ ⇨ ⟨b, hb⟩ : L) = ⟨a ⇨ b, himp_mem ha hb⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_ha", 4)
    if args is not None:
        try:
            rhs = OVar("a_b_himp_mem_ha_hb")
            results.append((rhs, "Mathlib: BooleanSubalgebra_mk_himp_mk"))
        except Exception:
            pass
    return results


def _r0018_subtype_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.subtype_apply
    # L.subtype a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_subtype", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: BooleanSubalgebra_subtype_apply"))
        except Exception:
            pass
    return results


def _r0019_inclusion_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.inclusion_apply
    # inclusion h a = Set.inclusion h a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inclusion", 2)
    if args is not None:
        try:
            rhs = OOp("Set_inclusion", (args[0], args[1],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_inclusion_apply"))
        except Exception:
            pass
    return results


def _r0020_subtype_comp_inclusion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.subtype_comp_inclusion
    # M.subtype.comp (inclusion h) = L.subtype
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "M_subtype_comp", 1)
    if args is not None:
        try:
            rhs = OVar("L_subtype")
            results.append((rhs, "Mathlib: BooleanSubalgebra_subtype_comp_inclusion"))
        except Exception:
            pass
    return results


def _r0021_coe_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_bot
    # (⊥ : BooleanSubalgebra α) = ({⊥, ⊤} : Set α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot", 3)
    if args is not None:
        try:
            rhs = OOp("bot_top", (args[0], OVar("Set"), args[2],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_bot"))
        except Exception:
            pass
    return results


def _r0022_coe_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_inf
    # L ⊓ M = (L : Set α) ∩ M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("L", (OVar("colon"), OVar("Set"), OVar("a"),)), args[1]))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_inf"))
        except Exception:
            pass
    return results


def _r0023_coe_sInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_sInf
    # sInf S = ⋂ L ∈ S, (L : Set α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sInf", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("L"),)), OOp("S", (OOp("L", (OVar("colon"), OVar("Set"), OVar("a"),)),))))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_sInf"))
        except Exception:
            pass
    return results


def _r0024_coe_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_iInf
    # ⨅ i, f i = ⋂ i, (f i : Set α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (args[2], OOp("f", (args[2], OVar("colon"), OVar("Set"), OVar("a"),)),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_iInf"))
        except Exception:
            pass
    return results


def _r0025_coe_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_eq_univ
    # L = (univ : Set α) ↔ L = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("univ_set", (OVar("colon"), OVar("Set"), OVar("a"),)), OVar("L"))), OVar("top")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_eq_univ"))
    except Exception:
        pass
    return results


def _r0026_mem_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_bot
    # a ∈ (⊥ : BooleanSubalgebra α) ↔ a = ⊥ ∨ a = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OVar("bot"), args[1])), OVar("top")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_bot"))
        except Exception:
            pass
    return results


def _r0027_comap_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.comap_id
    # L.comap (BoundedLatticeHom.id _) = L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_comap", 1)
    if args is not None:
        try:
            rhs = OVar("L")
            results.append((rhs, "Mathlib: BooleanSubalgebra_comap_id"))
        except Exception:
            pass
    return results


def _r0028_comap_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.comap_comap
    # (L.comap g).comap f = L.comap (g.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_comap_g_comap", 1)
    if args is not None:
        try:
            rhs = OOp("L_comap", (OOp("g_comp", (args[0],)),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_comap_comap"))
        except Exception:
            pass
    return results


def _r0029_mem_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_map
    # b ∈ L.map f ↔ ∃ a ∈ L, f a = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_map"))
        except Exception:
            pass
    return results


def _r0030_map_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.map_map
    # (L.map f).map g = L.map (g.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_map_f_map", 1)
    if args is not None:
        try:
            rhs = OOp("L_map", (OOp("g_comp", (OVar("f"),)),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_map_map"))
        except Exception:
            pass
    return results


def _r0031_map_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.map_sup
    # (L ⊔ M).map f = L.map f ⊔ M.map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_M_map", 1)
    if args is not None:
        try:
            rhs = OOp("L_map", (args[0], OVar("_unknown"), OVar("M_map"), args[0],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_map_sup"))
        except Exception:
            pass
    return results


def _r0032_comap_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.comap_inf
    # (L ⊓ M).comap f = L.comap f ⊓ M.comap f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_M_comap", 1)
    if args is not None:
        try:
            rhs = OOp("L_comap", (args[0], OVar("_unknown"), OVar("M_comap"), args[0],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_comap_inf"))
        except Exception:
            pass
    return results


def _r0033_compl_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.compl_comp
    # (comp a)ᶜ = lift a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("comp_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("lift", (OVar("a"),))
            results.append((rhs, "Mathlib: Booleanisation_compl_comp"))
    except Exception:
        pass
    return results


def _r0034_lift_sup_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_sup_lift
    # lift a ⊔ lift b = lift (a ⊔ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 4)
    if args is not None:
        try:
            rhs = OOp("lift", (OOp("a", (args[1], args[3],)),))
            results.append((rhs, "Mathlib: Booleanisation_lift_sup_lift"))
        except Exception:
            pass
    return results


def _r0035_lift_sup_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_sup_comp
    # lift a ⊔ comp b = comp (b \\ a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 4)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("b", (OVar("bsl"), args[0],)),))
            results.append((rhs, "Mathlib: Booleanisation_lift_sup_comp"))
        except Exception:
            pass
    return results


def _r0036_comp_sup_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.comp_sup_lift
    # comp a ⊔ lift b = comp (a \\ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 4)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("a", (OVar("bsl"), args[3],)),))
            results.append((rhs, "Mathlib: Booleanisation_comp_sup_lift"))
        except Exception:
            pass
    return results


def _r0037_comp_sup_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.comp_sup_comp
    # comp a ⊔ comp b = comp (a ⊓ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 4)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("a", (args[1], args[3],)),))
            results.append((rhs, "Mathlib: Booleanisation_comp_sup_comp"))
        except Exception:
            pass
    return results


def _r0038_lift_inf_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_inf_lift
    # lift a ⊓ lift b = lift (a ⊓ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 4)
    if args is not None:
        try:
            rhs = OOp("lift", (OOp("a", (args[1], args[3],)),))
            results.append((rhs, "Mathlib: Booleanisation_lift_inf_lift"))
        except Exception:
            pass
    return results


def _r0039_lift_inf_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_inf_comp
    # lift a ⊓ comp b = lift (a \\ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 4)
    if args is not None:
        try:
            rhs = OOp("lift", (OOp("a", (OVar("bsl"), args[3],)),))
            results.append((rhs, "Mathlib: Booleanisation_lift_inf_comp"))
        except Exception:
            pass
    return results


def _r0040_comp_inf_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.comp_inf_lift
    # comp a ⊓ lift b = lift (b \\ a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 4)
    if args is not None:
        try:
            rhs = OOp("lift", (OOp("b", (OVar("bsl"), args[0],)),))
            results.append((rhs, "Mathlib: Booleanisation_comp_inf_lift"))
        except Exception:
            pass
    return results


def _r0041_comp_inf_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.comp_inf_comp
    # comp a ⊓ comp b = comp (a ⊔ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 4)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("a", (args[1], args[3],)),))
            results.append((rhs, "Mathlib: Booleanisation_comp_inf_comp"))
        except Exception:
            pass
    return results


def _r0042_lift_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_bot
    # lift (⊥ : α) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Booleanisation_lift_bot"))
        except Exception:
            pass
    return results


def _r0043_comp_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.comp_bot
    # comp (⊥ : α) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Booleanisation_comp_bot"))
        except Exception:
            pass
    return results


def _r0044_lift_sdiff_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_sdiff_lift
    # lift a \\ lift b = lift (a \\ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 4)
    if args is not None:
        try:
            rhs = OOp("lift", (OOp("a", (args[1], args[3],)),))
            results.append((rhs, "Mathlib: Booleanisation_lift_sdiff_lift"))
        except Exception:
            pass
    return results


def _r0045_lift_sdiff_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_sdiff_comp
    # lift a \\ comp b = lift (a ⊓ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 4)
    if args is not None:
        try:
            rhs = OOp("lift", (OOp("a", (OVar("_unknown"), args[3],)),))
            results.append((rhs, "Mathlib: Booleanisation_lift_sdiff_comp"))
        except Exception:
            pass
    return results


def _r0046_comp_sdiff_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.comp_sdiff_lift
    # comp a \\ lift b = comp (a ⊔ b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 4)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("a", (OVar("_unknown"), args[3],)),))
            results.append((rhs, "Mathlib: Booleanisation_comp_sdiff_lift"))
        except Exception:
            pass
    return results


def _r0047_comp_sdiff_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.comp_sdiff_comp
    # comp a \\ comp b = lift (b \\ a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 4)
    if args is not None:
        try:
            rhs = OOp("lift", (OOp("b", (args[1], args[0],)),))
            results.append((rhs, "Mathlib: Booleanisation_comp_sdiff_comp"))
        except Exception:
            pass
    return results


def _r0048_forget_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.forget_map
    # (forget BoolAlg).map f = (f : _ → _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_BoolAlg_map", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("f", (OVar("colon"), OVar("_unknown"),)), OVar("_unknown")))
            results.append((rhs, "Mathlib: BoolAlg_forget_map"))
        except Exception:
            pass
    return results


def _r0049_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: BoolAlg_ext"))
    except Exception:
        pass
    return results


def _r0050_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.id_apply
    # (𝟙 X : X ⟶ X) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_X_colon_X_X", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: BoolAlg_id_apply"))
        except Exception:
            pass
    return results


def _r0051_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.ofHom_id
    # ofHom (BoundedLatticeHom.id _) = 𝟙 (of X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("X"),)),))
            results.append((rhs, "Mathlib: BoolAlg_ofHom_id"))
        except Exception:
            pass
    return results


def _r0052_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: BoolAlg_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0053_symmDiff_eq_xor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.symmDiff_eq_xor
    # ∀ p q : Bool, p ∆ q = xor p q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p", 2)
    if args is not None:
        try:
            rhs = OOp("xor", (OVar("p"), args[1],))
            results.append((rhs, "Mathlib: Bool_symmDiff_eq_xor"))
        except Exception:
            pass
    return results


def _r0054_compl_mem_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.compl_mem_iff
    # aᶜ ∈ L ↔ a ∈ L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], args[1]))
            results.append((rhs, "Mathlib: BooleanSubalgebra_compl_mem_iff"))
        except Exception:
            pass
    return results


def _r0055_mem_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_mk
    # a ∈ mk L h_compl h_bot ↔ a ∈ L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("L")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_mk"))
        except Exception:
            pass
    return results


def _r0056_mk_le_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mk_le_mk
    # mk L hL_compl hL_bot ≤ mk M hM_compl hM_bot ↔ L ≤ M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("L"), OVar("M")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mk_le_mk"))
        except Exception:
            pass
    return results


def _r0057_mk_lt_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mk_lt_mk
    # mk L hL_compl hL_bot < mk M hM_compl hM_bot ↔ L < M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("L"), OVar("M")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mk_lt_mk"))
        except Exception:
            pass
    return results


def _r0058_mem_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_inf
    # a ∈ L ⊓ M ↔ a ∈ L ∧ a ∈ M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (args[0], OVar("L"))), OOp("in", (args[0], OVar("M")))))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_inf"))
        except Exception:
            pass
    return results


def _r0059_mem_sInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_sInf
    # a ∈ sInf S ↔ ∀ L ∈ S, a ∈ L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("L"),)), OOp("in", (OOp("S", (args[0],)), OVar("L")))))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_sInf"))
        except Exception:
            pass
    return results


def _r0060_mem_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_iInf
    # a ∈ ⨅ i, f i ↔ ∀ i, a ∈ f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("i"), args[0],)), OOp("f", (OVar("i"),))))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_iInf"))
        except Exception:
            pass
    return results


def _r0061_mem_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_comap
    # a ∈ L.comap f ↔ f a ∈ L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("f", (args[0],)), OVar("L")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_comap"))
        except Exception:
            pass
    return results


def _r0062_mem_map_equiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_map_equiv
    # a ∈ L.map f ↔ f.symm a ∈ L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("f_symm", (args[0],)), OVar("L")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_map_equiv"))
        except Exception:
            pass
    return results


def _r0063_comp_le_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.comp_le_comp
    # comp a ≤ comp b ↔ b ≤ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("b"), OVar("a")))
            results.append((rhs, "Mathlib: Booleanisation_comp_le_comp"))
        except Exception:
            pass
    return results


def _r0064_lift_le_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_le_comp
    # lift a ≤ comp b ↔ Disjoint a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("Disjoint", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Booleanisation_lift_le_comp"))
        except Exception:
            pass
    return results


def _r0065_lift_lt_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_lt_lift
    # lift a < lift b ↔ a < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("a"), OVar("b")))
            results.append((rhs, "Mathlib: Booleanisation_lift_lt_lift"))
        except Exception:
            pass
    return results


def _r0066_comp_lt_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.comp_lt_comp
    # comp a < comp b ↔ b < a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("b"), OVar("a")))
            results.append((rhs, "Mathlib: Booleanisation_comp_lt_comp"))
        except Exception:
            pass
    return results


def _r0067_lift_lt_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_lt_comp
    # lift a < comp b ↔ Disjoint a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OOp("Disjoint", (OVar("a"), OVar("b"),))
            results.append((rhs, "Mathlib: Booleanisation_lift_lt_comp"))
        except Exception:
            pass
    return results


def _r0068_covBy_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.covBy_iff
    # ∀ {a b : Bool}, a ⋖ b ↔ a < b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("a"), args[1]))
            results.append((rhs, "Mathlib: Bool_covBy_iff"))
        except Exception:
            pass
    return results


def _r0069_coe_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolRing.coe_of
    # ↥(of α) = α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("of_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: BoolRing_coe_of"))
    except Exception:
        pass
    return results


def _r0070_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolRing.hom_ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: BoolRing_hom_ext"))
    except Exception:
        pass
    return results


def _r0071_mul_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.mul_self
    # a * a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: BooleanRing_mul_self"))
        except Exception:
            pass
    return results


def _r0072_add_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.add_self
    # a + a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: BooleanRing_add_self"))
        except Exception:
            pass
    return results


def _r0073_neg_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.neg_eq
    # -a = a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: BooleanRing_neg_eq"))
    except Exception:
        pass
    return results


def _r0074_mul_add_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.mul_add_mul
    # a * b + b * a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: BooleanRing_mul_add_mul"))
        except Exception:
            pass
    return results


def _r0075_sub_eq_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.sub_eq_add
    # a - b = a + b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: BooleanRing_sub_eq_add"))
        except Exception:
            pass
    return results


def _r0076_sup_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.sup_comm
    # a ⊔ b = b ⊔ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("b", (args[0], OVar("a"),))
            results.append((rhs, "Mathlib: BooleanRing_sup_comm"))
        except Exception:
            pass
    return results


def _r0077_inf_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.inf_comm
    # a ⊓ b = b ⊓ a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("b", (args[0], OVar("a"),))
            results.append((rhs, "Mathlib: BooleanRing_inf_comm"))
        except Exception:
            pass
    return results


def _r0078_sup_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.sup_assoc
    # a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = OOp("a", (args[2], OOp("b", (args[2], args[3],)),))
            results.append((rhs, "Mathlib: BooleanRing_sup_assoc"))
        except Exception:
            pass
    return results


def _r0079_inf_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.inf_assoc
    # a ⊓ b ⊓ c = a ⊓ (b ⊓ c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = OOp("a", (args[2], OOp("b", (args[2], args[3],)),))
            results.append((rhs, "Mathlib: BooleanRing_inf_assoc"))
        except Exception:
            pass
    return results


def _r0080_sup_inf_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.sup_inf_self
    # a ⊔ a ⊓ b = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: BooleanRing_sup_inf_self"))
        except Exception:
            pass
    return results


def _r0081_inf_sup_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.inf_sup_self
    # a ⊓ (a ⊔ b) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: BooleanRing_inf_sup_self"))
        except Exception:
            pass
    return results


def _r0082_le_sup_inf_aux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.le_sup_inf_aux
    # (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("a"), OOp("+", (OOp("*", (OVar("b"), OVar("c"))), OOp("*", (OVar("a"), OOp("*", (OVar("b"), OVar("c")))))))))
            results.append((rhs, "Mathlib: BooleanRing_le_sup_inf_aux"))
        except Exception:
            pass
    return results


def _r0083_le_sup_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanRing.le_sup_inf
    # (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_b", 4)
    if args is not None:
        try:
            rhs = OOp("a", (args[2], OVar("b"), args[2], OVar("c"),))
            results.append((rhs, "Mathlib: BooleanRing_le_sup_inf"))
        except Exception:
            pass
    return results


def _r0084_eq_false_eq_not_eq_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.eq_false_eq_not_eq_true
    # (¬(b = true)) = (b = false)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("b"), OLit(False)))
            results.append((rhs, "Mathlib: Bool_eq_false_eq_not_eq_true"))
        except Exception:
            pass
    return results


def _r0085_eq_true_eq_not_eq_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.eq_true_eq_not_eq_false
    # (¬(b = false)) = (b = true)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("b"), OLit(True)))
            results.append((rhs, "Mathlib: Bool_eq_true_eq_not_eq_false"))
        except Exception:
            pass
    return results


def _r0086_eq_false_of_not_eq_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.eq_false_of_not_eq_true
    # ¬b = true → b = false
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(False)
            results.append((rhs, "Mathlib: Bool_eq_false_of_not_eq_true"))
    except Exception:
        pass
    return results


def _r0087_eq_true_of_not_eq_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.eq_true_of_not_eq_false
    # ¬b = false → b = true
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(True)
            results.append((rhs, "Mathlib: Bool_eq_true_of_not_eq_false"))
    except Exception:
        pass
    return results


def _r0088_and_eq_true_eq_eq_true_and_eq_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.and_eq_true_eq_eq_true_and_eq_true
    # ((a && b) = true) = (a = true ∧ b = true)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("a"), OOp("==", (OOp("and", (OLit(True), OVar("b"))), OLit(True)))))
            results.append((rhs, "Mathlib: Bool_and_eq_true_eq_eq_true_and_eq_true"))
        except Exception:
            pass
    return results


def _r0089_or_eq_true_eq_eq_true_or_eq_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.or_eq_true_eq_eq_true_or_eq_true
    # ((a || b) = true) = (a = true ∨ b = true)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("a"), OOp("==", (OOp("or", (OLit(True), OVar("b"))), OLit(True)))))
            results.append((rhs, "Mathlib: Bool_or_eq_true_eq_eq_true_or_eq_true"))
        except Exception:
            pass
    return results


def _r0090_not_eq_true_eq_eq_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.not_eq_true_eq_eq_false
    # (not a = true) = (a = false)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("a"), OLit(False)))
            results.append((rhs, "Mathlib: Bool_not_eq_true_eq_eq_false"))
        except Exception:
            pass
    return results


def _r0091_and_eq_false_eq_eq_false_or_eq_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.and_eq_false_eq_eq_false_or_eq_false
    # ((a && b) = false) = (a = false ∨ b = false)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("a"), OOp("==", (OOp("or", (OLit(False), OVar("b"))), OLit(False)))))
            results.append((rhs, "Mathlib: Bool_and_eq_false_eq_eq_false_or_eq_false"))
        except Exception:
            pass
    return results


def _r0092_or_eq_false_eq_eq_false_and_eq_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.or_eq_false_eq_eq_false_and_eq_false
    # ((a || b) = false) = (a = false ∧ b = false)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("a"), OOp("==", (OOp("and", (OLit(False), OVar("b"))), OLit(False)))))
            results.append((rhs, "Mathlib: Bool_or_eq_false_eq_eq_false_and_eq_false"))
        except Exception:
            pass
    return results


def _r0093_not_eq_false_eq_eq_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.not_eq_false_eq_eq_true
    # (not a = false) = (a = true)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("a"), OLit(True)))
            results.append((rhs, "Mathlib: Bool_not_eq_false_eq_eq_true"))
        except Exception:
            pass
    return results


def _r0094_coe_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.coe_false
    # ↑false = False
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("false")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(False)
            results.append((rhs, "Mathlib: Bool_coe_false"))
    except Exception:
        pass
    return results


def _r0095_coe_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.coe_true
    # ↑true = True
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("true")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(True)
            results.append((rhs, "Mathlib: Bool_coe_true"))
    except Exception:
        pass
    return results


def _r0096_coe_sort_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.coe_sort_false
    # (false : Prop) = False
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "False", 2)
    if args is not None:
        try:
            rhs = OLit(False)
            results.append((rhs, "Mathlib: Bool_coe_sort_false"))
        except Exception:
            pass
    return results


def _r0097_coe_sort_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.coe_sort_true
    # (true : Prop) = True
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "True", 2)
    if args is not None:
        try:
            rhs = OLit(True)
            results.append((rhs, "Mathlib: Bool_coe_sort_true"))
        except Exception:
            pass
    return results


def _r0098_decide_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.decide_iff
    # decide p = true ↔ p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decide", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(True), args[0]))
            results.append((rhs, "Mathlib: Bool_decide_iff"))
        except Exception:
            pass
    return results


def _r0099_bool_iff_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.bool_iff_false
    # ¬b ↔ b = false
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(False)
            results.append((rhs, "Mathlib: Bool_bool_iff_false"))
        except Exception:
            pass
    return results


def _r0100_bool_eq_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.bool_eq_false
    # ¬b → b = false
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("b")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(False)
            results.append((rhs, "Mathlib: Bool_bool_eq_false"))
    except Exception:
        pass
    return results


def _r0101_decide_false_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.decide_false_iff
    # decide p = false ↔ ¬p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decide", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(False), OOp("not", (args[0],))))
            results.append((rhs, "Mathlib: Bool_decide_false_iff"))
        except Exception:
            pass
    return results


def _r0102_decide_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.decide_false
    # ¬p → decide p = false
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decide", 1)
    if args is not None:
        try:
            rhs = OLit(False)
            results.append((rhs, "Mathlib: Bool_decide_false"))
        except Exception:
            pass
    return results


def _r0103_of_decide_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.of_decide_false
    # decide p = false → ¬p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decide", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (OLit(False), OOp("not", (args[0],))))
            results.append((rhs, "Mathlib: Bool_of_decide_false"))
        except Exception:
            pass
    return results


def _r0104_decide_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.decide_congr
    # decide p = decide q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "decide", 1)
    if args is not None:
        try:
            rhs = OOp("decide", (OVar("q"),))
            results.append((rhs, "Mathlib: Bool_decide_congr"))
        except Exception:
            pass
    return results


def _r0105_univ_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.univ_eq
    # (univ : Set Bool) = {false, true}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "univ_set", 3)
    if args is not None:
        try:
            rhs = OVar("false_true")
            results.append((rhs, "Mathlib: Bool_univ_eq"))
        except Exception:
            pass
    return results


def _r0106_eq_iff_atom_le_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanAlgebra.eq_iff_atom_le_iff
    # x = y ↔ ∀ a, IsAtom a → (a ≤ x ↔ a ≤ y)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("y"), OOp("implies", (OOp("forall", (OVar("a"), OVar("IsAtom"), OVar("a"),)), OOp("<=", (OVar("a"), OOp("<=", (OOp("iff", (OVar("x"), OVar("a"))), OVar("y")))))))))
            results.append((rhs, "Mathlib: BooleanAlgebra_eq_iff_atom_le_iff"))
    except Exception:
        pass
    return results


def _r0107_sup_eq_bor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.sup_eq_bor
    # (· ⊔ ·) = or
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OVar("or")
            results.append((rhs, "Mathlib: Bool_sup_eq_bor"))
        except Exception:
            pass
    return results


def _r0108_inf_eq_band(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.inf_eq_band
    # (· ⊓ ·) = and
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 2)
    if args is not None:
        try:
            rhs = OVar("and")
            results.append((rhs, "Mathlib: Bool_inf_eq_band"))
        except Exception:
            pass
    return results


def _r0109_compl_eq_bnot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.compl_eq_bnot
    # Compl.compl = not
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Compl_compl")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("not")
            results.append((rhs, "Mathlib: Bool_compl_eq_bnot"))
    except Exception:
        pass
    return results


def _r0110_atomistic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsCompactlyGenerated.BooleanGenerators.atomistic
    # ∃ T ⊆ S, a = sSup T
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("sSup", (OVar("T"),))
            results.append((rhs, "Mathlib: IsCompactlyGenerated_BooleanGenerators_atomistic"))
        except Exception:
            pass
    return results


def _r0111_sSup_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsCompactlyGenerated.BooleanGenerators.sSup_inter
    # sSup (T₁ ∩ T₂) = (sSup T₁) ⊓ (sSup T₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sSup", 1)
    if args is not None:
        try:
            rhs = OOp("sSup_T_1", (OVar("_unknown"), OOp("sSup", (OVar("T_2"),)),))
            results.append((rhs, "Mathlib: IsCompactlyGenerated_BooleanGenerators_sSup_inter"))
        except Exception:
            pass
    return results


def _r0112_eq_atoms_of_sSup_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsCompactlyGenerated.BooleanGenerators.eq_atoms_of_sSup_eq_top
    # S = {a : α | IsAtom a}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a_colon_a_pipe_IsAtom_a")
            results.append((rhs, "Mathlib: IsCompactlyGenerated_BooleanGenerators_eq_atoms_of_sSup_eq_top"))
    except Exception:
        pass
    return results


def _r0113_coe_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_inj
    # (L : Set α) = M ↔ L = M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("M"), OVar("L"))), OVar("M")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_inj"))
        except Exception:
            pass
    return results


def _r0114_coe_copy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_copy
    # L.copy s hs = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_copy", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_copy"))
        except Exception:
            pass
    return results


def _r0115_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.ext
    # (∀ a, a ∈ L ↔ a ∈ M) → L = M
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("M")
            results.append((rhs, "Mathlib: BooleanSubalgebra_ext"))
    except Exception:
        pass
    return results


def _r0116_val_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.val_bot
    # (⊥ : L) = (⊥ : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot", 2)
    if args is not None:
        try:
            rhs = OOp("bot", (args[0], OVar("a"),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_val_bot"))
        except Exception:
            pass
    return results


def _r0117_coe_subtype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_subtype
    # L.subtype = ((↑) : L → α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("L_subtype")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("implies", (OOp("_unknown", (OVar("colon"), OVar("L"),)), OVar("a")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_subtype"))
    except Exception:
        pass
    return results


def _r0118_coe_inclusion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_inclusion
    # inclusion h = Set.inclusion h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inclusion", 1)
    if args is not None:
        try:
            rhs = OOp("Set_inclusion", (args[0],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_inclusion"))
        except Exception:
            pass
    return results


def _r0119_inclusion_rfl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.inclusion_rfl
    # inclusion le_rfl = .id L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inclusion", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("L"),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_inclusion_rfl"))
        except Exception:
            pass
    return results


def _r0120_coe_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_top
    # (⊤ : BooleanSubalgebra α) = (univ : Set α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top", 3)
    if args is not None:
        try:
            rhs = OOp("univ_set", (args[0], OVar("Set"), args[2],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_top"))
        except Exception:
            pass
    return results


def _r0121_coe_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_comap
    # L.comap f = f ⁻¹' L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_comap", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("inv_prime"), OVar("L"),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_comap"))
        except Exception:
            pass
    return results


def _r0122_coe_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.coe_map
    # (L.map f : Set β) = f '' L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_map", 4)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("prime_prime"), OVar("L"),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_coe_map"))
        except Exception:
            pass
    return results


def _r0123_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.map_id
    # L.map (.id α) = L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_map", 1)
    if args is not None:
        try:
            rhs = OVar("L")
            results.append((rhs, "Mathlib: BooleanSubalgebra_map_id"))
        except Exception:
            pass
    return results


def _r0124_map_equiv_eq_comap_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.map_equiv_eq_comap_symm
    # L.map f = L.comap (f.symm : BoundedLatticeHom β α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_map", 1)
    if args is not None:
        try:
            rhs = OOp("L_comap", (OOp("f_symm", (OVar("colon"), OVar("BoundedLatticeHom"), OVar("b"), OVar("a"),)),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_map_equiv_eq_comap_symm"))
        except Exception:
            pass
    return results


def _r0125_comap_equiv_eq_map_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.comap_equiv_eq_map_symm
    # L.comap f = L.map (f.symm : BoundedLatticeHom α β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_comap", 1)
    if args is not None:
        try:
            rhs = OOp("L_map", (OOp("f_symm", (OVar("colon"), OVar("BoundedLatticeHom"), OVar("a"), OVar("b"),)),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_comap_equiv_eq_map_symm"))
        except Exception:
            pass
    return results


def _r0126_map_symm_eq_iff_eq_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.map_symm_eq_iff_eq_map
    # L.map ↑e.symm = M ↔ L = M.map ↑e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "L_map", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("M"), OVar("L"))), OOp("M_map", (OVar("e"),))))
            results.append((rhs, "Mathlib: BooleanSubalgebra_map_symm_eq_iff_eq_map"))
        except Exception:
            pass
    return results


def _r0127_map_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.map_bot
    # (⊥ : BooleanSubalgebra α).map f = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_BooleanSubalgebra_a_map", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: BooleanSubalgebra_map_bot"))
        except Exception:
            pass
    return results


def _r0128_map_iSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.map_iSup
    # (⨆ i, L i).map f = ⨆ i, (L i).map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_L_i_map", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("L_i_map"), args[0],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_map_iSup"))
        except Exception:
            pass
    return results


def _r0129_comap_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.comap_top
    # (⊤ : BooleanSubalgebra β).comap f = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_BooleanSubalgebra_b_comap", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: BooleanSubalgebra_comap_top"))
        except Exception:
            pass
    return results


def _r0130_comap_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.comap_iInf
    # (⨅ i, L i).comap f = ⨅ i, (L i).comap f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_L_i_comap", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("L_i_comap"), args[0],))
            results.append((rhs, "Mathlib: BooleanSubalgebra_comap_iInf"))
        except Exception:
            pass
    return results


def _r0131_map_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.map_inf
    # map f (L ⊓ M) = map f L ⊓ map f M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("map", (args[0], OVar("L"), OVar("_unknown"), OVar("map"), args[0], OVar("M"),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_map_inf"))
        except Exception:
            pass
    return results


def _r0132_map_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.map_top
    # BooleanSubalgebra.map f ⊤ = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BooleanSubalgebra_map", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: BooleanSubalgebra_map_top"))
        except Exception:
            pass
    return results


def _r0133_closure_latticeClosure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.closure_latticeClosure
    # closure (latticeClosure s) = closure s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("closure", (OVar("s"),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_closure_latticeClosure"))
        except Exception:
            pass
    return results


def _r0134_mem_closure_iff_sup_sdiff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_closure_iff_sup_sdiff
    # a ∈ closure s ↔ ∃ t : Finset (s × s), a = t.sup fun x ↦ x.1.1 \\ x.2.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("t_sup", (OVar("fun"), OVar("x"), OVar("_unknown"), OVar("x_1_1"), OVar("bsl"), OVar("x_2_1"),))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_closure_iff_sup_sdiff"))
        except Exception:
            pass
    return results


def _r0135_compl_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.compl_lift
    # (lift a)ᶜ = comp a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("lift_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("a"),))
            results.append((rhs, "Mathlib: Booleanisation_compl_lift"))
    except Exception:
        pass
    return results


def _r0136_coe_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.coe_of
    # (BoolAlg.of X : Type u) = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BoolAlg_of", 4)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: BoolAlg_coe_of"))
        except Exception:
            pass
    return results


def _r0137_hom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.hom_id
    # (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_X_colon_X_X_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("BoundedLatticeHom_id", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: BoolAlg_hom_id"))
    except Exception:
        pass
    return results


def _r0138_hom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.hom_comp
    # (f ≫ g).hom = g.hom.comp f.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g_hom_comp", (OVar("f_hom"),))
            results.append((rhs, "Mathlib: BoolAlg_hom_comp"))
    except Exception:
        pass
    return results


def _r0139_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.comp_apply
    # (f ≫ g) x = g (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: BoolAlg_comp_apply"))
        except Exception:
            pass
    return results


def _r0140_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.hom_ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: BoolAlg_hom_ext"))
    except Exception:
        pass
    return results


def _r0141_hom_ofHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.hom_ofHom
    # (ofHom f).hom = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofHom_f_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: BoolAlg_hom_ofHom"))
    except Exception:
        pass
    return results


def _r0142_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: BoolAlg_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0143_ofHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.ofHom_apply
    # (ofHom f) x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom_f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: BoolAlg_ofHom_apply"))
        except Exception:
            pass
    return results


def _r0144_inv_hom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.inv_hom_apply
    # e.inv (e.hom x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_inv", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: BoolAlg_inv_hom_apply"))
        except Exception:
            pass
    return results


def _r0145_hom_inv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.hom_inv_apply
    # e.hom (e.inv s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_hom", 1)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: BoolAlg_hom_inv_apply"))
        except Exception:
            pass
    return results


def _r0146_coe_toBddDistLat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BoolAlg.coe_toBddDistLat
    # ↥X.toBddDistLat = ↥X
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("X_toBddDistLat")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("X")
            results.append((rhs, "Mathlib: BoolAlg_coe_toBddDistLat"))
    except Exception:
        pass
    return results


def _r0147_coe_xor_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.coe_xor_iff
    # xor a b ↔ Xor' (a = true) (b = true)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "xor", 2)
    if args is not None:
        try:
            rhs = OOp("Xor_prime", (OOp("==", (args[0], OLit(True))), OOp("==", (args[1], OLit(True))),))
            results.append((rhs, "Mathlib: Bool_coe_xor_iff"))
        except Exception:
            pass
    return results


def _r0148_le_iff_atom_le_imp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanAlgebra.le_iff_atom_le_imp
    # x ≤ y ↔ ∀ a, IsAtom a → a ≤ x → a ≤ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("implies", (OOp("forall", (OVar("a"), OVar("IsAtom"), OVar("a"),)), OVar("a"))), OOp("<=", (OOp("implies", (args[0], OVar("a"))), args[1]))))
            results.append((rhs, "Mathlib: BooleanAlgebra_le_iff_atom_le_imp"))
        except Exception:
            pass
    return results


def _r0149_sSup_le_sSup_iff_of_atoms(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsCompactlyGenerated.BooleanGenerators.sSup_le_sSup_iff_of_atoms
    # sSup X ≤ sSup Y ↔ X ⊆ Y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("subset", (OVar("X"), OVar("Y")))
            results.append((rhs, "Mathlib: IsCompactlyGenerated_BooleanGenerators_sSup_le_sSup_iff_of_atoms"))
        except Exception:
            pass
    return results


def _r0150_mem_carrier(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_carrier
    # a ∈ L.carrier ↔ a ∈ L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("L")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_carrier"))
        except Exception:
            pass
    return results


def _r0151_mem_toSublattice(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_toSublattice
    # a ∈ L.toSublattice ↔ a ∈ L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("L")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_toSublattice"))
        except Exception:
            pass
    return results


def _r0152_apply_mem_map_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.apply_mem_map_iff
    # f a ∈ L.map f ↔ a ∈ L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("a"), OVar("L")))
            results.append((rhs, "Mathlib: BooleanSubalgebra_apply_mem_map_iff"))
        except Exception:
            pass
    return results


def _r0153_map_le_iff_le_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.map_le_iff_le_comap
    # L.map f ≤ M ↔ L ≤ M.comap f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("L"), OOp("M_comap", (OVar("f"),))))
            results.append((rhs, "Mathlib: BooleanSubalgebra_map_le_iff_le_comap"))
        except Exception:
            pass
    return results


def _r0154_mem_closure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.mem_closure
    # x ∈ closure s ↔ ∀ ⦃L : BooleanSubalgebra α⦄, s ⊆ L → x ∈ L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("subset", (OOp("forall", (OVar("L"), OVar("colon"), OVar("BooleanSubalgebra"), OVar("a"), OVar("s"),)), OVar("L"))), OOp("in", (args[0], OVar("L")))))
            results.append((rhs, "Mathlib: BooleanSubalgebra_mem_closure"))
        except Exception:
            pass
    return results


def _r0155_closure_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: BooleanSubalgebra.closure_le
    # closure s ≤ L ↔ s ⊆ L
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("subset", (OVar("s"), args[1]))
            results.append((rhs, "Mathlib: BooleanSubalgebra_closure_le"))
        except Exception:
            pass
    return results


def _r0156_lift_le_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Booleanisation.lift_le_lift
    # lift a ≤ lift b ↔ a ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("a"), OVar("b")))
            results.append((rhs, "Mathlib: Booleanisation_lift_le_lift"))
        except Exception:
            pass
    return results


def _r0157_wcovBy_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Bool.wcovBy_iff
    # ∀ {a b : Bool}, a ⩿ b ↔ a ≤ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("a"), args[1]))
            results.append((rhs, "Mathlib: Bool_wcovBy_iff"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_bool rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "+", "-", "<", "<=", "==", "BoolAlg_of", "BooleanSubalgebra_map", "BoundedLatticeHom_id", "False", "Hom_hom", "L", "L_M_comap", "L_M_map", "L_comap", "L_comap_g_comap", "L_copy", "L_map", "L_map_f_map", "L_subtype", "M_subtype_comp", "S", "True", "_1_X_colon_X_X", "_unknown", "a", "a_b", "a_ha", "b", "bot", "bot_bot_mem", "bot_colon_BooleanSubalgebra_a_map", "closure", "comp", "decide", "e_hom", "e_inv", "exists", "f", "f_g", "forget_BoolAlg_map", "g_comp", "i_L_i_comap", "i_L_i_map", "id", "iff", "in", "inclusion", "inter", "latticeClosure",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_bool axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_bool rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_mul_one_add_self(term, ctx))
    results.extend(_r0001_range_eq(term, ctx))
    results.extend(_r0002_compl_singleton(term, ctx))
    results.extend(_r0003_coe_mk(term, ctx))
    results.extend(_r0004_copy_eq(term, ctx))
    results.extend(_r0005_val_top(term, ctx))
    results.extend(_r0006_val_sup(term, ctx))
    results.extend(_r0007_val_inf(term, ctx))
    results.extend(_r0008_val_compl(term, ctx))
    results.extend(_r0009_val_sdiff(term, ctx))
    results.extend(_r0010_val_himp(term, ctx))
    results.extend(_r0011_mk_bot(term, ctx))
    results.extend(_r0012_mk_top(term, ctx))
    results.extend(_r0013_mk_sup_mk(term, ctx))
    results.extend(_r0014_mk_inf_mk(term, ctx))
    results.extend(_r0015_compl_mk(term, ctx))
    results.extend(_r0016_mk_sdiff_mk(term, ctx))
    results.extend(_r0017_mk_himp_mk(term, ctx))
    results.extend(_r0018_subtype_apply(term, ctx))
    results.extend(_r0019_inclusion_apply(term, ctx))
    results.extend(_r0020_subtype_comp_inclusion(term, ctx))
    results.extend(_r0021_coe_bot(term, ctx))
    results.extend(_r0022_coe_inf(term, ctx))
    results.extend(_r0023_coe_sInf(term, ctx))
    results.extend(_r0024_coe_iInf(term, ctx))
    results.extend(_r0025_coe_eq_univ(term, ctx))
    results.extend(_r0026_mem_bot(term, ctx))
    results.extend(_r0027_comap_id(term, ctx))
    results.extend(_r0028_comap_comap(term, ctx))
    results.extend(_r0029_mem_map(term, ctx))
    results.extend(_r0030_map_map(term, ctx))
    results.extend(_r0031_map_sup(term, ctx))
    results.extend(_r0032_comap_inf(term, ctx))
    results.extend(_r0033_compl_comp(term, ctx))
    results.extend(_r0034_lift_sup_lift(term, ctx))
    results.extend(_r0035_lift_sup_comp(term, ctx))
    results.extend(_r0036_comp_sup_lift(term, ctx))
    results.extend(_r0037_comp_sup_comp(term, ctx))
    results.extend(_r0038_lift_inf_lift(term, ctx))
    results.extend(_r0039_lift_inf_comp(term, ctx))
    results.extend(_r0040_comp_inf_lift(term, ctx))
    results.extend(_r0041_comp_inf_comp(term, ctx))
    results.extend(_r0042_lift_bot(term, ctx))
    results.extend(_r0043_comp_bot(term, ctx))
    results.extend(_r0044_lift_sdiff_lift(term, ctx))
    results.extend(_r0045_lift_sdiff_comp(term, ctx))
    results.extend(_r0046_comp_sdiff_lift(term, ctx))
    results.extend(_r0047_comp_sdiff_comp(term, ctx))
    results.extend(_r0048_forget_map(term, ctx))
    results.extend(_r0049_ext(term, ctx))
    results.extend(_r0050_id_apply(term, ctx))
    results.extend(_r0051_ofHom_id(term, ctx))
    results.extend(_r0052_ofHom_comp(term, ctx))
    results.extend(_r0053_symmDiff_eq_xor(term, ctx))
    results.extend(_r0054_compl_mem_iff(term, ctx))
    results.extend(_r0055_mem_mk(term, ctx))
    results.extend(_r0056_mk_le_mk(term, ctx))
    results.extend(_r0057_mk_lt_mk(term, ctx))
    results.extend(_r0058_mem_inf(term, ctx))
    results.extend(_r0059_mem_sInf(term, ctx))
    results.extend(_r0060_mem_iInf(term, ctx))
    results.extend(_r0061_mem_comap(term, ctx))
    results.extend(_r0062_mem_map_equiv(term, ctx))
    results.extend(_r0063_comp_le_comp(term, ctx))
    results.extend(_r0064_lift_le_comp(term, ctx))
    results.extend(_r0065_lift_lt_lift(term, ctx))
    results.extend(_r0066_comp_lt_comp(term, ctx))
    results.extend(_r0067_lift_lt_comp(term, ctx))
    results.extend(_r0068_covBy_iff(term, ctx))
    results.extend(_r0069_coe_of(term, ctx))
    results.extend(_r0070_hom_ext(term, ctx))
    results.extend(_r0071_mul_self(term, ctx))
    results.extend(_r0072_add_self(term, ctx))
    results.extend(_r0073_neg_eq(term, ctx))
    results.extend(_r0074_mul_add_mul(term, ctx))
    results.extend(_r0075_sub_eq_add(term, ctx))
    results.extend(_r0076_sup_comm(term, ctx))
    results.extend(_r0077_inf_comm(term, ctx))
    results.extend(_r0078_sup_assoc(term, ctx))
    results.extend(_r0079_inf_assoc(term, ctx))
    results.extend(_r0080_sup_inf_self(term, ctx))
    results.extend(_r0081_inf_sup_self(term, ctx))
    results.extend(_r0082_le_sup_inf_aux(term, ctx))
    results.extend(_r0083_le_sup_inf(term, ctx))
    results.extend(_r0084_eq_false_eq_not_eq_true(term, ctx))
    results.extend(_r0085_eq_true_eq_not_eq_false(term, ctx))
    results.extend(_r0086_eq_false_of_not_eq_true(term, ctx))
    results.extend(_r0087_eq_true_of_not_eq_false(term, ctx))
    results.extend(_r0088_and_eq_true_eq_eq_true_and_eq_true(term, ctx))
    results.extend(_r0089_or_eq_true_eq_eq_true_or_eq_true(term, ctx))
    results.extend(_r0090_not_eq_true_eq_eq_false(term, ctx))
    results.extend(_r0091_and_eq_false_eq_eq_false_or_eq_false(term, ctx))
    results.extend(_r0092_or_eq_false_eq_eq_false_and_eq_false(term, ctx))
    results.extend(_r0093_not_eq_false_eq_eq_true(term, ctx))
    results.extend(_r0094_coe_false(term, ctx))
    results.extend(_r0095_coe_true(term, ctx))
    results.extend(_r0096_coe_sort_false(term, ctx))
    results.extend(_r0097_coe_sort_true(term, ctx))
    results.extend(_r0098_decide_iff(term, ctx))
    results.extend(_r0099_bool_iff_false(term, ctx))
    results.extend(_r0100_bool_eq_false(term, ctx))
    results.extend(_r0101_decide_false_iff(term, ctx))
    results.extend(_r0102_decide_false(term, ctx))
    results.extend(_r0103_of_decide_false(term, ctx))
    results.extend(_r0104_decide_congr(term, ctx))
    results.extend(_r0105_univ_eq(term, ctx))
    results.extend(_r0106_eq_iff_atom_le_iff(term, ctx))
    results.extend(_r0107_sup_eq_bor(term, ctx))
    results.extend(_r0108_inf_eq_band(term, ctx))
    results.extend(_r0109_compl_eq_bnot(term, ctx))
    results.extend(_r0110_atomistic(term, ctx))
    results.extend(_r0111_sSup_inter(term, ctx))
    results.extend(_r0112_eq_atoms_of_sSup_eq_top(term, ctx))
    results.extend(_r0113_coe_inj(term, ctx))
    results.extend(_r0114_coe_copy(term, ctx))
    results.extend(_r0115_ext(term, ctx))
    results.extend(_r0116_val_bot(term, ctx))
    results.extend(_r0117_coe_subtype(term, ctx))
    results.extend(_r0118_coe_inclusion(term, ctx))
    results.extend(_r0119_inclusion_rfl(term, ctx))
    results.extend(_r0120_coe_top(term, ctx))
    results.extend(_r0121_coe_comap(term, ctx))
    results.extend(_r0122_coe_map(term, ctx))
    results.extend(_r0123_map_id(term, ctx))
    results.extend(_r0124_map_equiv_eq_comap_symm(term, ctx))
    results.extend(_r0125_comap_equiv_eq_map_symm(term, ctx))
    results.extend(_r0126_map_symm_eq_iff_eq_map(term, ctx))
    results.extend(_r0127_map_bot(term, ctx))
    results.extend(_r0128_map_iSup(term, ctx))
    results.extend(_r0129_comap_top(term, ctx))
    results.extend(_r0130_comap_iInf(term, ctx))
    results.extend(_r0131_map_inf(term, ctx))
    results.extend(_r0132_map_top(term, ctx))
    results.extend(_r0133_closure_latticeClosure(term, ctx))
    results.extend(_r0134_mem_closure_iff_sup_sdiff(term, ctx))
    results.extend(_r0135_compl_lift(term, ctx))
    results.extend(_r0136_coe_of(term, ctx))
    results.extend(_r0137_hom_id(term, ctx))
    results.extend(_r0138_hom_comp(term, ctx))
    results.extend(_r0139_comp_apply(term, ctx))
    results.extend(_r0140_hom_ext(term, ctx))
    results.extend(_r0141_hom_ofHom(term, ctx))
    results.extend(_r0142_ofHom_hom(term, ctx))
    results.extend(_r0143_ofHom_apply(term, ctx))
    results.extend(_r0144_inv_hom_apply(term, ctx))
    results.extend(_r0145_hom_inv_apply(term, ctx))
    results.extend(_r0146_coe_toBddDistLat(term, ctx))
    results.extend(_r0147_coe_xor_iff(term, ctx))
    results.extend(_r0148_le_iff_atom_le_imp(term, ctx))
    results.extend(_r0149_sSup_le_sSup_iff_of_atoms(term, ctx))
    results.extend(_r0150_mem_carrier(term, ctx))
    results.extend(_r0151_mem_toSublattice(term, ctx))
    results.extend(_r0152_apply_mem_map_iff(term, ctx))
    results.extend(_r0153_map_le_iff_le_comap(term, ctx))
    results.extend(_r0154_mem_closure(term, ctx))
    results.extend(_r0155_closure_le(term, ctx))
    results.extend(_r0156_lift_le_lift(term, ctx))
    results.extend(_r0157_wcovBy_iff(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_bool rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("BooleanRing_add_eq_zero", "_unknown", "Empty proposition"),
    ("Bool_true_eq_false_eq_False", "not_true_eq_false", "Not an equality or iff proposition"),
    ("Bool_false_eq_true_eq_False", "not_false_eq_true", "Not an equality or iff proposition"),
    ("Bool_decide_true", "p_to_decide_p", "Not an equality or iff proposition"),
    ("Bool_of_decide_true", "decide_p_to_p", "Not an equality or iff proposition"),
    ("Bool_not_bijective", "Bijective_not", "Not an equality or iff proposition"),
    ("Bool_not_injective", "Injective_not", "Not an equality or iff proposition"),
    ("Bool_not_surjective", "Surjective_not", "Not an equality or iff proposition"),
    ("Bool_not_leftInverse", "LeftInverse_not_not", "Not an equality or iff proposition"),
    ("Bool_not_rightInverse", "RightInverse_not_not", "Not an equality or iff proposition"),
    ("Bool_not_hasLeftInverse", "HasLeftInverse_not", "Not an equality or iff proposition"),
    ("Bool_not_hasRightInverse", "HasRightInverse_not", "Not an equality or iff proposition"),
    ("Bool_involutive_not", "Involutive_not", "Not an equality or iff proposition"),
    ("IsCompactlyGenerated_BooleanGenerators_mono", "BooleanGenerators_T", "Not an equality or iff proposition"),
    ("IsCompactlyGenerated_BooleanGenerators_isAtomistic_of_sSup_eq_top", "IsAtomistic_a", "Not an equality or iff proposition"),
    ("IsCompactlyGenerated_BooleanGenerators_mem_of_isAtom_of_le_sSup_atoms", "a_in_S", "Not an equality or iff proposition"),
    ("IsCompactlyGenerated_BooleanGenerators_complementedLattice_of_sSup_eq_top", "ComplementedLattice_a", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_supClosed", "SupClosed_L_colon_Set_a", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_infClosed", "InfClosed_L_colon_Set_a", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_compl_mem", "a_in_L", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_bot_mem", "bot_in_L", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_top_mem", "top_in_L", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_sup_mem", "a_b_in_L", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_inf_mem", "a_b_in_L", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_sdiff_mem", "a_bsl_b_in_L", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_himp_mem", "a_b_in_L", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_subtype_injective", "Injective_lt_pipe_subtype_L", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_inclusion_injective", "Injective_lt_pipe_inclusion_h", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_mem_top", "a_in_top_colon_BooleanSubalgebra_a", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_comap_mono", "Monotone_comap_f", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_mem_map_of_mem", "a_in_L_to_f_a_in_L_map_f", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_apply_coe_mem_map", "f_a_in_L_map_f", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_map_mono", "Monotone_map_f", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_gc_map_comap", "GaloisConnection_map_f_comap_f", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_map_inf_le", "map_f_L_M_le_map_f_L_map_f_M", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_le_comap_sup", "comap_f_L_comap_f_M_le_comap_f_L_M", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_le_comap_iSup", "i_L_i_comap_f_le_i_L_i_comap_f", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_subset_closure", "s_sub_closure_s", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_mem_closure_of_mem", "x_in_closure_s", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_closure_mono", "closure_s_le_closure_t", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_latticeClosure_subset_closure", "latticeClosure_s_sub_closure_s", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_closure_bot_sup_induction", "p_x_hx", "Not an equality or iff proposition"),
    ("BooleanSubalgebra_closure_sdiff_sup_induction", "p_x_hx", "Not an equality or iff proposition"),
    ("Booleanisation_not_comp_le_lift", "not_comp_a_le_lift_b", "Not an equality or iff proposition"),
    ("Booleanisation_not_comp_lt_lift", "not_comp_a_lt_lift_b", "Not an equality or iff proposition"),
    ("Booleanisation_liftLatticeHom_injective", "Injective_liftLatticeHom_a_colon_eq_a", "Not an equality or iff proposition"),
    ("BoolAlg_coe_id", "_1_X_colon_X_to_X_eq_id", "Not an equality or iff proposition"),
    ("BoolAlg_coe_comp", "f_g_colon_X_to_Z_eq_g_comp_f", "Not an equality or iff proposition"),
]
