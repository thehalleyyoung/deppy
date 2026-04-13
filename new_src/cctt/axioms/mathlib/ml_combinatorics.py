"""Mathlib: Combinatorics — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 742 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_combinatorics"
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

def _r0000_vertical_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.vertical_apply
    # l.vertical v x = Sum.elim v (l x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_vertical", 2)
    if args is not None:
        try:
            rhs = OOp("Sum_elim", (args[0], OOp("l", (args[1],)),))
            results.append((rhs, "Mathlib: Combinatorics_Line_vertical_apply"))
        except Exception:
            pass
    return results


def _r0001_compl_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.compl_zero
    # (0 : Matrix V V α).compl = (completeGraph V).adjMatrix α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Matrix_V_V_a_compl")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("completeGraph_V_adjMatrix", (OVar("a"),))
            results.append((rhs, "Mathlib: Matrix_compl_zero"))
    except Exception:
        pass
    return results


def _r0002_adjMatrix_completeGraph_eq_of_one_sub_on(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_completeGraph_eq_of_one_sub_one
    # (completeGraph V).adjMatrix α = of 1 - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completeGraph_V_adjMatrix", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("of", (OLit(1),)), OLit(1)))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_completeGraph_eq_of_one_sub_one"))
        except Exception:
            pass
    return results


def _r0003_adjMatrix_mul_self_apply_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_mul_self_apply_self
    # (G.adjMatrix α * G.adjMatrix α) i i = degree G i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_adjMatrix_a_star_G_adjMatrix_a", 2)
    if args is not None:
        try:
            rhs = OOp("degree", (OVar("G"), args[1],))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_mul_self_apply_self"))
        except Exception:
            pass
    return results


def _r0004_completeGraph_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.completeGraph_eq_top
    # completeGraph V = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completeGraph", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: SimpleGraph_completeGraph_eq_top"))
        except Exception:
            pass
    return results


def _r0005_emptyGraph_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.emptyGraph_eq_bot
    # emptyGraph V = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "emptyGraph", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: SimpleGraph_emptyGraph_eq_bot"))
        except Exception:
            pass
    return results


def _r0006_mulCayley_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.mulCayley_union
    # mulCayley (s₁ ∪ s₂) = mulCayley s₁ ⊔ mulCayley s₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulCayley", 1)
    if args is not None:
        try:
            rhs = OOp("mulCayley", (OVar("s_1"), OVar("_unknown"), OVar("mulCayley"), OVar("s_2"),))
            results.append((rhs, "Mathlib: SimpleGraph_mulCayley_union"))
        except Exception:
            pass
    return results


def _r0007_map_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.map_comp
    # (C.map φ).map ψ = C.map (ψ.comp φ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "C_map_phi_map", 1)
    if args is not None:
        try:
            rhs = OOp("C_map", (OOp("psi_comp", (OVar("phi"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_map_comp"))
        except Exception:
            pass
    return results


def _r0008_spanningCoe_toSubgraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.spanningCoe_toSubgraph
    # C.toSubgraph.spanningCoe = C.toSimpleGraph.spanningCoe
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("C_toSubgraph_spanningCoe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("C_toSimpleGraph_spanningCoe")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_spanningCoe_toSubgraph"))
    except Exception:
        pass
    return results


def _r0009_toSubgraph_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.toSubgraph_append
    # (p.append q).toSubgraph = p.toSubgraph ⊔ q.toSubgraph
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_append_q_toSubgraph")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_toSubgraph", (OVar("_unknown"), OVar("q_toSubgraph"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_toSubgraph_append"))
    except Exception:
        pass
    return results


def _r0010_toSubgraph_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.toSubgraph_reverse
    # p.reverse.toSubgraph = p.toSubgraph
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_reverse_toSubgraph")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_toSubgraph")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_toSubgraph_reverse"))
    except Exception:
        pass
    return results


def _r0011_toHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.toHom_apply
    # ⇑f.toHom a = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toHom", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: SimpleGraph_Copy_toHom_apply"))
        except Exception:
            pass
    return results


def _r0012_coe_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.coe_mk
    # ⇑(.mk f hf : Copy A B) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mk_f_hf_colon_Copy_A_B")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: SimpleGraph_Copy_coe_mk"))
    except Exception:
        pass
    return results


def _r0013_coe_ofLE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.coe_ofLE
    # ⇑(ofLE G₁ G₂ h) = _root_.id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofLE_G_1_G_2_h")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("root_id")
            results.append((rhs, "Mathlib: SimpleGraph_Copy_coe_ofLE"))
    except Exception:
        pass
    return results


def _r0014_ofLE_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.ofLE_refl
    # ofLE G G le_rfl = id G
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLE", 3)
    if args is not None:
        try:
            rhs = OOp("id", (args[1],))
            results.append((rhs, "Mathlib: SimpleGraph_Copy_ofLE_refl"))
        except Exception:
            pass
    return results


def _r0015_ofLE_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.ofLE_comp
    # (ofLE _ _ h₂₃).comp (ofLE _ _ h₁₂) = ofLE _ _ (h₁₂.trans h₂₃)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLE_h_2_3_comp", 1)
    if args is not None:
        try:
            rhs = OOp("ofLE", (OVar("_unknown"), OVar("_unknown"), OOp("h_1_2_trans", (OVar("h_2_3"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_Copy_ofLE_comp"))
        except Exception:
            pass
    return results


def _r0016_symm_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Dart.symm_mk
    # (Dart.mk p h).symm = Dart.mk p.swap h.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Dart_mk_p_h_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Dart_mk", (OVar("p_swap"), OVar("h_symm"),))
            results.append((rhs, "Mathlib: SimpleGraph_Dart_symm_mk"))
    except Exception:
        pass
    return results


def _r0017_edge_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Dart.edge_symm
    # d.symm.edge = d.edge
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("d_symm_edge")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("d_edge")
            results.append((rhs, "Mathlib: SimpleGraph_Dart_edge_symm"))
    except Exception:
        pass
    return results


def _r0018_edge_comp_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Dart.edge_comp_symm
    # Dart.edge ∘ Dart.symm = (Dart.edge : G.Dart → Sym2 V)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("Dart_edge", (OVar("colon"), OVar("G_Dart"),)), OOp("Sym2", (OVar("V"),))))
            results.append((rhs, "Mathlib: SimpleGraph_Dart_edge_comp_symm"))
        except Exception:
            pass
    return results


def _r0019_symm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Dart.symm_symm
    # d.symm.symm = d
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("d_symm_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("d")
            results.append((rhs, "Mathlib: SimpleGraph_Dart_symm_symm"))
    except Exception:
        pass
    return results


def _r0020_deleteEdges_edgeSet(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.deleteEdges_edgeSet
    # G.deleteEdges G'.edgeSet = G \\ G'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_deleteEdges", 1)
    if args is not None:
        try:
            rhs = OOp("G", (OVar("bsl"), OVar("G_prime"),))
            results.append((rhs, "Mathlib: SimpleGraph_deleteEdges_edgeSet"))
        except Exception:
            pass
    return results


def _r0021_deleteEdges_deleteEdges(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.deleteEdges_deleteEdges
    # (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_deleteEdges_s_deleteEdges", 1)
    if args is not None:
        try:
            rhs = OOp("G_deleteEdges", (OOp("union", (OVar("s"), args[0])),))
            results.append((rhs, "Mathlib: SimpleGraph_deleteEdges_deleteEdges"))
        except Exception:
            pass
    return results


def _r0022_deleteEdges_eq_inter_edgeSet(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.deleteEdges_eq_inter_edgeSet
    # G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_deleteEdges", 1)
    if args is not None:
        try:
            rhs = OOp("G_deleteEdges", (OOp("inter", (args[0], OVar("G_edgeSet"))),))
            results.append((rhs, "Mathlib: SimpleGraph_deleteEdges_eq_inter_edgeSet"))
        except Exception:
            pass
    return results


def _r0023_deleteEdges_sdiff_eq_of_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.deleteEdges_sdiff_eq_of_le
    # G.deleteEdges (G.edgeSet \\ H.edgeSet) = H
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_deleteEdges", 1)
    if args is not None:
        try:
            rhs = OVar("H")
            results.append((rhs, "Mathlib: SimpleGraph_deleteEdges_sdiff_eq_of_le"))
        except Exception:
            pass
    return results


def _r0024_edgeFinset_deleteEdges(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeFinset_deleteEdges
    # (G.deleteEdges s).edgeFinset = G.edgeFinset \\ s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_deleteEdges_s_edgeFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_edgeFinset", (OVar("bsl"), OVar("s"),))
            results.append((rhs, "Mathlib: SimpleGraph_edgeFinset_deleteEdges"))
    except Exception:
        pass
    return results


def _r0025_deleteEdges_fromEdgeSet(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.deleteEdges_fromEdgeSet
    # (fromEdgeSet s).deleteEdges t = fromEdgeSet (s \\ t)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fromEdgeSet_s_deleteEdges", 1)
    if args is not None:
        try:
            rhs = OOp("fromEdgeSet", (OOp("s", (OVar("bsl"), args[0],)),))
            results.append((rhs, "Mathlib: SimpleGraph_deleteEdges_fromEdgeSet"))
        except Exception:
            pass
    return results


def _r0026_deleteEdges_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.deleteEdges_eq_bot
    # G.deleteEdges s = ⊥ ↔ G.edgeSet ⊆ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_deleteEdges", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("bot"), OOp("subset", (OVar("G_edgeSet"), args[0]))))
            results.append((rhs, "Mathlib: SimpleGraph_deleteEdges_eq_bot"))
        except Exception:
            pass
    return results


def _r0027_eccent_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.eccent_top
    # (⊤ : SimpleGraph α).eccent u = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_SimpleGraph_a_eccent", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: SimpleGraph_eccent_top"))
        except Exception:
            pass
    return results


def _r0028_get_pullback(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.EdgeLabeling.get_pullback
    # (C.pullback f).get x y h = C.get (f x) (f y) (by simpa)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "C_pullback_f_get", 3)
    if args is not None:
        try:
            rhs = OOp("C_get", (OOp("f", (args[0],)), OOp("f", (args[1],)), OOp("by", (OVar("simpa"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_EdgeLabeling_get_pullback"))
        except Exception:
            pass
    return results


def _r0029_compRight_get(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.EdgeLabeling.compRight_get
    # (C.compRight f).get x y h = f (C.get x y h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "C_compRight_f_get", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("C_get", (args[0], args[1], args[2],)),))
            results.append((rhs, "Mathlib: SimpleGraph_EdgeLabeling_compRight_get"))
        except Exception:
            pass
    return results


def _r0030_toTopEdgeLabeling_labelGraph_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.toTopEdgeLabeling_labelGraph_compl
    # G.toTopEdgeLabeling.labelGraph 0 = Gᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_toTopEdgeLabeling_labelGraph", 1)
    if args is not None:
        try:
            rhs = OVar("G")
            results.append((rhs, "Mathlib: SimpleGraph_toTopEdgeLabeling_labelGraph_compl"))
        except Exception:
            pass
    return results


def _r0031_labelGraph_toTopEdgeLabeling(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.TopEdgeLabeling.labelGraph_toTopEdgeLabeling
    # (C.labelGraph 1).toTopEdgeLabeling = C
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("C_labelGraph_1_toTopEdgeLabeling")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("C")
            results.append((rhs, "Mathlib: SimpleGraph_TopEdgeLabeling_labelGraph_toTopEdgeLabeling"))
    except Exception:
        pass
    return results


def _r0032_exists_eq_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ComponentCompl.exists_eq_mk
    # ∃ (v : _) (h : v ∉ K), G.componentComplMk h = C
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 4)
    if args is not None:
        try:
            rhs = OVar("C")
            results.append((rhs, "Mathlib: SimpleGraph_ComponentCompl_exists_eq_mk"))
        except Exception:
            pass
    return results


def _r0033_turanGraph_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.turanGraph_eq_top
    # turanGraph n r = ⊤ ↔ r = 0 ∨ n ≤ r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "turanGraph", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[1])), OOp("<=", (OOp("or", (OLit(0), args[0])), args[1]))))
            results.append((rhs, "Mathlib: SimpleGraph_turanGraph_eq_top"))
        except Exception:
            pass
    return results


def _r0034_edgeFinset_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeFinset_sup
    # (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset ∪ G₂.edgeFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_1_G_2_edgeFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("G_1_edgeFinset"), OVar("G_2_edgeFinset")))
            results.append((rhs, "Mathlib: SimpleGraph_edgeFinset_sup"))
    except Exception:
        pass
    return results


def _r0035_edgeFinset_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeFinset_inf
    # (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset ∩ G₂.edgeFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_1_G_2_edgeFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OVar("G_1_edgeFinset"), OVar("G_2_edgeFinset")))
            results.append((rhs, "Mathlib: SimpleGraph_edgeFinset_inf"))
    except Exception:
        pass
    return results


def _r0036_edgeFinset_sdiff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeFinset_sdiff
    # (G₁ \\ G₂).edgeFinset = G₁.edgeFinset \\ G₂.edgeFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_1_bsl_G_2_edgeFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_1_edgeFinset", (OVar("bsl"), OVar("G_2_edgeFinset"),))
            results.append((rhs, "Mathlib: SimpleGraph_edgeFinset_sdiff"))
    except Exception:
        pass
    return results


def _r0037_edgeFinset_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeFinset_eq_empty
    # G.edgeFinset = ∅ ↔ G = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_edgeFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("G"))), OVar("bot")))
            results.append((rhs, "Mathlib: SimpleGraph_edgeFinset_eq_empty"))
    except Exception:
        pass
    return results


def _r0038_edgeFinset_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeFinset_card
    # #G.edgeFinset = Fintype.card G.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_G_edgeFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Fintype_card", (OVar("G_edgeSet"),))
            results.append((rhs, "Mathlib: SimpleGraph_edgeFinset_card"))
    except Exception:
        pass
    return results


def _r0039_edgeSet_univ_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeSet_univ_card
    # #(univ : Finset G.edgeSet) = #G.edgeFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_univ_colon_Finset_G_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_G_edgeFinset")
            results.append((rhs, "Mathlib: SimpleGraph_edgeSet_univ_card"))
    except Exception:
        pass
    return results


def _r0040_coe_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Finsubgraph.coe_sup
    # ↑(G₁ ⊔ G₂) = (G₁ ⊔ G₂ : G.Subgraph)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_1_G_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_1", (OVar("_unknown"), OVar("G_2"), OVar("colon"), OVar("G_Subgraph"),))
            results.append((rhs, "Mathlib: SimpleGraph_Finsubgraph_coe_sup"))
    except Exception:
        pass
    return results


def _r0041_coe_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Finsubgraph.coe_inf
    # ↑(G₁ ⊓ G₂) = (G₁ ⊓ G₂ : G.Subgraph)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_1_G_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_1", (OVar("_unknown"), OVar("G_2"), OVar("colon"), OVar("G_Subgraph"),))
            results.append((rhs, "Mathlib: SimpleGraph_Finsubgraph_coe_inf"))
    except Exception:
        pass
    return results


def _r0042_coe_sdiff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Finsubgraph.coe_sdiff
    # ↑(G₁ \\ G₂) = (G₁ \\ G₂ : G.Subgraph)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_1_bsl_G_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_1", (OVar("bsl"), OVar("G_2"), OVar("colon"), OVar("G_Subgraph"),))
            results.append((rhs, "Mathlib: SimpleGraph_Finsubgraph_coe_sdiff"))
    except Exception:
        pass
    return results


def _r0043_coe_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Finsubgraph.coe_compl
    # ↑(G'ᶜ) = (G'ᶜ : G.Subgraph)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_prime")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_prime", (OVar("colon"), OVar("G_Subgraph"),))
            results.append((rhs, "Mathlib: SimpleGraph_Finsubgraph_coe_compl"))
    except Exception:
        pass
    return results


def _r0044_coe_hnot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Finsubgraph.coe_hnot
    # ↑(￢G') = (￢G' : G.Subgraph)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_prime")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_prime", (OVar("colon"), OVar("G_Subgraph"),))
            results.append((rhs, "Mathlib: SimpleGraph_Finsubgraph_coe_hnot"))
    except Exception:
        pass
    return results


def _r0045_coe_himp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Finsubgraph.coe_himp
    # ↑(G₁ ⇨ G₂) = (G₁ ⇨ G₂ : G.Subgraph)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_1_G_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_1", (OVar("_unknown"), OVar("G_2"), OVar("colon"), OVar("G_Subgraph"),))
            results.append((rhs, "Mathlib: SimpleGraph_Finsubgraph_coe_himp"))
    except Exception:
        pass
    return results


def _r0046_coe_sSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Finsubgraph.coe_sSup
    # sSup s = (⨆ G ∈ s, G : G.Subgraph)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sSup", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("G"),)), OOp("s", (OVar("G"), OVar("colon"), OVar("G_Subgraph"),))))
            results.append((rhs, "Mathlib: SimpleGraph_Finsubgraph_coe_sSup"))
        except Exception:
            pass
    return results


def _r0047_coe_sInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Finsubgraph.coe_sInf
    # sInf s = (⨅ G ∈ s, G : G.Subgraph)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sInf", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("G"),)), OOp("s", (OVar("G"), OVar("colon"), OVar("G_Subgraph"),))))
            results.append((rhs, "Mathlib: SimpleGraph_Finsubgraph_coe_sInf"))
        except Exception:
            pass
    return results


def _r0048_coe_iSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Finsubgraph.coe_iSup
    # ⨆ i, f i = (⨆ i, f i : G.Subgraph)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (args[2], args[1], args[2], OVar("colon"), OVar("G_Subgraph"),))
            results.append((rhs, "Mathlib: SimpleGraph_Finsubgraph_coe_iSup"))
        except Exception:
            pass
    return results


def _r0049_coe_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Finsubgraph.coe_iInf
    # ⨅ i, f i = (⨅ i, f i : G.Subgraph)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (args[2], args[1], args[2], OVar("colon"), OVar("G_Subgraph"),))
            results.append((rhs, "Mathlib: SimpleGraph_Finsubgraph_coe_iInf"))
        except Exception:
            pass
    return results


def _r0050_hasseDualIso_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.hasseDualIso_symm_apply
    # hasseDualIso.symm a = toDual a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hasseDualIso_symm", 1)
    if args is not None:
        try:
            rhs = OOp("toDual", (args[0],))
            results.append((rhs, "Mathlib: SimpleGraph_hasseDualIso_symm_apply"))
        except Exception:
            pass
    return results


def _r0051_comap_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.comap_id
    # G.comap id = G
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_comap", 1)
    if args is not None:
        try:
            rhs = OVar("G")
            results.append((rhs, "Mathlib: SimpleGraph_comap_id"))
        except Exception:
            pass
    return results


def _r0052_comap_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.comap_comap
    # (G.comap g).comap f = G.comap (g ∘ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_comap_g_comap", 1)
    if args is not None:
        try:
            rhs = OOp("G_comap", (OOp("comp", (OVar("g"), args[0])),))
            results.append((rhs, "Mathlib: SimpleGraph_comap_comap"))
        except Exception:
            pass
    return results


def _r0053_comap_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.comap_top
    # (completeGraph W).comap f = completeGraph V
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completeGraph_W_comap", 1)
    if args is not None:
        try:
            rhs = OOp("completeGraph", (OVar("V"),))
            results.append((rhs, "Mathlib: SimpleGraph_comap_top"))
        except Exception:
            pass
    return results


def _r0054_simpleGraph_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.simpleGraph_trans
    # (e₁.trans e₂).simpleGraph = e₁.simpleGraph.trans e₂.simpleGraph
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_1_trans_e_2_simpleGraph")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("e_1_simpleGraph_trans", (OVar("e_2_simpleGraph"),))
            results.append((rhs, "Mathlib: Equiv_simpleGraph_trans"))
    except Exception:
        pass
    return results


def _r0055_symm_simpleGraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.symm_simpleGraph
    # e.simpleGraph.symm = e.symm.simpleGraph
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_simpleGraph_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm_simpleGraph")
            results.append((rhs, "Mathlib: Equiv_symm_simpleGraph"))
    except Exception:
        pass
    return results


def _r0056_induce_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.induce_bot
    # (⊥ : SimpleGraph V).induce s = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_SimpleGraph_V_induce", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: SimpleGraph_induce_bot"))
        except Exception:
            pass
    return results


def _r0057_spanningCoe_induce_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.spanningCoe_induce_univ
    # (G.induce .univ).spanningCoe = G
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_induce_univ_spanningCoe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("G")
            results.append((rhs, "Mathlib: SimpleGraph_spanningCoe_induce_univ"))
    except Exception:
        pass
    return results


def _r0058_ofLE_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Hom.ofLE_apply
    # ofLE h v = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofLE", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: SimpleGraph_Hom_ofLE_apply"))
        except Exception:
            pass
    return results


def _r0059_comp_comap_ofLE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Hom.comp_comap_ofLE
    # .comp (.comap f G) (.ofLE f.le_comap) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: SimpleGraph_Hom_comp_comap_ofLE"))
        except Exception:
            pass
    return results


def _r0060_comap_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Embedding.comap_eq
    # G.comap f = H
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_comap", 1)
    if args is not None:
        try:
            rhs = OVar("H")
            results.append((rhs, "Mathlib: SimpleGraph_Embedding_comap_eq"))
        except Exception:
            pass
    return results


def _r0061_ne_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.IsCycle.ne_bot
    # ∀ {p : G.Walk u u}, p.IsCycle → G ≠ ⊥   | nil, hp =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_IsCycle_ne_bot"))
        except Exception:
            pass
    return results


def _r0062_edges_cycleBypass_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Walk.edges_cycleBypass_subset
    # ∀ {w : G.Walk v v}, w.cycleBypass.edges ⊆ w.edges   | .nil =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: Walk_edges_cycleBypass_subset"))
        except Exception:
            pass
    return results


def _r0063_edgeSet_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.edgeSet_coe
    # G'.coe.edgeSet = Sym2.map (↑) ⁻¹' G'.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_prime_coe_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Sym2_map", (OVar("_unknown"), OVar("inv_prime"), OVar("G_prime_edgeSet"),))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_edgeSet_coe"))
    except Exception:
        pass
    return results


def _r0064_image_coe_edgeSet_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.image_coe_edgeSet_coe
    # Sym2.map (↑) '' G'.coe.edgeSet = G'.edgeSet
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sym2_map", 3)
    if args is not None:
        try:
            rhs = OVar("G_prime_edgeSet")
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_image_coe_edgeSet_coe"))
        except Exception:
            pass
    return results


def _r0065_verts_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.verts_sup
    # (G₁ ⊔ G₂).verts = G₁.verts ∪ G₂.verts
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_1_G_2_verts")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("G_1_verts"), OVar("G_2_verts")))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_verts_sup"))
    except Exception:
        pass
    return results


def _r0066_verts_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.verts_inf
    # (G₁ ⊓ G₂).verts = G₁.verts ∩ G₂.verts
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_1_G_2_verts")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OVar("G_1_verts"), OVar("G_2_verts")))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_verts_inf"))
    except Exception:
        pass
    return results


def _r0067_verts_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.verts_top
    # (⊤ : G.Subgraph).verts = Set.univ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_G_Subgraph_verts")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_verts_top"))
    except Exception:
        pass
    return results


def _r0068_verts_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.verts_bot
    # (⊥ : G.Subgraph).verts = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_G_Subgraph_verts")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_verts_bot"))
    except Exception:
        pass
    return results


def _r0069_eq_bot_iff_verts_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.eq_bot_iff_verts_eq_empty
    # G' = ⊥ ↔ G'.verts = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_prime")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("bot"), OVar("G_prime_verts"))), OVar("empty")))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_eq_bot_iff_verts_eq_empty"))
    except Exception:
        pass
    return results


def _r0070_verts_sInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.verts_sInf
    # (sInf s).verts = ⋂ G' ∈ s, verts G'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sInf_s_verts")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("G_prime"),)), OOp("s", (OVar("verts"), OVar("G_prime"),))))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_verts_sInf"))
    except Exception:
        pass
    return results


def _r0071_verts_iSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.verts_iSup
    # (⨆ i, f i).verts = ⋃ i, (f i).verts
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_f_i_verts")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("f_i_verts"),))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_verts_iSup"))
    except Exception:
        pass
    return results


def _r0072_verts_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.verts_iInf
    # (⨅ i, f i).verts = ⋂ i, (f i).verts
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_f_i_verts")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("i"), OVar("f_i_verts"),))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_verts_iInf"))
    except Exception:
        pass
    return results


def _r0073_coe_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.coe_bot
    # (⊥ : G.Subgraph).coe = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_G_Subgraph_coe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_coe_bot"))
    except Exception:
        pass
    return results


def _r0074_neighborSet_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.neighborSet_sup
    # (H ⊔ H').neighborSet v = H.neighborSet v ∪ H'.neighborSet v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_H_prime_neighborSet", 1)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("H_neighborSet", (args[0],)), OOp("H_prime_neighborSet", (args[0],))))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_neighborSet_sup"))
        except Exception:
            pass
    return results


def _r0075_neighborSet_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.neighborSet_inf
    # (H ⊓ H').neighborSet v = H.neighborSet v ∩ H'.neighborSet v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_H_prime_neighborSet", 1)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("H_neighborSet", (args[0],)), OOp("H_prime_neighborSet", (args[0],))))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_neighborSet_inf"))
        except Exception:
            pass
    return results


def _r0076_neighborSet_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.neighborSet_top
    # (⊤ : G.Subgraph).neighborSet v = G.neighborSet v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_G_Subgraph_neighborSet", 1)
    if args is not None:
        try:
            rhs = OOp("G_neighborSet", (args[0],))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_neighborSet_top"))
        except Exception:
            pass
    return results


def _r0077_neighborSet_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.neighborSet_bot
    # (⊥ : G.Subgraph).neighborSet v = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_G_Subgraph_neighborSet", 1)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_neighborSet_bot"))
        except Exception:
            pass
    return results


def _r0078_neighborSet_sSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.neighborSet_sSup
    # (sSup s).neighborSet v = ⋃ G' ∈ s, neighborSet G' v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sSup_s_neighborSet", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("G_prime"),)), OOp("s", (OVar("neighborSet"), OVar("G_prime"), args[0],))))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_neighborSet_sSup"))
        except Exception:
            pass
    return results


def _r0079_neighborSet_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.neighborSet_iInf
    # (⨅ i, f i).neighborSet v = (⋂ i, (f i).neighborSet v) ∩ G.neighborSet v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_f_i_neighborSet", 1)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("_unknown", (OVar("i"), OVar("f_i_neighborSet"), args[0],)), OOp("G_neighborSet", (args[0],))))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_neighborSet_iInf"))
        except Exception:
            pass
    return results


def _r0080_edgeSet_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.edgeSet_top
    # (⊤ : Subgraph G).edgeSet = G.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_Subgraph_G_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("G_edgeSet")
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_edgeSet_top"))
    except Exception:
        pass
    return results


def _r0081_edgeSet_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.edgeSet_bot
    # (⊥ : Subgraph G).edgeSet = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Subgraph_G_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_edgeSet_bot"))
    except Exception:
        pass
    return results


def _r0082_edgeSet_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.edgeSet_inf
    # (H₁ ⊓ H₂).edgeSet = H₁.edgeSet ∩ H₂.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_1_H_2_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OVar("H_1_edgeSet"), OVar("H_2_edgeSet")))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_edgeSet_inf"))
    except Exception:
        pass
    return results


def _r0083_edgeSet_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.edgeSet_sup
    # (H₁ ⊔ H₂).edgeSet = H₁.edgeSet ∪ H₂.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_1_H_2_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("H_1_edgeSet"), OVar("H_2_edgeSet")))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_edgeSet_sup"))
    except Exception:
        pass
    return results


def _r0084_edgeSet_sSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.edgeSet_sSup
    # (sSup s).edgeSet = ⋃ G' ∈ s, edgeSet G'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sSup_s_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("G_prime"),)), OOp("s", (OVar("edgeSet"), OVar("G_prime"),))))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_edgeSet_sSup"))
    except Exception:
        pass
    return results


def _r0085_edgeSet_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.edgeSet_iInf
    # (⨅ i, f i).edgeSet = (⋂ i, (f i).edgeSet) ∩ G.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_f_i_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OOp("_unknown", (OVar("i"), OVar("f_i_edgeSet"),)), OVar("G_edgeSet")))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_edgeSet_iInf"))
    except Exception:
        pass
    return results


def _r0086_spanningCoe_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.spanningCoe_bot
    # (⊥ : Subgraph G).spanningCoe = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Subgraph_G_spanningCoe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_spanningCoe_bot"))
    except Exception:
        pass
    return results


def _r0087_map_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.map_comp
    # H.map (g.comp f) = (H.map f).map g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_map", 1)
    if args is not None:
        try:
            rhs = OOp("H_map_f_map", (OVar("g"),))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_map_comp"))
        except Exception:
            pass
    return results


def _r0088_edgeSet_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.edgeSet_map
    # (H.map f).edgeSet = Sym2.map f '' H.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_map_f_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Sym2_map", (OVar("f"), OVar("prime_prime"), OVar("H_edgeSet"),))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_edgeSet_map"))
    except Exception:
        pass
    return results


def _r0089_sumRight_sum(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Coloring.sumRight_sum
    # (cG.sum cH).sumRight = cH
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cG_sum_cH_sumRight")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("cH")
            results.append((rhs, "Mathlib: SimpleGraph_Coloring_sumRight_sum"))
    except Exception:
        pass
    return results


def _r0090_sum_sumLeft_sumRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Coloring.sum_sumLeft_sumRight
    # c.sumLeft.sum c.sumRight = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_sumLeft_sum", 1)
    if args is not None:
        try:
            rhs = OVar("c")
            results.append((rhs, "Mathlib: SimpleGraph_Coloring_sum_sumLeft_sumRight"))
        except Exception:
            pass
    return results


def _r0091_exists_of_universalVerts(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.IsMatching.exists_of_universalVerts
    # ∃ t ⊆ G.universalVerts, ∃ (M : Subgraph G), M.verts = s ∪ t ∧ M.IsMatching
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("union", (OVar("s"), OVar("t"))), OVar("M_IsMatching")))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_IsMatching_exists_of_universalVerts"))
        except Exception:
            pass
    return results


def _r0092_length_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.length_cons
    # (cons h p).length = p.length + 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_p_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("p_length"), OLit(1)))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_length_cons"))
    except Exception:
        pass
    return results


def _r0093_eq_of_length_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.eq_of_length_eq_zero
    # ∀ {p : G.Walk u v}, p.length = 0 → u = v   | nil, _ => rfl  theorem adj_of_length_eq_one {u v : V} : ∀ {p : G.Walk u v},
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_Adj", 7)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("gt", (OVar("h_at_simp_theorem"), OVar("exists_length_eq_zero_iff"), OVar("u_v_colon_V"), OVar("colon"), OOp("==", (OOp("exists", (OVar("p"), OVar("colon"), OVar("G_Walk"), args[0], args[1], OVar("p_length"),)), OLit(0))),)), args[0])), args[1]))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_eq_of_length_eq_zero"))
        except Exception:
            pass
    return results


def _r0094_length_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.length_eq_zero_iff
    # p.length = 0 ↔ p = nil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("p"))), OVar("nil")))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_length_eq_zero_iff"))
    except Exception:
        pass
    return results


def _r0095_support_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.support_cons
    # (cons h p).support = u :: p.support
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_p_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("u", (OVar("colon_colon"), OVar("p_support"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_support_cons"))
    except Exception:
        pass
    return results


def _r0096_head_support(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.head_support
    # p.support.head (by simp) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_support_head", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_head_support"))
        except Exception:
            pass
    return results


def _r0097_getLast_support(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.getLast_support
    # p.support.getLast (by simp) = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_support_getLast", 1)
    if args is not None:
        try:
            rhs = OVar("b")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_getLast_support"))
        except Exception:
            pass
    return results


def _r0098_support_eq_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.support_eq_cons
    # p.support = u :: p.support.tail
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("u", (OVar("colon_colon"), OVar("p_support_tail"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_support_eq_cons"))
    except Exception:
        pass
    return results


def _r0099_mem_support_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.mem_support_iff
    # w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OVar("u"), OOp("in", (args[1], OVar("p_support_tail")))))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_mem_support_iff"))
        except Exception:
            pass
    return results


def _r0100_darts_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.darts_cons
    # (cons h p).darts = ⟨(u, v), h⟩ :: p.darts
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_p_darts")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("u_v_h", (OVar("colon_colon"), OVar("p_darts"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_darts_cons"))
    except Exception:
        pass
    return results


def _r0101_cons_map_snd_darts(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.cons_map_snd_darts
    # (u :: p.darts.map (·.snd)) = p.support
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "u", 3)
    if args is not None:
        try:
            rhs = OVar("p_support")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_cons_map_snd_darts"))
        except Exception:
            pass
    return results


def _r0102_edges_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.edges_cons
    # (cons h p).edges = s(u, v) :: p.edges
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_p_edges")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s_u_v", (OVar("colon_colon"), OVar("p_edges"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_edges_cons"))
    except Exception:
        pass
    return results


def _r0103_length_support(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.length_support
    # p.support.length = p.length + 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_support_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("p_length"), OLit(1)))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_length_support"))
    except Exception:
        pass
    return results


def _r0104_length_darts(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.length_darts
    # p.darts.length = p.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_darts_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_length")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_length_darts"))
    except Exception:
        pass
    return results


def _r0105_length_edges(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.length_edges
    # p.edges.length = p.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_edges_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_length")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_length_edges"))
    except Exception:
        pass
    return results


def _r0106_fst_darts_getElem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.fst_darts_getElem
    # p.darts[i].fst = p.support.dropLast[i]'(by grind)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_darts_i_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_support_dropLast_i_prime_by_grind")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_fst_darts_getElem"))
    except Exception:
        pass
    return results


def _r0107_support_getElem_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.support_getElem_length
    # p.support[p.length] = v
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_support_p_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("v")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_support_getElem_length"))
    except Exception:
        pass
    return results


def _r0108_edgeSet_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.edgeSet_nil
    # (nil : G.Walk u u).edgeSet = ∅
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("nil_colon_G_Walk_u_u_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_edgeSet_nil"))
    except Exception:
        pass
    return results


def _r0109_edgeSet_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.edgeSet_cons
    # (cons h p).edgeSet = insert s(u, v) p.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_p_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("insert", (OVar("s_u_v"), OVar("p_edgeSet"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_edgeSet_cons"))
    except Exception:
        pass
    return results


def _r0110_coe_edges_toFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.coe_edges_toFinset
    # (p.edges.toFinset : Set (Sym2 V)) = p.edgeSet
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_edges_toFinset", 3)
    if args is not None:
        try:
            rhs = OVar("p_edgeSet")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_coe_edges_toFinset"))
        except Exception:
            pass
    return results


def _r0111_edges_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.edges_eq_nil
    # p.edges = [] ↔ p.Nil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_edges")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OSeq(()), OVar("p_Nil")))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_edges_eq_nil"))
    except Exception:
        pass
    return results


def _r0112_nil_iff_length_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.nil_iff_length_eq
    # p.Nil ↔ p.length = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: SimpleGraph_Walk_nil_iff_length_eq"))
        except Exception:
            pass
    return results


def _r0113_takeUntil_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.takeUntil_cons
    # (p.cons hadj).takeUntil w (List.mem_of_mem_tail hwp) = (p.takeUntil w hwp).cons hadj
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_cons_hadj_takeUntil", 2)
    if args is not None:
        try:
            rhs = OOp("p_takeUntil_w_hwp_cons", (OVar("hadj"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_takeUntil_cons"))
        except Exception:
            pass
    return results


def _r0114_nil_takeUntil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.nil_takeUntil
    # (p.takeUntil w hwp).Nil ↔ u = w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("w")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_nil_takeUntil"))
        except Exception:
            pass
    return results


def _r0115_takeUntil_eq_take(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.takeUntil_eq_take
    # p.takeUntil w h = (p.take <| p.support.idxOf w).copy rfl (p.getVert_support_idxOf h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_takeUntil", 2)
    if args is not None:
        try:
            rhs = OOp("p_take_lt_pipe_p_support_idxOf_w_copy", (OVar("rfl"), OOp("p_getVert_support_idxOf", (args[1],)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_takeUntil_eq_take"))
        except Exception:
            pass
    return results


def _r0116_rotate_eq_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.rotate_eq_nil
    # c.rotate u h = nil ↔ c = nil
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_rotate", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("nil"), OVar("c"))), OVar("nil")))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_rotate_eq_nil"))
        except Exception:
            pass
    return results


def _r0117_map_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.map_cons
    # (cons h p).map f = cons (f.map_adj h) (p.map f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons_h_p_map", 1)
    if args is not None:
        try:
            rhs = OOp("cons", (OOp("f_map_adj", (OVar("h"),)), OOp("p_map", (args[0],)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_map_cons"))
        except Exception:
            pass
    return results


def _r0118_map_copy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.map_copy
    # (p.copy hu hv).map f = (p.map f).copy (hu ▸ rfl) (hv ▸ rfl)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_copy_hu_hv_map", 1)
    if args is not None:
        try:
            rhs = OOp("p_map_f_copy", (OOp("subst", (OVar("hu"), OVar("rfl"))), OOp("subst", (OVar("hv"), OVar("rfl"))),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_map_copy"))
        except Exception:
            pass
    return results


def _r0119_map_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.map_map
    # (p.map f).map f' = p.map (f'.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_map_f_map", 1)
    if args is not None:
        try:
            rhs = OOp("p_map", (OOp("f_prime_comp", (OVar("f"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_map_map"))
        except Exception:
            pass
    return results


def _r0120_length_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.length_map
    # (p.map f).length = p.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_map_f_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_length")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_length_map"))
    except Exception:
        pass
    return results


def _r0121_map_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.map_append
    # (p.append q).map f = (p.map f).append (q.map f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_append_q_map", 1)
    if args is not None:
        try:
            rhs = OOp("p_map_f_append", (OOp("q_map", (args[0],)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_map_append"))
        except Exception:
            pass
    return results


def _r0122_support_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.support_map
    # (p.map f).support = p.support.map f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_map_f_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_support_map", (OVar("f"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_support_map"))
    except Exception:
        pass
    return results


def _r0123_darts_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.darts_map
    # (p.map f).darts = p.darts.map f.mapDart
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_map_f_darts")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_darts_map", (OVar("f_mapDart"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_darts_map"))
    except Exception:
        pass
    return results


def _r0124_edges_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.edges_map
    # (p.map f).edges = p.edges.map (Sym2.map f)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_map_f_edges")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_edges_map", (OOp("Sym2_map", (OVar("f"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_edges_map"))
    except Exception:
        pass
    return results


def _r0125_edgeSet_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.edgeSet_map
    # (p.map f).edgeSet = Sym2.map f '' p.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_map_f_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Sym2_map", (OVar("f"), OVar("prime_prime"), OVar("p_edgeSet"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_edgeSet_map"))
    except Exception:
        pass
    return results


def _r0126_getVert_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.getVert_map
    # (p.map f).getVert n = f (p.getVert n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_map_f_getVert", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("p_getVert", (args[0],)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_getVert_map"))
        except Exception:
            pass
    return results


def _r0127_edgeSet_transfer(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeSet_transfer
    # (p.transfer H hp).edgeSet = p.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_transfer_H_hp_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_edgeSet")
            results.append((rhs, "Mathlib: SimpleGraph_edgeSet_transfer"))
    except Exception:
        pass
    return results


def _r0128_support_transfer(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.support_transfer
    # (p.transfer H hp).support = p.support
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_transfer_H_hp_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_support")
            results.append((rhs, "Mathlib: SimpleGraph_support_transfer"))
    except Exception:
        pass
    return results


def _r0129_length_transfer(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.length_transfer
    # (p.transfer H hp).length = p.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_transfer_H_hp_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_length")
            results.append((rhs, "Mathlib: SimpleGraph_length_transfer"))
    except Exception:
        pass
    return results


def _r0130_transfer_transfer(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.transfer_transfer
    # (p.transfer H hp).transfer K hp' = p.transfer K (p.edges_transfer hp ▸ hp')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_transfer_H_hp_transfer", 2)
    if args is not None:
        try:
            rhs = OOp("p_transfer", (args[0], OOp("subst", (OOp("p_edges_transfer", (OVar("hp"),)), args[1])),))
            results.append((rhs, "Mathlib: SimpleGraph_transfer_transfer"))
        except Exception:
            pass
    return results


def _r0131_induce_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.induce_cons
    # (w.cons huu').induce s hw = .cons (induce_adj.2 huu') (w.induce s <| by simp_all)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "w_cons_huu_prime_induce", 2)
    if args is not None:
        try:
            rhs = OOp("cons", (OOp("induce_adj_2", (OVar("huu_prime"),)), OOp("w_induce", (args[0], OVar("lt_pipe"), OVar("by"), OVar("simp_all"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_induce_cons"))
        except Exception:
            pass
    return results


def _r0132_support_induce(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.support_induce
    # ∀ (w : G.Walk u v) (hw), (w.induce s hw).support = w.support.attachWith _ hw   | .nil, hw => rfl   | .cons (v := u') hu 
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("w_induce_s_hw_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("w_support_attachWith", (OVar("_unknown"), OVar("hw"), OVar("pipe"), OVar("nil"), OVar("hw"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("cons"), OOp("v", (OVar("colon_eq"), OVar("u_prime"),)), OVar("hu"), OVar("w"), OVar("hw"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: SimpleGraph_support_induce"))
    except Exception:
        pass
    return results


def _r0133_toDeleteEdges_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.toDeleteEdges_cons
    # (Walk.cons h p).toDeleteEdges s hp =       Walk.cons (deleteEdges_adj.mpr ⟨h, hp _ (List.Mem.head _)⟩)         (p.toDele
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Walk_cons_h_p_toDeleteEdges", 2)
    if args is not None:
        try:
            rhs = OOp("Walk_cons", (OOp("deleteEdges_adj_mpr", (OVar("h_hp_List_Mem_head"),)), OOp("p_toDeleteEdges", (args[0], OVar("fun"), OVar("_unknown"), OVar("he"), OVar("eq_gt"), args[1], OVar("_unknown"), OVar("lt_pipe"), OVar("List_Mem_tail"), OVar("_unknown"), OVar("he"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_toDeleteEdges_cons"))
        except Exception:
            pass
    return results


def _r0134_copy_copy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.copy_copy
    # (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_copy_hu_hv_copy", 2)
    if args is not None:
        try:
            rhs = OOp("p_copy", (OOp("hu_trans", (args[0],)), OOp("hv_trans", (args[1],)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_copy_copy"))
        except Exception:
            pass
    return results


def _r0135_cons_nil_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.cons_nil_append
    # (cons h nil).append p = cons h p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons_h_nil_append", 1)
    if args is not None:
        try:
            rhs = OOp("cons", (OVar("h"), args[0],))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_cons_nil_append"))
        except Exception:
            pass
    return results


def _r0136_nil_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.nil_append
    # nil.append p = p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nil_append", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: SimpleGraph_Walk_nil_append"))
        except Exception:
            pass
    return results


def _r0137_append_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.append_nil
    # p.append nil = p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_append", 1)
    if args is not None:
        try:
            rhs = OVar("p")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_append_nil"))
        except Exception:
            pass
    return results


def _r0138_append_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.append_assoc
    # p.append (q.append r) = (p.append q).append r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_append", 1)
    if args is not None:
        try:
            rhs = OOp("p_append_q_append", (OVar("r"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_append_assoc"))
        except Exception:
            pass
    return results


def _r0139_append_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.append_concat
    # p.append (q.concat h) = (p.append q).concat h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_append", 1)
    if args is not None:
        try:
            rhs = OOp("p_append_q_concat", (OVar("h"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_append_concat"))
        except Exception:
            pass
    return results


def _r0140_reverse_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.reverse_singleton
    # (cons h nil).reverse = cons (G.symm h) nil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_nil_reverse")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("cons", (OOp("G_symm", (OVar("h"),)), OVar("nil"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_reverse_singleton"))
    except Exception:
        pass
    return results


def _r0141_cons_reverseAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.cons_reverseAux
    # (cons h p).reverseAux q = p.reverseAux (cons (G.symm h) q)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cons_h_p_reverseAux", 1)
    if args is not None:
        try:
            rhs = OOp("p_reverseAux", (OOp("cons", (OOp("G_symm", (OVar("h"),)), args[0],)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_cons_reverseAux"))
        except Exception:
            pass
    return results


def _r0142_append_reverseAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.append_reverseAux
    # (p.append q).reverseAux r = q.reverseAux (p.reverseAux r)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_append_q_reverseAux", 1)
    if args is not None:
        try:
            rhs = OOp("q_reverseAux", (OOp("p_reverseAux", (args[0],)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_append_reverseAux"))
        except Exception:
            pass
    return results


def _r0143_reverse_copy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.reverse_copy
    # (p.copy hu hv).reverse = p.reverse.copy hv hu
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_copy_hu_hv_reverse")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_reverse_copy", (OVar("hv"), OVar("hu"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_reverse_copy"))
    except Exception:
        pass
    return results


def _r0144_reverse_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.reverse_concat
    # (p.concat h).reverse = cons (G.symm h) p.reverse
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_concat_h_reverse")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("cons", (OOp("G_symm", (OVar("h"),)), OVar("p_reverse"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_reverse_concat"))
    except Exception:
        pass
    return results


def _r0145_reverse_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.reverse_reverse
    # p.reverse.reverse = p
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_reverse_reverse")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_reverse_reverse"))
    except Exception:
        pass
    return results


def _r0146_length_reverseAux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.length_reverseAux
    # (p.reverseAux q).length = p.length + q.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_reverseAux_q_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("p_length"), OVar("q_length")))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_length_reverseAux"))
    except Exception:
        pass
    return results


def _r0147_getVert_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.getVert_append
    # (p.append q).getVert i = if i < p.length then p.getVert i else q.getVert (i - p.length)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_append_q_getVert", 1)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("if", (args[0],)), OOp("p_length", (OVar("then"), OVar("p_getVert"), args[0], OVar("else"), OVar("q_getVert"), OOp("-", (args[0], OVar("p_length"))),))))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_getVert_append"))
        except Exception:
            pass
    return results


def _r0148_concatRec_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.concatRec_concat
    # @concatRec _ _ motive @Hnil @Hconcat _ _ (p.concat h) =       Hconcat p h (concatRec @Hnil @Hconcat p)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_concatRec", 8)
    if args is not None:
        try:
            rhs = OOp("Hconcat", (OVar("p"), OVar("h"), OOp("concatRec", (args[3], args[4], OVar("p"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_concatRec_concat"))
        except Exception:
            pass
    return results


def _r0149_support_append_eq_support_dropLast_appen(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.support_append_eq_support_dropLast_append
    # (p.append p').support = p.support.dropLast ++ p'.support
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_append_p_prime_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("concat", (OVar("p_support_dropLast"), OVar("p_prime_support")))
            results.append((rhs, "Mathlib: SimpleGraph_support_append_eq_support_dropLast_append"))
    except Exception:
        pass
    return results


def _r0150_edges_copy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edges_copy
    # (p.copy hu hv).edges = p.edges
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_copy_hu_hv_edges")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_edges")
            results.append((rhs, "Mathlib: SimpleGraph_edges_copy"))
    except Exception:
        pass
    return results


def _r0151_edges_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edges_reverse
    # p.reverse.edges = p.edges.reverse
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_reverse_edges")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_edges_reverse")
            results.append((rhs, "Mathlib: SimpleGraph_edges_reverse"))
    except Exception:
        pass
    return results


def _r0152_edgeSet_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeSet_concat
    # (p.concat h).edgeSet = insert s(v, w) p.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_concat_h_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("insert", (OVar("s_v_w"), OVar("p_edgeSet"),))
            results.append((rhs, "Mathlib: SimpleGraph_edgeSet_concat"))
    except Exception:
        pass
    return results


def _r0153_edgeSet_append(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeSet_append
    # (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_append_q_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("union", (OVar("p_edgeSet"), OVar("q_edgeSet")))
            results.append((rhs, "Mathlib: SimpleGraph_edgeSet_append"))
    except Exception:
        pass
    return results


def _r0154_take_length(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.take_length
    # (p.take n).length = n ⊓ p.length
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_take_n_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n", (OVar("_unknown"), OVar("p_length"),))
            results.append((rhs, "Mathlib: SimpleGraph_take_length"))
    except Exception:
        pass
    return results


def _r0155_snd_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.snd_reverse
    # p.reverse.snd = p.penultimate
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_reverse_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_penultimate")
            results.append((rhs, "Mathlib: SimpleGraph_snd_reverse"))
    except Exception:
        pass
    return results


def _r0156_penultimate_reverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.penultimate_reverse
    # p.reverse.penultimate = p.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_reverse_penultimate")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_snd")
            results.append((rhs, "Mathlib: SimpleGraph_penultimate_reverse"))
    except Exception:
        pass
    return results


def _r0157_tail_cons_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.tail_cons_nil
    # (Walk.cons h .nil).tail = .nil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Walk_cons_h_nil_tail")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("nil")
            results.append((rhs, "Mathlib: SimpleGraph_tail_cons_nil"))
    except Exception:
        pass
    return results


def _r0158_tail_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.tail_cons
    # (p.cons h).tail = p.copy (getVert_zero p).symm rfl
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_cons_h_tail")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_copy", (OVar("getVert_zero_p_symm"), OVar("rfl"),))
            results.append((rhs, "Mathlib: SimpleGraph_tail_cons"))
    except Exception:
        pass
    return results


def _r0159_dropLast_cons_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dropLast_cons_nil
    # (cons h nil).dropLast = nil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_nil_dropLast")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("nil")
            results.append((rhs, "Mathlib: SimpleGraph_dropLast_cons_nil"))
    except Exception:
        pass
    return results


def _r0160_dropLast_cons_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dropLast_cons_cons
    # (cons h (cons h₂ p)).dropLast = cons h (cons h₂ p).dropLast
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_cons_h_2_p_dropLast")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("cons", (OVar("h"), OVar("cons_h_2_p_dropLast"),))
            results.append((rhs, "Mathlib: SimpleGraph_dropLast_cons_cons"))
    except Exception:
        pass
    return results


def _r0161_dropLast_cons_of_not_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dropLast_cons_of_not_nil
    # (cons h p).dropLast = cons h (p.dropLast.copy rfl (penultimate_cons_of_not_nil _ _ hp).symm)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_p_dropLast")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("cons", (OVar("h"), OOp("p_dropLast_copy", (OVar("rfl"), OVar("penultimate_cons_of_not_nil_hp_symm"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_dropLast_cons_of_not_nil"))
    except Exception:
        pass
    return results


def _r0162_support_dropLast_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.support_dropLast_concat
    # p.dropLast.support ++ [v] = p.support
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "concat", 2)
    if args is not None:
        try:
            rhs = OVar("p_support")
            results.append((rhs, "Mathlib: SimpleGraph_support_dropLast_concat"))
        except Exception:
            pass
    return results


def _r0163_length_dropLast_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.length_dropLast_add_one
    # p.dropLast.length + 1 = p.length
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("p_length")
            results.append((rhs, "Mathlib: SimpleGraph_length_dropLast_add_one"))
        except Exception:
            pass
    return results


def _r0164_getVert_mem_tail_support(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.getVert_mem_tail_support
    # ∀ {i : ℕ}, i ≠ 0 → p.getVert i ∈ p.support.tail   | i + 1, _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: SimpleGraph_getVert_mem_tail_support"))
        except Exception:
            pass
    return results


def _r0165_getVert_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.getVert_nil
    # (@nil _ G u).getVert i = u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "at_nil_G_u_getVert", 1)
    if args is not None:
        try:
            rhs = OVar("u")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_getVert_nil"))
        except Exception:
            pass
    return results


def _r0166_getVert_of_length_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.getVert_of_length_le
    # w.getVert i = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "w_getVert", 1)
    if args is not None:
        try:
            rhs = OVar("v")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_getVert_of_length_le"))
        except Exception:
            pass
    return results


def _r0167_getVert_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.getVert_cons
    # (p.cons h).getVert n = p.getVert (n - 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_cons_h_getVert", 1)
    if args is not None:
        try:
            rhs = OOp("p_getVert", (OOp("-", (args[0], OLit(1))),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_getVert_cons"))
        except Exception:
            pass
    return results


def _r0168_snd_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.snd_cons
    # (q.cons hadj).snd = v
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_cons_hadj_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("v")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_snd_cons"))
    except Exception:
        pass
    return results


def _r0169_penultimate_cons_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.penultimate_cons_nil
    # (cons h nil).penultimate = u
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_nil_penultimate")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("u")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_penultimate_cons_nil"))
    except Exception:
        pass
    return results


def _r0170_penultimate_cons_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.penultimate_cons_cons
    # (cons h (cons h₂ p)).penultimate = (cons h₂ p).penultimate
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_cons_h_2_p_penultimate")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("cons_h_2_p_penultimate")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_penultimate_cons_cons"))
    except Exception:
        pass
    return results


def _r0171_penultimate_cons_of_not_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.penultimate_cons_of_not_nil
    # (cons h p).penultimate = p.penultimate
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_p_penultimate")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_penultimate")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_penultimate_cons_of_not_nil"))
    except Exception:
        pass
    return results


def _r0172_getLast_darts_eq_lastDart(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.getLast_darts_eq_lastDart
    # p.darts.getLast hnil = p.lastDart (darts_eq_nil.not.mp hnil)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_darts_getLast", 1)
    if args is not None:
        try:
            rhs = OOp("p_lastDart", (OOp("darts_eq_nil_not_mp", (args[0],)),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_getLast_darts_eq_lastDart"))
        except Exception:
            pass
    return results


def _r0173_binomialRandom_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.binomialRandom_one
    # G(V, 1) = dirac ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_V_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("dirac", (OVar("top"),))
            results.append((rhs, "Mathlib: SimpleGraph_binomialRandom_one"))
    except Exception:
        pass
    return results


def _r0174_toSubspaceUnit_isMono(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.toSubspaceUnit_isMono
    # l.toSubspaceUnit.IsMono C ↔ l.IsMono C
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toSubspaceUnit_IsMono", 1)
    if args is not None:
        try:
            rhs = OOp("l_IsMono", (args[0],))
            results.append((rhs, "Mathlib: Combinatorics_Line_toSubspaceUnit_isMono"))
        except Exception:
            pass
    return results


def _r0175_toSubspace_isMono(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.toSubspace_isMono
    # l.toSubspace.IsMono C ↔ l.IsMono fun x : ι → η → α ↦ C fun (i, e) ↦ x i e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toSubspace_IsMono", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("l_IsMono", (OVar("fun"), OVar("x"), OVar("colon"), OVar("i"),)), OOp("implies", (OVar("eta"), OOp("a", (OVar("_unknown"), args[0], OVar("fun"), OOp("i", (OVar("e"),)), OVar("_unknown"), OVar("x"), OVar("i"), OVar("e"),))))))
            results.append((rhs, "Mathlib: Combinatorics_Line_toSubspace_isMono"))
        except Exception:
            pass
    return results


def _r0176_adj_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adj_comm
    # G.Adj u v ↔ G.Adj v u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("G_Adj", (args[1], args[0],))
            results.append((rhs, "Mathlib: SimpleGraph_adj_comm"))
        except Exception:
            pass
    return results


def _r0177_adj_congr_of_sym2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adj_congr_of_sym2
    # G.Adj u v ↔ G.Adj w x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("G_Adj", (OVar("w"), OVar("x"),))
            results.append((rhs, "Mathlib: SimpleGraph_adj_congr_of_sym2"))
        except Exception:
            pass
    return results


def _r0178_sInf_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.sInf_adj
    # (sInf s).Adj a b ↔ (∀ G ∈ s, Adj G a b) ∧ a ≠ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sInf_s_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OOp("in", (OOp("forall", (OVar("G"),)), OOp("s", (OVar("Adj"), OVar("G"), args[0], args[1],)))), args[0])), args[1]))
            results.append((rhs, "Mathlib: SimpleGraph_sInf_adj"))
        except Exception:
            pass
    return results


def _r0179_iSup_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.iSup_adj
    # (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_f_i_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("exists", (OVar("i"), OVar("f_i_Adj"), args[0], args[1],))
            results.append((rhs, "Mathlib: SimpleGraph_iSup_adj"))
        except Exception:
            pass
    return results


def _r0180_iInf_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.iInf_adj
    # (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ a ≠ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_f_i_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("!=", (OOp("and", (OOp("forall", (OVar("i"), OVar("f_i_Adj"), args[0], args[1],)), args[0])), args[1]))
            results.append((rhs, "Mathlib: SimpleGraph_iInf_adj"))
        except Exception:
            pass
    return results


def _r0181_sInf_adj_of_nonempty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.sInf_adj_of_nonempty
    # (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sInf_s_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("G"),)), OOp("s", (OVar("Adj"), OVar("G"), args[0], args[1],))))
            results.append((rhs, "Mathlib: SimpleGraph_sInf_adj_of_nonempty"))
        except Exception:
            pass
    return results


def _r0182_bot_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.bot_adj
    # (⊥ : SimpleGraph V).Adj v w ↔ False
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_SimpleGraph_V_Adj", 2)
    if args is not None:
        try:
            rhs = OLit(False)
            results.append((rhs, "Mathlib: SimpleGraph_bot_adj"))
        except Exception:
            pass
    return results


def _r0183_isClique_insert_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isClique_insert_of_notMem
    # G.IsClique (insert a s) ↔ G.IsClique s ∧ ∀ b ∈ s, G.Adj a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_IsClique", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("G_IsClique", (OVar("s"),)), OOp("in", (OOp("forall", (OVar("b"),)), OOp("s", (OVar("G_Adj"), OVar("a"), OVar("b"),))))))
            results.append((rhs, "Mathlib: SimpleGraph_isClique_insert_of_notMem"))
        except Exception:
            pass
    return results


def _r0184_isEdgeReachable_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isEdgeReachable_one
    # G.IsEdgeReachable 1 u v ↔ G.Reachable u v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_IsEdgeReachable", 3)
    if args is not None:
        try:
            rhs = OOp("G_Reachable", (args[1], args[2],))
            results.append((rhs, "Mathlib: SimpleGraph_isEdgeReachable_one"))
        except Exception:
            pass
    return results


def _r0185_isEdgeConnected_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isEdgeConnected_one
    # G.IsEdgeConnected 1 ↔ G.Preconnected
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_IsEdgeConnected", 1)
    if args is not None:
        try:
            rhs = OVar("G_Preconnected")
            results.append((rhs, "Mathlib: SimpleGraph_isEdgeConnected_one"))
        except Exception:
            pass
    return results


def _r0186_mem_edges_toSubgraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.mem_edges_toSubgraph
    # e ∈ p.toSubgraph.edgeSet ↔ e ∈ p.edges
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("p_edges")))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_mem_edges_toSubgraph"))
        except Exception:
            pass
    return results


def _r0187_deleteEdges_le_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.deleteEdges_le_iff
    # G.deleteEdges s ≤ G' ↔ G ≤ fromEdgeSet s ⊔ G'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("G"), OOp("fromEdgeSet", (OVar("s"), OVar("_unknown"), args[1],))))
            results.append((rhs, "Mathlib: SimpleGraph_deleteEdges_le_iff"))
        except Exception:
            pass
    return results


def _r0188_edgeFinset_subset_edgeFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeFinset_subset_edgeFinset
    # G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subset", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("G_1"), OVar("G_2")))
            results.append((rhs, "Mathlib: SimpleGraph_edgeFinset_subset_edgeFinset"))
        except Exception:
            pass
    return results


def _r0189_edgeFinset_ssubset_edgeFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeFinset_ssubset_edgeFinset
    # G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "strict_subset", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OVar("G_1"), OVar("G_2")))
            results.append((rhs, "Mathlib: SimpleGraph_edgeFinset_ssubset_edgeFinset"))
        except Exception:
            pass
    return results


def _r0190_disjoint_edgeFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.disjoint_edgeFinset
    # Disjoint G₁.edgeFinset G₂.edgeFinset ↔ Disjoint G₁ G₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Disjoint", 2)
    if args is not None:
        try:
            rhs = OOp("Disjoint", (OVar("G_1"), OVar("G_2"),))
            results.append((rhs, "Mathlib: SimpleGraph_disjoint_edgeFinset"))
        except Exception:
            pass
    return results


def _r0191_edgeFinset_nonempty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.edgeFinset_nonempty
    # G.edgeFinset.Nonempty ↔ G ≠ ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_edgeFinset_Nonempty")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("!=", (OVar("G"), OVar("bot")))
            results.append((rhs, "Mathlib: SimpleGraph_edgeFinset_nonempty"))
    except Exception:
        pass
    return results


def _r0192_isHamiltonianCycle_isCycle_and_isHamilto(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.isHamiltonianCycle_isCycle_and_isHamiltonian_tail
    # p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.tail.IsHamiltonian
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_IsHamiltonianCycle")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("and", (OVar("p_IsCycle"), OVar("p_tail_IsHamiltonian")))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_isHamiltonianCycle_isCycle_and_isHamiltonian_tail"))
    except Exception:
        pass
    return results


def _r0193_map_adj_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Embedding.map_adj_iff
    # G'.Adj (f v) (f w) ↔ G.Adj v w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_prime_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("G_Adj", (OVar("v"), OVar("w"),))
            results.append((rhs, "Mathlib: SimpleGraph_Embedding_map_adj_iff"))
        except Exception:
            pass
    return results


def _r0194_map_mem_edgeSet_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Embedding.map_mem_edgeSet_iff
    # e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("e"), OVar("G_edgeSet")))
            results.append((rhs, "Mathlib: SimpleGraph_Embedding_map_mem_edgeSet_iff"))
        except Exception:
            pass
    return results


def _r0195_isCircuit_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.isCircuit_rotate
    # (c.rotate u hu).IsCircuit ↔ c.IsCircuit
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c_rotate_u_hu_IsCircuit")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("c_IsCircuit")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_isCircuit_rotate"))
    except Exception:
        pass
    return results


def _r0196_isCycle_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.isCycle_rotate
    # (c.rotate u hu).IsCycle ↔ c.IsCycle
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c_rotate_u_hu_IsCycle")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("c_IsCycle")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_isCycle_rotate"))
    except Exception:
        pass
    return results


def _r0197_inf_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.inf_adj
    # (G₁ ⊓ G₂).Adj a b ↔ G₁.Adj a b ∧ G₂.Adj a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_1_G_2_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("G_1_Adj", (args[0], args[1],)), OOp("G_2_Adj", (args[0], args[1],))))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_inf_adj"))
        except Exception:
            pass
    return results


def _r0198_top_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.top_adj
    # (⊤ : Subgraph G).Adj a b ↔ G.Adj a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Subgraph_G_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("G_Adj", (args[0], args[1],))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_top_adj"))
        except Exception:
            pass
    return results


def _r0199_sInf_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.sInf_adj
    # (sInf s).Adj a b ↔ (∀ G' ∈ s, Adj G' a b) ∧ G.Adj a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sInf_s_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (OOp("forall", (OVar("G_prime"),)), OOp("s", (OVar("Adj"), OVar("G_prime"), args[0], args[1],)))), OOp("G_Adj", (args[0], args[1],))))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_sInf_adj"))
        except Exception:
            pass
    return results


def _r0200_iSup_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.iSup_adj
    # (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_f_i_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("exists", (OVar("i"), OVar("f_i_Adj"), args[0], args[1],))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_iSup_adj"))
        except Exception:
            pass
    return results


def _r0201_iInf_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.iInf_adj
    # (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ G.Adj a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_f_i_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("forall", (OVar("i"), OVar("f_i_Adj"), args[0], args[1],)), OOp("G_Adj", (args[0], args[1],))))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_iInf_adj"))
        except Exception:
            pass
    return results


def _r0202_sInf_adj_of_nonempty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.sInf_adj_of_nonempty
    # (sInf s).Adj a b ↔ ∀ G' ∈ s, Adj G' a b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sInf_s_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("G_prime"),)), OOp("s", (OVar("Adj"), OVar("G_prime"), args[0], args[1],))))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_sInf_adj_of_nonempty"))
        except Exception:
            pass
    return results


def _r0203_map_le_iff_le_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.map_le_iff_le_comap
    # H.map f ≤ H' ↔ H ≤ H'.comap f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OVar("H"), OOp("H_prime_comap", (OVar("f"),))))
            results.append((rhs, "Mathlib: SimpleGraph_map_le_iff_le_comap"))
        except Exception:
            pass
    return results


def _r0204_in_0_1_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.TripartiteFromTriangles.Graph.in₀₁_iff
    # (graph t).Adj (in₀ a) (in₁ b) ↔ ∃ c, (a, b, c) ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graph_t_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("c"), OOp("a", (OVar("b"), OVar("c"),)),)), OVar("t")))
            results.append((rhs, "Mathlib: SimpleGraph_TripartiteFromTriangles_Graph_in_0_1_iff"))
        except Exception:
            pass
    return results


def _r0205_in_1_0_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.TripartiteFromTriangles.Graph.in₁₀_iff
    # (graph t).Adj (in₁ b) (in₀ a) ↔ ∃ c, (a, b, c) ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graph_t_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("c"), OOp("a", (OVar("b"), OVar("c"),)),)), OVar("t")))
            results.append((rhs, "Mathlib: SimpleGraph_TripartiteFromTriangles_Graph_in_1_0_iff"))
        except Exception:
            pass
    return results


def _r0206_in_0_2_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.TripartiteFromTriangles.Graph.in₀₂_iff
    # (graph t).Adj (in₀ a) (in₂ c) ↔ ∃ b, (a, b, c) ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graph_t_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("b"), OOp("a", (OVar("b"), OVar("c"),)),)), OVar("t")))
            results.append((rhs, "Mathlib: SimpleGraph_TripartiteFromTriangles_Graph_in_0_2_iff"))
        except Exception:
            pass
    return results


def _r0207_in_2_0_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.TripartiteFromTriangles.Graph.in₂₀_iff
    # (graph t).Adj (in₂ c) (in₀ a) ↔ ∃ b, (a, b, c) ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graph_t_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("b"), OOp("a", (OVar("b"), OVar("c"),)),)), OVar("t")))
            results.append((rhs, "Mathlib: SimpleGraph_TripartiteFromTriangles_Graph_in_2_0_iff"))
        except Exception:
            pass
    return results


def _r0208_in_1_2_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.TripartiteFromTriangles.Graph.in₁₂_iff
    # (graph t).Adj (in₁ b) (in₂ c) ↔ ∃ a, (a, b, c) ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graph_t_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("a"), OOp("a", (OVar("b"), OVar("c"),)),)), OVar("t")))
            results.append((rhs, "Mathlib: SimpleGraph_TripartiteFromTriangles_Graph_in_1_2_iff"))
        except Exception:
            pass
    return results


def _r0209_in_2_1_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.TripartiteFromTriangles.Graph.in₂₁_iff
    # (graph t).Adj (in₂ c) (in₁ b) ↔ ∃ a, (a, b, c) ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "graph_t_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("exists", (OVar("a"), OOp("a", (OVar("b"), OVar("c"),)),)), OVar("t")))
            results.append((rhs, "Mathlib: SimpleGraph_TripartiteFromTriangles_Graph_in_2_1_iff"))
        except Exception:
            pass
    return results


def _r0210_exists_length_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.exists_length_eq_one_iff
    # (∃ (p : G.Walk u v), p.length = 1) ↔ G.Adj u v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 2)
    if args is not None:
        try:
            rhs = OOp("G_Adj", (OVar("u"), OVar("v"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_exists_length_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0211_mem_darts_iff_infix_support(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.mem_darts_iff_infix_support
    # ⟨⟨u', v'⟩, h⟩ ∈ p.darts ↔ [u', v'] <:+: p.support
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("u_prime_v_prime", (OVar("lt_colon_plus_colon"), OVar("p_support"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_mem_darts_iff_infix_support"))
        except Exception:
            pass
    return results


def _r0212_nil_append_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.nil_append_iff
    # (p.append q).Nil ↔ p.Nil ∧ q.Nil
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_append_q_Nil")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("and", (OVar("p_Nil"), OVar("q_Nil")))
            results.append((rhs, "Mathlib: SimpleGraph_nil_append_iff"))
    except Exception:
        pass
    return results


def _r0213_coe_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Subspace.coe_apply
    # l x i = (l.idxFun i).elim id x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = OOp("l_idxFun_i_elim", (OVar("id"), args[0],))
            results.append((rhs, "Mathlib: Combinatorics_Subspace_coe_apply"))
        except Exception:
            pass
    return results


def _r0214_apply_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Subspace.apply_def
    # l x i = (l.idxFun i).elim id x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = OOp("l_idxFun_i_elim", (OVar("id"), args[0],))
            results.append((rhs, "Mathlib: Combinatorics_Subspace_apply_def"))
        except Exception:
            pass
    return results


def _r0215_apply_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Subspace.apply_inl
    # l x i = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Combinatorics_Subspace_apply_inl"))
        except Exception:
            pass
    return results


def _r0216_apply_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Subspace.apply_inr
    # l x i = x e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("e"),))
            results.append((rhs, "Mathlib: Combinatorics_Subspace_apply_inr"))
        except Exception:
            pass
    return results


def _r0217_reindex_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Subspace.reindex_apply
    # l.reindex eη eα eι x i = eα (l (eα.symm ∘ x ∘ eη) <| eι.symm i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_reindex", 5)
    if args is not None:
        try:
            rhs = OOp("ea", (OOp("l", (OOp("comp", (OVar("ea_symm"), OOp("comp", (args[3], args[0])))), OVar("lt_pipe"), OVar("ei_symm"), args[4],)),))
            results.append((rhs, "Mathlib: Combinatorics_Subspace_reindex_apply"))
        except Exception:
            pass
    return results


def _r0218_coe_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.coe_apply
    # l x i = (l.idxFun i).getD x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = OOp("l_idxFun_i_getD", (args[0],))
            results.append((rhs, "Mathlib: Combinatorics_Line_coe_apply"))
        except Exception:
            pass
    return results


def _r0219_toSubspaceUnit_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.toSubspaceUnit_apply
    # ⇑l.toSubspaceUnit a = l (a ())
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toSubspaceUnit", 1)
    if args is not None:
        try:
            rhs = OOp("l", (OOp("a", (OVar("_"),)),))
            results.append((rhs, "Mathlib: Combinatorics_Line_toSubspaceUnit_apply"))
        except Exception:
            pass
    return results


def _r0220_toSubspace_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.toSubspace_apply
    # ⇑l.toSubspace a ie = l a ie.1 ie.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_toSubspace", 2)
    if args is not None:
        try:
            rhs = OOp("l", (args[0], OVar("ie_1"), OVar("ie_2"),))
            results.append((rhs, "Mathlib: Combinatorics_Line_toSubspace_apply"))
        except Exception:
            pass
    return results


def _r0221_apply_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.apply_def
    # l x = fun i => (l.idxFun i).getD x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 1)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("i"), OVar("eq_gt"), OVar("l_idxFun_i_getD"), args[0],))
            results.append((rhs, "Mathlib: Combinatorics_Line_apply_def"))
        except Exception:
            pass
    return results


def _r0222_apply_none(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.apply_none
    # l x i = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Combinatorics_Line_apply_none"))
        except Exception:
            pass
    return results


def _r0223_apply_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.apply_some
    # l x i = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Combinatorics_Line_apply_some"))
        except Exception:
            pass
    return results


def _r0224_map_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.map_apply
    # l.map f (f x) = f ∘ l x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_map", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (args[0], OOp("l", (OVar("x"),))))
            results.append((rhs, "Mathlib: Combinatorics_Line_map_apply"))
        except Exception:
            pass
    return results


def _r0225_horizontal_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.horizontal_apply
    # l.horizontal v x = Sum.elim (l x) v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_horizontal", 2)
    if args is not None:
        try:
            rhs = OOp("Sum_elim", (OOp("l", (args[1],)), args[0],))
            results.append((rhs, "Mathlib: Combinatorics_Line_horizontal_apply"))
        except Exception:
            pass
    return results


def _r0226_prod_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.prod_apply
    # l.prod l' x = Sum.elim (l x) (l' x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "l_prod", 2)
    if args is not None:
        try:
            rhs = OOp("Sum_elim", (OOp("l", (args[1],)), OOp("l_prime", (args[1],)),))
            results.append((rhs, "Mathlib: Combinatorics_Line_prod_apply"))
        except Exception:
            pass
    return results


def _r0227_diagonal_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.Line.diagonal_apply
    # diagonal α ι x = fun _ => x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "diagonal", 3)
    if args is not None:
        try:
            rhs = OOp("fun", (OVar("_unknown"), OVar("eq_gt"), args[2],))
            results.append((rhs, "Mathlib: Combinatorics_Line_diagonal_apply"))
        except Exception:
            pass
    return results


def _r0228_exists_mono_homothetic_copy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Combinatorics.exists_mono_homothetic_copy
    # ∃ a > 0, ∃ (b : M) (c : κ), ∀ s ∈ S, C (a • s + b) = c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, ">", 2)
    if args is not None:
        try:
            rhs = OVar("c")
            results.append((rhs, "Mathlib: Combinatorics_exists_mono_homothetic_copy"))
        except Exception:
            pass
    return results


def _r0229_path_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.IsAcyclic.path_unique
    # p = q
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q")
            results.append((rhs, "Mathlib: SimpleGraph_IsAcyclic_path_unique"))
    except Exception:
        pass
    return results


def _r0230_isAcyclic_iff_path_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isAcyclic_iff_path_unique
    # G.IsAcyclic ↔ ∀ ⦃v w : V⦄ (p q : G.Path v w), p = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: SimpleGraph_isAcyclic_iff_path_unique"))
        except Exception:
            pass
    return results


def _r0231_path_concat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.IsAcyclic.path_concat
    # q = p.concat hadj
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_concat", (OVar("hadj"),))
            results.append((rhs, "Mathlib: SimpleGraph_IsAcyclic_path_concat"))
    except Exception:
        pass
    return results


def _r0232_card_edgeFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.IsTree.card_edgeFinset
    # Finset.card G.edgeFinset + 1 = Fintype.card V
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("Fintype_card", (OVar("V"),))
            results.append((rhs, "Mathlib: SimpleGraph_IsTree_card_edgeFinset"))
        except Exception:
            pass
    return results


def _r0233_isAcyclic_sup_fromEdgeSet_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isAcyclic_sup_fromEdgeSet_iff
    # (G ⊔ edge u v).IsAcyclic ↔       G.IsAcyclic ∧ (G.Reachable u v → u = v ∨ G.Adj u v)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("u")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("or", (OVar("v"), OOp("G_Adj", (OVar("u"), OVar("v"),))))
            results.append((rhs, "Mathlib: SimpleGraph_isAcyclic_sup_fromEdgeSet_iff"))
    except Exception:
        pass
    return results


def _r0234_reachable_eq_of_maximal_isAcyclic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.reachable_eq_of_maximal_isAcyclic
    # F.Reachable = G.Reachable
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("F_Reachable")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("G_Reachable")
            results.append((rhs, "Mathlib: SimpleGraph_reachable_eq_of_maximal_isAcyclic"))
    except Exception:
        pass
    return results


def _r0235_maximal_isAcyclic_iff_reachable_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.maximal_isAcyclic_iff_reachable_eq
    # Maximal (fun F ↦ F ≤ G ∧ F.IsAcyclic) F ↔ F.Reachable = G.Reachable
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("G_Reachable")
            results.append((rhs, "Mathlib: SimpleGraph_maximal_isAcyclic_iff_reachable_eq"))
        except Exception:
            pass
    return results


def _r0236_exists_isAcyclic_reachable_eq_le_of_le_o(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic
    # ∃ F : SimpleGraph V, H ≤ F ∧ F ≤ G ∧ F.IsAcyclic ∧ F.Reachable = G.Reachable
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("G_Reachable")
            results.append((rhs, "Mathlib: SimpleGraph_exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic"))
        except Exception:
            pass
    return results


def _r0237_exists_isAcyclic_reachable_eq_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.exists_isAcyclic_reachable_eq_le
    # ∃ F ≤ G, F.IsAcyclic ∧ F.Reachable = G.Reachable
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("G_Reachable")
            results.append((rhs, "Mathlib: SimpleGraph_exists_isAcyclic_reachable_eq_le"))
        except Exception:
            pass
    return results


def _r0238_isTree_iff_connected_and_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isTree_iff_connected_and_card
    # G.IsTree ↔ G.Connected ∧ Nat.card G.edgeSet + 1 = Nat.card V
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("Nat_card", (OVar("V"),))
            results.append((rhs, "Mathlib: SimpleGraph_isTree_iff_connected_and_card"))
        except Exception:
            pass
    return results


def _r0239_minDegree_eq_one_of_nontrivial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial
    # G.minDegree = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_minDegree")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: SimpleGraph_IsTree_minDegree_eq_one_of_nontrivial"))
    except Exception:
        pass
    return results


def _r0240_exists_vert_degree_one_of_nontrivial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial
    # ∃ v, G.degree v = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: SimpleGraph_IsTree_exists_vert_degree_one_of_nontrivial"))
        except Exception:
            pass
    return results


def _r0241_dist_eq_dist_add_one_of_adj_of_reachable(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.IsAcyclic.dist_eq_dist_add_one_of_adj_of_reachable
    # G.dist u v = G.dist u w + 1 ∨ G.dist u w = G.dist u v + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_dist", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OOp("+", (OOp("G_dist", (args[0], OVar("w"),)), OLit(1))), OOp("G_dist", (args[0], OVar("w"),)))), OOp("+", (OOp("G_dist", (args[0], args[1],)), OLit(1)))))
            results.append((rhs, "Mathlib: SimpleGraph_IsAcyclic_dist_eq_dist_add_one_of_adj_of_reachable"))
        except Exception:
            pass
    return results


def _r0242_dist_eq_dist_add_one_of_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.IsTree.dist_eq_dist_add_one_of_adj
    # G.dist u v = G.dist u w + 1 ∨ G.dist u w = G.dist u v + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_dist", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OOp("+", (OOp("G_dist", (args[0], OVar("w"),)), OLit(1))), OOp("G_dist", (args[0], OVar("w"),)))), OOp("+", (OOp("G_dist", (args[0], args[1],)), OLit(1)))))
            results.append((rhs, "Mathlib: SimpleGraph_IsTree_dist_eq_dist_add_one_of_adj"))
        except Exception:
            pass
    return results


def _r0243_adjMatrix_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_apply
    # G.adjMatrix α v w = if G.Adj v w then 1 else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_adjMatrix", 3)
    if args is not None:
        try:
            rhs = OOp("if", (OVar("G_Adj"), args[1], args[2], OVar("then"), OLit(1), OVar("else"), OLit(0),))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_apply"))
        except Exception:
            pass
    return results


def _r0244_adjMatrix_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_bot
    # (⊥ : SimpleGraph V).adjMatrix α = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_SimpleGraph_V_adjMatrix", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_bot"))
        except Exception:
            pass
    return results


def _r0245_adjMatrix_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_top
    # (⊤ : SimpleGraph V).adjMatrix α = .of (fun i j ↦ if i = j then 0 else 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_SimpleGraph_V_adjMatrix", 1)
    if args is not None:
        try:
            rhs = OOp("of", (OOp("==", (OOp("fun", (OVar("i"), OVar("j"), OVar("_unknown"), OVar("if"), OVar("i"),)), OOp("j", (OVar("then"), OLit(0), OVar("else"), OLit(1),)))),))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_top"))
        except Exception:
            pass
    return results


def _r0246_transpose_adjMatrix(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.transpose_adjMatrix
    # (G.adjMatrix α)ᵀ = G.adjMatrix α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_adjMatrix_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_adjMatrix", (OVar("a"),))
            results.append((rhs, "Mathlib: SimpleGraph_transpose_adjMatrix"))
    except Exception:
        pass
    return results


def _r0247_diag_adjMatrix(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.diag_adjMatrix
    # (G.adjMatrix α).diag = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_adjMatrix_a_diag")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: SimpleGraph_diag_adjMatrix"))
    except Exception:
        pass
    return results


def _r0248_toGraph_adjMatrix_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.toGraph_adjMatrix_eq
    # (G.isAdjMatrix_adjMatrix α).toGraph = G
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_isAdjMatrix_adjMatrix_a_toGraph")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("G")
            results.append((rhs, "Mathlib: SimpleGraph_toGraph_adjMatrix_eq"))
    except Exception:
        pass
    return results


def _r0249_compl_adjMatrix_eq_adjMatrix_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.compl_adjMatrix_eq_adjMatrix_compl
    # (G.adjMatrix α).compl = Gᶜ.adjMatrix α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_adjMatrix_a_compl")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_adjMatrix", (OVar("a"),))
            results.append((rhs, "Mathlib: SimpleGraph_compl_adjMatrix_eq_adjMatrix_compl"))
    except Exception:
        pass
    return results


def _r0250_adjMatrix_add_adjMatrix_eq_adjMatrix_com(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph
    # G.adjMatrix α + H.adjMatrix α = (completeGraph V).adjMatrix α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("completeGraph_V_adjMatrix", (OVar("a"),))
            results.append((rhs, "Mathlib: SimpleGraph_IsCompl_adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph"))
        except Exception:
            pass
    return results


def _r0251_adjMatrix_add_compl_adjMatrix_eq_adjMatr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph
    # G.adjMatrix α + (G.adjMatrix α).compl = (completeGraph V).adjMatrix α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("completeGraph_V_adjMatrix", (OVar("a"),))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph"))
        except Exception:
            pass
    return results


def _r0252_one_add_adjMatrix_add_compl_adjMatrix_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one
    # 1 + G.adjMatrix α + (G.adjMatrix α).compl = of 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("of", (OLit(1),))
            results.append((rhs, "Mathlib: SimpleGraph_one_add_adjMatrix_add_compl_adjMatrix_eq_of_one"))
        except Exception:
            pass
    return results


def _r0253_compl_adjMatrix_completeGraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.compl_adjMatrix_completeGraph
    # ((completeGraph V).adjMatrix α).compl = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("completeGraph_V_adjMatrix_a_compl")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: SimpleGraph_compl_adjMatrix_completeGraph"))
    except Exception:
        pass
    return results


def _r0254_compl_zero_eq_of_one_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.compl_zero_eq_of_one_sub_one
    # (0 : Matrix V V α).compl = of 1 - 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Matrix_V_V_a_compl")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OOp("of", (OLit(1),)), OLit(1)))
            results.append((rhs, "Mathlib: Matrix_compl_zero_eq_of_one_sub_one"))
    except Exception:
        pass
    return results


def _r0255_compl_of_one_sub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.compl_of_one_sub_one
    # (of 1 - 1 : Matrix V V α).compl = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("of_1_minus_1_colon_Matrix_V_V_a_compl")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Matrix_compl_of_one_sub_one"))
    except Exception:
        pass
    return results


def _r0256_adjMatrix_hadamard_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_hadamard_self
    # G.adjMatrix α ⊙ G.adjMatrix α = G.adjMatrix α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_adjMatrix", 4)
    if args is not None:
        try:
            rhs = OOp("G_adjMatrix", (args[3],))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_hadamard_self"))
        except Exception:
            pass
    return results


def _r0257_adjMatrix_dotProduct(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_dotProduct
    # G.adjMatrix α v ⬝ᵥ vec = ∑ u ∈ G.neighborFinset v, vec u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_adjMatrix", 4)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("u"),)), OOp("G_neighborFinset", (args[1], args[3], OVar("u"),))))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_dotProduct"))
        except Exception:
            pass
    return results


def _r0258_dotProduct_adjMatrix(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dotProduct_adjMatrix
    # vec ⬝ᵥ G.adjMatrix α v = ∑ u ∈ G.neighborFinset v, vec u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "vec", 4)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("u"),)), OOp("G_neighborFinset", (args[3], OVar("vec"), OVar("u"),))))
            results.append((rhs, "Mathlib: SimpleGraph_dotProduct_adjMatrix"))
        except Exception:
            pass
    return results


def _r0259_adjMatrix_mulVec_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_mulVec_apply
    # (G.adjMatrix α *ᵥ vec) v = ∑ u ∈ G.neighborFinset v, vec u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_adjMatrix_a_star_vec", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("u"),)), OOp("G_neighborFinset", (args[0], OVar("vec"), OVar("u"),))))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_mulVec_apply"))
        except Exception:
            pass
    return results


def _r0260_adjMatrix_vecMul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_vecMul_apply
    # (vec ᵥ* G.adjMatrix α) v = ∑ u ∈ G.neighborFinset v, vec u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "vec_star_G_adjMatrix_a", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("u"),)), OOp("G_neighborFinset", (args[0], OVar("vec"), OVar("u"),))))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_vecMul_apply"))
        except Exception:
            pass
    return results


def _r0261_adjMatrix_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_mul_apply
    # (G.adjMatrix α * M) v w = ∑ u ∈ G.neighborFinset v, M u w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_adjMatrix_a_star_M", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("u"),)), OOp("G_neighborFinset", (args[0], OVar("M"), OVar("u"), args[1],))))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_mul_apply"))
        except Exception:
            pass
    return results


def _r0262_mul_adjMatrix_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.mul_adjMatrix_apply
    # (M * G.adjMatrix α) v w = ∑ u ∈ G.neighborFinset w, M v u
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "M_star_G_adjMatrix_a", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("u"),)), OOp("G_neighborFinset", (args[1], OVar("M"), args[0], OVar("u"),))))
            results.append((rhs, "Mathlib: SimpleGraph_mul_adjMatrix_apply"))
        except Exception:
            pass
    return results


def _r0263_trace_adjMatrix(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.trace_adjMatrix
    # Matrix.trace (G.adjMatrix α) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Matrix_trace", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: SimpleGraph_trace_adjMatrix"))
        except Exception:
            pass
    return results


def _r0264_natCast_card_dart_eq_dotProduct(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.natCast_card_dart_eq_dotProduct
    # (Fintype.card G.Dart : α) = adjMatrix α G *ᵥ 1 ⬝ᵥ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fintype_card", 3)
    if args is not None:
        try:
            rhs = OOp("adjMatrix", (args[2], OVar("G"), OVar("star"), OLit(1), OVar("_unknown"), OLit(1),))
            results.append((rhs, "Mathlib: SimpleGraph_natCast_card_dart_eq_dotProduct"))
        except Exception:
            pass
    return results


def _r0265_adjMatrix_mulVec_const_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_mulVec_const_apply
    # (G.adjMatrix α *ᵥ Function.const _ a) v = G.degree v * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_adjMatrix_a_star_Function_const_a", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("G_degree", (args[0],)), OVar("a")))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_mulVec_const_apply"))
        except Exception:
            pass
    return results


def _r0266_adjMatrix_mulVec_const_apply_of_regular(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_mulVec_const_apply_of_regular
    # (G.adjMatrix α *ᵥ Function.const _ a) v = d * a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_adjMatrix_a_star_Function_const_a", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("d"), OVar("a")))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_mulVec_const_apply_of_regular"))
        except Exception:
            pass
    return results


def _r0267_adjMatrix_pow_apply_eq_card_walk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adjMatrix_pow_apply_eq_card_walk
    # (G.adjMatrix α ^ n) u v = Fintype.card { p : G.Walk u v | p.length = n }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_adjMatrix_a_pow_n", 2)
    if args is not None:
        try:
            rhs = OOp("Fintype_card", (OVar("p_colon_G_Walk_u_v_pipe_p_length_eq_n"),))
            results.append((rhs, "Mathlib: SimpleGraph_adjMatrix_pow_apply_eq_card_walk"))
        except Exception:
            pass
    return results


def _r0268_dotProduct_mulVec_adjMatrix(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dotProduct_mulVec_adjMatrix
    # x ⬝ᵥ G.adjMatrix α *ᵥ y = ∑ i : V, ∑ j : V, if G.Adj i j then x i * y j else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 5)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("_unknown", (OVar("i"), OVar("colon"), OVar("V"), args[0], OVar("j"), OVar("colon"), OVar("V"), OVar("if"), OVar("G_Adj"), OVar("i"), OVar("j"), OVar("then"), OVar("x"), OVar("i"),)), OOp("y", (OVar("j"), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: SimpleGraph_dotProduct_mulVec_adjMatrix"))
        except Exception:
            pass
    return results


def _r0269_adj_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.adj_inj
    # G.Adj = H.Adj ↔ G = H
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_Adj")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("H_Adj"), OVar("G"))), OVar("H")))
            results.append((rhs, "Mathlib: SimpleGraph_adj_inj"))
    except Exception:
        pass
    return results


def _r0270_eq_bot_iff_forall_not_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.eq_bot_iff_forall_not_adj
    # G = ⊥ ↔ ∀ a b : V, ¬G.Adj a b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("bot"), OOp("forall", (OVar("a"), OVar("b"), OVar("colon"), OVar("V"), OOp("not", (OVar("G_Adj"),)), OVar("a"), OVar("b"),))))
            results.append((rhs, "Mathlib: SimpleGraph_eq_bot_iff_forall_not_adj"))
    except Exception:
        pass
    return results


def _r0271_eq_top_iff_forall_ne_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.eq_top_iff_forall_ne_adj
    # G = ⊤ ↔ ∀ a b : V, a ≠ b → G.Adj a b
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("!=", (OOp("iff", (OVar("top"), OOp("forall", (OVar("a"), OVar("b"), OVar("colon"), OVar("V"), OVar("a"),)))), OOp("implies", (OVar("b"), OOp("G_Adj", (OVar("a"), OVar("b"),))))))
            results.append((rhs, "Mathlib: SimpleGraph_eq_top_iff_forall_ne_adj"))
    except Exception:
        pass
    return results


def _r0272_isBipartiteWith_neighborSet(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isBipartiteWith_neighborSet
    # G.neighborSet v = { w ∈ t | G.Adj v w }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_neighborSet", 1)
    if args is not None:
        try:
            rhs = OVar("w_in_t_pipe_G_Adj_v_w")
            results.append((rhs, "Mathlib: SimpleGraph_isBipartiteWith_neighborSet"))
        except Exception:
            pass
    return results


def _r0273_isBipartiteWith_neighborFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isBipartiteWith_neighborFinset
    # G.neighborFinset v = { w ∈ t | G.Adj v w }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_neighborFinset", 1)
    if args is not None:
        try:
            rhs = OVar("w_in_t_pipe_G_Adj_v_w")
            results.append((rhs, "Mathlib: SimpleGraph_isBipartiteWith_neighborFinset"))
        except Exception:
            pass
    return results


def _r0274_isBipartiteWith_bipartiteAbove(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isBipartiteWith_bipartiteAbove
    # G.neighborFinset v = bipartiteAbove G.Adj t v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_neighborFinset", 1)
    if args is not None:
        try:
            rhs = OOp("bipartiteAbove", (OVar("G_Adj"), OVar("t"), args[0],))
            results.append((rhs, "Mathlib: SimpleGraph_isBipartiteWith_bipartiteAbove"))
        except Exception:
            pass
    return results


def _r0275_isBipartiteWith_bipartiteBelow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isBipartiteWith_bipartiteBelow
    # G.neighborFinset w = bipartiteBelow G.Adj s w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_neighborFinset", 1)
    if args is not None:
        try:
            rhs = OOp("bipartiteBelow", (OVar("G_Adj"), OVar("s"), args[0],))
            results.append((rhs, "Mathlib: SimpleGraph_isBipartiteWith_bipartiteBelow"))
        except Exception:
            pass
    return results


def _r0276_mulCayley_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.mulCayley_empty
    # mulCayley (∅ : Set M) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulCayley", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: SimpleGraph_mulCayley_empty"))
        except Exception:
            pass
    return results


def _r0277_circulantGraph_eq_erase_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.circulantGraph_eq_erase_zero
    # circulantGraph s = circulantGraph (s \\ {0})
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "circulantGraph", 1)
    if args is not None:
        try:
            rhs = OOp("circulantGraph", (OOp("s", (OVar("bsl"), OVar("_0"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_circulantGraph_eq_erase_zero"))
        except Exception:
            pass
    return results


def _r0278_circulantGraph_eq_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.circulantGraph_eq_symm
    # circulantGraph s = circulantGraph (s ∪ (-s))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "circulantGraph", 1)
    if args is not None:
        try:
            rhs = OOp("circulantGraph", (OOp("union", (args[0], OVar("minus_s"))),))
            results.append((rhs, "Mathlib: SimpleGraph_circulantGraph_eq_symm"))
        except Exception:
            pass
    return results


def _r0279_cycleGraph_eq_circulantGraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_eq_circulantGraph
    # cycleGraph (n + 1) = circulantGraph {1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph", 1)
    if args is not None:
        try:
            rhs = OOp("circulantGraph", (OVar("_1"),))
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_eq_circulantGraph"))
        except Exception:
            pass
    return results


def _r0280_cycleGraph_zero_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_zero_eq_bot
    # cycleGraph 0 = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_zero_eq_bot"))
        except Exception:
            pass
    return results


def _r0281_cycleGraph_one_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_one_eq_bot
    # cycleGraph 1 = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_one_eq_bot"))
        except Exception:
            pass
    return results


def _r0282_cycleGraph_zero_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_zero_eq_top
    # cycleGraph 0 = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_zero_eq_top"))
        except Exception:
            pass
    return results


def _r0283_cycleGraph_one_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_one_eq_top
    # cycleGraph 1 = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_one_eq_top"))
        except Exception:
            pass
    return results


def _r0284_cycleGraph_two_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_two_eq_top
    # cycleGraph 2 = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_two_eq_top"))
        except Exception:
            pass
    return results


def _r0285_cycleGraph_three_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_three_eq_top
    # cycleGraph 3 = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_three_eq_top"))
        except Exception:
            pass
    return results


def _r0286_cycleGraph_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_adj
    # (cycleGraph (n + 2)).Adj u v ↔ u - v = 1 ∨ v - u = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("or", (OLit(1), OOp("-", (OVar("v"), OVar("u"))))), OLit(1)))
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_adj"))
        except Exception:
            pass
    return results


def _r0287_cycleGraph_neighborSet(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_neighborSet
    # (cycleGraph (n + 2)).neighborSet v = {v - 1, v + 1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph_n_plus_2_neighborSet", 1)
    if args is not None:
        try:
            rhs = OVar("v_minus_1_v_plus_1")
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_neighborSet"))
        except Exception:
            pass
    return results


def _r0288_cycleGraph_neighborFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_neighborFinset
    # (cycleGraph (n + 2)).neighborFinset v = {v - 1, v + 1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph_n_plus_2_neighborFinset", 1)
    if args is not None:
        try:
            rhs = OVar("v_minus_1_v_plus_1")
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_neighborFinset"))
        except Exception:
            pass
    return results


def _r0289_cycleGraph_degree_two_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_degree_two_le
    # (cycleGraph (n + 2)).degree v = Finset.card {v - 1, v + 1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph_n_plus_2_degree", 1)
    if args is not None:
        try:
            rhs = OOp("len", (OVar("v_minus_1_v_plus_1"),))
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_degree_two_le"))
        except Exception:
            pass
    return results


def _r0290_cycleGraph_degree_three_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph_degree_three_le
    # (cycleGraph (n + 3)).degree v = 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cycleGraph_n_plus_3_degree", 1)
    if args is not None:
        try:
            rhs = OLit(2)
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_degree_three_le"))
        except Exception:
            pass
    return results


def _r0291_length_cycle_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph.length_cycle_cons
    # ∀ m : Fin (n + 3), (cycleGraph.cycleCons n m).length = m.val   | ⟨0, h⟩ =>
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cycleGraph_cycleCons_n_m_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("m_val", (OVar("pipe"), OVar("_0_h"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_length_cycle_cons"))
    except Exception:
        pass
    return results


def _r0292_length_cycle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.cycleGraph.length_cycle
    # (cycleGraph.cycle n).length = n + 3
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cycleGraph_cycle_n_length")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("n"), OLit(3)))
            results.append((rhs, "Mathlib: SimpleGraph_cycleGraph_length_cycle"))
    except Exception:
        pass
    return results


def _r0293_isClique_iff_induce_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isClique_iff_induce_eq
    # G.IsClique s ↔ G.induce s = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: SimpleGraph_isClique_iff_induce_eq"))
        except Exception:
            pass
    return results


def _r0294_isClique_map_iff_of_nontrivial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isClique_map_iff_of_nontrivial
    # (G.map f).IsClique t ↔ ∃ (s : Set α), G.IsClique s ∧ f '' s = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("t")
            results.append((rhs, "Mathlib: SimpleGraph_isClique_map_iff_of_nontrivial"))
        except Exception:
            pass
    return results


def _r0295_isClique_map_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isClique_map_iff
    # (G.map f).IsClique t ↔ t.Subsingleton ∨ ∃ (s : Set α), G.IsClique s ∧ f '' s = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("t")
            results.append((rhs, "Mathlib: SimpleGraph_isClique_map_iff"))
        except Exception:
            pass
    return results


def _r0296_isClique_map_finset_iff_of_nontrivial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isClique_map_finset_iff_of_nontrivial
    # (G.map f).IsClique t ↔ ∃ (s : Finset α), G.IsClique s ∧ s.map f = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OVar("t")
            results.append((rhs, "Mathlib: SimpleGraph_isClique_map_finset_iff_of_nontrivial"))
        except Exception:
            pass
    return results


def _r0297_isClique_map_finset_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.isClique_map_finset_iff
    # (G.map f).IsClique t ↔ #t ≤ 1 ∨ ∃ (s : Finset α), G.IsClique s ∧ s.map f = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("t")
            results.append((rhs, "Mathlib: SimpleGraph_isClique_map_finset_iff"))
        except Exception:
            pass
    return results


def _r0298_chromaticNumber_eq_biInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_eq_biInf
    # G.chromaticNumber = ⨅ n ∈ setOf G.Colorable, (n : ℕ∞)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("n"),)), OOp("setOf", (OVar("G_Colorable"), OOp("n", (OVar("colon"), OVar("inf"),)),))))
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_eq_biInf"))
    except Exception:
        pass
    return results


def _r0299_chromaticNumber_eq_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_eq_iInf
    # G.chromaticNumber = ⨅ n : {m | G.Colorable m}, (n : ℕ∞)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_unknown", (OVar("n"), OVar("colon"), OVar("m_pipe_G_Colorable_m"), OOp("n", (OVar("colon"), OVar("inf"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_eq_iInf"))
    except Exception:
        pass
    return results


def _r0300_chromaticNumber_eq_sInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Colorable.chromaticNumber_eq_sInf
    # G.chromaticNumber = sInf {n' : ℕ | G.Colorable n'}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sInf", (OVar("n_prime_colon_pipe_G_Colorable_n_prime"),))
            results.append((rhs, "Mathlib: SimpleGraph_Colorable_chromaticNumber_eq_sInf"))
    except Exception:
        pass
    return results


def _r0301_coe_recolorOfEmbedding(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.coe_recolorOfEmbedding
    # ⇑(G.recolorOfEmbedding f) = (Embedding.completeGraph f).toHom.comp
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_recolorOfEmbedding_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Embedding_completeGraph_f_toHom_comp")
            results.append((rhs, "Mathlib: SimpleGraph_coe_recolorOfEmbedding"))
    except Exception:
        pass
    return results


def _r0302_coe_recolorOfEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.coe_recolorOfEquiv
    # ⇑(G.recolorOfEquiv f) = (Embedding.completeGraph f).toHom.comp
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_recolorOfEquiv_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Embedding_completeGraph_f_toHom_comp")
            results.append((rhs, "Mathlib: SimpleGraph_coe_recolorOfEquiv"))
    except Exception:
        pass
    return results


def _r0303_coe_recolorOfCardLE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.coe_recolorOfCardLE
    # ⇑(G.recolorOfCardLE hαβ) =       (Embedding.completeGraph (Embedding.nonempty_of_card_le hαβ).some).toHom.comp
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_recolorOfCardLE_hab")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Embedding_completeGraph_Embedding_nonempty_of_card_le_hab_some_toHom_comp")
            results.append((rhs, "Mathlib: SimpleGraph_coe_recolorOfCardLE"))
    except Exception:
        pass
    return results


def _r0304_chromaticNumber_eq_iff_colorable_not_col(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable
    # G.chromaticNumber = n + 1 ↔ G.Colorable (n + 1) ∧ ¬G.Colorable n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("and", (OOp("iff", (OOp("+", (OVar("n"), OLit(1))), OOp("G_Colorable", (OOp("+", (OVar("n"), OLit(1))),)))), OOp("not_G_Colorable", (OVar("n"),))))
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_eq_iff_colorable_not_colorable"))
    except Exception:
        pass
    return results


def _r0305_chromaticNumber_eq_zero_of_isEmpty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_eq_zero_of_isEmpty
    # G.chromaticNumber = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_eq_zero_of_isEmpty"))
    except Exception:
        pass
    return results


def _r0306_chromaticNumber_eq_card_iff_forall_surje(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_eq_card_iff_forall_surjective
    # G.chromaticNumber = card α ↔ ∀ C : G.Coloring α, Surjective C
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("len", (OVar("a"),)), OOp("forall", (OVar("C"), OVar("colon"), OVar("G_Coloring"), OVar("a"), OVar("Surjective"), OVar("C"),))))
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_eq_card_iff_forall_surjective"))
    except Exception:
        pass
    return results


def _r0307_chromaticNumber_eq_iff_forall_surjective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_eq_iff_forall_surjective
    # G.chromaticNumber = n ↔ ∀ C : G.Coloring (Fin n), Surjective C
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("n"), OOp("forall", (OVar("C"), OVar("colon"), OVar("G_Coloring"), OVar("Fin_n"), OVar("Surjective"), OVar("C"),))))
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_eq_iff_forall_surjective"))
    except Exception:
        pass
    return results


def _r0308_chromaticNumber_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_bot
    # (⊥ : SimpleGraph V).chromaticNumber = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_SimpleGraph_V_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_bot"))
    except Exception:
        pass
    return results


def _r0309_chromaticNumber_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_top
    # (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_SimpleGraph_V_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Fintype_card", (OVar("V"),))
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_top"))
    except Exception:
        pass
    return results


def _r0310_chromaticNumber_top_eq_top_of_infinite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_top_eq_top_of_infinite
    # (⊤ : SimpleGraph V).chromaticNumber = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_SimpleGraph_V_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_top_eq_top_of_infinite"))
    except Exception:
        pass
    return results


def _r0311_eq_top_of_chromaticNumber_eq_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.eq_top_of_chromaticNumber_eq_card
    # G = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: SimpleGraph_eq_top_of_chromaticNumber_eq_card"))
    except Exception:
        pass
    return results


def _r0312_chromaticNumber_eq_card_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_eq_card_iff
    # G.chromaticNumber = Fintype.card V ↔ G = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("Fintype_card", (OVar("V"),)), OVar("G"))), OVar("top")))
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_eq_card_iff"))
    except Exception:
        pass
    return results


def _r0313_chromaticNumber_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_eq_one_iff
    # G.chromaticNumber = 1 ↔ G = ⊥ ∧ Nonempty V
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("G"))), OOp("and", (OVar("bot"), OOp("Nonempty", (OVar("V"),))))))
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0314_chromaticNumber(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.CompleteBipartiteGraph.chromaticNumber
    # (completeBipartiteGraph V W).chromaticNumber = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("completeBipartiteGraph_V_W_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(2)
            results.append((rhs, "Mathlib: SimpleGraph_CompleteBipartiteGraph_chromaticNumber"))
    except Exception:
        pass
    return results


def _r0315_chromaticNumber(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.completeMultipartiteGraph.chromaticNumber
    # (completeMultipartiteGraph V).chromaticNumber = Fintype.card ι
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("completeMultipartiteGraph_V_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Fintype_card", (OVar("i"),))
            results.append((rhs, "Mathlib: SimpleGraph_completeMultipartiteGraph_chromaticNumber"))
    except Exception:
        pass
    return results


def _r0316_completeEquipartiteGraph_eq_bot_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.completeEquipartiteGraph_eq_bot_iff
    # completeEquipartiteGraph r t = ⊥ ↔ r ≤ 1 ∨ t = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completeEquipartiteGraph", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("<=", (OOp("iff", (OVar("bot"), args[0])), OOp("or", (OLit(1), args[1])))), OLit(0)))
            results.append((rhs, "Mathlib: SimpleGraph_completeEquipartiteGraph_eq_bot_iff"))
        except Exception:
            pass
    return results


def _r0317_neighborSet_completeEquipartiteGraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.neighborSet_completeEquipartiteGraph
    # (completeEquipartiteGraph r t).neighborSet v = {v.1}ᶜ ×ˢ Set.univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completeEquipartiteGraph_r_t_neighborSet", 1)
    if args is not None:
        try:
            rhs = OOp("v_1", (OVar("times"), OVar("Set_univ"),))
            results.append((rhs, "Mathlib: SimpleGraph_neighborSet_completeEquipartiteGraph"))
        except Exception:
            pass
    return results


def _r0318_neighborFinset_completeEquipartiteGraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.neighborFinset_completeEquipartiteGraph
    # (completeEquipartiteGraph r t).neighborFinset v = {v.1}ᶜ ×ˢ univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completeEquipartiteGraph_r_t_neighborFinset", 1)
    if args is not None:
        try:
            rhs = OOp("v_1", (OVar("times"), OVar("univ"),))
            results.append((rhs, "Mathlib: SimpleGraph_neighborFinset_completeEquipartiteGraph"))
        except Exception:
            pass
    return results


def _r0319_degree_completeEquipartiteGraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.degree_completeEquipartiteGraph
    # (completeEquipartiteGraph r t).degree v = (r - 1) * t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "completeEquipartiteGraph_r_t_degree", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("-", (OVar("r"), OLit(1))), OVar("t")))
            results.append((rhs, "Mathlib: SimpleGraph_degree_completeEquipartiteGraph"))
        except Exception:
            pass
    return results


def _r0320_card_edgeFinset_completeEquipartiteGraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.card_edgeFinset_completeEquipartiteGraph
    # #(completeEquipartiteGraph r t).edgeFinset = r.choose 2 * t ^ 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_completeEquipartiteGraph_r_t_edgeFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OOp("r_choose", (OLit(2),)), OOp("**", (OVar("t"), OLit(2)))))
            results.append((rhs, "Mathlib: SimpleGraph_card_edgeFinset_completeEquipartiteGraph"))
    except Exception:
        pass
    return results


def _r0321_chromaticNumber_eq_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_eq_two_iff
    # G.chromaticNumber = 2 ↔ G.IsBipartite ∧ G ≠ ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("!=", (OOp("and", (OOp("iff", (OLit(2), OVar("G_IsBipartite"))), OVar("G"))), OVar("bot")))
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_eq_two_iff"))
    except Exception:
        pass
    return results


def _r0322_chromaticNumber_pathGraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_pathGraph
    # (pathGraph n).chromaticNumber = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pathGraph_n_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(2)
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_pathGraph"))
    except Exception:
        pass
    return results


def _r0323_chromaticNumber_cycleGraph_of_even(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_cycleGraph_of_even
    # (cycleGraph n).chromaticNumber = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cycleGraph_n_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(2)
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_cycleGraph_of_even"))
    except Exception:
        pass
    return results


def _r0324_chromaticNumber_cycleGraph_of_odd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.chromaticNumber_cycleGraph_of_odd
    # (cycleGraph n).chromaticNumber = 3
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cycleGraph_n_chromaticNumber")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(3)
            results.append((rhs, "Mathlib: SimpleGraph_chromaticNumber_cycleGraph_of_odd"))
    except Exception:
        pass
    return results


def _r0325_reachable_eq_reflTransGen(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.reachable_eq_reflTransGen
    # G.Reachable = Relation.ReflTransGen G.Adj
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_Reachable")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Relation_ReflTransGen", (OVar("G_Adj"),))
            results.append((rhs, "Mathlib: SimpleGraph_reachable_eq_reflTransGen"))
    except Exception:
        pass
    return results


def _r0326_reachable_fromEdgeSet_eq_reflTransGen_to(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.reachable_fromEdgeSet_eq_reflTransGen_toRel
    # (fromEdgeSet s).Reachable = Relation.ReflTransGen (Sym2.ToRel s)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fromEdgeSet_s_Reachable")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Relation_ReflTransGen", (OOp("Sym2_ToRel", (OVar("s"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_reachable_fromEdgeSet_eq_reflTransGen_toRel"))
    except Exception:
        pass
    return results


def _r0327_reachable_fromEdgeSet_fromRel_eq_reflTra(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.reachable_fromEdgeSet_fromRel_eq_reflTransGen
    # (fromEdgeSet <| Sym2.fromRel sym).Reachable = Relation.ReflTransGen r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("fromEdgeSet_lt_pipe_Sym2_fromRel_sym_Reachable")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Relation_ReflTransGen", (OVar("r"),))
            results.append((rhs, "Mathlib: SimpleGraph_reachable_fromEdgeSet_fromRel_eq_reflTransGen"))
    except Exception:
        pass
    return results


def _r0328_reachable_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.reachable_bot
    # (⊥ : SimpleGraph V).Reachable u v ↔ u = v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("v")
            results.append((rhs, "Mathlib: SimpleGraph_reachable_bot"))
        except Exception:
            pass
    return results


def _r0329_preconnected_iff_reachable_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.preconnected_iff_reachable_eq_top
    # G.Preconnected ↔ G.Reachable = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: SimpleGraph_preconnected_iff_reachable_eq_top"))
        except Exception:
            pass
    return results


def _r0330_support_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Preconnected.support_eq_univ
    # G.support = Set.univ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: SimpleGraph_Preconnected_support_eq_univ"))
    except Exception:
        pass
    return results


def _r0331_sound(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.sound
    # G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_connectedComponentMk", 1)
    if args is not None:
        try:
            rhs = OOp("G_connectedComponentMk", (OVar("w"),))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_sound"))
        except Exception:
            pass
    return results


def _r0332_exact(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.exact
    # G.connectedComponentMk v = G.connectedComponentMk w → G.Reachable v w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_connectedComponentMk", 1)
    if args is not None:
        try:
            rhs = OOp("implies", (OOp("G_connectedComponentMk", (OVar("w"),)), OOp("G_Reachable", (args[0], OVar("w"),))))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_exact"))
        except Exception:
            pass
    return results


def _r0333_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.eq
    # G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_connectedComponentMk", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OOp("G_connectedComponentMk", (OVar("w"),)), OOp("G_Reachable", (args[0], OVar("w"),))))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_eq"))
        except Exception:
            pass
    return results


def _r0334_connectedComponentMk_eq_of_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    # G.connectedComponentMk v = G.connectedComponentMk w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_connectedComponentMk", 1)
    if args is not None:
        try:
            rhs = OOp("G_connectedComponentMk", (OVar("w"),))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_connectedComponentMk_eq_of_adj"))
        except Exception:
            pass
    return results


def _r0335_lift_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.lift_mk
    # ConnectedComponent.lift f h (G.connectedComponentMk v) = f v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ConnectedComponent_lift", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("v"),))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_lift_mk"))
        except Exception:
            pass
    return results


def _r0336_map_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.map_mk
    # (G.connectedComponentMk v).map φ = G'.connectedComponentMk (φ v)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_connectedComponentMk_v_map", 1)
    if args is not None:
        try:
            rhs = OOp("G_prime_connectedComponentMk", (OOp("phi", (OVar("v"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_map_mk"))
        except Exception:
            pass
    return results


def _r0337_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.map_id
    # C.map Hom.id = C
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "C_map", 1)
    if args is not None:
        try:
            rhs = OVar("C")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_map_id"))
        except Exception:
            pass
    return results


def _r0338_iso_image_comp_eq_map_iff_eq_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
    # G'.connectedComponentMk (φ v) = C.map ↑(↑φ : G ↪g G') ↔ G.connectedComponentMk v = C
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_prime_connectedComponentMk", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("C_map", (OVar("phi_colon_G_g_G_prime"),)), OOp("G_connectedComponentMk", (OVar("v"),)))), OVar("C")))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_iso_image_comp_eq_map_iff_eq_comp"))
        except Exception:
            pass
    return results


def _r0339_iso_inv_image_comp_eq_iff_eq_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map
    # G.connectedComponentMk (φ.symm v') = C ↔ G'.connectedComponentMk v' = C.map φ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_connectedComponentMk", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("C"), OOp("G_prime_connectedComponentMk", (OVar("v_prime"),)))), OOp("C_map", (OVar("phi"),))))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_iso_inv_image_comp_eq_iff_eq_map"))
        except Exception:
            pass
    return results


def _r0340_connectedComponentEquiv_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Iso.connectedComponentEquiv_refl
    # (Iso.refl : G ≃g G).connectedComponentEquiv = Equiv.refl _
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Iso_refl_colon_G_g_G_connectedComponentEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Equiv_refl", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: SimpleGraph_Iso_connectedComponentEquiv_refl"))
    except Exception:
        pass
    return results


def _r0341_connectedComponentEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Iso.connectedComponentEquiv_symm
    # φ.symm.connectedComponentEquiv = φ.connectedComponentEquiv.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_symm_connectedComponentEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("phi_connectedComponentEquiv_symm")
            results.append((rhs, "Mathlib: SimpleGraph_Iso_connectedComponentEquiv_symm"))
    except Exception:
        pass
    return results


def _r0342_connectedComponentEquiv_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Iso.connectedComponentEquiv_trans
    # connectedComponentEquiv (φ.trans φ') =     φ.connectedComponentEquiv.trans φ'.connectedComponentEquiv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "connectedComponentEquiv", 1)
    if args is not None:
        try:
            rhs = OOp("phi_connectedComponentEquiv_trans", (OVar("phi_prime_connectedComponentEquiv"),))
            results.append((rhs, "Mathlib: SimpleGraph_Iso_connectedComponentEquiv_trans"))
        except Exception:
            pass
    return results


def _r0343_supp_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.supp_inj
    # C.supp = D.supp ↔ C = D
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("C_supp")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("D_supp"), OVar("C"))), OVar("D")))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_supp_inj"))
    except Exception:
        pass
    return results


def _r0344_mem_supp_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.mem_supp_iff
    # v ∈ C.supp ↔ G.connectedComponentMk v = C
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("C")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_mem_supp_iff"))
        except Exception:
            pass
    return results


def _r0345_eq_of_common_vertex(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.eq_of_common_vertex
    # c = c'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("c_prime")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_eq_of_common_vertex"))
    except Exception:
        pass
    return results


def _r0346_biUnion_supp_eq_supp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.biUnion_supp_eq_supp
    # ⋃ (c : ConnectedComponent G) (_ : c.supp ⊆ c'.supp), c.supp = c'.supp
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OVar("c_prime_supp")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_biUnion_supp_eq_supp"))
        except Exception:
            pass
    return results


def _r0347_top_supp_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.top_supp_eq_univ
    # c.supp = (Set.univ : Set V)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c_supp")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("univ_set", (OVar("colon"), OVar("Set"), OVar("V"),))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_top_supp_eq_univ"))
    except Exception:
        pass
    return results


def _r0348_toSimpleGraph_hom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.toSimpleGraph_hom_apply
    # C.toSimpleGraph_hom u = u.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "C_toSimpleGraph_hom", 1)
    if args is not None:
        try:
            rhs = OVar("u_val")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_toSimpleGraph_hom_apply"))
        except Exception:
            pass
    return results


def _r0349_maximal_connected_induce_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.maximal_connected_induce_iff
    # Maximal (G.induce · |>.Connected) s ↔ ∃ C : G.ConnectedComponent, C.supp = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_maximal_connected_induce_iff"))
        except Exception:
            pass
    return results


def _r0350_iUnion_connectedComponentSupp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.iUnion_connectedComponentSupp
    # ⋃ c : G.ConnectedComponent, c.supp = Set.univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 4)
    if args is not None:
        try:
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: SimpleGraph_iUnion_connectedComponentSupp"))
        except Exception:
            pass
    return results


def _r0351_disjiUnion_supp_toFinset_eq_supp_toFinse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.disjiUnion_supp_toFinset_eq_supp_toFinset
    # .disjiUnion {c : ConnectedComponent G | c.supp ⊆ c'.supp} (fun c ↦ c.supp.toFinset)       (fun x _ y _ hxy ↦ by simpa us
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "disjiUnion", 3)
    if args is not None:
        try:
            rhs = OVar("c_prime_supp_toFinset")
            results.append((rhs, "Mathlib: SimpleGraph_disjiUnion_supp_toFinset_eq_supp_toFinset"))
        except Exception:
            pass
    return results


def _r0352_exists_inter_eq_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.Represents.exists_inter_eq_singleton
    # ∃ x, s ∩ c.supp = {x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_Represents_exists_inter_eq_singleton"))
        except Exception:
            pass
    return results


def _r0353_ncard_inter(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.Represents.ncard_inter
    # (s ∩ c.supp).ncard = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_inter_c_supp_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_Represents_ncard_inter"))
    except Exception:
        pass
    return results


def _r0354_ncard_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.Represents.ncard_eq
    # s.ncard = C.ncard
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("C_ncard")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_Represents_ncard_eq"))
    except Exception:
        pass
    return results


def _r0355_ncard_sdiff_of_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.Represents.ncard_sdiff_of_mem
    # (c.supp \\ s).ncard = c.supp.ncard - 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c_supp_bsl_s_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("c_supp_ncard"), OLit(1)))
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_Represents_ncard_sdiff_of_mem"))
    except Exception:
        pass
    return results


def _r0356_ncard_sdiff_of_notMem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.Represents.ncard_sdiff_of_notMem
    # (c.supp \\ s).ncard = c.supp.ncard
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c_supp_bsl_s_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("c_supp_ncard")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_Represents_ncard_sdiff_of_notMem"))
    except Exception:
        pass
    return results


def _r0357_degree_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.Preconnected.degree_zero_iff
    # H.degree v = 0 ↔ H.verts.Subsingleton
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_degree", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OVar("H_verts_Subsingleton")))
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_Preconnected_degree_zero_iff"))
        except Exception:
            pass
    return results


def _r0358_exists_verts_eq_connectedComponentSupp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Subgraph.Connected.exists_verts_eq_connectedComponentSupp
    # ∃ c : G.ConnectedComponent, H.verts = c.supp
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 4)
    if args is not None:
        try:
            rhs = OVar("c_supp")
            results.append((rhs, "Mathlib: SimpleGraph_Subgraph_Connected_exists_verts_eq_connectedComponentSupp"))
        except Exception:
            pass
    return results


def _r0359_coe_toSubgraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.coe_toSubgraph
    # C.toSubgraph.coe = C.toSimpleGraph
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("C_toSubgraph_coe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("C_toSimpleGraph")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_coe_toSubgraph"))
    except Exception:
        pass
    return results


def _r0360_maximal_subgraph_connected_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.ConnectedComponent.maximal_subgraph_connected_iff
    # Maximal Subgraph.Connected G' ↔ ∃ C : G.ConnectedComponent, C.toSubgraph = G'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("G_prime")
            results.append((rhs, "Mathlib: SimpleGraph_ConnectedComponent_maximal_subgraph_connected_iff"))
        except Exception:
            pass
    return results


def _r0361_toSubgraph_cons_nil_eq_subgraphOfAdj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.toSubgraph_cons_nil_eq_subgraphOfAdj
    # (cons h nil).toSubgraph = G.subgraphOfAdj h
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cons_h_nil_toSubgraph")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_subgraphOfAdj", (OVar("h"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_toSubgraph_cons_nil_eq_subgraphOfAdj"))
    except Exception:
        pass
    return results


def _r0362_verts_toSubgraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.verts_toSubgraph
    # p.toSubgraph.verts = { w | w ∈ p.support }
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_toSubgraph_verts")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("w_pipe_w_in_p_support")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_verts_toSubgraph"))
    except Exception:
        pass
    return results


def _r0363_edgeSet_toSubgraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.edgeSet_toSubgraph
    # p.toSubgraph.edgeSet = p.edgeSet
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_toSubgraph_edgeSet")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("p_edgeSet")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_edgeSet_toSubgraph"))
    except Exception:
        pass
    return results


def _r0364_toSubgraph_rotate(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.toSubgraph_rotate
    # (c.rotate u h).toSubgraph = c.toSubgraph
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c_rotate_u_h_toSubgraph")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("c_toSubgraph")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_toSubgraph_rotate"))
    except Exception:
        pass
    return results


def _r0365_toSubgraph_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.toSubgraph_map
    # (p.map f).toSubgraph = p.toSubgraph.map f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_map_f_toSubgraph")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("p_toSubgraph_map", (OVar("f"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_toSubgraph_map"))
    except Exception:
        pass
    return results


def _r0366_toSubgraph_adj_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.toSubgraph_adj_iff
    # w.toSubgraph.Adj u' v' ↔ ∃ i, s(w.getVert i, w.getVert (i + 1)) =       s(u', v') ∧ i < w.length
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("and", (OVar("s_u_prime_v_prime"), OVar("i"))), OVar("w_length")))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_toSubgraph_adj_iff"))
        except Exception:
            pass
    return results


def _r0367_map_mapToSubgraph_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.map_mapToSubgraph_hom
    # ∀ w : G.Walk u v, w.mapToSubgraph.map w.toSubgraph.hom = w   | nil => rfl   | cons _ w =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "w_mapToSubgraph_map", 1)
    if args is not None:
        try:
            rhs = OOp("w", (OVar("pipe"), OVar("nil"), OVar("eq_gt"), OVar("rfl"), OVar("pipe"), OVar("cons"), OVar("_unknown"), OVar("w"), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_map_mapToSubgraph_hom"))
        except Exception:
            pass
    return results


def _r0368_neighborSet_toSubgraph_startpoint(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.IsPath.neighborSet_toSubgraph_startpoint
    # p.toSubgraph.neighborSet u = {p.snd}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_toSubgraph_neighborSet", 1)
    if args is not None:
        try:
            rhs = OVar("p_snd")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_IsPath_neighborSet_toSubgraph_startpoint"))
        except Exception:
            pass
    return results


def _r0369_neighborSet_toSubgraph_endpoint(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.IsPath.neighborSet_toSubgraph_endpoint
    # p.toSubgraph.neighborSet v = {p.penultimate}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_toSubgraph_neighborSet", 1)
    if args is not None:
        try:
            rhs = OVar("p_penultimate")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_IsPath_neighborSet_toSubgraph_endpoint"))
        except Exception:
            pass
    return results


def _r0370_neighborSet_toSubgraph_internal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.IsPath.neighborSet_toSubgraph_internal
    # p.toSubgraph.neighborSet (p.getVert i) = {p.getVert (i - 1), p.getVert (i + 1)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_toSubgraph_neighborSet", 1)
    if args is not None:
        try:
            rhs = OVar("p_getVert_i_minus_1_p_getVert_i_plus_1")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_IsPath_neighborSet_toSubgraph_internal"))
        except Exception:
            pass
    return results


def _r0371_ncard_neighborSet_toSubgraph_internal_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.IsPath.ncard_neighborSet_toSubgraph_internal_eq_two
    # (p.toSubgraph.neighborSet (p.getVert i)).ncard = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_toSubgraph_neighborSet_p_getVert_i_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(2)
            results.append((rhs, "Mathlib: SimpleGraph_Walk_IsPath_ncard_neighborSet_toSubgraph_internal_eq_two"))
    except Exception:
        pass
    return results


def _r0372_snd_of_toSubgraph_adj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.IsPath.snd_of_toSubgraph_adj
    # p.snd = v'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("v_prime")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_IsPath_snd_of_toSubgraph_adj"))
    except Exception:
        pass
    return results


def _r0373_neighborSet_toSubgraph_endpoint(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.IsCycle.neighborSet_toSubgraph_endpoint
    # p.toSubgraph.neighborSet u = {p.snd, p.penultimate}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_toSubgraph_neighborSet", 1)
    if args is not None:
        try:
            rhs = OVar("p_snd_p_penultimate")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_IsCycle_neighborSet_toSubgraph_endpoint"))
        except Exception:
            pass
    return results


def _r0374_neighborSet_toSubgraph_internal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.IsCycle.neighborSet_toSubgraph_internal
    # p.toSubgraph.neighborSet (p.getVert i) = {p.getVert (i - 1), p.getVert (i + 1)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_toSubgraph_neighborSet", 1)
    if args is not None:
        try:
            rhs = OVar("p_getVert_i_minus_1_p_getVert_i_plus_1")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_IsCycle_neighborSet_toSubgraph_internal"))
        except Exception:
            pass
    return results


def _r0375_ncard_neighborSet_toSubgraph_eq_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two
    # (p.toSubgraph.neighborSet v).ncard = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_toSubgraph_neighborSet_v_ncard")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(2)
            results.append((rhs, "Mathlib: SimpleGraph_Walk_IsCycle_ncard_neighborSet_toSubgraph_eq_two"))
    except Exception:
        pass
    return results


def _r0376_exists_isCycle_snd_verts_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.IsCycle.exists_isCycle_snd_verts_eq
    # ∃ (p' : G.Walk v v), p'.IsCycle ∧ p'.snd = w ∧ p'.toSubgraph.verts = p.toSubgraph.verts
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "and", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OVar("w"), OVar("p_prime_toSubgraph_verts"))), OVar("p_toSubgraph_verts")))
            results.append((rhs, "Mathlib: SimpleGraph_Walk_IsCycle_exists_isCycle_snd_verts_eq"))
        except Exception:
            pass
    return results


def _r0377_exists_mem_support_mem_erase_mem_support(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty
    # ∃ x ∈ s, ∃ hx : x ∈ p.support, {t ∈ s.erase x | t ∈ (p.takeUntil x hx).support} = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty"))
        except Exception:
            pass
    return results


def _r0378_exists_mem_support_forall_mem_support_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Walk.exists_mem_support_forall_mem_support_imp_eq
    # ∃ x ∈ s, ∃ (hx : x ∈ p.support),       ∀ t ∈ s, t ∈ (p.takeUntil x hx).support → t = x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("t")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x")
            results.append((rhs, "Mathlib: SimpleGraph_Walk_exists_mem_support_forall_mem_support_imp_eq"))
    except Exception:
        pass
    return results


def _r0379_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.ext
    # (∀ a, f a = g a) → f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: SimpleGraph_Copy_ext"))
    except Exception:
        pass
    return results


def _r0380_coe_toHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.coe_toHom
    # ⇑f.toHom = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: SimpleGraph_Copy_coe_toHom"))
    except Exception:
        pass
    return results


def _r0381_coe_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.coe_id
    # ⇑(id G) = _root_.id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("id_G")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("root_id")
            results.append((rhs, "Mathlib: SimpleGraph_Copy_coe_id"))
    except Exception:
        pass
    return results


def _r0382_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.comp_apply
    # g.comp f a = g (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 2)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[1],)),))
            results.append((rhs, "Mathlib: SimpleGraph_Copy_comp_apply"))
        except Exception:
            pass
    return results


def _r0383_coe_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.coe_comp
    # ⇑(g.comp f) = g ∘ f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_comp_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("g"), OVar("f")))
            results.append((rhs, "Mathlib: SimpleGraph_Copy_coe_comp"))
    except Exception:
        pass
    return results


def _r0384_range_toSubgraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Copy.range_toSubgraph
    # .range (toSubgraph (A := A)) = {B' : B.Subgraph | Nonempty (A ≃g B'.coe)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OVar("B_prime_colon_B_Subgraph_pipe_Nonempty_A_g_B_prime_coe")
            results.append((rhs, "Mathlib: SimpleGraph_Copy_range_toSubgraph"))
        except Exception:
            pass
    return results


def _r0385_ext_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Dart.ext_iff
    # d₁ = d₂ ↔ d₁.toProd = d₂.toProd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("d_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("d_2"), OVar("d_1_toProd"))), OVar("d_2_toProd")))
            results.append((rhs, "Mathlib: SimpleGraph_Dart_ext_iff"))
    except Exception:
        pass
    return results


def _r0386_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Dart.ext
    # d₁ = d₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("d_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("d_2")
            results.append((rhs, "Mathlib: SimpleGraph_Dart_ext"))
    except Exception:
        pass
    return results


def _r0387_edge_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Dart.edge_mk
    # (Dart.mk p h).edge = s(p.1, p.2)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Dart_mk_p_h_edge")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_p_1_p_2")
            results.append((rhs, "Mathlib: SimpleGraph_Dart_edge_mk"))
    except Exception:
        pass
    return results


def _r0388_dart_edge_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dart_edge_eq_iff
    # ∀ d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("d_1_edge")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("d_2_edge"), OVar("d_1"))), OOp("==", (OOp("or", (OVar("d_2"), OVar("d_1"))), OVar("d_2_symm")))))
            results.append((rhs, "Mathlib: SimpleGraph_dart_edge_eq_iff"))
    except Exception:
        pass
    return results


def _r0389_dart_fst_fiber(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dart_fst_fiber
    # ({d : G.Dart | d.fst = v} : Finset _) = univ.image (G.dartOfNeighborSet v)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d_colon_G_Dart_pipe_d_fst_eq_v", 3)
    if args is not None:
        try:
            rhs = OOp("univ_image", (OOp("G_dartOfNeighborSet", (OVar("v"),)),))
            results.append((rhs, "Mathlib: SimpleGraph_dart_fst_fiber"))
        except Exception:
            pass
    return results


def _r0390_dart_fst_fiber_card_eq_degree(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dart_fst_fiber_card_eq_degree
    # #{d : G.Dart | d.fst = v} = G.degree v
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_d_colon_G_Dart_pipe_d_fst_eq_v")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("G_degree", (OVar("v"),))
            results.append((rhs, "Mathlib: SimpleGraph_dart_fst_fiber_card_eq_degree"))
    except Exception:
        pass
    return results


def _r0391_dart_card_eq_sum_degrees(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dart_card_eq_sum_degrees
    # Fintype.card G.Dart = ∑ v, G.degree v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fintype_card", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("v"), OVar("G_degree"), OVar("v"),))
            results.append((rhs, "Mathlib: SimpleGraph_dart_card_eq_sum_degrees"))
        except Exception:
            pass
    return results


def _r0392_edge_fiber(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.Dart.edge_fiber
    # ({d' : G.Dart | d'.edge = d.edge} : Finset _) = {d, d.symm}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d_prime_colon_G_Dart_pipe_d_prime_edge_eq_d_edge", 3)
    if args is not None:
        try:
            rhs = OVar("d_d_symm")
            results.append((rhs, "Mathlib: SimpleGraph_Dart_edge_fiber"))
        except Exception:
            pass
    return results


def _r0393_dart_edge_fiber_card(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dart_edge_fiber_card
    # #{d : G.Dart | d.edge = e} = 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_d_colon_G_Dart_pipe_d_edge_eq_e")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(2)
            results.append((rhs, "Mathlib: SimpleGraph_dart_edge_fiber_card"))
    except Exception:
        pass
    return results


def _r0394_dart_card_eq_twice_card_edges(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.dart_card_eq_twice_card_edges
    # Fintype.card G.Dart = 2 * #G.edgeFinset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fintype_card", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OLit(2), OVar("hash_G_edgeFinset")))
            results.append((rhs, "Mathlib: SimpleGraph_dart_card_eq_twice_card_edges"))
        except Exception:
            pass
    return results


def _r0395_sum_degrees_eq_twice_card_edges(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.sum_degrees_eq_twice_card_edges
    # ∑ v, G.degree v = 2 * #G.edgeFinset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OLit(2), OVar("hash_G_edgeFinset")))
            results.append((rhs, "Mathlib: SimpleGraph_sum_degrees_eq_twice_card_edges"))
        except Exception:
            pass
    return results


def _r0396_two_mul_card_edgeFinset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.two_mul_card_edgeFinset
    # 2 * #G.edgeFinset = #(univ.filter fun (x, y) ↦ G.Adj x y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("hash_univ_filter_fun_x_y_G_Adj_x_y")
            results.append((rhs, "Mathlib: SimpleGraph_two_mul_card_edgeFinset"))
        except Exception:
            pass
    return results


def _r0397_sum_degrees_support_eq_twice_card_edges(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.sum_degrees_support_eq_twice_card_edges
    # ∑ v ∈ G.support, G.degree v = 2 * #G.edgeFinset
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OLit(2), OVar("hash_G_edgeFinset")))
            results.append((rhs, "Mathlib: SimpleGraph_sum_degrees_support_eq_twice_card_edges"))
        except Exception:
            pass
    return results


def _r0398_deleteEdges_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.deleteEdges_empty
    # G.deleteEdges ∅ = G
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_deleteEdges", 1)
    if args is not None:
        try:
            rhs = OVar("G")
            results.append((rhs, "Mathlib: SimpleGraph_deleteEdges_empty"))
        except Exception:
            pass
    return results


def _r0399_deleteEdges_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SimpleGraph.deleteEdges_univ
    # G.deleteEdges Set.univ = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_deleteEdges", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: SimpleGraph_deleteEdges_univ"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_combinatorics rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "+", "-", "<=", "==", ">", "A", "C_compRight_f_get", "C_map", "C_map_phi_map", "C_pullback_f_get", "C_toSimpleGraph_hom", "ConnectedComponent_lift", "Disjoint", "Fintype_card", "G", "G_1_G_2_Adj", "G_Adj", "G_IsClique", "G_IsEdgeConnected", "G_IsEdgeReachable", "G_adjMatrix", "G_adjMatrix_a_pow_n", "G_adjMatrix_a_star_Function_const_a", "G_adjMatrix_a_star_G_adjMatrix_a", "G_adjMatrix_a_star_M", "G_adjMatrix_a_star_vec", "G_comap", "G_comap_g_comap", "G_connectedComponentMk", "G_connectedComponentMk_v_map", "G_deleteEdges", "G_deleteEdges_s_deleteEdges", "G_dist", "G_edgeSet", "G_induce", "G_map_f_IsClique", "G_neighborFinset", "G_neighborSet", "G_prime_Adj", "G_prime_connectedComponentMk", "G_support", "G_toTopEdgeLabeling_labelGraph", "G_universalVerts", "H_H_prime_neighborSet", "H_adjMatrix", "H_degree", "H_map", "List_mem_of_mem_tail",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_combinatorics axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_combinatorics rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_vertical_apply(term, ctx))
    results.extend(_r0001_compl_zero(term, ctx))
    results.extend(_r0002_adjMatrix_completeGraph_eq_of_one_sub_on(term, ctx))
    results.extend(_r0003_adjMatrix_mul_self_apply_self(term, ctx))
    results.extend(_r0004_completeGraph_eq_top(term, ctx))
    results.extend(_r0005_emptyGraph_eq_bot(term, ctx))
    results.extend(_r0006_mulCayley_union(term, ctx))
    results.extend(_r0007_map_comp(term, ctx))
    results.extend(_r0008_spanningCoe_toSubgraph(term, ctx))
    results.extend(_r0009_toSubgraph_append(term, ctx))
    results.extend(_r0010_toSubgraph_reverse(term, ctx))
    results.extend(_r0011_toHom_apply(term, ctx))
    results.extend(_r0012_coe_mk(term, ctx))
    results.extend(_r0013_coe_ofLE(term, ctx))
    results.extend(_r0014_ofLE_refl(term, ctx))
    results.extend(_r0015_ofLE_comp(term, ctx))
    results.extend(_r0016_symm_mk(term, ctx))
    results.extend(_r0017_edge_symm(term, ctx))
    results.extend(_r0018_edge_comp_symm(term, ctx))
    results.extend(_r0019_symm_symm(term, ctx))
    results.extend(_r0020_deleteEdges_edgeSet(term, ctx))
    results.extend(_r0021_deleteEdges_deleteEdges(term, ctx))
    results.extend(_r0022_deleteEdges_eq_inter_edgeSet(term, ctx))
    results.extend(_r0023_deleteEdges_sdiff_eq_of_le(term, ctx))
    results.extend(_r0024_edgeFinset_deleteEdges(term, ctx))
    results.extend(_r0025_deleteEdges_fromEdgeSet(term, ctx))
    results.extend(_r0026_deleteEdges_eq_bot(term, ctx))
    results.extend(_r0027_eccent_top(term, ctx))
    results.extend(_r0028_get_pullback(term, ctx))
    results.extend(_r0029_compRight_get(term, ctx))
    results.extend(_r0030_toTopEdgeLabeling_labelGraph_compl(term, ctx))
    results.extend(_r0031_labelGraph_toTopEdgeLabeling(term, ctx))
    results.extend(_r0032_exists_eq_mk(term, ctx))
    results.extend(_r0033_turanGraph_eq_top(term, ctx))
    results.extend(_r0034_edgeFinset_sup(term, ctx))
    results.extend(_r0035_edgeFinset_inf(term, ctx))
    results.extend(_r0036_edgeFinset_sdiff(term, ctx))
    results.extend(_r0037_edgeFinset_eq_empty(term, ctx))
    results.extend(_r0038_edgeFinset_card(term, ctx))
    results.extend(_r0039_edgeSet_univ_card(term, ctx))
    results.extend(_r0040_coe_sup(term, ctx))
    results.extend(_r0041_coe_inf(term, ctx))
    results.extend(_r0042_coe_sdiff(term, ctx))
    results.extend(_r0043_coe_compl(term, ctx))
    results.extend(_r0044_coe_hnot(term, ctx))
    results.extend(_r0045_coe_himp(term, ctx))
    results.extend(_r0046_coe_sSup(term, ctx))
    results.extend(_r0047_coe_sInf(term, ctx))
    results.extend(_r0048_coe_iSup(term, ctx))
    results.extend(_r0049_coe_iInf(term, ctx))
    results.extend(_r0050_hasseDualIso_symm_apply(term, ctx))
    results.extend(_r0051_comap_id(term, ctx))
    results.extend(_r0052_comap_comap(term, ctx))
    results.extend(_r0053_comap_top(term, ctx))
    results.extend(_r0054_simpleGraph_trans(term, ctx))
    results.extend(_r0055_symm_simpleGraph(term, ctx))
    results.extend(_r0056_induce_bot(term, ctx))
    results.extend(_r0057_spanningCoe_induce_univ(term, ctx))
    results.extend(_r0058_ofLE_apply(term, ctx))
    results.extend(_r0059_comp_comap_ofLE(term, ctx))
    results.extend(_r0060_comap_eq(term, ctx))
    results.extend(_r0061_ne_bot(term, ctx))
    results.extend(_r0062_edges_cycleBypass_subset(term, ctx))
    results.extend(_r0063_edgeSet_coe(term, ctx))
    results.extend(_r0064_image_coe_edgeSet_coe(term, ctx))
    results.extend(_r0065_verts_sup(term, ctx))
    results.extend(_r0066_verts_inf(term, ctx))
    results.extend(_r0067_verts_top(term, ctx))
    results.extend(_r0068_verts_bot(term, ctx))
    results.extend(_r0069_eq_bot_iff_verts_eq_empty(term, ctx))
    results.extend(_r0070_verts_sInf(term, ctx))
    results.extend(_r0071_verts_iSup(term, ctx))
    results.extend(_r0072_verts_iInf(term, ctx))
    results.extend(_r0073_coe_bot(term, ctx))
    results.extend(_r0074_neighborSet_sup(term, ctx))
    results.extend(_r0075_neighborSet_inf(term, ctx))
    results.extend(_r0076_neighborSet_top(term, ctx))
    results.extend(_r0077_neighborSet_bot(term, ctx))
    results.extend(_r0078_neighborSet_sSup(term, ctx))
    results.extend(_r0079_neighborSet_iInf(term, ctx))
    results.extend(_r0080_edgeSet_top(term, ctx))
    results.extend(_r0081_edgeSet_bot(term, ctx))
    results.extend(_r0082_edgeSet_inf(term, ctx))
    results.extend(_r0083_edgeSet_sup(term, ctx))
    results.extend(_r0084_edgeSet_sSup(term, ctx))
    results.extend(_r0085_edgeSet_iInf(term, ctx))
    results.extend(_r0086_spanningCoe_bot(term, ctx))
    results.extend(_r0087_map_comp(term, ctx))
    results.extend(_r0088_edgeSet_map(term, ctx))
    results.extend(_r0089_sumRight_sum(term, ctx))
    results.extend(_r0090_sum_sumLeft_sumRight(term, ctx))
    results.extend(_r0091_exists_of_universalVerts(term, ctx))
    results.extend(_r0092_length_cons(term, ctx))
    results.extend(_r0093_eq_of_length_eq_zero(term, ctx))
    results.extend(_r0094_length_eq_zero_iff(term, ctx))
    results.extend(_r0095_support_cons(term, ctx))
    results.extend(_r0096_head_support(term, ctx))
    results.extend(_r0097_getLast_support(term, ctx))
    results.extend(_r0098_support_eq_cons(term, ctx))
    results.extend(_r0099_mem_support_iff(term, ctx))
    results.extend(_r0100_darts_cons(term, ctx))
    results.extend(_r0101_cons_map_snd_darts(term, ctx))
    results.extend(_r0102_edges_cons(term, ctx))
    results.extend(_r0103_length_support(term, ctx))
    results.extend(_r0104_length_darts(term, ctx))
    results.extend(_r0105_length_edges(term, ctx))
    results.extend(_r0106_fst_darts_getElem(term, ctx))
    results.extend(_r0107_support_getElem_length(term, ctx))
    results.extend(_r0108_edgeSet_nil(term, ctx))
    results.extend(_r0109_edgeSet_cons(term, ctx))
    results.extend(_r0110_coe_edges_toFinset(term, ctx))
    results.extend(_r0111_edges_eq_nil(term, ctx))
    results.extend(_r0112_nil_iff_length_eq(term, ctx))
    results.extend(_r0113_takeUntil_cons(term, ctx))
    results.extend(_r0114_nil_takeUntil(term, ctx))
    results.extend(_r0115_takeUntil_eq_take(term, ctx))
    results.extend(_r0116_rotate_eq_nil(term, ctx))
    results.extend(_r0117_map_cons(term, ctx))
    results.extend(_r0118_map_copy(term, ctx))
    results.extend(_r0119_map_map(term, ctx))
    results.extend(_r0120_length_map(term, ctx))
    results.extend(_r0121_map_append(term, ctx))
    results.extend(_r0122_support_map(term, ctx))
    results.extend(_r0123_darts_map(term, ctx))
    results.extend(_r0124_edges_map(term, ctx))
    results.extend(_r0125_edgeSet_map(term, ctx))
    results.extend(_r0126_getVert_map(term, ctx))
    results.extend(_r0127_edgeSet_transfer(term, ctx))
    results.extend(_r0128_support_transfer(term, ctx))
    results.extend(_r0129_length_transfer(term, ctx))
    results.extend(_r0130_transfer_transfer(term, ctx))
    results.extend(_r0131_induce_cons(term, ctx))
    results.extend(_r0132_support_induce(term, ctx))
    results.extend(_r0133_toDeleteEdges_cons(term, ctx))
    results.extend(_r0134_copy_copy(term, ctx))
    results.extend(_r0135_cons_nil_append(term, ctx))
    results.extend(_r0136_nil_append(term, ctx))
    results.extend(_r0137_append_nil(term, ctx))
    results.extend(_r0138_append_assoc(term, ctx))
    results.extend(_r0139_append_concat(term, ctx))
    results.extend(_r0140_reverse_singleton(term, ctx))
    results.extend(_r0141_cons_reverseAux(term, ctx))
    results.extend(_r0142_append_reverseAux(term, ctx))
    results.extend(_r0143_reverse_copy(term, ctx))
    results.extend(_r0144_reverse_concat(term, ctx))
    results.extend(_r0145_reverse_reverse(term, ctx))
    results.extend(_r0146_length_reverseAux(term, ctx))
    results.extend(_r0147_getVert_append(term, ctx))
    results.extend(_r0148_concatRec_concat(term, ctx))
    results.extend(_r0149_support_append_eq_support_dropLast_appen(term, ctx))
    results.extend(_r0150_edges_copy(term, ctx))
    results.extend(_r0151_edges_reverse(term, ctx))
    results.extend(_r0152_edgeSet_concat(term, ctx))
    results.extend(_r0153_edgeSet_append(term, ctx))
    results.extend(_r0154_take_length(term, ctx))
    results.extend(_r0155_snd_reverse(term, ctx))
    results.extend(_r0156_penultimate_reverse(term, ctx))
    results.extend(_r0157_tail_cons_nil(term, ctx))
    results.extend(_r0158_tail_cons(term, ctx))
    results.extend(_r0159_dropLast_cons_nil(term, ctx))
    results.extend(_r0160_dropLast_cons_cons(term, ctx))
    results.extend(_r0161_dropLast_cons_of_not_nil(term, ctx))
    results.extend(_r0162_support_dropLast_concat(term, ctx))
    results.extend(_r0163_length_dropLast_add_one(term, ctx))
    results.extend(_r0164_getVert_mem_tail_support(term, ctx))
    results.extend(_r0165_getVert_nil(term, ctx))
    results.extend(_r0166_getVert_of_length_le(term, ctx))
    results.extend(_r0167_getVert_cons(term, ctx))
    results.extend(_r0168_snd_cons(term, ctx))
    results.extend(_r0169_penultimate_cons_nil(term, ctx))
    results.extend(_r0170_penultimate_cons_cons(term, ctx))
    results.extend(_r0171_penultimate_cons_of_not_nil(term, ctx))
    results.extend(_r0172_getLast_darts_eq_lastDart(term, ctx))
    results.extend(_r0173_binomialRandom_one(term, ctx))
    results.extend(_r0174_toSubspaceUnit_isMono(term, ctx))
    results.extend(_r0175_toSubspace_isMono(term, ctx))
    results.extend(_r0176_adj_comm(term, ctx))
    results.extend(_r0177_adj_congr_of_sym2(term, ctx))
    results.extend(_r0178_sInf_adj(term, ctx))
    results.extend(_r0179_iSup_adj(term, ctx))
    results.extend(_r0180_iInf_adj(term, ctx))
    results.extend(_r0181_sInf_adj_of_nonempty(term, ctx))
    results.extend(_r0182_bot_adj(term, ctx))
    results.extend(_r0183_isClique_insert_of_notMem(term, ctx))
    results.extend(_r0184_isEdgeReachable_one(term, ctx))
    results.extend(_r0185_isEdgeConnected_one(term, ctx))
    results.extend(_r0186_mem_edges_toSubgraph(term, ctx))
    results.extend(_r0187_deleteEdges_le_iff(term, ctx))
    results.extend(_r0188_edgeFinset_subset_edgeFinset(term, ctx))
    results.extend(_r0189_edgeFinset_ssubset_edgeFinset(term, ctx))
    results.extend(_r0190_disjoint_edgeFinset(term, ctx))
    results.extend(_r0191_edgeFinset_nonempty(term, ctx))
    results.extend(_r0192_isHamiltonianCycle_isCycle_and_isHamilto(term, ctx))
    results.extend(_r0193_map_adj_iff(term, ctx))
    results.extend(_r0194_map_mem_edgeSet_iff(term, ctx))
    results.extend(_r0195_isCircuit_rotate(term, ctx))
    results.extend(_r0196_isCycle_rotate(term, ctx))
    results.extend(_r0197_inf_adj(term, ctx))
    results.extend(_r0198_top_adj(term, ctx))
    results.extend(_r0199_sInf_adj(term, ctx))
    results.extend(_r0200_iSup_adj(term, ctx))
    results.extend(_r0201_iInf_adj(term, ctx))
    results.extend(_r0202_sInf_adj_of_nonempty(term, ctx))
    results.extend(_r0203_map_le_iff_le_comap(term, ctx))
    results.extend(_r0204_in_0_1_iff(term, ctx))
    results.extend(_r0205_in_1_0_iff(term, ctx))
    results.extend(_r0206_in_0_2_iff(term, ctx))
    results.extend(_r0207_in_2_0_iff(term, ctx))
    results.extend(_r0208_in_1_2_iff(term, ctx))
    results.extend(_r0209_in_2_1_iff(term, ctx))
    results.extend(_r0210_exists_length_eq_one_iff(term, ctx))
    results.extend(_r0211_mem_darts_iff_infix_support(term, ctx))
    results.extend(_r0212_nil_append_iff(term, ctx))
    results.extend(_r0213_coe_apply(term, ctx))
    results.extend(_r0214_apply_def(term, ctx))
    results.extend(_r0215_apply_inl(term, ctx))
    results.extend(_r0216_apply_inr(term, ctx))
    results.extend(_r0217_reindex_apply(term, ctx))
    results.extend(_r0218_coe_apply(term, ctx))
    results.extend(_r0219_toSubspaceUnit_apply(term, ctx))
    results.extend(_r0220_toSubspace_apply(term, ctx))
    results.extend(_r0221_apply_def(term, ctx))
    results.extend(_r0222_apply_none(term, ctx))
    results.extend(_r0223_apply_some(term, ctx))
    results.extend(_r0224_map_apply(term, ctx))
    results.extend(_r0225_horizontal_apply(term, ctx))
    results.extend(_r0226_prod_apply(term, ctx))
    results.extend(_r0227_diagonal_apply(term, ctx))
    results.extend(_r0228_exists_mono_homothetic_copy(term, ctx))
    results.extend(_r0229_path_unique(term, ctx))
    results.extend(_r0230_isAcyclic_iff_path_unique(term, ctx))
    results.extend(_r0231_path_concat(term, ctx))
    results.extend(_r0232_card_edgeFinset(term, ctx))
    results.extend(_r0233_isAcyclic_sup_fromEdgeSet_iff(term, ctx))
    results.extend(_r0234_reachable_eq_of_maximal_isAcyclic(term, ctx))
    results.extend(_r0235_maximal_isAcyclic_iff_reachable_eq(term, ctx))
    results.extend(_r0236_exists_isAcyclic_reachable_eq_le_of_le_o(term, ctx))
    results.extend(_r0237_exists_isAcyclic_reachable_eq_le(term, ctx))
    results.extend(_r0238_isTree_iff_connected_and_card(term, ctx))
    results.extend(_r0239_minDegree_eq_one_of_nontrivial(term, ctx))
    results.extend(_r0240_exists_vert_degree_one_of_nontrivial(term, ctx))
    results.extend(_r0241_dist_eq_dist_add_one_of_adj_of_reachable(term, ctx))
    results.extend(_r0242_dist_eq_dist_add_one_of_adj(term, ctx))
    results.extend(_r0243_adjMatrix_apply(term, ctx))
    results.extend(_r0244_adjMatrix_bot(term, ctx))
    results.extend(_r0245_adjMatrix_top(term, ctx))
    results.extend(_r0246_transpose_adjMatrix(term, ctx))
    results.extend(_r0247_diag_adjMatrix(term, ctx))
    results.extend(_r0248_toGraph_adjMatrix_eq(term, ctx))
    results.extend(_r0249_compl_adjMatrix_eq_adjMatrix_compl(term, ctx))
    results.extend(_r0250_adjMatrix_add_adjMatrix_eq_adjMatrix_com(term, ctx))
    results.extend(_r0251_adjMatrix_add_compl_adjMatrix_eq_adjMatr(term, ctx))
    results.extend(_r0252_one_add_adjMatrix_add_compl_adjMatrix_eq(term, ctx))
    results.extend(_r0253_compl_adjMatrix_completeGraph(term, ctx))
    results.extend(_r0254_compl_zero_eq_of_one_sub_one(term, ctx))
    results.extend(_r0255_compl_of_one_sub_one(term, ctx))
    results.extend(_r0256_adjMatrix_hadamard_self(term, ctx))
    results.extend(_r0257_adjMatrix_dotProduct(term, ctx))
    results.extend(_r0258_dotProduct_adjMatrix(term, ctx))
    results.extend(_r0259_adjMatrix_mulVec_apply(term, ctx))
    results.extend(_r0260_adjMatrix_vecMul_apply(term, ctx))
    results.extend(_r0261_adjMatrix_mul_apply(term, ctx))
    results.extend(_r0262_mul_adjMatrix_apply(term, ctx))
    results.extend(_r0263_trace_adjMatrix(term, ctx))
    results.extend(_r0264_natCast_card_dart_eq_dotProduct(term, ctx))
    results.extend(_r0265_adjMatrix_mulVec_const_apply(term, ctx))
    results.extend(_r0266_adjMatrix_mulVec_const_apply_of_regular(term, ctx))
    results.extend(_r0267_adjMatrix_pow_apply_eq_card_walk(term, ctx))
    results.extend(_r0268_dotProduct_mulVec_adjMatrix(term, ctx))
    results.extend(_r0269_adj_inj(term, ctx))
    results.extend(_r0270_eq_bot_iff_forall_not_adj(term, ctx))
    results.extend(_r0271_eq_top_iff_forall_ne_adj(term, ctx))
    results.extend(_r0272_isBipartiteWith_neighborSet(term, ctx))
    results.extend(_r0273_isBipartiteWith_neighborFinset(term, ctx))
    results.extend(_r0274_isBipartiteWith_bipartiteAbove(term, ctx))
    results.extend(_r0275_isBipartiteWith_bipartiteBelow(term, ctx))
    results.extend(_r0276_mulCayley_empty(term, ctx))
    results.extend(_r0277_circulantGraph_eq_erase_zero(term, ctx))
    results.extend(_r0278_circulantGraph_eq_symm(term, ctx))
    results.extend(_r0279_cycleGraph_eq_circulantGraph(term, ctx))
    results.extend(_r0280_cycleGraph_zero_eq_bot(term, ctx))
    results.extend(_r0281_cycleGraph_one_eq_bot(term, ctx))
    results.extend(_r0282_cycleGraph_zero_eq_top(term, ctx))
    results.extend(_r0283_cycleGraph_one_eq_top(term, ctx))
    results.extend(_r0284_cycleGraph_two_eq_top(term, ctx))
    results.extend(_r0285_cycleGraph_three_eq_top(term, ctx))
    results.extend(_r0286_cycleGraph_adj(term, ctx))
    results.extend(_r0287_cycleGraph_neighborSet(term, ctx))
    results.extend(_r0288_cycleGraph_neighborFinset(term, ctx))
    results.extend(_r0289_cycleGraph_degree_two_le(term, ctx))
    results.extend(_r0290_cycleGraph_degree_three_le(term, ctx))
    results.extend(_r0291_length_cycle_cons(term, ctx))
    results.extend(_r0292_length_cycle(term, ctx))
    results.extend(_r0293_isClique_iff_induce_eq(term, ctx))
    results.extend(_r0294_isClique_map_iff_of_nontrivial(term, ctx))
    results.extend(_r0295_isClique_map_iff(term, ctx))
    results.extend(_r0296_isClique_map_finset_iff_of_nontrivial(term, ctx))
    results.extend(_r0297_isClique_map_finset_iff(term, ctx))
    results.extend(_r0298_chromaticNumber_eq_biInf(term, ctx))
    results.extend(_r0299_chromaticNumber_eq_iInf(term, ctx))
    results.extend(_r0300_chromaticNumber_eq_sInf(term, ctx))
    results.extend(_r0301_coe_recolorOfEmbedding(term, ctx))
    results.extend(_r0302_coe_recolorOfEquiv(term, ctx))
    results.extend(_r0303_coe_recolorOfCardLE(term, ctx))
    results.extend(_r0304_chromaticNumber_eq_iff_colorable_not_col(term, ctx))
    results.extend(_r0305_chromaticNumber_eq_zero_of_isEmpty(term, ctx))
    results.extend(_r0306_chromaticNumber_eq_card_iff_forall_surje(term, ctx))
    results.extend(_r0307_chromaticNumber_eq_iff_forall_surjective(term, ctx))
    results.extend(_r0308_chromaticNumber_bot(term, ctx))
    results.extend(_r0309_chromaticNumber_top(term, ctx))
    results.extend(_r0310_chromaticNumber_top_eq_top_of_infinite(term, ctx))
    results.extend(_r0311_eq_top_of_chromaticNumber_eq_card(term, ctx))
    results.extend(_r0312_chromaticNumber_eq_card_iff(term, ctx))
    results.extend(_r0313_chromaticNumber_eq_one_iff(term, ctx))
    results.extend(_r0314_chromaticNumber(term, ctx))
    results.extend(_r0315_chromaticNumber(term, ctx))
    results.extend(_r0316_completeEquipartiteGraph_eq_bot_iff(term, ctx))
    results.extend(_r0317_neighborSet_completeEquipartiteGraph(term, ctx))
    results.extend(_r0318_neighborFinset_completeEquipartiteGraph(term, ctx))
    results.extend(_r0319_degree_completeEquipartiteGraph(term, ctx))
    results.extend(_r0320_card_edgeFinset_completeEquipartiteGraph(term, ctx))
    results.extend(_r0321_chromaticNumber_eq_two_iff(term, ctx))
    results.extend(_r0322_chromaticNumber_pathGraph(term, ctx))
    results.extend(_r0323_chromaticNumber_cycleGraph_of_even(term, ctx))
    results.extend(_r0324_chromaticNumber_cycleGraph_of_odd(term, ctx))
    results.extend(_r0325_reachable_eq_reflTransGen(term, ctx))
    results.extend(_r0326_reachable_fromEdgeSet_eq_reflTransGen_to(term, ctx))
    results.extend(_r0327_reachable_fromEdgeSet_fromRel_eq_reflTra(term, ctx))
    results.extend(_r0328_reachable_bot(term, ctx))
    results.extend(_r0329_preconnected_iff_reachable_eq_top(term, ctx))
    results.extend(_r0330_support_eq_univ(term, ctx))
    results.extend(_r0331_sound(term, ctx))
    results.extend(_r0332_exact(term, ctx))
    results.extend(_r0333_eq(term, ctx))
    results.extend(_r0334_connectedComponentMk_eq_of_adj(term, ctx))
    results.extend(_r0335_lift_mk(term, ctx))
    results.extend(_r0336_map_mk(term, ctx))
    results.extend(_r0337_map_id(term, ctx))
    results.extend(_r0338_iso_image_comp_eq_map_iff_eq_comp(term, ctx))
    results.extend(_r0339_iso_inv_image_comp_eq_iff_eq_map(term, ctx))
    results.extend(_r0340_connectedComponentEquiv_refl(term, ctx))
    results.extend(_r0341_connectedComponentEquiv_symm(term, ctx))
    results.extend(_r0342_connectedComponentEquiv_trans(term, ctx))
    results.extend(_r0343_supp_inj(term, ctx))
    results.extend(_r0344_mem_supp_iff(term, ctx))
    results.extend(_r0345_eq_of_common_vertex(term, ctx))
    results.extend(_r0346_biUnion_supp_eq_supp(term, ctx))
    results.extend(_r0347_top_supp_eq_univ(term, ctx))
    results.extend(_r0348_toSimpleGraph_hom_apply(term, ctx))
    results.extend(_r0349_maximal_connected_induce_iff(term, ctx))
    results.extend(_r0350_iUnion_connectedComponentSupp(term, ctx))
    results.extend(_r0351_disjiUnion_supp_toFinset_eq_supp_toFinse(term, ctx))
    results.extend(_r0352_exists_inter_eq_singleton(term, ctx))
    results.extend(_r0353_ncard_inter(term, ctx))
    results.extend(_r0354_ncard_eq(term, ctx))
    results.extend(_r0355_ncard_sdiff_of_mem(term, ctx))
    results.extend(_r0356_ncard_sdiff_of_notMem(term, ctx))
    results.extend(_r0357_degree_zero_iff(term, ctx))
    results.extend(_r0358_exists_verts_eq_connectedComponentSupp(term, ctx))
    results.extend(_r0359_coe_toSubgraph(term, ctx))
    results.extend(_r0360_maximal_subgraph_connected_iff(term, ctx))
    results.extend(_r0361_toSubgraph_cons_nil_eq_subgraphOfAdj(term, ctx))
    results.extend(_r0362_verts_toSubgraph(term, ctx))
    results.extend(_r0363_edgeSet_toSubgraph(term, ctx))
    results.extend(_r0364_toSubgraph_rotate(term, ctx))
    results.extend(_r0365_toSubgraph_map(term, ctx))
    results.extend(_r0366_toSubgraph_adj_iff(term, ctx))
    results.extend(_r0367_map_mapToSubgraph_hom(term, ctx))
    results.extend(_r0368_neighborSet_toSubgraph_startpoint(term, ctx))
    results.extend(_r0369_neighborSet_toSubgraph_endpoint(term, ctx))
    results.extend(_r0370_neighborSet_toSubgraph_internal(term, ctx))
    results.extend(_r0371_ncard_neighborSet_toSubgraph_internal_eq(term, ctx))
    results.extend(_r0372_snd_of_toSubgraph_adj(term, ctx))
    results.extend(_r0373_neighborSet_toSubgraph_endpoint(term, ctx))
    results.extend(_r0374_neighborSet_toSubgraph_internal(term, ctx))
    results.extend(_r0375_ncard_neighborSet_toSubgraph_eq_two(term, ctx))
    results.extend(_r0376_exists_isCycle_snd_verts_eq(term, ctx))
    results.extend(_r0377_exists_mem_support_mem_erase_mem_support(term, ctx))
    results.extend(_r0378_exists_mem_support_forall_mem_support_im(term, ctx))
    results.extend(_r0379_ext(term, ctx))
    results.extend(_r0380_coe_toHom(term, ctx))
    results.extend(_r0381_coe_id(term, ctx))
    results.extend(_r0382_comp_apply(term, ctx))
    results.extend(_r0383_coe_comp(term, ctx))
    results.extend(_r0384_range_toSubgraph(term, ctx))
    results.extend(_r0385_ext_iff(term, ctx))
    results.extend(_r0386_ext(term, ctx))
    results.extend(_r0387_edge_mk(term, ctx))
    results.extend(_r0388_dart_edge_eq_iff(term, ctx))
    results.extend(_r0389_dart_fst_fiber(term, ctx))
    results.extend(_r0390_dart_fst_fiber_card_eq_degree(term, ctx))
    results.extend(_r0391_dart_card_eq_sum_degrees(term, ctx))
    results.extend(_r0392_edge_fiber(term, ctx))
    results.extend(_r0393_dart_edge_fiber_card(term, ctx))
    results.extend(_r0394_dart_card_eq_twice_card_edges(term, ctx))
    results.extend(_r0395_sum_degrees_eq_twice_card_edges(term, ctx))
    results.extend(_r0396_two_mul_card_edgeFinset(term, ctx))
    results.extend(_r0397_sum_degrees_support_eq_twice_card_edges(term, ctx))
    results.extend(_r0398_deleteEdges_empty(term, ctx))
    results.extend(_r0399_deleteEdges_univ(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_combinatorics rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("SimpleGraph_LocallyLinear_le_ruzsaSzemerediNumber", "hash_G_cliqueFinset_3_le_ruzsaSzemerediNumber_a", "Not an equality or iff proposition"),
    ("Combinatorics_Subspace_coe_injective", "Injective_colon_Subspace_eta_a_i_to_eta_to_a_to_i_to_a", "Not an equality or iff proposition"),
    ("Combinatorics_Subspace_IsMono_reindex", "l_reindex_eeta_ea_ei_IsMono_fun_x_C_lt_pipe_ea_symm_comp_x_comp_ei", "Not an equality or iff proposition"),
    ("Combinatorics_Line_coe_injective", "Injective_colon_Line_a_i_to_a_to_i_to_a", "Not an equality or iff proposition"),
    ("Combinatorics_Line_exists_mono_in_high_dimension", "_unknown", "Empty proposition"),
    ("Combinatorics_Line_exists_mono_in_high_dimension", "exists_i_colon_Type_colon_Fintype_i_forall_C_colon_i_to_a_to_k_exists_l_colon_Line_a_i_l_IsMono_C", "Not an equality or iff proposition"),
    ("Combinatorics_Subspace_exists_mono_in_high_dimension", "exists_i_colon_Type_colon_Fintype_i_forall_C_colon_i_to_a_to_k_exists_l_colon_Subspace_eta_a_i_l_IsMono", "Not an equality or iff proposition"),
    ("Combinatorics_Subspace_exists_mono_in_high_dimension_fin", "exists_n_forall_C_colon_Fin_n_to_a_to_k_exists_l_colon_Subspace_eta_a_Fin_n_l_IsMono_C", "Not an equality or iff proposition"),
    ("SimpleGraph_isAcyclic_bot", "IsAcyclic_bot_colon_SimpleGraph_V", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_comap", "G_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_embedding", "G_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_of_map", "G_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_of_comap", "G_comap_f_pipe_gt_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_induce", "G_induce_s_pipe_gt_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_subgraph", "H_coe_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_anti", "G_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_Walk_exists_mem_contains_edges_of_directed", "exists_H_in_Hs_forall_e_in_p_edges_e_in_H_edgeSet", "Not an equality or iff proposition"),
    ("SimpleGraph_isAcyclic_sSup_of_isAcyclic_directedOn", "IsAcyclic_sSup_Hs", "Not an equality or iff proposition"),
    ("SimpleGraph_exists_maximal_isAcyclic_of_le_isAcyclic", "exists_H_prime_colon_SimpleGraph_V_H_le_H_prime_and_Maximal_fun_H_eq_gt_H_le_G_and_H_IsAcyclic_H_prime", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_isTree_connectedComponent", "c_toSimpleGraph_IsTree", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_of_card_le_two", "G_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_of_subsingleton", "G_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_Subgraph_isAcyclic_coe_bot", "bot_colon_G_Subgraph_coe_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_IsTree_of_subsingleton", "G_IsTree", "Not an equality or iff proposition"),
    ("SimpleGraph_IsTree_coe_singletonSubgraph", "G_singletonSubgraph_v_pipe_gt_coe_IsTree", "Not an equality or iff proposition"),
    ("SimpleGraph_IsTree_coe_subgraphOfAdj", "G_subgraphOfAdj_h_pipe_gt_coe_IsTree", "Not an equality or iff proposition"),
    ("SimpleGraph_isAcyclic_of_path_unique", "G_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_mem_support_of_ne_mem_support_of_adj_of_isPath", "w_in_p_support", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_ne_mem_support_of_support_of_adj_of_isPath", "v_notin_q_support", "Not an equality or iff proposition"),
    ("SimpleGraph_IsTree_existsUnique_path", "forall_v_w_exists_bang_p_colon_G_Walk_v_w_p_IsPath", "Not an equality or iff proposition"),
    ("SimpleGraph_isTree_of_minimal_connected", "IsTree_G", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_sup_edge_of_not_reachable", "G_edge_u_v_IsAcyclic", "Not an equality or iff proposition"),
    ("SimpleGraph_Connected_exists_isTree_le_of_le_of_isAcyclic", "exists_F_colon_SimpleGraph_V_H_le_F_and_F_le_G_and_F_IsTree", "Not an equality or iff proposition"),
    ("SimpleGraph_Connected_exists_isTree_le", "exists_T_le_G_IsTree_T", "Not an equality or iff proposition"),
    ("SimpleGraph_Connected_card_vert_le_card_edgeSet_add_one", "Nat_card_V_le_Nat_card_G_edgeSet_plus_1", "Not an equality or iff proposition"),
    ("SimpleGraph_Connected_induce_compl_singleton_of_degree_eq_one", "G_induce_v_Connected", "Not an equality or iff proposition"),
    ("SimpleGraph_Connected_exists_connected_induce_compl_singleton_of_finite_nontrivial", "exists_v_colon_V_G_induce_v_Connected", "Not an equality or iff proposition"),
    ("SimpleGraph_Connected_exists_preconnected_induce_compl_singleton_of_finite", "exists_v_colon_V_G_induce_v_Preconnected", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_dist_ne_of_adj", "G_dist_u_v_ne_G_dist_u_w", "Not an equality or iff proposition"),
    ("SimpleGraph_IsTree_dist_ne_of_adj", "G_dist_u_v_ne_G_dist_u_w", "Not an equality or iff proposition"),
    ("SimpleGraph_IsTree_isBipartite", "G_IsBipartite", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_isBipartite", "G_IsBipartite", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_colorable_two", "G_Colorable_2", "Not an equality or iff proposition"),
    ("SimpleGraph_IsTree_colorable_two", "G_Colorable_2", "Not an equality or iff proposition"),
    ("SimpleGraph_IsAcyclic_chromaticNumber_le_two", "G_chromaticNumber_le_2", "Not an equality or iff proposition"),
    ("SimpleGraph_IsTree_chromaticNumber_le_two", "G_chromaticNumber_le_2", "Not an equality or iff proposition"),
    ("SimpleGraph_exists_isCycle_of_two_le_isEdgeReachable", "exists_w_colon_G_Walk_u_u_w_IsCycle", "Not an equality or iff proposition"),
    ("SimpleGraph_isSymm_adjMatrix", "G_adjMatrix_a_IsSymm", "Not an equality or iff proposition"),
    ("SimpleGraph_isAdjMatrix_adjMatrix", "G_adjMatrix_a_IsAdjMatrix", "Not an equality or iff proposition"),
    ("SimpleGraph_irrefl", "not_G_Adj_v_v", "Not an equality or iff proposition"),
    ("SimpleGraph_adj_symm", "G_Adj_v_u", "Not an equality or iff proposition"),
    ("SimpleGraph_Adj_symm", "G_Adj_v_u", "Not an equality or iff proposition"),
    ("SimpleGraph_ne_of_adj", "a_ne_b", "Not an equality or iff proposition"),
    ("SimpleGraph_Adj_ne", "a_ne_b", "Not an equality or iff proposition"),
    ("SimpleGraph_Adj_ne", "_unknown", "Empty proposition"),
    ("SimpleGraph_ne_of_adj_of_not_adj", "v_ne_w", "Not an equality or iff proposition"),
    ("SimpleGraph_adj_injective", "Injective_Adj_colon_SimpleGraph_V_to_V_to_V_to_Prop", "Not an equality or iff proposition"),
    ("SimpleGraph_IsBipartiteWith_symm", "G_IsBipartiteWith_t_s", "Not an equality or iff proposition"),
    ("SimpleGraph_IsBipartiteWith_mem_of_mem_adj", "w_in_t", "Not an equality or iff proposition"),
    ("SimpleGraph_isBipartiteWith_neighborSet_subset", "G_neighborSet_v_sub_t", "Not an equality or iff proposition"),
    ("SimpleGraph_isBipartiteWith_neighborSet_disjoint", "Disjoint_G_neighborSet_v_s", "Not an equality or iff proposition"),
    ("SimpleGraph_IsBipartiteWith_mem_of_mem_adj", "_unknown", "Empty proposition"),
    ("SimpleGraph_isBipartiteWith_neighborSet", "_unknown", "Empty proposition"),
    ("SimpleGraph_isBipartiteWith_neighborSet_subset", "_unknown", "Empty proposition"),
    ("SimpleGraph_isBipartiteWith_support_subset", "G_support_sub_s_union_t", "Not an equality or iff proposition"),
    ("SimpleGraph_isBipartiteWith_neighborSet_disjoint", "_unknown", "Empty proposition"),
    ("SimpleGraph_isBipartiteWith_neighborFinset", "_unknown", "Empty proposition"),
    ("SimpleGraph_mulCayley_adj", "_unknown", "Empty proposition"),
    ("SimpleGraph_mulCayley_gc", "GaloisConnection_mulCayley_g_colon_M_pipe_forall_a_a_star_g_ne_a_to_Adj_a_star_g_a", "Not an equality or iff proposition"),
    ("SimpleGraph_mulCayley_monotone", "Monotone_mulCayley_M_colon_eq_M", "Not an equality or iff proposition"),
    ("SimpleGraph_mulCayley_mono", "mulCayley_U_le_mulCayley_V", "Not an equality or iff proposition"),
    ("SimpleGraph_cycleGraph_zero_adj", "not_cycleGraph_0_Adj_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_cycleGraph_one_adj", "not_cycleGraph_1_Adj_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_cycleGraph_adj", "_unknown", "Empty proposition"),
    ("SimpleGraph_pathGraph_le_cycleGraph", "pathGraph_n_le_cycleGraph_n", "Not an equality or iff proposition"),
    ("SimpleGraph_cycleGraph_preconnected", "cycleGraph_n_Preconnected", "Not an equality or iff proposition"),
    ("SimpleGraph_cycleGraph_connected", "cycleGraph_n_plus_1_Connected", "Not an equality or iff proposition"),
    ("SimpleGraph_isClique_empty", "G_IsClique_empty", "Not an equality or iff proposition"),
    ("SimpleGraph_isClique_singleton", "G_IsClique_a", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_of_subsingleton", "G_IsClique_s", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_insert", "G_IsClique_insert_a_s", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_mono", "G_IsClique_s_to_H_IsClique_s", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_subset", "G_IsClique_s_to_G_IsClique_t", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_map", "G_map_f_IsClique_f_prime_prime_s", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_finsetMap", "G_map_f_IsClique_s_map_f", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_of_induce", "G_IsClique_Subtype_val_prime_prime_A", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_sdiff_of_sup_edge", "G_IsClique_s_bsl_v", "Not an equality or iff proposition"),
    ("SimpleGraph_isClique_sup_edge_of_ne_sdiff", "G_edge_v_w_IsClique_s", "Not an equality or iff proposition"),
    ("SimpleGraph_isClique_range_copy_top", "G_IsClique_Set_range_f", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_valid", "C_v_ne_C_w", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_injective_comp_of_pairwise_adj", "C_comp_f_Injective", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_mem_colorClass", "v_in_C_colorClass_C_v", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_colorClasses_isPartition", "Setoid_IsPartition_C_colorClasses", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_mem_colorClasses", "C_colorClass_C_v_in_C_colorClasses", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_colorClasses_finite", "C_colorClasses_Finite", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_card_colorClasses_le", "Fintype_card_C_colorClasses_le_Fintype_card_a", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_not_adj_of_mem_colorClass", "not_G_Adj_v_w", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_isIndepSet_colorClass", "G_IsIndepSet_lt_pipe_C_colorClass_c", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_color_classes_independent", "IsAntichain_G_Adj_C_colorClass_c", "Not an equality or iff proposition"),
    ("SimpleGraph_Colorable_of_isEmpty", "G_Colorable_n", "Not an equality or iff proposition"),
    ("SimpleGraph_isEmpty_of_colorable_zero", "IsEmpty_V", "Not an equality or iff proposition"),
    ("SimpleGraph_Colorable_map", "G_map_f_Colorable_n", "Not an equality or iff proposition"),
    ("SimpleGraph_Colorable_card_le_of_pairwise_adj", "Nat_card_i_le_n", "Not an equality or iff proposition"),
    ("SimpleGraph_le_chromaticNumber_of_pairwise_adj", "n_le_G_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_Colorable_mono", "G_Colorable_m", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_colorable", "G_Colorable_Fintype_card_a", "Not an equality or iff proposition"),
    ("SimpleGraph_colorable_of_fintype", "G_Colorable_Fintype_card_V", "Not an equality or iff proposition"),
    ("SimpleGraph_Colorable_of_hom", "G_Colorable_n", "Not an equality or iff proposition"),
    ("SimpleGraph_colorable_set_nonempty_of_colorable", "n_colon_pipe_G_Colorable_n_Nonempty", "Not an equality or iff proposition"),
    ("SimpleGraph_chromaticNumber_bddBelow", "BddBelow_n_colon_pipe_G_Colorable_n", "Not an equality or iff proposition"),
    ("SimpleGraph_Colorable_chromaticNumber_le", "G_chromaticNumber_le_n", "Not an equality or iff proposition"),
    ("SimpleGraph_colorable_chromaticNumber", "G_Colorable_ENat_toNat_G_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_colorable_chromaticNumber_of_fintype", "G_Colorable_ENat_toNat_G_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_chromaticNumber_le_one_of_subsingleton", "G_chromaticNumber_le_1", "Not an equality or iff proposition"),
    ("SimpleGraph_chromaticNumber_pos", "_0_lt_G_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_colorable_of_chromaticNumber_ne_top", "G_Colorable_ENat_toNat_G_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_isEmpty_of_chromaticNumber_eq_zero", "IsEmpty_V", "Not an equality or iff proposition"),
    ("SimpleGraph_Colorable_mono_left", "G_Colorable_n", "Not an equality or iff proposition"),
    ("SimpleGraph_chromaticNumber_le_of_forall_imp", "G_chromaticNumber_le_G_prime_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_chromaticNumber_mono", "G_chromaticNumber_le_G_prime_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_chromaticNumber_mono_of_hom", "G_chromaticNumber_le_G_prime_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_chromaticNumber_le_card", "G_chromaticNumber_le_Fintype_card_V", "Not an equality or iff proposition"),
    ("SimpleGraph_two_le_chromaticNumber_of_adj", "_2_le_G_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_card_le_of_colorable", "s_card_le_n", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_card_le_of_coloring", "s_card_le_Fintype_card_a", "Not an equality or iff proposition"),
    ("SimpleGraph_IsClique_card_le_chromaticNumber", "s_card_le_G_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_cliqueNum_le_chromaticNumber", "G_cliqueNum_le_G_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_Colorable_cliqueFree", "G_CliqueFree_m", "Not an equality or iff proposition"),
    ("SimpleGraph_cliqueFree_of_chromaticNumber_lt", "G_CliqueFree_n", "Not an equality or iff proposition"),
    ("SimpleGraph_Coloring_surjOn_of_card_le_isClique", "Set_SurjOn_C_s_Set_univ", "Not an equality or iff proposition"),
    ("SimpleGraph_completeMultipartiteGraph_colorable", "completeMultipartiteGraph_V_Colorable_Fintype_card_i", "Not an equality or iff proposition"),
    ("SimpleGraph_completeMultipartiteGraph_colorable_of_cliqueFree", "completeMultipartiteGraph_V_Colorable_n_minus_1", "Not an equality or iff proposition"),
    ("SimpleGraph_free_of_colorable", "H_Free_G", "Not an equality or iff proposition"),
    ("SimpleGraph_bot_isCompleteMultipartite", "bot_colon_SimpleGraph_a_IsCompleteMultipartite", "Not an equality or iff proposition"),
    ("SimpleGraph_IsCompleteMultipartite_induce", "G_induce_s_IsCompleteMultipartite", "Not an equality or iff proposition"),
    ("SimpleGraph_completeMultipartiteGraph_isCompleteMultipartite", "completeMultipartiteGraph_V_IsCompleteMultipartite", "Not an equality or iff proposition"),
    ("SimpleGraph_IsCompleteMultipartite_colorable_of_cliqueFree", "G_Colorable_n_minus_1", "Not an equality or iff proposition"),
    ("SimpleGraph_IsPathGraph3Compl_ne_fst", "v_ne_w_1", "Not an equality or iff proposition"),
    ("SimpleGraph_IsPathGraph3Compl_ne_snd", "v_ne_w_2", "Not an equality or iff proposition"),
    ("SimpleGraph_IsPathGraph3Compl_fst_ne_snd", "w_1_ne_w_2", "Not an equality or iff proposition"),
    ("SimpleGraph_IsPathGraph3Compl_symm", "G_IsPathGraph3Compl_v_w_2_w_1", "Not an equality or iff proposition"),
    ("SimpleGraph_exists_isPathGraph3Compl_of_not_isCompleteMultipartite", "exists_v_w_1_w_2_G_IsPathGraph3Compl_v_w_1_w_2", "Not an equality or iff proposition"),
    ("SimpleGraph_not_isCompleteMultipartite_of_pathGraph3ComplEmbedding", "not_IsCompleteMultipartite_G", "Not an equality or iff proposition"),
    ("SimpleGraph_IsCompleteMultipartite_comap", "G_IsCompleteMultipartite_to_H_IsCompleteMultipartite", "Not an equality or iff proposition"),
    ("SimpleGraph_completeEquipartiteGraph_isCompleteMultipartite", "completeEquipartiteGraph_r_t_IsCompleteMultipartite", "Not an equality or iff proposition"),
    ("SimpleGraph_isContained_completeEquipartiteGraph_of_colorable", "G_completeEquipartiteGraph_n_t", "Not an equality or iff proposition"),
    ("SimpleGraph_Walk_three_le_chromaticNumber_of_odd_loop", "_3_le_G_chromaticNumber", "Not an equality or iff proposition"),
    ("SimpleGraph_completeEquipartiteGraph_colorable", "completeEquipartiteGraph_r_t_Colorable_r", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_elim", "p", "Proposition too short"),
    ("SimpleGraph_Reachable_elim_path", "p", "Proposition too short"),
    ("SimpleGraph_Walk_reachable", "G_Reachable_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_Adj_reachable", "G_Reachable_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_adj_le_reachable", "G_Adj_le_G_Reachable", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_refl", "G_Reachable_u_u", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_rfl", "G_Reachable_u_u", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_symm", "G_Reachable_v_u", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_trans", "G_Reachable_u_w", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_map", "G_prime_Reachable_f_u_f_v", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_mono", "G_prime_Reachable_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_mono", "_unknown", "Empty proposition"),
    ("SimpleGraph_Reachable_exists_isPath", "exists_p_colon_G_Walk_u_v_p_IsPath", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_mem_subgraphVerts", "v_in_H_verts", "Not an equality or iff proposition"),
    ("SimpleGraph_reachable_is_equivalence", "Equivalence_G_Reachable", "Not an equality or iff proposition"),
    ("SimpleGraph_reachable_top", "completeGraph_V_Reachable_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_of_subsingleton", "G_Reachable_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_nonempty_neighborSet_left", "G_neighborSet_u_Nonempty", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_nonempty_neighborSet_right", "G_neighborSet_v_Nonempty", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_degree_pos_left", "_0_lt_G_degree_u", "Not an equality or iff proposition"),
    ("SimpleGraph_Reachable_degree_pos_right", "_0_lt_G_degree_v", "Not an equality or iff proposition"),
    ("SimpleGraph_not_reachable_of_neighborSet_left_eq_empty", "not_G_Reachable_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_not_reachable_of_neighborSet_right_eq_empty", "not_G_Reachable_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_not_reachable_of_left_degree_zero", "not_G_Reachable_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_not_reachable_of_right_degree_zero", "not_G_Reachable_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_Preconnected_map", "H_Preconnected", "Not an equality or iff proposition"),
    ("SimpleGraph_Preconnected_mono", "G_prime_Preconnected", "Not an equality or iff proposition"),
    ("SimpleGraph_preconnected_bot", "bot_colon_SimpleGraph_V_Preconnected", "Not an equality or iff proposition"),
    ("SimpleGraph_not_preconnected_bot", "not_bot_colon_SimpleGraph_V_Preconnected", "Not an equality or iff proposition"),
    ("SimpleGraph_preconnected_top", "top_colon_SimpleGraph_V_Preconnected", "Not an equality or iff proposition"),
    ("SimpleGraph_Preconnected_of_subsingleton", "G_Preconnected", "Not an equality or iff proposition"),
    ("SimpleGraph_Preconnected_not_isIsolated", "not_G_IsIsolated_v", "Not an equality or iff proposition"),
    ("SimpleGraph_Preconnected_degree_pos_of_nontrivial", "_0_lt_G_degree_v", "Not an equality or iff proposition"),
    ("SimpleGraph_Preconnected_minDegree_pos_of_nontrivial", "_0_lt_G_minDegree", "Not an equality or iff proposition"),
    ("SimpleGraph_adj_of_mem_walk_support", "exists_y_in_p_support_G_Adj_x_y", "Not an equality or iff proposition"),
    ("SimpleGraph_mem_support_of_mem_walk_support", "w_in_G_support", "Not an equality or iff proposition"),
    ("SimpleGraph_mem_support_of_reachable", "u_in_G_support", "Not an equality or iff proposition"),
    ("SimpleGraph_Preconnected_exists_isPath", "exists_p_colon_G_Walk_u_v_p_IsPath", "Not an equality or iff proposition"),
    ("SimpleGraph_Connected_map", "H_Connected", "Not an equality or iff proposition"),
    ("SimpleGraph_Connected_mono", "G_prime_Connected", "Not an equality or iff proposition"),
    ("SimpleGraph_Connected_exists_isPath", "exists_p_colon_G_Walk_u_v_p_IsPath", "Not an equality or iff proposition"),
    ("SimpleGraph_not_connected_bot", "not_bot_colon_SimpleGraph_V_Connected", "Not an equality or iff proposition"),
    ("SimpleGraph_connected_top", "completeGraph_V_Connected", "Not an equality or iff proposition"),
    ("SimpleGraph_Connected_of_subsingleton", "G_Connected", "Not an equality or iff proposition"),
    ("SimpleGraph_reachable_or_compl_adj", "G_Reachable_u_v_or_G_Adj_u_v", "Not an equality or iff proposition"),
    ("SimpleGraph_reachable_or_reachable_compl", "G_Reachable_u_v_or_G_Reachable_u_w", "Not an equality or iff proposition"),
    ("SimpleGraph_connected_or_preconnected_compl", "G_Connected_or_G_Preconnected", "Not an equality or iff proposition"),
    ("SimpleGraph_connected_or_connected_compl", "G_Connected_or_G_Connected", "Not an equality or iff proposition"),
    ("SimpleGraph_ConnectedComponent_ind", "b_c", "Not an equality or iff proposition"),
    ("SimpleGraph_ConnectedComponent_ind_2", "b_c_d", "Not an equality or iff proposition"),
    ("SimpleGraph_Preconnected_subsingleton_connectedComponent", "Subsingleton_G_ConnectedComponent", "Not an equality or iff proposition"),
    ("SimpleGraph_ConnectedComponent_surjective_map_ofLE", "map_lt_pipe_Hom_ofLE_h_Surjective", "Not an equality or iff proposition"),
]
