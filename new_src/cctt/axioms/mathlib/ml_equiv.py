"""Mathlib: Equiv — auto-generated from Mathlib4.

Contains 153 rewrite rules derived from Mathlib theorems.
Plus 57 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_equiv"
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
# Rewrite rules (153 total)
# ════════════════════════════════════════════════════════════

def _r0000_affineIsometryOfStrictConvexSpace_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.affineIsometryOfStrictConvexSpace_apply
    # hi.affineIsometryOfStrictConvexSpace p = f p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hi_affineIsometryOfStrictConvexSpace", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: Isometry_affineIsometryOfStrictConvexSpace_apply"))
        except Exception:
            pass
    return results


def _r0001_coe_toRealAffineIsometryEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_toRealAffineIsometryEquiv
    # f.toRealAffineIsometryEquiv.toIsometryEquiv = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toRealAffineIsometryEquiv_toIsometryEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_toRealAffineIsometryEquiv"))
    except Exception:
        pass
    return results


def _r0002_coe_withLpUniqueProd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_withLpUniqueProd
    # ⇑(withLpUniqueProd p α β) = WithLp.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("withLpUniqueProd_p_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("WithLp_snd")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_withLpUniqueProd"))
    except Exception:
        pass
    return results


def _r0003_op_unop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.op_unop
    # f.op.unop = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_op_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Iso_op_unop"))
    except Exception:
        pass
    return results


def _r0004_op_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.op_refl
    # Iso.op (Iso.refl X) = Iso.refl (op X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_op", 1)
    if args is not None:
        try:
            rhs = OOp("Iso_refl", (OOp("op", (OVar("X"),)),))
            results.append((rhs, "Mathlib: Iso_op_refl"))
        except Exception:
            pass
    return results


def _r0005_op_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.op_trans
    # Iso.op (α ≪≫ β) = Iso.op β ≪≫ Iso.op α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_op", 1)
    if args is not None:
        try:
            rhs = OOp("Iso_op", (OVar("b"), OVar("_unknown"), OVar("Iso_op"), OVar("a"),))
            results.append((rhs, "Mathlib: Iso_op_trans"))
        except Exception:
            pass
    return results


def _r0006_unop_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.unop_refl
    # Iso.unop (Iso.refl X) = Iso.refl X.unop
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_unop", 1)
    if args is not None:
        try:
            rhs = OOp("Iso_refl", (OVar("X_unop"),))
            results.append((rhs, "Mathlib: Iso_unop_refl"))
        except Exception:
            pass
    return results


def _r0007_unop_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.unop_trans
    # Iso.unop (α ≪≫ β) = Iso.unop β ≪≫ Iso.unop α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_unop", 1)
    if args is not None:
        try:
            rhs = OOp("Iso_unop", (OVar("b"), OVar("_unknown"), OVar("Iso_unop"), OVar("a"),))
            results.append((rhs, "Mathlib: Iso_unop_trans"))
        except Exception:
            pass
    return results


def _r0008_unop_inv_hom_id_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.unop_inv_hom_id_app
    # (e.inv.app X).unop ≫ (e.hom.app X).unop = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_inv_app_X_unop", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: Iso_unop_inv_hom_id_app"))
        except Exception:
            pass
    return results


def _r0009_map_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.map_symm_apply
    # (SimpleGraph.Iso.map f G).symm w = f.symm w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "SimpleGraph_Iso_map_f_G_symm", 1)
    if args is not None:
        try:
            rhs = OOp("f_symm", (args[0],))
            results.append((rhs, "Mathlib: Iso_map_symm_apply"))
        except Exception:
            pass
    return results


def _r0010_coe_toLinearMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.coe_toLinearMap
    # ⇑f.toLinearMap = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_coe_toLinearMap"))
    except Exception:
        pass
    return results


def _r0011_comp_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.comp_id
    # f.comp (id Q₁) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_comp_id"))
        except Exception:
            pass
    return results


def _r0012_comp_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.comp_assoc
    # (h.comp g).comp f = h.comp (g.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_comp_g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("h_comp", (OOp("g_comp", (args[0],)),))
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_comp_assoc"))
        except Exception:
            pass
    return results


def _r0013_map_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.IsometryEquiv.map_app
    # Q₂ (f m) = Q₁ m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Q_2", 1)
    if args is not None:
        try:
            rhs = OOp("Q_1", (OVar("m"),))
            results.append((rhs, "Mathlib: QuadraticMap_IsometryEquiv_map_app"))
        except Exception:
            pass
    return results


def _r0014_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.IsometryEquiv.symm_apply_apply
    # f.symm (f x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: QuadraticMap_IsometryEquiv_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0015_coe_symm_toLinearEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.IsometryEquiv.coe_symm_toLinearEquiv
    # f.toLinearEquiv.symm = f.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toLinearEquiv_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_symm")
            results.append((rhs, "Mathlib: QuadraticMap_IsometryEquiv_coe_symm_toLinearEquiv"))
    except Exception:
        pass
    return results


def _r0016_hausdorffMeasure_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.hausdorffMeasure_preimage
    # μH[d] (e ⁻¹' s) = μH[d] s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "muH_d", 1)
    if args is not None:
        try:
            rhs = OOp("muH_d", (OVar("s"),))
            results.append((rhs, "Mathlib: IsometryEquiv_hausdorffMeasure_preimage"))
        except Exception:
            pass
    return results


def _r0017_map_hausdorffMeasure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.map_hausdorffMeasure
    # Measure.map e μH[d] = μH[d]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Measure_map", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: IsometryEquiv_map_hausdorffMeasure"))
        except Exception:
            pass
    return results


def _r0018_coe_symm_toDilationEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_symm_toDilationEquiv
    # ⇑e.toDilationEquiv.symm = e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toDilationEquiv_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_symm_toDilationEquiv"))
    except Exception:
        pass
    return results


def _r0019_dimH_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.dimH_preimage
    # dimH (e ⁻¹' s) = dimH s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dimH", 1)
    if args is not None:
        try:
            rhs = OOp("dimH", (OVar("s"),))
            results.append((rhs, "Mathlib: IsometryEquiv_dimH_preimage"))
        except Exception:
            pass
    return results


def _r0020_dimH_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.dimH_univ
    # dimH (univ : Set X) = dimH (univ : Set Y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dimH", 1)
    if args is not None:
        try:
            rhs = OOp("dimH", (OOp("univ_set", (OVar("colon"), OVar("Set"), OVar("Y"),)),))
            results.append((rhs, "Mathlib: IsometryEquiv_dimH_univ"))
        except Exception:
            pass
    return results


def _r0021_coe_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_mk
    # ⇑(mk e h) = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mk_e_h")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_mk"))
    except Exception:
        pass
    return results


def _r0022_symm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.symm_symm
    # h.symm.symm = h
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h_symm_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("h")
            results.append((rhs, "Mathlib: IsometryEquiv_symm_symm"))
    except Exception:
        pass
    return results


def _r0023_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.symm_apply_apply
    # h.symm (h x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: IsometryEquiv_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0024_symm_apply_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.symm_apply_eq
    # h.symm y = x ↔ y = h x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_symm", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("x"), args[0])), OOp("h", (OVar("x"),))))
            results.append((rhs, "Mathlib: IsometryEquiv_symm_apply_eq"))
        except Exception:
            pass
    return results


def _r0025_preimage_eball(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.preimage_eball
    # h ⁻¹' Metric.eball x r = Metric.eball (h.symm x) r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h", 4)
    if args is not None:
        try:
            rhs = OOp("Metric_eball", (OOp("h_symm", (args[2],)), args[3],))
            results.append((rhs, "Mathlib: IsometryEquiv_preimage_eball"))
        except Exception:
            pass
    return results


def _r0026_coe_toHomeomorph_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_toHomeomorph_symm
    # ⇑h.toHomeomorph.symm = h.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h_toHomeomorph_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("h_symm")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_toHomeomorph_symm"))
    except Exception:
        pass
    return results


def _r0027_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_mul
    # ⇑(e₁ * e₂) = e₁ ∘ e₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_1_star_e_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("e_1"), OVar("e_2")))
            results.append((rhs, "Mathlib: IsometryEquiv_coe_mul"))
    except Exception:
        pass
    return results


def _r0028_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.mul_apply
    # (e₁ * e₂) x = e₁ (e₂ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_1_star_e_2", 1)
    if args is not None:
        try:
            rhs = OOp("e_1", (OOp("e_2", (args[0],)),))
            results.append((rhs, "Mathlib: IsometryEquiv_mul_apply"))
        except Exception:
            pass
    return results


def _r0029_inv_apply_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.inv_apply_self
    # e⁻¹ (e x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "einv", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: IsometryEquiv_inv_apply_self"))
        except Exception:
            pass
    return results


def _r0030_apply_inv_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.apply_inv_self
    # e (e⁻¹ x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: IsometryEquiv_apply_inv_self"))
        except Exception:
            pass
    return results


def _r0031_comp_continuousOn_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.comp_continuousOn_iff
    # ContinuousOn (h ∘ f) s ↔ ContinuousOn f s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ContinuousOn", 2)
    if args is not None:
        try:
            rhs = OOp("ContinuousOn", (OVar("f"), args[1],))
            results.append((rhs, "Mathlib: IsometryEquiv_comp_continuousOn_iff"))
        except Exception:
            pass
    return results


def _r0032_completeSpace_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.completeSpace_iff
    # CompleteSpace α ↔ CompleteSpace β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "CompleteSpace", 1)
    if args is not None:
        try:
            rhs = OOp("CompleteSpace", (OVar("b"),))
            results.append((rhs, "Mathlib: IsometryEquiv_completeSpace_iff"))
        except Exception:
            pass
    return results


def _r0033_conj_eq_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.conj_eq_conj
    # Iso.conj i f = FGModuleCat.ofHom (LinearEquiv.conj (isoToLinearEquiv i) f.hom.hom)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_conj", 2)
    if args is not None:
        try:
            rhs = OOp("FGModuleCat_ofHom", (OOp("LinearEquiv_conj", (OOp("isoToLinearEquiv", (args[0],)), OVar("f_hom_hom"),)),))
            results.append((rhs, "Mathlib: Iso_conj_eq_conj"))
        except Exception:
            pass
    return results


def _r0034_conj_hom_eq_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.conj_hom_eq_conj
    # (Iso.conj i f).hom.hom = (LinearEquiv.conj (isoToLinearEquiv i) f.hom.hom)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Iso_conj_i_f_hom_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("LinearEquiv_conj", (OOp("isoToLinearEquiv", (OVar("i"),)), OVar("f_hom_hom"),))
            results.append((rhs, "Mathlib: Iso_conj_hom_eq_conj"))
    except Exception:
        pass
    return results


def _r0035_homCongr_eq_arrowCongr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.homCongr_eq_arrowCongr
    # Iso.homCongr i j f = ⟨LinearEquiv.arrowCongr i.toLinearEquiv j.toLinearEquiv f.hom⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_homCongr", 3)
    if args is not None:
        try:
            rhs = OVar("LinearEquiv_arrowCongr_i_toLinearEquiv_j_toLinearEquiv_f_hom")
            results.append((rhs, "Mathlib: Iso_homCongr_eq_arrowCongr"))
        except Exception:
            pass
    return results


def _r0036_conj_eq_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.conj_eq_conj
    # Iso.conj i f = ⟨LinearEquiv.conj i.toLinearEquiv f.hom⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_conj", 2)
    if args is not None:
        try:
            rhs = OVar("LinearEquiv_conj_i_toLinearEquiv_f_hom")
            results.append((rhs, "Mathlib: Iso_conj_eq_conj"))
        except Exception:
            pass
    return results


def _r0037_homCongr_eq_arrowCongr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.homCongr_eq_arrowCongr
    # Iso.homCongr i j f = ⟨LinearEquiv.arrowCongr i.toLinearEquivₛ j.toLinearEquivₛ f.hom⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_homCongr", 3)
    if args is not None:
        try:
            rhs = OVar("LinearEquiv_arrowCongr_i_toLinearEquiv_j_toLinearEquiv_f_hom")
            results.append((rhs, "Mathlib: Iso_homCongr_eq_arrowCongr"))
        except Exception:
            pass
    return results


def _r0038_conj_eq_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.conj_eq_conj
    # Iso.conj i f = ⟨LinearEquiv.conj i.toLinearEquivₛ f.hom⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_conj", 2)
    if args is not None:
        try:
            rhs = OVar("LinearEquiv_conj_i_toLinearEquiv_f_hom")
            results.append((rhs, "Mathlib: Iso_conj_eq_conj"))
        except Exception:
            pass
    return results


def _r0039_coe_affineIsometryOfStrictConvexSpace(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.coe_affineIsometryOfStrictConvexSpace
    # ⇑hi.affineIsometryOfStrictConvexSpace = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hi_affineIsometryOfStrictConvexSpace")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Isometry_coe_affineIsometryOfStrictConvexSpace"))
    except Exception:
        pass
    return results


def _r0040_midpoint_fixed(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.midpoint_fixed
    # ∀ e : PE ≃ᵢ PE, e x = x → e y = y → e (midpoint ℝ x y) = midpoint ℝ x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OOp("midpoint", (OVar("_unknown"), OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: IsometryEquiv_midpoint_fixed"))
        except Exception:
            pass
    return results


def _r0041_map_midpoint(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.map_midpoint
    # f (midpoint ℝ x y) = midpoint ℝ (f x) (f y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("midpoint", (OVar("_unknown"), OOp("f", (OVar("x"),)), OOp("f", (OVar("y"),)),))
            results.append((rhs, "Mathlib: IsometryEquiv_map_midpoint"))
        except Exception:
            pass
    return results


def _r0042_coe_toRealLinearIsometryEquivOfMapZero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero
    # ⇑(f.toRealLinearIsometryEquivOfMapZero h0) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toRealLinearIsometryEquivOfMapZero_h0")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_toRealLinearIsometryEquivOfMapZero"))
    except Exception:
        pass
    return results


def _r0043_coe_toRealLinearIsometryEquivOfMapZero_s(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero_symm
    # ⇑(f.toRealLinearIsometryEquivOfMapZero h0).symm = f.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toRealLinearIsometryEquivOfMapZero_h0_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_symm")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_toRealLinearIsometryEquivOfMapZero_symm"))
    except Exception:
        pass
    return results


def _r0044_coeFn_toRealAffineIsometryEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coeFn_toRealAffineIsometryEquiv
    # ⇑f.toRealAffineIsometryEquiv = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toRealAffineIsometryEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: IsometryEquiv_coeFn_toRealAffineIsometryEquiv"))
    except Exception:
        pass
    return results


def _r0045_norm_map_of_map_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.norm_map_of_map_one
    # ‖f x‖ = ‖x‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Isometry_norm_map_of_map_one"))
        except Exception:
            pass
    return results


def _r0046_nnnorm_map_of_map_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.nnnorm_map_of_map_one
    # ‖f x‖₊ = ‖x‖₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Isometry_nnnorm_map_of_map_one"))
        except Exception:
            pass
    return results


def _r0047_withLpProdComm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.withLpProdComm_apply
    # withLpProdComm p α β x = .toLp p (x.snd, x.fst)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "withLpProdComm", 4)
    if args is not None:
        try:
            rhs = OOp("toLp", (args[0], OOp("x_snd", (OVar("x_fst"),)),))
            results.append((rhs, "Mathlib: IsometryEquiv_withLpProdComm_apply"))
        except Exception:
            pass
    return results


def _r0048_withLpProdComm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.withLpProdComm_symm
    # (withLpProdComm p α β).symm = withLpProdComm p β α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("withLpProdComm_p_a_b_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("withLpProdComm", (OVar("p"), OVar("b"), OVar("a"),))
            results.append((rhs, "Mathlib: IsometryEquiv_withLpProdComm_symm"))
    except Exception:
        pass
    return results


def _r0049_coe_withLpProdUnique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_withLpProdUnique
    # ⇑(withLpProdUnique p α β) = WithLp.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("withLpProdUnique_p_a_b")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("WithLp_fst")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_withLpProdUnique"))
    except Exception:
        pass
    return results


def _r0050_conj_rho(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.conj_ρ
    # N.ρ g = ((forget V G).mapIso f).conj (M.ρ g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "N_rho", 1)
    if args is not None:
        try:
            rhs = OOp("forget_V_G_mapIso_f_conj", (OOp("M_rho", (args[0],)),))
            results.append((rhs, "Mathlib: Iso_conj_rho"))
        except Exception:
            pass
    return results


def _r0051_isoFunctorOfIsoInverse_isoInverseOfIsoFu(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.isoFunctorOfIsoInverse_isoInverseOfIsoFunctor
    # isoFunctorOfIsoInverse (isoInverseOfIsoFunctor i) = i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "isoFunctorOfIsoInverse", 1)
    if args is not None:
        try:
            rhs = OVar("i")
            results.append((rhs, "Mathlib: Iso_isoFunctorOfIsoInverse_isoInverseOfIsoFunctor"))
        except Exception:
            pass
    return results


def _r0052_isoInverseOfIsoFunctor_isoFunctorOfIsoIn(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.isoInverseOfIsoFunctor_isoFunctorOfIsoInverse
    # isoInverseOfIsoFunctor (isoFunctorOfIsoInverse i) = i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "isoInverseOfIsoFunctor", 1)
    if args is not None:
        try:
            rhs = OVar("i")
            results.append((rhs, "Mathlib: Iso_isoInverseOfIsoFunctor_isoFunctorOfIsoInverse"))
        except Exception:
            pass
    return results


def _r0053_unop_op(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.unop_op
    # f.unop.op = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_unop_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: Iso_unop_op"))
    except Exception:
        pass
    return results


def _r0054_op_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.op_symm
    # Iso.op α.symm = (Iso.op α).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_op", 1)
    if args is not None:
        try:
            rhs = OVar("Iso_op_a_symm")
            results.append((rhs, "Mathlib: Iso_op_symm"))
        except Exception:
            pass
    return results


def _r0055_unop_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.unop_symm
    # Iso.unop α.symm = (Iso.unop α).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_unop", 1)
    if args is not None:
        try:
            rhs = OVar("Iso_unop_a_symm")
            results.append((rhs, "Mathlib: Iso_unop_symm"))
        except Exception:
            pass
    return results


def _r0056_unop_hom_inv_id_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.unop_hom_inv_id_app
    # (e.hom.app X).unop ≫ (e.inv.app X).unop = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_hom_app_X_unop", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: Iso_unop_hom_inv_id_app"))
        except Exception:
            pass
    return results


def _r0057_card_edgeFinset_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.card_edgeFinset_eq
    # #G.edgeFinset = #G'.edgeFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hash_G_edgeFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("hash_G_prime_edgeFinset")
            results.append((rhs, "Mathlib: Iso_card_edgeFinset_eq"))
    except Exception:
        pass
    return results


def _r0058_degree_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.degree_eq
    # G'.degree (f x) = G.degree x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_prime_degree", 1)
    if args is not None:
        try:
            rhs = OOp("G_degree", (OVar("x"),))
            results.append((rhs, "Mathlib: Iso_degree_eq"))
        except Exception:
            pass
    return results


def _r0059_minDegree_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.minDegree_eq
    # G.minDegree = G'.minDegree
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_minDegree")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("G_prime_minDegree")
            results.append((rhs, "Mathlib: Iso_minDegree_eq"))
    except Exception:
        pass
    return results


def _r0060_maxDegree_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.maxDegree_eq
    # G.maxDegree = G'.maxDegree
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("G_maxDegree")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("G_prime_maxDegree")
            results.append((rhs, "Mathlib: Iso_maxDegree_eq"))
    except Exception:
        pass
    return results


def _r0061_symm_toHom_comp_toHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.symm_toHom_comp_toHom
    # f.symm.toHom.comp f.toHom = Hom.id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_symm_toHom_comp", 1)
    if args is not None:
        try:
            rhs = OVar("Hom_id")
            results.append((rhs, "Mathlib: Iso_symm_toHom_comp_toHom"))
        except Exception:
            pass
    return results


def _r0062_toHom_comp_symm_toHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.toHom_comp_symm_toHom
    # f.toHom.comp f.symm.toHom = Hom.id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toHom_comp", 1)
    if args is not None:
        try:
            rhs = OVar("Hom_id")
            results.append((rhs, "Mathlib: Iso_toHom_comp_symm_toHom"))
        except Exception:
            pass
    return results


def _r0063_card_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.card_eq
    # Fintype.card V = Fintype.card W
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fintype_card", 1)
    if args is not None:
        try:
            rhs = OOp("Fintype_card", (OVar("W"),))
            results.append((rhs, "Mathlib: Iso_card_eq"))
        except Exception:
            pass
    return results


def _r0064_comap_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.comap_apply
    # SimpleGraph.Iso.comap f G v = f v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "SimpleGraph_Iso_comap", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[2],))
            results.append((rhs, "Mathlib: Iso_comap_apply"))
        except Exception:
            pass
    return results


def _r0065_comap_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.comap_symm_apply
    # (SimpleGraph.Iso.comap f G).symm w = f.symm w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "SimpleGraph_Iso_comap_f_G_symm", 1)
    if args is not None:
        try:
            rhs = OOp("f_symm", (args[0],))
            results.append((rhs, "Mathlib: Iso_comap_symm_apply"))
        except Exception:
            pass
    return results


def _r0066_map_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.map_apply
    # SimpleGraph.Iso.map f G v = f v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "SimpleGraph_Iso_map", 3)
    if args is not None:
        try:
            rhs = OOp("f", (args[2],))
            results.append((rhs, "Mathlib: Iso_map_apply"))
        except Exception:
            pass
    return results


def _r0067_toEmbedding_completeGraph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.toEmbedding_completeGraph
    # (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Iso_completeGraph_f_toEmbedding")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Embedding_completeGraph", (OVar("f_toEmbedding"),))
            results.append((rhs, "Mathlib: Iso_toEmbedding_completeGraph"))
    except Exception:
        pass
    return results


def _r0068_coe_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.coe_comp
    # ⇑(f'.comp f) = f' ∘ f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_prime_comp_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("f_prime"), OVar("f")))
            results.append((rhs, "Mathlib: Iso_coe_comp"))
    except Exception:
        pass
    return results


def _r0069_preimage_perpBisector(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.preimage_perpBisector
    # f ⁻¹' (perpBisector (f p₁) (f p₂)) = perpBisector p₁ p₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("perpBisector", (OVar("p_1"), OVar("p_2"),))
            results.append((rhs, "Mathlib: Isometry_preimage_perpBisector"))
        except Exception:
            pass
    return results


def _r0070_euclideanHausdorffMeasure_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.euclideanHausdorffMeasure_image
    # μHE[d] (f '' s) = μHE[d] s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "muHE_d", 1)
    if args is not None:
        try:
            rhs = OOp("muHE_d", (OVar("s"),))
            results.append((rhs, "Mathlib: Isometry_euclideanHausdorffMeasure_image"))
        except Exception:
            pass
    return results


def _r0071_euclideanHausdorffMeasure_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.euclideanHausdorffMeasure_preimage
    # μHE[d] (f ⁻¹' s) = μHE[d] (s ∩ Set.range f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "muHE_d", 1)
    if args is not None:
        try:
            rhs = OOp("muHE_d", (OOp("inter", (OVar("s"), OOp("Set_range", (OVar("f"),)))),))
            results.append((rhs, "Mathlib: Isometry_euclideanHausdorffMeasure_preimage"))
        except Exception:
            pass
    return results


def _r0072_map_euclideanHausdorffMeasure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.map_euclideanHausdorffMeasure
    # μHE[d].map f = μHE[d].restrict (Set.range f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "muHE_d_map", 1)
    if args is not None:
        try:
            rhs = OOp("muHE_d_restrict", (OOp("Set_range", (args[0],)),))
            results.append((rhs, "Mathlib: Isometry_map_euclideanHausdorffMeasure"))
        except Exception:
            pass
    return results


def _r0073_map_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.map_app
    # Q₂ (f m) = Q₁ m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Q_2", 1)
    if args is not None:
        try:
            rhs = OOp("Q_1", (OVar("m"),))
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_map_app"))
        except Exception:
            pass
    return results


def _r0074_ofEq_rfl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.ofEq_rfl
    # ofEq (rfl : Q = Q) = .id Q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("Q"),))
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_ofEq_rfl"))
        except Exception:
            pass
    return results


def _r0075_toLinearMap_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.toLinearMap_comp
    # (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_comp_f_toLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g_toLinearMap_comp", (OVar("f_toLinearMap"),))
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_toLinearMap_comp"))
    except Exception:
        pass
    return results


def _r0076_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.id_comp
    # (id Q₂).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "id_Q_2_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_id_comp"))
        except Exception:
            pass
    return results


def _r0077_coe_toLinearEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.IsometryEquiv.coe_toLinearEquiv
    # ⇑(f : M₁ ≃ₗ[R] M₂) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_colon_M_1_R_M_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: QuadraticMap_IsometryEquiv_coe_toLinearEquiv"))
    except Exception:
        pass
    return results


def _r0078_apply_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.IsometryEquiv.apply_symm_apply
    # f (f.symm x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: QuadraticMap_IsometryEquiv_apply_symm_apply"))
        except Exception:
            pass
    return results


def _r0079_fst_comp_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.fst_comp_inl
    # (fst M₂ Q₁).comp (inl Q₁ (0 : QuadraticMap R M₂ P)) = .id _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_M_2_Q_1_comp", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_fst_comp_inl"))
        except Exception:
            pass
    return results


def _r0080_snd_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.snd_comp_inr
    # (snd M₁ Q₂).comp (inr (0 : QuadraticMap R M₁ P) Q₂) = .id _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_M_1_Q_2_comp", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_snd_comp_inr"))
        except Exception:
            pass
    return results


def _r0081_snd_comp_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.snd_comp_inl
    # (snd M₁ Q₂).comp (inl (0 : QuadraticMap R M₁ P) Q₂) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_M_1_Q_2_comp", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_snd_comp_inl"))
        except Exception:
            pass
    return results


def _r0082_fst_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.fst_comp_inr
    # (fst M₂ Q₁).comp (inr Q₁ (0 : QuadraticMap R M₂ P)) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_M_2_Q_1_comp", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_fst_comp_inr"))
        except Exception:
            pass
    return results


def _r0083_proj_comp_single_of_same(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.proj_comp_single_of_same
    # (proj i Q).comp (single _ i) = .ofEq (Pi.single_eq_same _ _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "proj_i_Q_comp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("Pi_single_eq_same", (OVar("_unknown"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: Isometry_proj_comp_single_of_same"))
        except Exception:
            pass
    return results


def _r0084_proj_comp_single_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.proj_comp_single_of_ne
    # (proj i Q).comp (single _ j) = (0 : 0 →qᵢ Q).comp (ofEq (Pi.single_eq_of_ne h.symm _))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "proj_i_Q_comp", 1)
    if args is not None:
        try:
            rhs = OOp("_0_colon_0_to_q_Q_comp", (OOp("==", (OOp("Pi_single_eq_of_ne", (OVar("h_symm"), OVar("_unknown"),)),)),))
            results.append((rhs, "Mathlib: Isometry_proj_comp_single_of_ne"))
        except Exception:
            pass
    return results


def _r0085_map_radical(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.IsometryEquiv.map_radical
    # Q.radical.map e.toLinearMap = Q'.radical
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Q_radical_map", 1)
    if args is not None:
        try:
            rhs = OVar("Q_prime_radical")
            results.append((rhs, "Mathlib: QuadraticMap_IsometryEquiv_map_radical"))
        except Exception:
            pass
    return results


def _r0086_tmul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.Isometry.tmul_apply
    # f.tmul g x = TensorProduct.map f.toLinearMap g.toLinearMap x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_tmul", 2)
    if args is not None:
        try:
            rhs = OOp("TensorProduct_map", (OVar("f_toLinearMap"), OVar("g_toLinearMap"), args[1],))
            results.append((rhs, "Mathlib: QuadraticMap_Isometry_tmul_apply"))
        except Exception:
            pass
    return results


def _r0087_hausdorffMeasure_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.hausdorffMeasure_image
    # μH[d] (f '' s) = μH[d] s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "muH_d", 1)
    if args is not None:
        try:
            rhs = OOp("muH_d", (OVar("s"),))
            results.append((rhs, "Mathlib: Isometry_hausdorffMeasure_image"))
        except Exception:
            pass
    return results


def _r0088_hausdorffMeasure_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.hausdorffMeasure_preimage
    # μH[d] (f ⁻¹' s) = μH[d] (s ∩ range f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "muH_d", 1)
    if args is not None:
        try:
            rhs = OOp("muH_d", (OOp("inter", (OVar("s"), OOp("range", (OVar("f"),)))),))
            results.append((rhs, "Mathlib: Isometry_hausdorffMeasure_preimage"))
        except Exception:
            pass
    return results


def _r0089_map_hausdorffMeasure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.map_hausdorffMeasure
    # Measure.map f μH[d] = μH[d].restrict (range f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Measure_map", 2)
    if args is not None:
        try:
            rhs = OOp("muH_d_restrict", (OOp("range", (args[0],)),))
            results.append((rhs, "Mathlib: Isometry_map_hausdorffMeasure"))
        except Exception:
            pass
    return results


def _r0090_hausdorffMeasure_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.hausdorffMeasure_image
    # μH[d] (e '' s) = μH[d] s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "muH_d", 1)
    if args is not None:
        try:
            rhs = OOp("muH_d", (OVar("s"),))
            results.append((rhs, "Mathlib: IsometryEquiv_hausdorffMeasure_image"))
        except Exception:
            pass
    return results


def _r0091_conj_rho(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FDRep.Iso.conj_ρ
    # W.ρ g = (FDRep.isoToLinearEquiv i).conj (V.ρ g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "W_rho", 1)
    if args is not None:
        try:
            rhs = OOp("FDRep_isoToLinearEquiv_i_conj", (OOp("V_rho", (args[0],)),))
            results.append((rhs, "Mathlib: FDRep_Iso_conj_rho"))
        except Exception:
            pass
    return results


def _r0092_eq_whisker(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Mathlib.Tactic.Reassoc.Iso.eq_whisker
    # f ≪≫ h = g ≪≫ h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("g", (args[0], args[1],))
            results.append((rhs, "Mathlib: Mathlib_Tactic_Reassoc_Iso_eq_whisker"))
        except Exception:
            pass
    return results


def _r0093_extensionHom_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.extensionHom_coe
    # h.extensionHom x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_extensionHom", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: Isometry_extensionHom_coe"))
        except Exception:
            pass
    return results


def _r0094_mapRingHom_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.mapRingHom_coe
    # h.mapRingHom x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_mapRingHom", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: Isometry_mapRingHom_coe"))
        except Exception:
            pass
    return results


def _r0095_coveringNumber_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.coveringNumber_image
    # coveringNumber ε (f '' A) = coveringNumber ε A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coveringNumber", 2)
    if args is not None:
        try:
            rhs = OOp("coveringNumber", (args[0], OVar("A"),))
            results.append((rhs, "Mathlib: Isometry_coveringNumber_image"))
        except Exception:
            pass
    return results


def _r0096_toDilation_ratio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.toDilation_ratio
    # ratio hf.toDilation = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ratio", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Isometry_toDilation_ratio"))
        except Exception:
            pass
    return results


def _r0097_toDilationEquiv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.toDilationEquiv_apply
    # e.toDilationEquiv x = e x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_toDilationEquiv", 1)
    if args is not None:
        try:
            rhs = OOp("e", (args[0],))
            results.append((rhs, "Mathlib: IsometryEquiv_toDilationEquiv_apply"))
        except Exception:
            pass
    return results


def _r0098_toDilationEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.toDilationEquiv_symm
    # e.symm.toDilationEquiv = e.toDilationEquiv.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_toDilationEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_toDilationEquiv_symm")
            results.append((rhs, "Mathlib: IsometryEquiv_toDilationEquiv_symm"))
    except Exception:
        pass
    return results


def _r0099_coe_toDilationEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_toDilationEquiv
    # ⇑e.toDilationEquiv = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toDilationEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_toDilationEquiv"))
    except Exception:
        pass
    return results


def _r0100_toDilationEquiv_ratio(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.toDilationEquiv_ratio
    # ratio e.toDilationEquiv = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ratio", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: IsometryEquiv_toDilationEquiv_ratio"))
        except Exception:
            pass
    return results


def _r0101_dimH_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.dimH_image
    # dimH (f '' s) = dimH s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dimH", 1)
    if args is not None:
        try:
            rhs = OOp("dimH", (OVar("s"),))
            results.append((rhs, "Mathlib: Isometry_dimH_image"))
        except Exception:
            pass
    return results


def _r0102_dimH_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.dimH_image
    # dimH (e '' s) = dimH s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dimH", 1)
    if args is not None:
        try:
            rhs = OOp("dimH", (OVar("s"),))
            results.append((rhs, "Mathlib: IsometryEquiv_dimH_image"))
        except Exception:
            pass
    return results


def _r0103_constSMul_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.constSMul_symm
    # (constSMul c : X ≃ᵢ X).symm = constSMul c⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("constSMul_c_colon_X_X_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("constSMul", (OVar("cinv"),))
            results.append((rhs, "Mathlib: IsometryEquiv_constSMul_symm"))
    except Exception:
        pass
    return results


def _r0104_mulLeft_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.mulLeft_symm
    # (mulLeft x).symm = IsometryEquiv.mulLeft x⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mulLeft_x_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("IsometryEquiv_mulLeft", (OVar("xinv"),))
            results.append((rhs, "Mathlib: IsometryEquiv_mulLeft_symm"))
    except Exception:
        pass
    return results


def _r0105_mulRight_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.mulRight_symm
    # (mulRight x).symm = mulRight x⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mulRight_x_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("mulRight", (OVar("xinv"),))
            results.append((rhs, "Mathlib: IsometryEquiv_mulRight_symm"))
    except Exception:
        pass
    return results


def _r0106_divRight_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.divRight_symm
    # (divRight c).symm = mulRight c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("divRight_c_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("mulRight", (OVar("c"),))
            results.append((rhs, "Mathlib: IsometryEquiv_divRight_symm"))
    except Exception:
        pass
    return results


def _r0107_inv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.inv_symm
    # (inv G).symm = inv G
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inv_G_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inv", (OVar("G"),))
            results.append((rhs, "Mathlib: IsometryEquiv_inv_symm"))
    except Exception:
        pass
    return results


def _r0108_edist_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.edist_eq
    # edist (f x) (f y) = edist x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "edist", 2)
    if args is not None:
        try:
            rhs = OOp("edist", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: Isometry_edist_eq"))
        except Exception:
            pass
    return results


def _r0109_preimage_closedEBall(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.preimage_closedEBall
    # f ⁻¹' Metric.closedEBall (f x) r = Metric.closedEBall x r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 4)
    if args is not None:
        try:
            rhs = OOp("Metric_closedEBall", (OVar("x"), args[3],))
            results.append((rhs, "Mathlib: Isometry_preimage_closedEBall"))
        except Exception:
            pass
    return results


def _r0110_preimage_eball(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.preimage_eball
    # f ⁻¹' Metric.eball (f x) r = Metric.eball x r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 4)
    if args is not None:
        try:
            rhs = OOp("Metric_eball", (OVar("x"), args[3],))
            results.append((rhs, "Mathlib: Isometry_preimage_eball"))
        except Exception:
            pass
    return results


def _r0111_ediam_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.ediam_image
    # Metric.ediam (f '' s) = Metric.ediam s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Metric_ediam", 1)
    if args is not None:
        try:
            rhs = OOp("Metric_ediam", (OVar("s"),))
            results.append((rhs, "Mathlib: Isometry_ediam_image"))
        except Exception:
            pass
    return results


def _r0112_ediam_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.ediam_range
    # Metric.ediam (range f) = Metric.ediam (univ : Set α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Metric_ediam", 1)
    if args is not None:
        try:
            rhs = OOp("Metric_ediam", (OOp("univ_set", (OVar("colon"), OVar("Set"), OVar("a"),)),))
            results.append((rhs, "Mathlib: Isometry_ediam_range"))
        except Exception:
            pass
    return results


def _r0113_edist_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryClass.edist_eq
    # edist (f x) (f y) = edist x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "edist", 2)
    if args is not None:
        try:
            rhs = OOp("edist", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: IsometryClass_edist_eq"))
        except Exception:
            pass
    return results


def _r0114_ediam_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryClass.ediam_image
    # Metric.ediam (f '' s) = Metric.ediam s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Metric_ediam", 1)
    if args is not None:
        try:
            rhs = OOp("Metric_ediam", (OVar("s"),))
            results.append((rhs, "Mathlib: IsometryClass_ediam_image"))
        except Exception:
            pass
    return results


def _r0115_ediam_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryClass.ediam_range
    # Metric.ediam (range f) = Metric.ediam (univ : Set α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Metric_ediam", 1)
    if args is not None:
        try:
            rhs = OOp("Metric_ediam", (OOp("univ_set", (OVar("colon"), OVar("Set"), OVar("a"),)),))
            results.append((rhs, "Mathlib: IsometryClass_ediam_range"))
        except Exception:
            pass
    return results


def _r0116_toEquiv_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.toEquiv_inj
    # e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_1_toEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("e_2_toEquiv"), OVar("e_1"))), OVar("e_2")))
            results.append((rhs, "Mathlib: IsometryEquiv_toEquiv_inj"))
    except Exception:
        pass
    return results


def _r0117_coe_eq_toEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_eq_toEquiv
    # h a = h.toEquiv a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h", 1)
    if args is not None:
        try:
            rhs = OOp("h_toEquiv", (args[0],))
            results.append((rhs, "Mathlib: IsometryEquiv_coe_eq_toEquiv"))
        except Exception:
            pass
    return results


def _r0118_coe_toEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_toEquiv
    # ⇑h.toEquiv = h
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h_toEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("h")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_toEquiv"))
    except Exception:
        pass
    return results


def _r0119_edist_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.edist_eq
    # edist (h x) (h y) = edist x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "edist", 2)
    if args is not None:
        try:
            rhs = OOp("edist", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: IsometryEquiv_edist_eq"))
        except Exception:
            pass
    return results


def _r0120_dist_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.dist_eq
    # dist (h x) (h y) = dist x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dist", 2)
    if args is not None:
        try:
            rhs = OOp("dist", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: IsometryEquiv_dist_eq"))
        except Exception:
            pass
    return results


def _r0121_nndist_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.nndist_eq
    # nndist (h x) (h y) = nndist x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nndist", 2)
    if args is not None:
        try:
            rhs = OOp("nndist", (OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: IsometryEquiv_nndist_eq"))
        except Exception:
            pass
    return results


def _r0122_ediam_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.ediam_image
    # Metric.ediam (h '' s) = Metric.ediam s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Metric_ediam", 1)
    if args is not None:
        try:
            rhs = OOp("Metric_ediam", (OVar("s"),))
            results.append((rhs, "Mathlib: IsometryEquiv_ediam_image"))
        except Exception:
            pass
    return results


def _r0123_trans_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.trans_apply
    # h₁.trans h₂ x = h₂ (h₁ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_1_trans", 2)
    if args is not None:
        try:
            rhs = OOp("h_2", (OOp("h_1", (args[1],)),))
            results.append((rhs, "Mathlib: IsometryEquiv_trans_apply"))
        except Exception:
            pass
    return results


def _r0124_coe_symm_toEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_symm_toEquiv
    # ⇑h.toEquiv.symm = h.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h_toEquiv_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("h_symm")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_symm_toEquiv"))
    except Exception:
        pass
    return results


def _r0125_apply_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.apply_symm_apply
    # h (h.symm y) = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h", 1)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: IsometryEquiv_apply_symm_apply"))
        except Exception:
            pass
    return results


def _r0126_eq_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.eq_symm_apply
    # x = h.symm y ↔ h x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("h_symm", (OVar("y"),)), OOp("h", (OVar("x"),)))), OVar("y")))
            results.append((rhs, "Mathlib: IsometryEquiv_eq_symm_apply"))
    except Exception:
        pass
    return results


def _r0127_range_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.range_eq_univ
    # range h = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: IsometryEquiv_range_eq_univ"))
        except Exception:
            pass
    return results


def _r0128_image_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.image_symm
    # image h.symm = preimage h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image", 1)
    if args is not None:
        try:
            rhs = OOp("preimage", (OVar("h"),))
            results.append((rhs, "Mathlib: IsometryEquiv_image_symm"))
        except Exception:
            pass
    return results


def _r0129_preimage_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.preimage_symm
    # preimage h.symm = image h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preimage", 1)
    if args is not None:
        try:
            rhs = OOp("image", (OVar("h"),))
            results.append((rhs, "Mathlib: IsometryEquiv_preimage_symm"))
        except Exception:
            pass
    return results


def _r0130_symm_trans_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.symm_trans_apply
    # (h₁.trans h₂).symm x = h₁.symm (h₂.symm x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_1_trans_h_2_symm", 1)
    if args is not None:
        try:
            rhs = OOp("h_1_symm", (OOp("h_2_symm", (args[0],)),))
            results.append((rhs, "Mathlib: IsometryEquiv_symm_trans_apply"))
        except Exception:
            pass
    return results


def _r0131_ediam_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.ediam_univ
    # Metric.ediam (univ : Set α) = Metric.ediam (univ : Set β)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Metric_ediam", 1)
    if args is not None:
        try:
            rhs = OOp("Metric_ediam", (OOp("univ_set", (OVar("colon"), OVar("Set"), OVar("b"),)),))
            results.append((rhs, "Mathlib: IsometryEquiv_ediam_univ"))
        except Exception:
            pass
    return results


def _r0132_ediam_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.ediam_preimage
    # Metric.ediam (h ⁻¹' s) = Metric.ediam s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Metric_ediam", 1)
    if args is not None:
        try:
            rhs = OOp("Metric_ediam", (OVar("s"),))
            results.append((rhs, "Mathlib: IsometryEquiv_ediam_preimage"))
        except Exception:
            pass
    return results


def _r0133_preimage_closedEBall(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.preimage_closedEBall
    # h ⁻¹' Metric.closedEBall x r = Metric.closedEBall (h.symm x) r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h", 4)
    if args is not None:
        try:
            rhs = OOp("Metric_closedEBall", (OOp("h_symm", (args[2],)), args[3],))
            results.append((rhs, "Mathlib: IsometryEquiv_preimage_closedEBall"))
        except Exception:
            pass
    return results


def _r0134_image_eball(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.image_eball
    # h '' Metric.eball x r = Metric.eball (h x) r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h", 4)
    if args is not None:
        try:
            rhs = OOp("Metric_eball", (OOp("h", (args[2],)), args[3],))
            results.append((rhs, "Mathlib: IsometryEquiv_image_eball"))
        except Exception:
            pass
    return results


def _r0135_image_closedEBall(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.image_closedEBall
    # h '' Metric.closedEBall x r = Metric.closedEBall (h x) r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h", 4)
    if args is not None:
        try:
            rhs = OOp("Metric_closedEBall", (OOp("h", (args[2],)), args[3],))
            results.append((rhs, "Mathlib: IsometryEquiv_image_closedEBall"))
        except Exception:
            pass
    return results


def _r0136_coe_toHomeomorph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_toHomeomorph
    # ⇑h.toHomeomorph = h
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h_toHomeomorph")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("h")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_toHomeomorph"))
    except Exception:
        pass
    return results


def _r0137_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.coe_one
    # ⇑(1 : α ≃ᵢ α) = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_a_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: IsometryEquiv_coe_one"))
    except Exception:
        pass
    return results


def _r0138_sumArrowIsometryEquivProdArrow_toHomeomo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.sumArrowIsometryEquivProdArrow_toHomeomorph
    # sumArrowIsometryEquivProdArrow.toHomeomorph     = Homeomorph.sumArrowHomeomorphProdArrow (ι := α) (ι' := β) (X := γ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sumArrowIsometryEquivProdArrow_toHomeomorph")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Homeomorph_sumArrowHomeomorphProdArrow", (OOp("i", (OVar("colon_eq"), OVar("a"),)), OOp("i_prime", (OVar("colon_eq"), OVar("b"),)), OOp("X", (OVar("colon_eq"), OVar("g"),)),))
            results.append((rhs, "Mathlib: IsometryEquiv_sumArrowIsometryEquivProdArrow_toHomeomorph"))
    except Exception:
        pass
    return results


def _r0139_edist_append_eq_max_edist(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.edist_append_eq_max_edist
    # edist (Fin.append x y) (Fin.append x2 y2) = max (edist x x2) (edist y y2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "edist", 2)
    if args is not None:
        try:
            rhs = OOp("max", (OOp("edist", (OVar("x"), OVar("x2"),)), OOp("edist", (OVar("y"), OVar("y2"),)),))
            results.append((rhs, "Mathlib: Fin_edist_append_eq_max_edist"))
        except Exception:
            pass
    return results


def _r0140_appendIsometry_toHomeomorph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.appendIsometry_toHomeomorph
    # (Fin.appendIsometry m n).toHomeomorph = Fin.appendHomeomorph (X := α) m n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Fin_appendIsometry_m_n_toHomeomorph")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Fin_appendHomeomorph", (OOp("X", (OVar("colon_eq"), OVar("a"),)), OVar("m"), OVar("n"),))
            results.append((rhs, "Mathlib: Fin_appendIsometry_toHomeomorph"))
    except Exception:
        pass
    return results


def _r0141_coe_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryClass.coe_coe
    # ⇑(toIsometryEquiv f) = ⇑f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toIsometryEquiv_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: IsometryClass_coe_coe"))
    except Exception:
        pass
    return results


def _r0142_map_adj_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.map_adj_iff
    # G'.Adj (f v) (f w) ↔ G.Adj v w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G_prime_Adj", 2)
    if args is not None:
        try:
            rhs = OOp("G_Adj", (OVar("v"), OVar("w"),))
            results.append((rhs, "Mathlib: Iso_map_adj_iff"))
        except Exception:
            pass
    return results


def _r0143_map_mem_edgeSet_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.map_mem_edgeSet_iff
    # e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("e"), OVar("G_edgeSet")))
            results.append((rhs, "Mathlib: Iso_map_mem_edgeSet_iff"))
        except Exception:
            pass
    return results


def _r0144_apply_mem_neighborSet_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Iso.apply_mem_neighborSet_iff
    # f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("w"), OOp("G_neighborSet", (OVar("v"),))))
            results.append((rhs, "Mathlib: Iso_apply_mem_neighborSet_iff"))
        except Exception:
            pass
    return results


def _r0145_map_posDef_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.IsometryEquiv.map_posDef_iff
    # (Q'.restrict (V.map e.toLinearMap)).PosDef ↔ (Q.restrict V).PosDef
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Q_prime_restrict_V_map_e_toLinearMap_PosDef")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Q_restrict_V_PosDef")
            results.append((rhs, "Mathlib: QuadraticMap_IsometryEquiv_map_posDef_iff"))
    except Exception:
        pass
    return results


def _r0146_map_negDef_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuadraticMap.IsometryEquiv.map_negDef_iff
    # ((-Q').restrict (V.map e.toLinearMap)).PosDef ↔ ((-Q).restrict V).PosDef
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_Q_prime_restrict_V_map_e_toLinearMap_PosDef")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_Q_restrict_V_PosDef")
            results.append((rhs, "Mathlib: QuadraticMap_IsometryEquiv_map_negDef_iff"))
    except Exception:
        pass
    return results


def _r0147_tendsto_nhds_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.tendsto_nhds_iff
    # Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto (f ∘ g) a (𝓝 (f b))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Filter_Tendsto", 3)
    if args is not None:
        try:
            rhs = OOp("Filter_Tendsto", (OOp("comp", (OVar("f"), args[0])), args[1], OOp("_unknown", (OOp("f", (OVar("b"),)),)),))
            results.append((rhs, "Mathlib: Isometry_tendsto_nhds_iff"))
        except Exception:
            pass
    return results


def _r0148_comp_continuousOn_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.comp_continuousOn_iff
    # ContinuousOn (f ∘ g) s ↔ ContinuousOn g s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ContinuousOn", 2)
    if args is not None:
        try:
            rhs = OOp("ContinuousOn", (OVar("g"), args[1],))
            results.append((rhs, "Mathlib: Isometry_comp_continuousOn_iff"))
        except Exception:
            pass
    return results


def _r0149_comp_continuous_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.comp_continuous_iff
    # Continuous (f ∘ g) ↔ Continuous g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Continuous", 1)
    if args is not None:
        try:
            rhs = OOp("Continuous", (OVar("g"),))
            results.append((rhs, "Mathlib: Isometry_comp_continuous_iff"))
        except Exception:
            pass
    return results


def _r0150_toEquiv_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.toEquiv_injective
    # Injective (toEquiv : (α ≃ᵢ β) → (α ≃ β))   | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl  @[simp] theorem toEquiv_inj {e₁ e₂ : α ≃ᵢ β} : 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("e_1"), OVar("e_2")))
            results.append((rhs, "Mathlib: IsometryEquiv_toEquiv_injective"))
        except Exception:
            pass
    return results


def _r0151_comp_continuous_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsometryEquiv.comp_continuous_iff
    # Continuous (h ∘ f) ↔ Continuous f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Continuous", 1)
    if args is not None:
        try:
            rhs = OOp("Continuous", (OVar("f"),))
            results.append((rhs, "Mathlib: IsometryEquiv_comp_continuous_iff"))
        except Exception:
            pass
    return results


def _r0152_lipschitzWith_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Isometry.lipschitzWith_iff
    # LipschitzWith K (g ∘ f) ↔ LipschitzWith K f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LipschitzWith", 2)
    if args is not None:
        try:
            rhs = OOp("LipschitzWith", (args[0], OVar("f"),))
            results.append((rhs, "Mathlib: Isometry_lipschitzWith_iff"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_equiv rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("==", "CompleteSpace", "Continuous", "ContinuousOn", "Filter_Tendsto", "Fin_append", "Fintype_card", "G_prime_Adj", "G_prime_degree", "G_prime_neighborSet", "Iso_conj", "Iso_homCongr", "Iso_op", "Iso_refl", "Iso_unop", "LipschitzWith", "Measure_map", "Metric_ediam", "N_rho", "Q_2", "Q_radical_map", "SimpleGraph_Iso_comap", "SimpleGraph_Iso_comap_f_G_symm", "SimpleGraph_Iso_map", "SimpleGraph_Iso_map_f_G_symm", "W_rho", "_0", "_unknown", "a", "comp", "coveringNumber", "dimH", "dist", "e", "e_1_star_e_2", "e_hom_app_X_unop", "e_inv_app_X_unop", "e_map", "e_toDilationEquiv", "edist", "einv", "f", "f_comp", "f_symm", "f_symm_toHom_comp", "f_tmul", "f_toHom_comp", "fst_M_2_Q_1_comp", "h", "h_1_trans",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_equiv axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_equiv rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_affineIsometryOfStrictConvexSpace_apply(term, ctx))
    results.extend(_r0001_coe_toRealAffineIsometryEquiv(term, ctx))
    results.extend(_r0002_coe_withLpUniqueProd(term, ctx))
    results.extend(_r0003_op_unop(term, ctx))
    results.extend(_r0004_op_refl(term, ctx))
    results.extend(_r0005_op_trans(term, ctx))
    results.extend(_r0006_unop_refl(term, ctx))
    results.extend(_r0007_unop_trans(term, ctx))
    results.extend(_r0008_unop_inv_hom_id_app(term, ctx))
    results.extend(_r0009_map_symm_apply(term, ctx))
    results.extend(_r0010_coe_toLinearMap(term, ctx))
    results.extend(_r0011_comp_id(term, ctx))
    results.extend(_r0012_comp_assoc(term, ctx))
    results.extend(_r0013_map_app(term, ctx))
    results.extend(_r0014_symm_apply_apply(term, ctx))
    results.extend(_r0015_coe_symm_toLinearEquiv(term, ctx))
    results.extend(_r0016_hausdorffMeasure_preimage(term, ctx))
    results.extend(_r0017_map_hausdorffMeasure(term, ctx))
    results.extend(_r0018_coe_symm_toDilationEquiv(term, ctx))
    results.extend(_r0019_dimH_preimage(term, ctx))
    results.extend(_r0020_dimH_univ(term, ctx))
    results.extend(_r0021_coe_mk(term, ctx))
    results.extend(_r0022_symm_symm(term, ctx))
    results.extend(_r0023_symm_apply_apply(term, ctx))
    results.extend(_r0024_symm_apply_eq(term, ctx))
    results.extend(_r0025_preimage_eball(term, ctx))
    results.extend(_r0026_coe_toHomeomorph_symm(term, ctx))
    results.extend(_r0027_coe_mul(term, ctx))
    results.extend(_r0028_mul_apply(term, ctx))
    results.extend(_r0029_inv_apply_self(term, ctx))
    results.extend(_r0030_apply_inv_self(term, ctx))
    results.extend(_r0031_comp_continuousOn_iff(term, ctx))
    results.extend(_r0032_completeSpace_iff(term, ctx))
    results.extend(_r0033_conj_eq_conj(term, ctx))
    results.extend(_r0034_conj_hom_eq_conj(term, ctx))
    results.extend(_r0035_homCongr_eq_arrowCongr(term, ctx))
    results.extend(_r0036_conj_eq_conj(term, ctx))
    results.extend(_r0037_homCongr_eq_arrowCongr(term, ctx))
    results.extend(_r0038_conj_eq_conj(term, ctx))
    results.extend(_r0039_coe_affineIsometryOfStrictConvexSpace(term, ctx))
    results.extend(_r0040_midpoint_fixed(term, ctx))
    results.extend(_r0041_map_midpoint(term, ctx))
    results.extend(_r0042_coe_toRealLinearIsometryEquivOfMapZero(term, ctx))
    results.extend(_r0043_coe_toRealLinearIsometryEquivOfMapZero_s(term, ctx))
    results.extend(_r0044_coeFn_toRealAffineIsometryEquiv(term, ctx))
    results.extend(_r0045_norm_map_of_map_one(term, ctx))
    results.extend(_r0046_nnnorm_map_of_map_one(term, ctx))
    results.extend(_r0047_withLpProdComm_apply(term, ctx))
    results.extend(_r0048_withLpProdComm_symm(term, ctx))
    results.extend(_r0049_coe_withLpProdUnique(term, ctx))
    results.extend(_r0050_conj_rho(term, ctx))
    results.extend(_r0051_isoFunctorOfIsoInverse_isoInverseOfIsoFu(term, ctx))
    results.extend(_r0052_isoInverseOfIsoFunctor_isoFunctorOfIsoIn(term, ctx))
    results.extend(_r0053_unop_op(term, ctx))
    results.extend(_r0054_op_symm(term, ctx))
    results.extend(_r0055_unop_symm(term, ctx))
    results.extend(_r0056_unop_hom_inv_id_app(term, ctx))
    results.extend(_r0057_card_edgeFinset_eq(term, ctx))
    results.extend(_r0058_degree_eq(term, ctx))
    results.extend(_r0059_minDegree_eq(term, ctx))
    results.extend(_r0060_maxDegree_eq(term, ctx))
    results.extend(_r0061_symm_toHom_comp_toHom(term, ctx))
    results.extend(_r0062_toHom_comp_symm_toHom(term, ctx))
    results.extend(_r0063_card_eq(term, ctx))
    results.extend(_r0064_comap_apply(term, ctx))
    results.extend(_r0065_comap_symm_apply(term, ctx))
    results.extend(_r0066_map_apply(term, ctx))
    results.extend(_r0067_toEmbedding_completeGraph(term, ctx))
    results.extend(_r0068_coe_comp(term, ctx))
    results.extend(_r0069_preimage_perpBisector(term, ctx))
    results.extend(_r0070_euclideanHausdorffMeasure_image(term, ctx))
    results.extend(_r0071_euclideanHausdorffMeasure_preimage(term, ctx))
    results.extend(_r0072_map_euclideanHausdorffMeasure(term, ctx))
    results.extend(_r0073_map_app(term, ctx))
    results.extend(_r0074_ofEq_rfl(term, ctx))
    results.extend(_r0075_toLinearMap_comp(term, ctx))
    results.extend(_r0076_id_comp(term, ctx))
    results.extend(_r0077_coe_toLinearEquiv(term, ctx))
    results.extend(_r0078_apply_symm_apply(term, ctx))
    results.extend(_r0079_fst_comp_inl(term, ctx))
    results.extend(_r0080_snd_comp_inr(term, ctx))
    results.extend(_r0081_snd_comp_inl(term, ctx))
    results.extend(_r0082_fst_comp_inr(term, ctx))
    results.extend(_r0083_proj_comp_single_of_same(term, ctx))
    results.extend(_r0084_proj_comp_single_of_ne(term, ctx))
    results.extend(_r0085_map_radical(term, ctx))
    results.extend(_r0086_tmul_apply(term, ctx))
    results.extend(_r0087_hausdorffMeasure_image(term, ctx))
    results.extend(_r0088_hausdorffMeasure_preimage(term, ctx))
    results.extend(_r0089_map_hausdorffMeasure(term, ctx))
    results.extend(_r0090_hausdorffMeasure_image(term, ctx))
    results.extend(_r0091_conj_rho(term, ctx))
    results.extend(_r0092_eq_whisker(term, ctx))
    results.extend(_r0093_extensionHom_coe(term, ctx))
    results.extend(_r0094_mapRingHom_coe(term, ctx))
    results.extend(_r0095_coveringNumber_image(term, ctx))
    results.extend(_r0096_toDilation_ratio(term, ctx))
    results.extend(_r0097_toDilationEquiv_apply(term, ctx))
    results.extend(_r0098_toDilationEquiv_symm(term, ctx))
    results.extend(_r0099_coe_toDilationEquiv(term, ctx))
    results.extend(_r0100_toDilationEquiv_ratio(term, ctx))
    results.extend(_r0101_dimH_image(term, ctx))
    results.extend(_r0102_dimH_image(term, ctx))
    results.extend(_r0103_constSMul_symm(term, ctx))
    results.extend(_r0104_mulLeft_symm(term, ctx))
    results.extend(_r0105_mulRight_symm(term, ctx))
    results.extend(_r0106_divRight_symm(term, ctx))
    results.extend(_r0107_inv_symm(term, ctx))
    results.extend(_r0108_edist_eq(term, ctx))
    results.extend(_r0109_preimage_closedEBall(term, ctx))
    results.extend(_r0110_preimage_eball(term, ctx))
    results.extend(_r0111_ediam_image(term, ctx))
    results.extend(_r0112_ediam_range(term, ctx))
    results.extend(_r0113_edist_eq(term, ctx))
    results.extend(_r0114_ediam_image(term, ctx))
    results.extend(_r0115_ediam_range(term, ctx))
    results.extend(_r0116_toEquiv_inj(term, ctx))
    results.extend(_r0117_coe_eq_toEquiv(term, ctx))
    results.extend(_r0118_coe_toEquiv(term, ctx))
    results.extend(_r0119_edist_eq(term, ctx))
    results.extend(_r0120_dist_eq(term, ctx))
    results.extend(_r0121_nndist_eq(term, ctx))
    results.extend(_r0122_ediam_image(term, ctx))
    results.extend(_r0123_trans_apply(term, ctx))
    results.extend(_r0124_coe_symm_toEquiv(term, ctx))
    results.extend(_r0125_apply_symm_apply(term, ctx))
    results.extend(_r0126_eq_symm_apply(term, ctx))
    results.extend(_r0127_range_eq_univ(term, ctx))
    results.extend(_r0128_image_symm(term, ctx))
    results.extend(_r0129_preimage_symm(term, ctx))
    results.extend(_r0130_symm_trans_apply(term, ctx))
    results.extend(_r0131_ediam_univ(term, ctx))
    results.extend(_r0132_ediam_preimage(term, ctx))
    results.extend(_r0133_preimage_closedEBall(term, ctx))
    results.extend(_r0134_image_eball(term, ctx))
    results.extend(_r0135_image_closedEBall(term, ctx))
    results.extend(_r0136_coe_toHomeomorph(term, ctx))
    results.extend(_r0137_coe_one(term, ctx))
    results.extend(_r0138_sumArrowIsometryEquivProdArrow_toHomeomo(term, ctx))
    results.extend(_r0139_edist_append_eq_max_edist(term, ctx))
    results.extend(_r0140_appendIsometry_toHomeomorph(term, ctx))
    results.extend(_r0141_coe_coe(term, ctx))
    results.extend(_r0142_map_adj_iff(term, ctx))
    results.extend(_r0143_map_mem_edgeSet_iff(term, ctx))
    results.extend(_r0144_apply_mem_neighborSet_iff(term, ctx))
    results.extend(_r0145_map_posDef_iff(term, ctx))
    results.extend(_r0146_map_negDef_iff(term, ctx))
    results.extend(_r0147_tendsto_nhds_iff(term, ctx))
    results.extend(_r0148_comp_continuousOn_iff(term, ctx))
    results.extend(_r0149_comp_continuous_iff(term, ctx))
    results.extend(_r0150_toEquiv_injective(term, ctx))
    results.extend(_r0151_comp_continuous_iff(term, ctx))
    results.extend(_r0152_lipschitzWith_iff(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_equiv rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("IsometricContinuousFunctionalCalculus_isGreatest_norm_spectrum", "IsGreatest_prime_prime_spectrum_a_a", "Not an equality or iff proposition"),
    ("IsometricContinuousFunctionalCalculus_norm_spectrum_le", "_unknown", "Empty proposition"),
    ("IsometricContinuousFunctionalCalculus_isGreatest_nnnorm_spectrum", "IsGreatest_prime_prime_spectrum_a_a", "Not an equality or iff proposition"),
    ("IsometricContinuousFunctionalCalculus_nnnorm_spectrum_le", "_unknown", "Empty proposition"),
    ("IsometricContinuousFunctionalCalculus_isGreatest_spectrum", "IsGreatest_sig_ge_0_a_a", "Not an equality or iff proposition"),
    ("IsometricContinuousFunctionalCalculus_spectrum_le", "_unknown", "Empty proposition"),
    ("IsometryEquiv_toRealLinearIsometryEquiv_apply", "f_toRealLinearIsometryEquiv_colon_E_to_F_x_eq_f_x_minus_f_0", "Not an equality or iff proposition"),
    ("IsometryEquiv_toRealLinearIsometryEquiv_symm_apply", "f_toRealLinearIsometryEquiv_symm_colon_F_to_E_y_eq_f_symm_y_plus_f_0", "Not an equality or iff proposition"),
    ("Isometry_withLpProdMap", "Isometry_WithLp_map_p_Prod_map_f_g", "Not an equality or iff proposition"),
    ("Iso_isContained", "G_H", "Not an equality or iff proposition"),
    ("Iso_isContained", "_unknown", "Empty proposition"),
    ("Iso_isIndContained", "G_H", "Not an equality or iff proposition"),
    ("Iso_isIndContained", "_unknown", "Empty proposition"),
    ("Isometry_mapsTo_perpBisector", "MapsTo_f_perpBisector_p_1_p_2_perpBisector_f_p_1_f_p_2", "Not an equality or iff proposition"),
    ("Isometry_cospherical", "Cospherical_f_prime_prime_ps", "Not an equality or iff proposition"),
    ("IsometryEquiv_measurePreserving_euclideanHausdorffMeasure", "MeasurePreserving_e_muHE_d_muHE_d", "Not an equality or iff proposition"),
    ("QuadraticMap_Isometry_toLinearMap_injective", "Function_Injective_Isometry_toLinearMap_colon_Q_1_to_q_Q_2_to_M_1_to_R_M_2", "Not an equality or iff proposition"),
    ("QuadraticMap_Isometry_ext", "_unknown", "Empty proposition"),
    ("IsometryEquiv_measurePreserving_hausdorffMeasure", "MeasurePreserving_e_muH_d_muH_d", "Not an equality or iff proposition"),
    ("Isometry_completion_extension", "Isometry_Completion_extension_f", "Not an equality or iff proposition"),
    ("Isometry_completion_map", "Isometry_Completion_map_f", "Not an equality or iff proposition"),
    ("Isometry_isometry_mapRingHom", "Isometry_h_mapRingHom", "Not an equality or iff proposition"),
    ("Isometry_coveringNumber_image", "_unknown", "Empty proposition"),
    ("IsometryEquiv_toDilationEquiv_toDilation", "e_toDilationEquiv_toDilation_colon_X_to_Y_eq_e_isometry_toDilation", "Not an equality or iff proposition"),
    ("Isometry_lipschitz", "LipschitzWith_1_f", "Not an equality or iff proposition"),
    ("Isometry_antilipschitz", "AntilipschitzWith_1_f", "Not an equality or iff proposition"),
    ("isometry_subsingleton", "Isometry_f", "Not an equality or iff proposition"),
    ("isometry_id", "Isometry_id_colon_a_to_a", "Not an equality or iff proposition"),
    ("Isometry_prodMap", "Isometry_Prod_map_f_g", "Not an equality or iff proposition"),
    ("Isometry_piMap", "Isometry_Pi_map_f", "Not an equality or iff proposition"),
    ("Isometry_single", "Isometry_Pi_single_M_colon_eq_E_i", "Not an equality or iff proposition"),
    ("Isometry_inl", "Isometry_AddMonoidHom_inl_a_b", "Not an equality or iff proposition"),
    ("Isometry_inr", "Isometry_AddMonoidHom_inr_a_b", "Not an equality or iff proposition"),
    ("Isometry_comp", "Isometry_g_comp_f", "Not an equality or iff proposition"),
    ("Isometry_uniformContinuous", "UniformContinuous_f", "Not an equality or iff proposition"),
    ("Isometry_isUniformInducing", "IsUniformInducing_f", "Not an equality or iff proposition"),
    ("Isometry_continuous", "Continuous_f", "Not an equality or iff proposition"),
    ("Isometry_right_inv", "Isometry_g", "Not an equality or iff proposition"),
    ("Isometry_mapsTo_eball", "MapsTo_f_Metric_eball_x_r_Metric_eball_f_x_r", "Not an equality or iff proposition"),
    ("Isometry_mapsTo_closedEBall", "MapsTo_f_Metric_closedEBall_x_r_Metric_closedEBall_f_x_r", "Not an equality or iff proposition"),
    ("isometry_subtype_coe", "Isometry_colon_s_to_a", "Not an equality or iff proposition"),
    ("NNReal_isometry_coe", "Isometry_colon_NNReal_to", "Not an equality or iff proposition"),
    ("IsometryClass_continuous", "Continuous_f", "Not an equality or iff proposition"),
    ("IsometryClass_lipschitz", "LipschitzWith_1_f", "Not an equality or iff proposition"),
    ("IsometryClass_antilipschitz", "AntilipschitzWith_1_f", "Not an equality or iff proposition"),
    ("IsometryEquiv_isometry", "Isometry_h", "Not an equality or iff proposition"),
    ("IsometryEquiv_bijective", "Bijective_h", "Not an equality or iff proposition"),
    ("IsometryEquiv_injective", "Injective_h", "Not an equality or iff proposition"),
    ("IsometryEquiv_surjective", "Surjective_h", "Not an equality or iff proposition"),
    ("IsometryEquiv_continuous", "Continuous_h", "Not an equality or iff proposition"),
    ("IsometryEquiv_ext", "_unknown", "Empty proposition"),
    ("IsometryEquiv_symm_bijective", "Bijective_IsometryEquiv_symm_colon_a_b_to_b_a", "Not an equality or iff proposition"),
    ("IsometryEquiv_symm_comp_self", "h_symm_colon_b_to_a_comp_h_eq_id", "Not an equality or iff proposition"),
    ("IsometryEquiv_self_comp_symm", "h_colon_a_to_b_comp_h_symm_eq_id", "Not an equality or iff proposition"),
    ("IsometryEquiv_comp_continuous_iff", "_unknown", "Empty proposition"),
    ("IsometryEquiv_completeSpace", "CompleteSpace_a", "Not an equality or iff proposition"),
    ("IsometryClass_toIsometryEquiv_injective", "Function_Injective_colon_F_to_a_b", "Not an equality or iff proposition"),
]
