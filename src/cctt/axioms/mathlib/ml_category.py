"""Mathlib: Category — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 2839 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_category"
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

def _r0000_toBialgEquiv_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toBialgEquiv_refl
    # toBialgEquiv (.refl X) = .refl _ _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toBialgEquiv", 1)
    if args is not None:
        try:
            rhs = OOp("refl", (OVar("_unknown"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toBialgEquiv_refl"))
        except Exception:
            pass
    return results


def _r0001_toBialgEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toBialgEquiv_symm
    # toBialgEquiv e.symm = (toBialgEquiv e).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toBialgEquiv", 1)
    if args is not None:
        try:
            rhs = OVar("toBialgEquiv_e_symm")
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toBialgEquiv_symm"))
        except Exception:
            pass
    return results


def _r0002_toBialgEquiv_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toBialgEquiv_trans
    # toBialgEquiv (e ≪≫ f) = e.toBialgEquiv.trans f.toBialgEquiv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toBialgEquiv", 1)
    if args is not None:
        try:
            rhs = OOp("e_toBialgEquiv_trans", (OVar("f_toBialgEquiv"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toBialgEquiv_trans"))
        except Exception:
            pass
    return results


def _r0003_toCoalgEquiv_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toCoalgEquiv_refl
    # toCoalgEquiv (.refl X) = .refl _ _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCoalgEquiv", 1)
    if args is not None:
        try:
            rhs = OOp("refl", (OVar("_unknown"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toCoalgEquiv_refl"))
        except Exception:
            pass
    return results


def _r0004_toCoalgEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toCoalgEquiv_symm
    # toCoalgEquiv e.symm = (toCoalgEquiv e).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCoalgEquiv", 1)
    if args is not None:
        try:
            rhs = OVar("toCoalgEquiv_e_symm")
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toCoalgEquiv_symm"))
        except Exception:
            pass
    return results


def _r0005_toCoalgEquiv_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toCoalgEquiv_trans
    # toCoalgEquiv (e ≪≫ f) = e.toCoalgEquiv.trans f.toCoalgEquiv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCoalgEquiv", 1)
    if args is not None:
        try:
            rhs = OOp("e_toCoalgEquiv_trans", (OVar("f_toCoalgEquiv"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toCoalgEquiv_trans"))
        except Exception:
            pass
    return results


def _r0006_toHopfAlgEquiv_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toHopfAlgEquiv_refl
    # toHopfAlgEquiv (.refl X) = .refl _ _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toHopfAlgEquiv", 1)
    if args is not None:
        try:
            rhs = OOp("refl", (OVar("_unknown"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toHopfAlgEquiv_refl"))
        except Exception:
            pass
    return results


def _r0007_toHopfAlgEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toHopfAlgEquiv_symm
    # toHopfAlgEquiv e.symm = (toHopfAlgEquiv e).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toHopfAlgEquiv", 1)
    if args is not None:
        try:
            rhs = OVar("toHopfAlgEquiv_e_symm")
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toHopfAlgEquiv_symm"))
        except Exception:
            pass
    return results


def _r0008_toHopfAlgEquiv_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toHopfAlgEquiv_trans
    # toHopfAlgEquiv (e ≪≫ f) = e.toHopfAlgEquiv.trans f.toHopfAlgEquiv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toHopfAlgEquiv", 1)
    if args is not None:
        try:
            rhs = OOp("e_toHopfAlgEquiv_trans", (OVar("f_toHopfAlgEquiv"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toHopfAlgEquiv_trans"))
        except Exception:
            pass
    return results


def _r0009_toLinearEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toLinearEquiv_symm
    # i.toLinearEquiv.symm = i.symm.toLinearEquiv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_toLinearEquiv_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("i_symm_toLinearEquiv")
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toLinearEquiv_symm"))
    except Exception:
        pass
    return results


def _r0010_toLinearMap_toLinearEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.toLinearMap_toLinearEquiv
    # i.toLinearEquiv = i.hom.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("i_toLinearEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("i_hom_hom")
            results.append((rhs, "Mathlib: CategoryTheory_Iso_toLinearMap_toLinearEquiv"))
    except Exception:
        pass
    return results


def _r0011_mk_0_homEquiv_0_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Abelian.mk₀_homEquiv₀_apply
    # mk₀ (homEquiv₀ f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mk_0", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CategoryTheory_Abelian_mk_0_homEquiv_0_apply"))
        except Exception:
            pass
    return results


def _r0012_mk_0_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Abelian.mk₀_add
    # mk₀ (f + g) = mk₀ f + mk₀ g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mk_0", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("mk_0", (OVar("f"),)), OOp("mk_0", (OVar("g"),))))
            results.append((rhs, "Mathlib: CategoryTheory_Abelian_mk_0_add"))
        except Exception:
            pass
    return results


def _r0013_mapExtAddHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Functor.mapExtAddHom_apply
    # F.mapExtAddHom X Y n e = e.mapExactFunctor F
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_mapExtAddHom", 4)
    if args is not None:
        try:
            rhs = OOp("e_mapExactFunctor", (OVar("F"),))
            results.append((rhs, "Mathlib: Functor_mapExtAddHom_apply"))
        except Exception:
            pass
    return results


def _r0014_mapExtLinearMap_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Functor.mapExtLinearMap_coe
    # ⇑(F.mapExtLinearMap R X Y n) = Ext.mapExactFunctor F
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("F_mapExtLinearMap_R_X_Y_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Ext_mapExactFunctor", (OVar("F"),))
            results.append((rhs, "Mathlib: Functor_mapExtLinearMap_coe"))
    except Exception:
        pass
    return results


def _r0015_mapToComposableArrows_app_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.mapToComposableArrows_app_1
    # (ShortComplex.mapToComposableArrows φ).app 1 = φ.τ₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ShortComplex_mapToComposableArrows_phi_app", 1)
    if args is not None:
        try:
            rhs = OVar("phi_tau_2")
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_mapToComposableArrows_app_1"))
        except Exception:
            pass
    return results


def _r0016_mapToComposableArrows_app_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.mapToComposableArrows_app_2
    # (ShortComplex.mapToComposableArrows φ).app 2 = φ.τ₃
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ShortComplex_mapToComposableArrows_phi_app", 1)
    if args is not None:
        try:
            rhs = OVar("phi_tau_3")
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_mapToComposableArrows_app_2"))
        except Exception:
            pass
    return results


def _r0017_mapToComposableArrows_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.mapToComposableArrows_id
    # (ShortComplex.mapToComposableArrows (𝟙 S₁)) = 𝟙 S₁.toComposableArrows
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ShortComplex_mapToComposableArrows", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("S_1_toComposableArrows"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_mapToComposableArrows_id"))
        except Exception:
            pass
    return results


def _r0018_comp_d(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.ShortExact.comp_δ
    # HomologicalComplex.homologyMap S.g i ≫ hS.δ i j hij = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "HomologicalComplex_homologyMap", 7)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_ShortExact_comp_d"))
        except Exception:
            pass
    return results


def _r0019_mapHomotopyCategory_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.NatTrans.mapHomotopyCategory_comp
    # NatTrans.mapHomotopyCategory (α ≫ β) c =       NatTrans.mapHomotopyCategory α c ≫ NatTrans.mapHomotopyCategory β c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NatTrans_mapHomotopyCategory", 2)
    if args is not None:
        try:
            rhs = OOp("NatTrans_mapHomotopyCategory", (OVar("a"), args[1], OVar("_unknown"), OVar("NatTrans_mapHomotopyCategory"), OVar("b"), args[1],))
            results.append((rhs, "Mathlib: CategoryTheory_NatTrans_mapHomotopyCategory_comp"))
        except Exception:
            pass
    return results


def _r0020_mapHomologicalComplex_commShiftIso_inv_a(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_inv_app_f
    # (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).inv.app K).f i = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_mapHomologicalComplex_ComplexShape_up_commShiftIso_n_inv_app_K_f", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_mapHomologicalComplex_commShiftIso_inv_app_f"))
        except Exception:
            pass
    return results


def _r0021_id_tau_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.id_τ₂
    # Hom.τ₂ (𝟙 S) = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_tau_2", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_id_tau_2"))
        except Exception:
            pass
    return results


def _r0022_id_tau_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.id_τ₃
    # Hom.τ₃ (𝟙 S) = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_tau_3", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_id_tau_3"))
        except Exception:
            pass
    return results


def _r0023_comp_tau_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.comp_τ₁
    # (φ₁₂ ≫ φ₂₃).τ₁ = φ₁₂.τ₁ ≫ φ₂₃.τ₁
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_1_2_phi_2_3_tau_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("phi_1_2_tau_1", (OVar("_unknown"), OVar("phi_2_3_tau_1"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_comp_tau_1"))
    except Exception:
        pass
    return results


def _r0024_comp_tau_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.comp_τ₂
    # (φ₁₂ ≫ φ₂₃).τ₂ = φ₁₂.τ₂ ≫ φ₂₃.τ₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_1_2_phi_2_3_tau_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("phi_1_2_tau_2", (OVar("_unknown"), OVar("phi_2_3_tau_2"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_comp_tau_2"))
    except Exception:
        pass
    return results


def _r0025_zero_tau_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.zero_τ₂
    # Hom.τ₂ (0 : S₁ ⟶ S₂) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_tau_2", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_zero_tau_2"))
        except Exception:
            pass
    return results


def _r0026_zero_tau_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.zero_τ₃
    # Hom.τ₃ (0 : S₁ ⟶ S₂) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_tau_3", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_zero_tau_3"))
        except Exception:
            pass
    return results


def _r0027_pi_1Topi_2_comp_pi_2Topi_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.π₁Toπ₂_comp_π₂Toπ₃
    # (π₁Toπ₂ : (_ : _ ⥤ C) ⟶ _) ≫ π₂Toπ₃ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pi_1Topi_2_colon_colon_C", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_pi_1Topi_2_comp_pi_2Topi_3"))
        except Exception:
            pass
    return results


def _r0028_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.map_id
    # S.map (𝟭 C) = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_map", 1)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_map_id"))
        except Exception:
            pass
    return results


def _r0029_map_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.map_comp
    # S.map (F ⋙ G) = (S.map F).map G
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_map", 1)
    if args is not None:
        try:
            rhs = OOp("S_map_F_map", (OVar("G"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_map_comp"))
        except Exception:
            pass
    return results


def _r0030_liftK_pi_eq_zero_of_boundary(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.LeftHomologyData.liftK_π_eq_zero_of_boundary
    # h.liftK k (by rw [hx, assoc, S.zero, comp_zero]) ≫ h.π = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_liftK", 4)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_LeftHomologyData_liftK_pi_eq_zero_of_boundary"))
        except Exception:
            pass
    return results


def _r0031_toCycles_i(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.toCycles_i
    # S.toCycles ≫ S.iCycles = S.f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_toCycles", 2)
    if args is not None:
        try:
            rhs = OVar("S_f")
            results.append((rhs, "Mathlib: CategoryTheory_toCycles_i"))
        except Exception:
            pass
    return results


def _r0032_cyclesIsoX_2_inv_hom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.cyclesIsoX₂_inv_hom_id
    # (S.cyclesIsoX₂ hg).inv ≫ S.iCycles = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_cyclesIsoX_2_hg_inv", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_cyclesIsoX_2_inv_hom_id"))
        except Exception:
            pass
    return results


def _r0033_smul_tau_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.smul_τ₂
    # (a • φ).τ₂ = a • φ.τ₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_phi_tau_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a", (OVar("_unknown"), OVar("phi_tau_2"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_smul_tau_2"))
    except Exception:
        pass
    return results


def _r0034_smul_tau_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.smul_τ₃
    # (a • φ).τ₃ = a • φ.τ₃
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_phi_tau_3")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a", (OVar("_unknown"), OVar("phi_tau_3"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_smul_tau_3"))
    except Exception:
        pass
    return results


def _r0035_cyclesMap_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.cyclesMap_smul
    # cyclesMap (a • φ) = a • cyclesMap φ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclesMap", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("cyclesMap"), OVar("phi"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_cyclesMap_smul"))
        except Exception:
            pass
    return results


def _r0036_moduleCat_exact_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.moduleCat_exact_iff
    # S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("x_2")
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_moduleCat_exact_iff"))
        except Exception:
            pass
    return results


def _r0037_moduleCatLeftHomologyData_descH_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.moduleCatLeftHomologyData_descH_hom
    # (S.moduleCatLeftHomologyData.descH φ h).hom =       (LinearMap.range <| ModuleCat.Hom.hom _).liftQ          φ.hom (Linea
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_moduleCatLeftHomologyData_descH_phi_h_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("LinearMap_range_lt_pipe_ModuleCat_Hom_hom_liftQ", (OVar("phi_hom"), OOp("LinearMap_range_le_ker_iff_2", (OVar("lt_pipe"), OVar("ModuleCat_hom_ext_iff_1"), OVar("h"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_moduleCatLeftHomologyData_descH_hom"))
    except Exception:
        pass
    return results


def _r0038_add_tau_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.add_τ₂
    # (φ + φ').τ₂ = φ.τ₂ + φ'.τ₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_plus_phi_prime_tau_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("phi_tau_2"), OVar("phi_prime_tau_2")))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_add_tau_2"))
    except Exception:
        pass
    return results


def _r0039_add_tau_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.add_τ₃
    # (φ + φ').τ₃ = φ.τ₃ + φ'.τ₃
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_plus_phi_prime_tau_3")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("phi_tau_3"), OVar("phi_prime_tau_3")))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_add_tau_3"))
    except Exception:
        pass
    return results


def _r0040_sub_tau_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.sub_τ₁
    # (φ - φ').τ₁ = φ.τ₁ - φ'.τ₁
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_minus_phi_prime_tau_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("phi_tau_1"), OVar("phi_prime_tau_1")))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_sub_tau_1"))
    except Exception:
        pass
    return results


def _r0041_sub_tau_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.sub_τ₂
    # (φ - φ').τ₂ = φ.τ₂ - φ'.τ₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_minus_phi_prime_tau_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("phi_tau_2"), OVar("phi_prime_tau_2")))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_sub_tau_2"))
    except Exception:
        pass
    return results


def _r0042_sub_tau_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.sub_τ₃
    # (φ - φ').τ₃ = φ.τ₃ - φ'.τ₃
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_minus_phi_prime_tau_3")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("phi_tau_3"), OVar("phi_prime_tau_3")))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_sub_tau_3"))
    except Exception:
        pass
    return results


def _r0043_neg_tau_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.neg_τ₁
    # (-φ).τ₁ = -φ.τ₁
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_phi_tau_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_phi_tau_1")
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_neg_tau_1"))
    except Exception:
        pass
    return results


def _r0044_neg_tau_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.neg_τ₂
    # (-φ).τ₂ = -φ.τ₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_phi_tau_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_phi_tau_2")
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_neg_tau_2"))
    except Exception:
        pass
    return results


def _r0045_neg_tau_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.neg_τ₃
    # (-φ).τ₃ = -φ.τ₃
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_phi_tau_3")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_phi_tau_3")
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_neg_tau_3"))
    except Exception:
        pass
    return results


def _r0046_cyclesMap_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.cyclesMap_neg
    # cyclesMap (-φ) = -cyclesMap φ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclesMap", 1)
    if args is not None:
        try:
            rhs = OOp("minus_cyclesMap", (OVar("phi"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_cyclesMap_neg"))
        except Exception:
            pass
    return results


def _r0047_leftHomologyMap_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.leftHomologyMap_add
    # leftHomologyMap (φ + φ') = leftHomologyMap φ + leftHomologyMap φ'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "leftHomologyMap", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("leftHomologyMap", (OVar("phi"),)), OOp("leftHomologyMap", (OVar("phi_prime"),))))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_leftHomologyMap_add"))
        except Exception:
            pass
    return results


def _r0048_cyclesMap_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.cyclesMap_add
    # cyclesMap (φ + φ') = cyclesMap φ + cyclesMap φ'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclesMap", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("cyclesMap", (OVar("phi"),)), OOp("cyclesMap", (OVar("phi_prime"),))))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_cyclesMap_add"))
        except Exception:
            pass
    return results


def _r0049_leftHomologyMap_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.leftHomologyMap_sub
    # leftHomologyMap (φ - φ') = leftHomologyMap φ - leftHomologyMap φ'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "leftHomologyMap", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("leftHomologyMap", (OVar("phi"),)), OOp("leftHomologyMap", (OVar("phi_prime"),))))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_leftHomologyMap_sub"))
        except Exception:
            pass
    return results


def _r0050_cyclesMap_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.cyclesMap_sub
    # cyclesMap (φ - φ') = cyclesMap φ - cyclesMap φ'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cyclesMap", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("cyclesMap", (OVar("phi"),)), OOp("cyclesMap", (OVar("phi_prime"),))))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_cyclesMap_sub"))
        except Exception:
            pass
    return results


def _r0051_i_descQ_eq_zero_of_boundary(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.RightHomologyData.ι_descQ_eq_zero_of_boundary
    # h.ι ≫ h.descQ k (by rw [hx, S.zero_assoc, zero_comp]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_i", 4)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_RightHomologyData_i_descQ_eq_zero_of_boundary"))
        except Exception:
            pass
    return results


def _r0052_p_fromOpcycles(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.p_fromOpcycles
    # S.pOpcycles ≫ S.fromOpcycles = S.g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_pOpcycles", 2)
    if args is not None:
        try:
            rhs = OVar("S_g")
            results.append((rhs, "Mathlib: CategoryTheory_p_fromOpcycles"))
        except Exception:
            pass
    return results


def _r0053_opcyclesIsoX_2_hom_inv_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.opcyclesIsoX₂_hom_inv_id
    # (S.opcyclesIsoX₂ hf).hom ≫ S.pOpcycles = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_opcyclesIsoX_2_hf_hom", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_opcyclesIsoX_2_hom_inv_id"))
        except Exception:
            pass
    return results


def _r0054_w_0_2_tau_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.w₀₂_τ₂
    # S.v₀₁.τ₂ ≫ S.v₁₂.τ₂ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_v_0_1_tau_2", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_w_0_2_tau_2"))
        except Exception:
            pass
    return results


def _r0055_w_0_2_tau_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.w₀₂_τ₃
    # S.v₀₁.τ₃ ≫ S.v₁₂.τ₃ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_v_0_1_tau_3", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_w_0_2_tau_3"))
        except Exception:
            pass
    return results


def _r0056_w_1_3_tau_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.w₁₃_τ₁
    # S.v₁₂.τ₁ ≫ S.v₂₃.τ₁ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_v_1_2_tau_1", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_w_1_3_tau_1"))
        except Exception:
            pass
    return results


def _r0057_w_1_3_tau_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.w₁₃_τ₂
    # S.v₁₂.τ₂ ≫ S.v₂₃.τ₂ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_v_1_2_tau_2", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_w_1_3_tau_2"))
        except Exception:
            pass
    return results


def _r0058_w_1_3_tau_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.w₁₃_τ₃
    # S.v₁₂.τ₃ ≫ S.v₂₃.τ₃ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_v_1_2_tau_3", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_w_1_3_tau_3"))
        except Exception:
            pass
    return results


def _r0059_L_0X_2ToP_comp_pullback_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.L₀X₂ToP_comp_pullback_snd
    # S.L₀X₂ToP ≫ pullback.snd _ _ = S.L₀.g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_L_0X_2ToP", 4)
    if args is not None:
        try:
            rhs = OVar("S_L_0_g")
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_L_0X_2ToP_comp_pullback_snd"))
        except Exception:
            pass
    return results


def _r0060_id_f_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.id_f₁
    # Hom.f₁ (𝟙 S) = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_f_1", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_id_f_1"))
        except Exception:
            pass
    return results


def _r0061_id_f_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.id_f₂
    # Hom.f₂ (𝟙 S) = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_f_2", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_id_f_2"))
        except Exception:
            pass
    return results


def _r0062_id_f_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.id_f₃
    # Hom.f₃ (𝟙 S) = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_f_3", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_id_f_3"))
        except Exception:
            pass
    return results


def _r0063_comp_f_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.comp_f₁
    # (f ≫ g).f₁ = f.f₁ ≫ g.f₁
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_f_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_f_1", (OVar("_unknown"), OVar("g_f_1"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_comp_f_1"))
    except Exception:
        pass
    return results


def _r0064_comp_f_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.comp_f₂
    # (f ≫ g).f₂ = f.f₂ ≫ g.f₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_f_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_f_2", (OVar("_unknown"), OVar("g_f_2"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_comp_f_2"))
    except Exception:
        pass
    return results


def _r0065_comp_f_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShortComplex.SnakeInput.comp_f₃
    # (f ≫ g).f₃ = f.f₃ ≫ g.f₃
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_f_3")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_f_3", (OVar("_unknown"), OVar("g_f_3"),))
            results.append((rhs, "Mathlib: CategoryTheory_ShortComplex_SnakeInput_comp_f_3"))
    except Exception:
        pass
    return results


def _r0066_equivalence_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Abelian.DoldKan.equivalence_inverse
    # (equivalence : SimplicialObject A ≌ _).inverse = Γ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("equivalence_colon_SimplicialObject_A_inverse")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("G")
            results.append((rhs, "Mathlib: CategoryTheory_Abelian_DoldKan_equivalence_inverse"))
    except Exception:
        pass
    return results


def _r0067_whiskering_obj_obj_d(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.SimplicialObject.whiskering_obj_obj_δ
    # dsimp% (((whiskering C D).obj F).obj X).δ i = F.map (X.δ i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dsimp", 2)
    if args is not None:
        try:
            rhs = OOp("F_map", (OOp("X_d", (args[1],)),))
            results.append((rhs, "Mathlib: CategoryTheory_SimplicialObject_whiskering_obj_obj_d"))
        except Exception:
            pass
    return results


def _r0068_whiskering_obj_obj_sig(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.SimplicialObject.whiskering_obj_obj_σ
    # dsimp% (((whiskering C D).obj F).obj X).σ i = F.map (X.σ i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dsimp", 2)
    if args is not None:
        try:
            rhs = OOp("F_map", (OOp("X_sig", (args[1],)),))
            results.append((rhs, "Mathlib: CategoryTheory_SimplicialObject_whiskering_obj_obj_sig"))
        except Exception:
            pass
    return results


def _r0069_nerveMap_app_mk_0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.nerveMap_app_mk₀
    # (nerveMap F).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =       ComposableArrows.mk₀ (F.obj x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nerveMap_F_app", 2)
    if args is not None:
        try:
            rhs = OOp("ComposableArrows_mk_0", (OOp("F_obj", (OVar("x"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_nerveMap_app_mk_0"))
        except Exception:
            pass
    return results


def _r0070_edgeMk_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.nerve.edgeMk_id
    # edgeMk (𝟙 x) = .id _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "edgeMk", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_nerve_edgeMk_id"))
        except Exception:
            pass
    return results


def _r0071_i_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.kernelCokernelCompSequence.ι_snd
    # ι f g ≫ biprod.snd = kernel.ι (f ≫ g) ≫ f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i", 4)
    if args is not None:
        try:
            rhs = OOp("kernel_i", (OOp("f", (args[2], args[1],)), args[2], args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_kernelCokernelCompSequence_i_snd"))
        except Exception:
            pass
    return results


def _r0072_inr_phi_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.kernelCokernelCompSequence.inr_φ_fst
    # biprod.inr ≫ φ f g ≫ biprod.fst = - 𝟙 Y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "biprod_inr", 6)
    if args is not None:
        try:
            rhs = OOp("minus", (OLit(1), OVar("Y"),))
            results.append((rhs, "Mathlib: CategoryTheory_kernelCokernelCompSequence_inr_phi_fst"))
        except Exception:
            pass
    return results


def _r0073_phi_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.kernelCokernelCompSequence.φ_snd
    # φ f g ≫ biprod.snd = biprod.snd ≫ g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 4)
    if args is not None:
        try:
            rhs = OOp("biprod_snd", (args[2], args[1],))
            results.append((rhs, "Mathlib: CategoryTheory_kernelCokernelCompSequence_phi_snd"))
        except Exception:
            pass
    return results


def _r0074_inr_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.kernelCokernelCompSequence.inr_π
    # biprod.inr ≫ π f g = cokernel.π (f ≫ g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "biprod_inr", 4)
    if args is not None:
        try:
            rhs = OOp("cokernel_pi", (OOp("f", (args[0], args[3],)),))
            results.append((rhs, "Mathlib: CategoryTheory_kernelCokernelCompSequence_inr_pi"))
        except Exception:
            pass
    return results


def _r0075_i_phi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.kernelCokernelCompSequence.ι_φ
    # ι f g ≫ φ f g = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i", 6)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_kernelCokernelCompSequence_i_phi"))
        except Exception:
            pass
    return results


def _r0076_homotopyEquiv_inv_i(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.homotopyEquiv_inv_ι
    # J.ι ≫ (homotopyEquiv I J).inv = I.ι
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "J_i", 2)
    if args is not None:
        try:
            rhs = OVar("I_i")
            results.append((rhs, "Mathlib: CategoryTheory_homotopyEquiv_inv_i"))
        except Exception:
            pass
    return results


def _r0077_leftDerivedToHomotopyCategory_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.NatTrans.leftDerivedToHomotopyCategory_comp
    # NatTrans.leftDerivedToHomotopyCategory (α ≫ β) =       NatTrans.leftDerivedToHomotopyCategory α ≫         NatTrans.leftD
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NatTrans_leftDerivedToHomotopyCategory", 1)
    if args is not None:
        try:
            rhs = OOp("NatTrans_leftDerivedToHomotopyCategory", (OVar("a"), OVar("_unknown"), OVar("NatTrans_leftDerivedToHomotopyCategory"), OVar("b"),))
            results.append((rhs, "Mathlib: CategoryTheory_NatTrans_leftDerivedToHomotopyCategory_comp"))
        except Exception:
            pass
    return results


def _r0078_leftDerivedZeroIsoSelf_hom_inv_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.leftDerivedZeroIsoSelf_hom_inv_id
    # F.fromLeftDerivedZero ≫ F.leftDerivedZeroIsoSelf.inv = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_fromLeftDerivedZero", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_leftDerivedZeroIsoSelf_hom_inv_id"))
        except Exception:
            pass
    return results


def _r0079_pi_op(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.cokernel.π_op
    # (cokernel.π f.op).unop =       (cokernelOpUnop f).hom ≫ kernel.ι f ≫ eqToHom (Opposite.unop_op _).symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cokernel_pi_f_op_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("cokernelOpUnop_f_hom", (OVar("_unknown"), OVar("kernel_i"), OVar("f"), OVar("_unknown"), OVar("eqToHom"), OVar("Opposite_unop_op_symm"),))
            results.append((rhs, "Mathlib: CategoryTheory_cokernel_pi_op"))
    except Exception:
        pass
    return results


def _r0080_i_unop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.kernel.ι_unop
    # (kernel.ι g.unop).op = eqToHom (Opposite.op_unop _) ≫ cokernel.π g ≫ (kernelUnopOp g).inv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("kernel_i_g_unop_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("eqToHom", (OOp("Opposite_op_unop", (OVar("_unknown"),)), OVar("_unknown"), OVar("cokernel_pi"), OVar("g"), OVar("_unknown"), OVar("kernelUnopOp_g_inv"),))
            results.append((rhs, "Mathlib: CategoryTheory_kernel_i_unop"))
    except Exception:
        pass
    return results


def _r0081_homotopyEquiv_inv_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.homotopyEquiv_inv_π
    # (homotopyEquiv P Q).inv ≫ P.π = Q.π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homotopyEquiv_P_Q_inv", 2)
    if args is not None:
        try:
            rhs = OVar("Q_pi")
            results.append((rhs, "Mathlib: CategoryTheory_homotopyEquiv_inv_pi"))
        except Exception:
            pass
    return results


def _r0082_rightDerivedToHomotopyCategory_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.NatTrans.rightDerivedToHomotopyCategory_comp
    # NatTrans.rightDerivedToHomotopyCategory (α ≫ β) =       NatTrans.rightDerivedToHomotopyCategory α ≫         NatTrans.rig
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "NatTrans_rightDerivedToHomotopyCategory", 1)
    if args is not None:
        try:
            rhs = OOp("NatTrans_rightDerivedToHomotopyCategory", (OVar("a"), OVar("_unknown"), OVar("NatTrans_rightDerivedToHomotopyCategory"), OVar("b"),))
            results.append((rhs, "Mathlib: CategoryTheory_NatTrans_rightDerivedToHomotopyCategory_comp"))
        except Exception:
            pass
    return results


def _r0083_rightDerivedZeroIsoSelf_hom_inv_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.rightDerivedZeroIsoSelf_hom_inv_id
    # F.rightDerivedZeroIsoSelf.hom ≫ F.toRightDerivedZero = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_rightDerivedZeroIsoSelf_hom", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_rightDerivedZeroIsoSelf_hom_inv_id"))
        except Exception:
            pass
    return results


def _r0084_pi_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ActionCategory.π_obj
    # (π M X).obj p = SingleObj.star M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pi_M_X_obj", 1)
    if args is not None:
        try:
            rhs = OOp("SingleObj_star", (OVar("M"),))
            results.append((rhs, "Mathlib: CategoryTheory_ActionCategory_pi_obj"))
        except Exception:
            pass
    return results


def _r0085_back_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ActionCategory.back_coe
    # ↑x.back = x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_back")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x")
            results.append((rhs, "Mathlib: CategoryTheory_ActionCategory_back_coe"))
    except Exception:
        pass
    return results


def _r0086_comp_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ActionCategory.comp_val
    # (f ≫ g).val = g.val * f.val
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("g_val"), OVar("f_val")))
            results.append((rhs, "Mathlib: CategoryTheory_ActionCategory_comp_val"))
    except Exception:
        pass
    return results


def _r0087_functor_eta(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FunctorCategoryEquivalence.functor_η
    # η (FunctorCategoryEquivalence.functor (V := V) (G := G)) = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eta", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: FunctorCategoryEquivalence_functor_eta"))
        except Exception:
            pass
    return results


def _r0088_functor_mu(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FunctorCategoryEquivalence.functor_μ
    # μ FunctorCategoryEquivalence.functor A B = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mu", 3)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: FunctorCategoryEquivalence_functor_mu"))
        except Exception:
            pass
    return results


def _r0089_functor_d(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FunctorCategoryEquivalence.functor_δ
    # δ FunctorCategoryEquivalence.functor A B = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d", 3)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: FunctorCategoryEquivalence_functor_d"))
        except Exception:
            pass
    return results


def _r0090_mapAction_mu_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.mapAction_μ_hom
    # (μ (F.mapAction G) X Y).hom = μ F X.V Y.V
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mu_F_mapAction_G_X_Y_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("mu", (OVar("F"), OVar("X_V"), OVar("Y_V"),))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_mapAction_mu_hom"))
    except Exception:
        pass
    return results


def _r0091_mapAction_d_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.mapAction_δ_hom
    # (δ (F.mapAction G) X Y).hom = δ F X.V Y.V
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("d_F_mapAction_G_X_Y_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("d", (OVar("F"), OVar("X_V"), OVar("Y_V"),))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_mapAction_d_hom"))
    except Exception:
        pass
    return results


def _r0092_homAddEquiv_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Adjunction.homAddEquiv_symm_apply
    # (adj.homAddEquiv X Y).symm f = (adj.homEquiv X Y).symm f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adj_homAddEquiv_X_Y_symm", 1)
    if args is not None:
        try:
            rhs = OOp("adj_homEquiv_X_Y_symm", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Adjunction_homAddEquiv_symm_apply"))
        except Exception:
            pass
    return results


def _r0093_homAddEquiv_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Adjunction.homAddEquiv_zero
    # adj.homEquiv X Y 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adj_homEquiv", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_Adjunction_homAddEquiv_zero"))
        except Exception:
            pass
    return results


def _r0094_homAddEquiv_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Adjunction.homAddEquiv_add
    # adj.homEquiv X Y (f + f') = adj.homEquiv X Y f + adj.homEquiv X Y f'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adj_homEquiv", 3)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("adj_homEquiv", (args[0], args[1], OVar("f"),)), OOp("adj_homEquiv", (args[0], args[1], OVar("f_prime"),))))
            results.append((rhs, "Mathlib: CategoryTheory_Adjunction_homAddEquiv_add"))
        except Exception:
            pass
    return results


def _r0095_homAddEquiv_symm_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Adjunction.homAddEquiv_symm_zero
    # (adj.homEquiv X Y).symm 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adj_homEquiv_X_Y_symm", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_Adjunction_homAddEquiv_symm_zero"))
        except Exception:
            pass
    return results


def _r0096_homAddEquiv_symm_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Adjunction.homAddEquiv_symm_add
    # (adj.homEquiv X Y).symm (f + f') = (adj.homEquiv X Y).symm f + (adj.homEquiv X Y).symm f'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adj_homEquiv_X_Y_symm", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("adj_homEquiv_X_Y_symm", (OVar("f"),)), OOp("adj_homEquiv_X_Y_symm", (OVar("f_prime"),))))
            results.append((rhs, "Mathlib: CategoryTheory_Adjunction_homAddEquiv_symm_add"))
        except Exception:
            pass
    return results


def _r0097_homEquiv_naturality_left_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Adjunction.homEquiv_naturality_left_symm
    # (adj.homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.homEquiv X Y).symm g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adj_homEquiv_X_prime_Y_symm", 1)
    if args is not None:
        try:
            rhs = OOp("F_map", (OVar("f"), OVar("_unknown"), OVar("adj_homEquiv_X_Y_symm"), OVar("g"),))
            results.append((rhs, "Mathlib: CategoryTheory_Adjunction_homEquiv_naturality_left_symm"))
        except Exception:
            pass
    return results


def _r0098_right_triangle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Adjunction.right_triangle
    # whiskerLeft G adj.unit ≫ whiskerRight adj.counit G = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "whiskerLeft", 6)
    if args is not None:
        try:
            rhs = OOp("_1", (args[2],))
            results.append((rhs, "Mathlib: CategoryTheory_Adjunction_right_triangle"))
        except Exception:
            pass
    return results


def _r0099_counit_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Adjunction.counit_naturality
    # F.map (G.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_map", 4)
    if args is not None:
        try:
            rhs = OOp("adj_counit_app", (OVar("X"), args[1], OVar("f"),))
            results.append((rhs, "Mathlib: CategoryTheory_Adjunction_counit_naturality"))
        except Exception:
            pass
    return results


def _r0100_conjugateEquiv_leftAdjointIdIso_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Adjunction.conjugateEquiv_leftAdjointIdIso_hom
    # conjugateEquiv .id adj (leftAdjointIdIso adj e).hom = e.inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "conjugateEquiv", 3)
    if args is not None:
        try:
            rhs = OVar("e_inv")
            results.append((rhs, "Mathlib: CategoryTheory_Adjunction_conjugateEquiv_leftAdjointIdIso_hom"))
        except Exception:
            pass
    return results


def _r0101_op_rightTriple(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Adjunction.Quadruple.op_rightTriple
    # q.op.rightTriple = q.leftTriple.op
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_op_rightTriple")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q_leftTriple_op")
            results.append((rhs, "Mathlib: CategoryTheory_Adjunction_Quadruple_op_rightTriple"))
    except Exception:
        pass
    return results


def _r0102_comp_left_triangle_aux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.Adjunction.comp_left_triangle_aux
    # leftZigzag (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (λ_ _).hom ≫ (ρ_ _).inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "leftZigzag", 2)
    if args is not None:
        try:
            rhs = OOp("lam_hom", (OVar("_unknown"), OVar("rho_inv"),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_Adjunction_comp_left_triangle_aux"))
        except Exception:
            pass
    return results


def _r0103_rightZigzagIso_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.rightZigzagIso_hom
    # (rightZigzagIso η ε).hom = rightZigzag η.hom ε.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("rightZigzagIso_eta_e_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("rightZigzag", (OVar("eta_hom"), OVar("e_hom"),))
            results.append((rhs, "Mathlib: CategoryTheory_rightZigzagIso_hom"))
    except Exception:
        pass
    return results


def _r0104_leftZigzagIso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.leftZigzagIso_inv
    # (leftZigzagIso η ε).inv = rightZigzag ε.inv η.inv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("leftZigzagIso_eta_e_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("rightZigzag", (OVar("e_inv"), OVar("eta_inv"),))
            results.append((rhs, "Mathlib: CategoryTheory_leftZigzagIso_inv"))
    except Exception:
        pass
    return results


def _r0105_rightZigzagIso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.rightZigzagIso_inv
    # (rightZigzagIso η ε).inv = leftZigzag ε.inv η.inv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("rightZigzagIso_eta_e_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("leftZigzag", (OVar("e_inv"), OVar("eta_inv"),))
            results.append((rhs, "Mathlib: CategoryTheory_rightZigzagIso_inv"))
    except Exception:
        pass
    return results


def _r0106_leftZigzagIso_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.leftZigzagIso_symm
    # (leftZigzagIso η ε).symm = rightZigzagIso ε.symm η.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("leftZigzagIso_eta_e_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("rightZigzagIso", (OVar("e_symm"), OVar("eta_symm"),))
            results.append((rhs, "Mathlib: CategoryTheory_leftZigzagIso_symm"))
    except Exception:
        pass
    return results


def _r0107_rightZigzagIso_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.rightZigzagIso_symm
    # (rightZigzagIso η ε).symm = leftZigzagIso ε.symm η.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("rightZigzagIso_eta_e_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("leftZigzagIso", (OVar("e_symm"), OVar("eta_symm"),))
            results.append((rhs, "Mathlib: CategoryTheory_rightZigzagIso_symm"))
    except Exception:
        pass
    return results


def _r0108_mateEquiv_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.mateEquiv_eq_iff
    # mateEquiv adj₁ adj₂ α = β ↔     adj₁.homEquiv₁.symm β = adj₂.homEquiv₂ α ≫ (α_ _ _ _).hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mateEquiv", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("b"), OOp("adj_1_homEquiv_1_symm", (OVar("b"),)))), OOp("adj_2_homEquiv_2", (args[2], OVar("_unknown"), OVar("a_hom"),))))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_mateEquiv_eq_iff"))
        except Exception:
            pass
    return results


def _r0109_hom_inv_whiskerRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.hom_inv_whiskerRight
    # η.hom ▷ h ≫ η.inv ▷ h = 𝟙 (f ≫ h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eta_hom", 6)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("f", (args[4], args[5],)),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_hom_inv_whiskerRight"))
        except Exception:
            pass
    return results


def _r0110_whiskerLeft_inv_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.whiskerLeft_inv_hom
    # f ◁ η.inv ≫ f ◁ η.hom = 𝟙 (f ≫ h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 6)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("f", (args[4], OVar("h"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_whiskerLeft_inv_hom"))
        except Exception:
            pass
    return results


def _r0111_inv_hom_whiskerRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.inv_hom_whiskerRight
    # η.inv ▷ h ≫ η.hom ▷ h = 𝟙 (g ≫ h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eta_inv", 6)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("g", (args[4], args[5],)),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_inv_hom_whiskerRight"))
        except Exception:
            pass
    return results


def _r0112_whiskerLeft_whiskerLeft_hom_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.whiskerLeft_whiskerLeft_hom_inv
    # f ◁ g ◁ η.hom ≫ f ◁ g ◁ η.inv = 𝟙 (f ≫ g ≫ h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 10)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("f", (args[8], args[7], args[8], OVar("h"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_whiskerLeft_whiskerLeft_hom_inv"))
        except Exception:
            pass
    return results


def _r0113_triangle_assoc_comp_right_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.triangle_assoc_comp_right_inv
    # (ρ_ f).inv ▷ g ≫ (α_ f (𝟙 b) g).hom = f ◁ (λ_ g).inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rho_f_inv", 4)
    if args is not None:
        try:
            rhs = OOp("f", (args[2], OVar("lam_g_inv"),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_triangle_assoc_comp_right_inv"))
        except Exception:
            pass
    return results


def _r0114_eqToHom_hComp_eqToHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.CatEnriched.eqToHom_hComp_eqToHom
    # hComp (eqToHom α) (eqToHom β) = eqToHom (α ▸ β ▸ rfl)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hComp", 2)
    if args is not None:
        try:
            rhs = OOp("eqToHom", (OOp("subst", (OVar("a"), OOp("subst", (OVar("b"), OVar("rfl"))))),))
            results.append((rhs, "Mathlib: CategoryTheory_CatEnriched_eqToHom_hComp_eqToHom"))
        except Exception:
            pass
    return results


def _r0115_preinclusion_map_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.FreeBicategory.preinclusion_map₂
    # (preinclusion B).map₂ η = eqToHom (congr_arg _ (Discrete.ext (Discrete.eq_of_hom η)))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "preinclusion_B_map_2", 1)
    if args is not None:
        try:
            rhs = OOp("eqToHom", (OOp("congr_arg", (OVar("_unknown"), OOp("Discrete_ext", (OOp("Discrete_eq_of_hom", (args[0],)),)),)),))
            results.append((rhs, "Mathlib: CategoryTheory_FreeBicategory_preinclusion_map_2"))
        except Exception:
            pass
    return results


def _r0116_mk_associator_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.mk_associator_hom
    # Quot.mk _ (Hom₂.associator f g h) = (α_ f g h).hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OVar("a_f_g_h_hom")
            results.append((rhs, "Mathlib: CategoryTheory_mk_associator_hom"))
        except Exception:
            pass
    return results


def _r0117_mk_associator_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.mk_associator_inv
    # Quot.mk _ (Hom₂.associator_inv f g h) = (α_ f g h).inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OVar("a_f_g_h_inv")
            results.append((rhs, "Mathlib: CategoryTheory_mk_associator_inv"))
        except Exception:
            pass
    return results


def _r0118_mk_left_unitor_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.mk_left_unitor_hom
    # Quot.mk _ (Hom₂.left_unitor f) = (λ_ f).hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OVar("lam_f_hom")
            results.append((rhs, "Mathlib: CategoryTheory_mk_left_unitor_hom"))
        except Exception:
            pass
    return results


def _r0119_mk_left_unitor_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.mk_left_unitor_inv
    # Quot.mk _ (Hom₂.left_unitor_inv f) = (λ_ f).inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OVar("lam_f_inv")
            results.append((rhs, "Mathlib: CategoryTheory_mk_left_unitor_inv"))
        except Exception:
            pass
    return results


def _r0120_mk_right_unitor_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.mk_right_unitor_hom
    # Quot.mk _ (Hom₂.right_unitor f) = (ρ_ f).hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OVar("rho_f_hom")
            results.append((rhs, "Mathlib: CategoryTheory_mk_right_unitor_hom"))
        except Exception:
            pass
    return results


def _r0121_mk_right_unitor_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.mk_right_unitor_inv
    # Quot.mk _ (Hom₂.right_unitor_inv f) = (ρ_ f).inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OVar("rho_f_inv")
            results.append((rhs, "Mathlib: CategoryTheory_mk_right_unitor_inv"))
        except Exception:
            pass
    return results


def _r0122_map_comp_forget(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Pseudofunctor.map_comp_forget
    # map α ⋙ forget G = forget F
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 4)
    if args is not None:
        try:
            rhs = OOp("forget", (OVar("F"),))
            results.append((rhs, "Mathlib: CategoryTheory_Pseudofunctor_map_comp_forget"))
        except Exception:
            pass
    return results


def _r0123_uniqueUpToIso_inv_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.LeftExtension.IsKan.uniqueUpToIso_inv_right
    # (uniqueUpToIso P Q).inv.right = Q.desc s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("uniqueUpToIso_P_Q_inv_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Q_desc", (OVar("s"),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_LeftExtension_IsKan_uniqueUpToIso_inv_right"))
    except Exception:
        pass
    return results


def _r0124_uniqueUpToIso_inv_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.LeftLift.IsKan.uniqueUpToIso_inv_right
    # (uniqueUpToIso P Q).inv.right = Q.desc s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("uniqueUpToIso_P_Q_inv_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Q_desc", (OVar("s"),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_LeftLift_IsKan_uniqueUpToIso_inv_right"))
    except Exception:
        pass
    return results


def _r0125_comp_as(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.LocallyDiscrete.comp_as
    # (f ≫ g).as = f.as ≫ g.as
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_as")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_as", (OVar("_unknown"), OVar("g_as"),))
            results.append((rhs, "Mathlib: CategoryTheory_LocallyDiscrete_comp_as"))
    except Exception:
        pass
    return results


def _r0126_comp_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.Pith.comp_of
    # (f ≫ g).of = f.of ≫ g.of
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_of")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_of", (OVar("_unknown"), OVar("g_of"),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_Pith_comp_of"))
    except Exception:
        pass
    return results


def _r0127_comp_2_iso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.Pith.comp₂_iso_inv
    # (f ≫ g).iso.inv = g.iso.inv ≫ f.iso.inv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_iso_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g_iso_inv", (OVar("_unknown"), OVar("f_iso_inv"),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_Pith_comp_2_iso_inv"))
    except Exception:
        pass
    return results


def _r0128_id_2_iso_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.Pith.id₂_iso_hom
    # (𝟙 x : x ⟶ x).iso.hom = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_x_colon_x_x_iso_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_Pith_id_2_iso_hom"))
    except Exception:
        pass
    return results


def _r0129_id_2_iso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.Pith.id₂_iso_inv
    # (𝟙 x : x ⟶ x).iso.inv = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_x_colon_x_x_iso_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_Pith_id_2_iso_inv"))
    except Exception:
        pass
    return results


def _r0130_comul_counit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.Comonad.comul_counit
    # Δ ≫ t ◁ ε = (ρ_ t).inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D", 4)
    if args is not None:
        try:
            rhs = OVar("rho_t_inv")
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_Comonad_comul_counit"))
        except Exception:
            pass
    return results


def _r0131_comul_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.Comonad.comul_assoc
    # Δ ≫ t ◁ Δ = Δ ≫ Δ ▷ t ≫ (α_ t t t).hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D", 4)
    if args is not None:
        try:
            rhs = OOp("D", (args[2], args[3], args[2], args[1], args[2], OVar("a_t_t_t_hom"),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_Comonad_comul_assoc"))
        except Exception:
            pass
    return results


def _r0132_comul_assoc_flip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Bicategory.Comonad.comul_assoc_flip
    # Δ ≫ Δ ▷ t = Δ ≫ t ◁ Δ ≫ (α_ t t t).inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D", 4)
    if args is not None:
        try:
            rhs = OOp("D", (args[2], args[3], args[2], args[1], args[2], OVar("a_t_t_t_inv"),))
            results.append((rhs, "Mathlib: CategoryTheory_Bicategory_Comonad_comul_assoc_flip"))
        except Exception:
            pass
    return results


def _r0133_toLax(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Lax.StrongTrans.id.toLax
    # (id F).toLax = LaxTrans.id F
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("id_F_toLax")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("LaxTrans_id", (OVar("F"),))
            results.append((rhs, "Mathlib: CategoryTheory_Lax_StrongTrans_id_toLax"))
    except Exception:
        pass
    return results


def _r0134_unop2_op2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.unop2_op2
    # η.unop2.op2 = η
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("eta_unop2_op2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("eta")
            results.append((rhs, "Mathlib: CategoryTheory_Iso_unop2_op2"))
    except Exception:
        pass
    return results


def _r0135_iso_hom_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.CatCommSq.iso_hom_naturality
    # R.map (T.map f) ≫ (iso T L R B).hom.app y = (iso T L R B).hom.app x ≫ B.map (L.map f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "R_map", 4)
    if args is not None:
        try:
            rhs = OOp("iso_T_L_R_B_hom_app", (OVar("x"), args[1], OVar("B_map"), OOp("L_map", (OVar("f"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_CatCommSq_iso_hom_naturality"))
        except Exception:
            pass
    return results


def _r0136_toNatTrans_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Cat.Hom.toNatTrans_comp
    # (η₁ ≫ η₂).toNatTrans = η₁.toNatTrans ≫ η₂.toNatTrans
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("eta_1_eta_2_toNatTrans")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("eta_1_toNatTrans", (OVar("_unknown"), OVar("eta_2_toNatTrans"),))
            results.append((rhs, "Mathlib: CategoryTheory_Cat_Hom_toNatTrans_comp"))
    except Exception:
        pass
    return results


def _r0137_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Cat.Hom₂.ext
    # η₁ = η₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("eta_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("eta_2")
            results.append((rhs, "Mathlib: CategoryTheory_Cat_Hom_2_ext"))
    except Exception:
        pass
    return results


def _r0138_toNatIso_isoMk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Cat.Hom.toNatIso_isoMk
    # Hom.toNatIso (isoMk e) = e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_toNatIso", 1)
    if args is not None:
        try:
            rhs = OVar("e")
            results.append((rhs, "Mathlib: CategoryTheory_Cat_Hom_toNatIso_isoMk"))
        except Exception:
            pass
    return results


def _r0139_id_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Hom.id_obj
    # (𝟙 C : C ⟶ C).toFunctor.obj X = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_C_colon_C_C_toFunctor_obj", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CategoryTheory_Hom_id_obj"))
        except Exception:
            pass
    return results


def _r0140_id_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Hom.id_map
    # (𝟙 C : C ⟶ C).toFunctor.map f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fmap", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CategoryTheory_Hom_id_map"))
        except Exception:
            pass
    return results


def _r0141_comp_toFunctor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Hom.comp_toFunctor
    # (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("F_G_toFunctor")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("F_toFunctor", (OVar("_unknown"), OVar("G_toFunctor"),))
            results.append((rhs, "Mathlib: CategoryTheory_Hom_comp_toFunctor"))
    except Exception:
        pass
    return results


def _r0142_comp_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Hom.comp_obj
    # (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_G_toFunctor_obj", 1)
    if args is not None:
        try:
            rhs = OOp("G_toFunctor_obj", (OOp("F_toFunctor_obj", (args[0],)),))
            results.append((rhs, "Mathlib: CategoryTheory_Hom_comp_obj"))
        except Exception:
            pass
    return results


def _r0143_eqToHom_toNatTrans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Hom₂.eqToHom_toNatTrans
    # (eqToHom h).toNatTrans = eqToHom congr(($h).toFunctor)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("eqToHom_h_toNatTrans")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("eqToHom", (OVar("congr_h_toFunctor"),))
            results.append((rhs, "Mathlib: CategoryTheory_Hom_2_eqToHom_toNatTrans"))
    except Exception:
        pass
    return results


def _r0144_eqToHom_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.eqToHom_app
    # (eqToHom h).toNatTrans.app X = eqToHom congr(($h).toFunctor.obj X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eqToHom_h_toNatTrans_app", 1)
    if args is not None:
        try:
            rhs = OOp("eqToHom", (OVar("congr_h_toFunctor_obj_X"),))
            results.append((rhs, "Mathlib: CategoryTheory_eqToHom_app"))
        except Exception:
            pass
    return results


def _r0145_whiskerLeft_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.whiskerLeft_app
    # (F ◁ η).toNatTrans.app X = η.toNatTrans.app (F.toFunctor.obj X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_eta_toNatTrans_app", 1)
    if args is not None:
        try:
            rhs = OOp("eta_toNatTrans_app", (OOp("F_toFunctor_obj", (args[0],)),))
            results.append((rhs, "Mathlib: CategoryTheory_whiskerLeft_app"))
        except Exception:
            pass
    return results


def _r0146_whiskerRight_toNatTrans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.whiskerRight_toNatTrans
    # (η ▷ H).toNatTrans = Functor.whiskerRight η.toNatTrans H.toFunctor
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("eta_H_toNatTrans")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Functor_whiskerRight", (OVar("eta_toNatTrans"), OVar("H_toFunctor"),))
            results.append((rhs, "Mathlib: CategoryTheory_whiskerRight_toNatTrans"))
    except Exception:
        pass
    return results


def _r0147_whiskerRight_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.whiskerRight_app
    # (η ▷ H).toNatTrans.app X = H.toFunctor.map (η.toNatTrans.app X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eta_H_toNatTrans_app", 1)
    if args is not None:
        try:
            rhs = OOp("fmap", (OOp("eta_toNatTrans_app", (args[0],)),))
            results.append((rhs, "Mathlib: CategoryTheory_whiskerRight_app"))
        except Exception:
            pass
    return results


def _r0148_toNatIso_leftUnitor(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Hom.toNatIso_leftUnitor
    # Hom.toNatIso (λ_ F) = F.toFunctor.leftUnitor
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_toNatIso", 1)
    if args is not None:
        try:
            rhs = OVar("F_toFunctor_leftUnitor")
            results.append((rhs, "Mathlib: CategoryTheory_Hom_toNatIso_leftUnitor"))
        except Exception:
            pass
    return results


def _r0149_leftUnitor_hom_toNatTrans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.leftUnitor_hom_toNatTrans
    # (λ_ F).hom.toNatTrans = (F.toFunctor.leftUnitor).hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("lam_F_hom_toNatTrans")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("F_toFunctor_leftUnitor_hom")
            results.append((rhs, "Mathlib: CategoryTheory_leftUnitor_hom_toNatTrans"))
    except Exception:
        pass
    return results


def _r0150_leftUnitor_inv_toNatTrans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.leftUnitor_inv_toNatTrans
    # (λ_ F).inv.toNatTrans = (F.toFunctor.leftUnitor).inv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("lam_F_inv_toNatTrans")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("F_toFunctor_leftUnitor_inv")
            results.append((rhs, "Mathlib: CategoryTheory_leftUnitor_inv_toNatTrans"))
    except Exception:
        pass
    return results


def _r0151_leftUnitor_hom_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.leftUnitor_hom_app
    # (λ_ F).hom.toNatTrans.app X = eqToHom (by simp)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lam_F_hom_toNatTrans_app", 1)
    if args is not None:
        try:
            rhs = OOp("eqToHom", (OOp("by", (OVar("simp"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_leftUnitor_hom_app"))
        except Exception:
            pass
    return results


def _r0152_rightUnitor_hom_toNatTrans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.rightUnitor_hom_toNatTrans
    # (ρ_ F).hom.toNatTrans = (F.toFunctor.rightUnitor).hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("rho_F_hom_toNatTrans")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("F_toFunctor_rightUnitor_hom")
            results.append((rhs, "Mathlib: CategoryTheory_rightUnitor_hom_toNatTrans"))
    except Exception:
        pass
    return results


def _r0153_rightUnitor_inv_toNatTrans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.rightUnitor_inv_toNatTrans
    # (ρ_ F).inv.toNatTrans = (F.toFunctor.rightUnitor).inv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("rho_F_inv_toNatTrans")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("F_toFunctor_rightUnitor_inv")
            results.append((rhs, "Mathlib: CategoryTheory_rightUnitor_inv_toNatTrans"))
    except Exception:
        pass
    return results


def _r0154_rightUnitor_hom_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.rightUnitor_hom_app
    # (ρ_ F).hom.toNatTrans.app X = eqToHom (by simp)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rho_F_hom_toNatTrans_app", 1)
    if args is not None:
        try:
            rhs = OOp("eqToHom", (OOp("by", (OVar("simp"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_rightUnitor_hom_app"))
        except Exception:
            pass
    return results


def _r0155_coe_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.coe_of
    # Cat.of C = C
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Cat_of", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CategoryTheory_coe_of"))
        except Exception:
            pass
    return results


def _r0156_comp_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.KleisliCat.comp_def
    # (xs ≫ ys) a = xs a >>= ys
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "xs_ys", 1)
    if args is not None:
        try:
            rhs = OOp("xs", (args[0], OVar("gt_gt_eq"), OVar("ys"),))
            results.append((rhs, "Mathlib: CategoryTheory_KleisliCat_comp_def"))
        except Exception:
            pass
    return results


def _r0157_homOfLE_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.homOfLE_comp
    # homOfLE h ≫ homOfLE k = homOfLE (h.trans k)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homOfLE", 4)
    if args is not None:
        try:
            rhs = OOp("homOfLE", (OOp("h_trans", (args[3],)),))
            results.append((rhs, "Mathlib: CategoryTheory_homOfLE_comp"))
        except Exception:
            pass
    return results


def _r0158_toOrderIso_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Equivalence.toOrderIso_symm_apply
    # e.toOrderIso.symm y = e.inverse.obj y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_toOrderIso_symm", 1)
    if args is not None:
        try:
            rhs = OOp("e_inverse_obj", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Equivalence_toOrderIso_symm_apply"))
        except Exception:
            pass
    return results


def _r0159_of_toQuivHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Prefunctor.of_toQuivHom
    # ofQuivHom (toQuivHom F) = F
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofQuivHom", 1)
    if args is not None:
        try:
            rhs = OVar("F")
            results.append((rhs, "Mathlib: CategoryTheory_Prefunctor_of_toQuivHom"))
        except Exception:
            pass
    return results


def _r0160_freeMap_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Cat.freeMap_id
    # freeMap (𝟭q V) = 𝟭 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "freeMap", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_Cat_freeMap_id"))
        except Exception:
            pass
    return results


def _r0161_hom_obj_inv_obj_of_iso(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Quiv.hom_obj_inv_obj_of_iso
    # e.hom.obj (e.inv.obj Y) = Y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_hom_obj", 1)
    if args is not None:
        try:
            rhs = OVar("Y")
            results.append((rhs, "Mathlib: CategoryTheory_Quiv_hom_obj_inv_obj_of_iso"))
        except Exception:
            pass
    return results


def _r0162_hom_map_inv_map_of_iso(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Quiv.hom_map_inv_map_of_iso
    # e.hom.map (e.inv.map f) = Quiver.homOfEq f (by simp) (by simp)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_hom_map", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("f"), OOp("by", (OVar("simp"),)), OOp("by", (OVar("simp"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Quiv_hom_map_inv_map_of_iso"))
        except Exception:
            pass
    return results


def _r0163_id_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ReflQuiv.id_map
    # (ReflPrefunctor.toPrefunctor (𝟙 X)).map f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ReflPrefunctor_toPrefunctor_1_X_map", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CategoryTheory_ReflQuiv_id_map"))
        except Exception:
            pass
    return results


def _r0164_comp_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ReflQuiv.comp_obj
    # (f ≫ g).obj x = g.obj (f.obj x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g_obj", 1)
    if args is not None:
        try:
            rhs = OOp("g_obj", (OOp("f_obj", (args[0],)),))
            results.append((rhs, "Mathlib: CategoryTheory_ReflQuiv_comp_obj"))
        except Exception:
            pass
    return results


def _r0165_comp_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ReflQuiv.comp_map
    # (f ≫ g).map a = g.map (f.map a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g_map", 1)
    if args is not None:
        try:
            rhs = OOp("g_map", (OOp("f_map", (args[0],)),))
            results.append((rhs, "Mathlib: CategoryTheory_ReflQuiv_comp_map"))
        except Exception:
            pass
    return results


def _r0166_quotientFunctor_map_nil(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Cat.FreeRefl.quotientFunctor_map_nil
    # (quotientFunctor V).map (.nil : x ⟶ x) = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "quotientFunctor_V_map", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_Cat_FreeRefl_quotientFunctor_map_nil"))
        except Exception:
            pass
    return results


def _r0167_lift_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Cat.FreeRefl.lift_map
    # (lift F).map (homMk f) = F.map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_F_map", 1)
    if args is not None:
        try:
            rhs = OOp("F_map", (OVar("f"),))
            results.append((rhs, "Mathlib: CategoryTheory_Cat_FreeRefl_lift_map"))
        except Exception:
            pass
    return results


def _r0168_rel_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.RelCat.Hom.rel_comp
    # (f ≫ g).rel = f.rel.comp g.rel
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_rel")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_rel_comp", (OVar("g_rel"),))
            results.append((rhs, "Mathlib: CategoryTheory_RelCat_Hom_rel_comp"))
    except Exception:
        pass
    return results


def _r0169_rel_id_apply_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.RelCat.Hom.rel_id_apply₂
    # x ~[rel (𝟙 X)] y ↔ x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: CategoryTheory_RelCat_Hom_rel_id_apply_2"))
        except Exception:
            pass
    return results


def _r0170_unopFunctor_comp_opFunctor_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.RelCat.unopFunctor_comp_opFunctor_eq
    # Functor.comp unopFunctor opFunctor = Functor.id _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Functor_comp", 2)
    if args is not None:
        try:
            rhs = OOp("Functor_id", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_RelCat_unopFunctor_comp_opFunctor_eq"))
        except Exception:
            pass
    return results


def _r0171_objUp_objDown(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.objUp_objDown
    # ULiftHom.objUp A.objDown = A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ULiftHom_objUp", 1)
    if args is not None:
        try:
            rhs = OVar("A")
            results.append((rhs, "Mathlib: CategoryTheory_objUp_objDown"))
        except Exception:
            pass
    return results


def _r0172_app_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.CatCenter.app_sub
    # (z₁ - z₂).app X = z₁.app X - z₂.app X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "z_1_minus_z_2_app", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("z_1_app", (args[0],)), OOp("z_2_app", (args[0],))))
            results.append((rhs, "Mathlib: CategoryTheory_CatCenter_app_sub"))
        except Exception:
            pass
    return results


def _r0173_app_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.CatCenter.app_neg
    # (-z).app X = - z.app X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_z_app", 1)
    if args is not None:
        try:
            rhs = OOp("minus", (OVar("z_app"), args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_CatCenter_app_neg"))
        except Exception:
            pass
    return results


def _r0174_fac_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.CommSq.fac_right
    # sq.lift ≫ p = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sq_lift", 2)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: CategoryTheory_CommSq_fac_right"))
        except Exception:
            pass
    return results


def _r0175_id_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Arrow.id_right
    # Arrow.Hom.right (𝟙 f) = 𝟙 f.right
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Arrow_Hom_right", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("f_right"),))
            results.append((rhs, "Mathlib: CategoryTheory_Arrow_id_right"))
        except Exception:
            pass
    return results


def _r0176_comp_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Arrow.comp_left
    # (f ≫ g).left = f.left ≫ g.left
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_left")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_left", (OVar("_unknown"), OVar("g_left"),))
            results.append((rhs, "Mathlib: CategoryTheory_Arrow_comp_left"))
    except Exception:
        pass
    return results


def _r0177_comp_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Arrow.comp_right
    # (f ≫ g).right = f.right ≫ g.right
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_right", (OVar("_unknown"), OVar("g_right"),))
            results.append((rhs, "Mathlib: CategoryTheory_Arrow_comp_right"))
    except Exception:
        pass
    return results


def _r0178_w(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Arrow.Hom.w
    # sq.left ≫ g.hom = f.hom ≫ sq.right
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sq_left", 2)
    if args is not None:
        try:
            rhs = OOp("f_hom", (args[0], OVar("sq_right"),))
            results.append((rhs, "Mathlib: CategoryTheory_Arrow_Hom_w"))
        except Exception:
            pass
    return results


def _r0179_inv_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Arrow.inv_right
    # (inv sq).right = inv sq.right
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inv_sq_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inv", (OVar("sq_right"),))
            results.append((rhs, "Mathlib: CategoryTheory_Arrow_inv_right"))
    except Exception:
        pass
    return results


def _r0180_left_hom_inv_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Arrow.left_hom_inv_right
    # sq.left ≫ g.hom ≫ inv sq.right = f.hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sq_left", 5)
    if args is not None:
        try:
            rhs = OVar("f_hom")
            results.append((rhs, "Mathlib: CategoryTheory_Arrow_left_hom_inv_right"))
        except Exception:
            pass
    return results


def _r0181_inv_hom_id_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Arrow.inv_hom_id_left
    # e.inv.left ≫ e.hom.left = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_inv_left", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Arrow_inv_hom_id_left"))
        except Exception:
            pass
    return results


def _r0182_hom_inv_id_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Arrow.hom_inv_id_right
    # e.hom.right ≫ e.inv.right = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_hom_right", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Arrow_hom_inv_id_right"))
        except Exception:
            pass
    return results


def _r0183_inv_hom_id_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Arrow.inv_hom_id_right
    # e.inv.right ≫ e.hom.right = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_inv_right", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Arrow_inv_hom_id_right"))
        except Exception:
            pass
    return results


def _r0184_id_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Comma.id_right
    # (𝟙 X : CommaMorphism X X).right = 𝟙 X.right
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_X_colon_CommaMorphism_X_X_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("X_right"),))
            results.append((rhs, "Mathlib: CategoryTheory_Comma_id_right"))
    except Exception:
        pass
    return results


def _r0185_comp_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Comma.comp_left
    # (f ≫ g).left = f.left ≫ g.left
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_left")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_left", (OVar("_unknown"), OVar("g_left"),))
            results.append((rhs, "Mathlib: CategoryTheory_Comma_comp_left"))
    except Exception:
        pass
    return results


def _r0186_comp_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Comma.comp_right
    # (f ≫ g).right = f.right ≫ g.right
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_right", (OVar("_unknown"), OVar("g_right"),))
            results.append((rhs, "Mathlib: CategoryTheory_Comma_comp_right"))
    except Exception:
        pass
    return results


def _r0187_eqToHom_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.eqToHom_left
    # CommaMorphism.left (eqToHom H) = eqToHom (by cases H; rfl)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "CommaMorphism_left", 1)
    if args is not None:
        try:
            rhs = OOp("eqToHom", (OOp("by", (OVar("cases"), OVar("H"), OVar("rfl"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_eqToHom_left"))
        except Exception:
            pass
    return results


def _r0188_id_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Over.id_left
    # CommaMorphism.left (𝟙 U) = 𝟙 U.left
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "CommaMorphism_left", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("U_left"),))
            results.append((rhs, "Mathlib: CategoryTheory_Over_id_left"))
        except Exception:
            pass
    return results


def _r0189_comp_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Over.comp_left
    # (f ≫ g).left = f.left ≫ g.left
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_left")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_left", (OVar("_unknown"), OVar("g_left"),))
            results.append((rhs, "Mathlib: CategoryTheory_Over_comp_left"))
    except Exception:
        pass
    return results


def _r0190_w(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Over.w
    # f.left ≫ B.hom = A.hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_left", 2)
    if args is not None:
        try:
            rhs = OVar("A_hom")
            results.append((rhs, "Mathlib: CategoryTheory_Over_w"))
        except Exception:
            pass
    return results


def _r0191_homMk_eta(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Over.homMk_eta
    # homMk f.left h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homMk", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CategoryTheory_Over_homMk_eta"))
        except Exception:
            pass
    return results


def _r0192_forget_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Over.forget_map
    # (forget X).map f = f.left
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_X_map", 1)
    if args is not None:
        try:
            rhs = OVar("f_left")
            results.append((rhs, "Mathlib: CategoryTheory_Over_forget_map"))
        except Exception:
            pass
    return results


def _r0193_map_obj_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Over.map_obj_hom
    # ((map f).obj U).hom = U.hom ≫ f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("map_f_obj_U_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("U_hom", (OVar("_unknown"), OVar("f"),))
            results.append((rhs, "Mathlib: CategoryTheory_Over_map_obj_hom"))
    except Exception:
        pass
    return results


def _r0194_map_map_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Over.map_map_left
    # ((map f).map g).left = g.left
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("map_f_map_g_left")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_left")
            results.append((rhs, "Mathlib: CategoryTheory_Over_map_map_left"))
    except Exception:
        pass
    return results


def _r0195_mapIso_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Over.mapIso_inverse
    # (mapIso f).inverse = map f.inv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mapIso_f_inverse")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("map", (OVar("f_inv"),))
            results.append((rhs, "Mathlib: CategoryTheory_Over_mapIso_inverse"))
    except Exception:
        pass
    return results


def _r0196_asOverHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.OverClass.asOverHom_comp
    # asOverHom S (f ≫ g) = asOverHom S f ≫ asOverHom S g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "asOverHom", 2)
    if args is not None:
        try:
            rhs = OOp("asOverHom", (args[0], OVar("f"), OVar("_unknown"), OVar("asOverHom"), args[0], OVar("g"),))
            results.append((rhs, "Mathlib: CategoryTheory_OverClass_asOverHom_comp"))
        except Exception:
            pass
    return results


def _r0197_asOverHom_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.OverClass.asOverHom_inv
    # asOverHom S (inv f) = inv (asOverHom S f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "asOverHom", 2)
    if args is not None:
        try:
            rhs = OOp("inv", (OOp("asOverHom", (args[0], OVar("f"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_OverClass_asOverHom_inv"))
        except Exception:
            pass
    return results


def _r0198_forgetAdjStar_unit_app_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Over.forgetAdjStar_unit_app_left
    # ((Over.forgetAdjStar X).unit.app Y).left = prod.lift Y.hom (𝟙 _)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Over_forgetAdjStar_X_unit_app_Y_left")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("prod_lift", (OVar("Y_hom"), OOp("_1", (OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Over_forgetAdjStar_unit_app_left"))
    except Exception:
        pass
    return results


def _r0199_mk_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.OverPresheafAux.YonedaCollection.mk_snd
    # (mk s x).snd = F.map (eqToHom <| by rw [YonedaCollection.mk_fst]) x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mk_s_x_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("F_map", (OOp("eqToHom", (OVar("lt_pipe"), OVar("by"), OVar("rw"), OSeq((OVar("YonedaCollection_mk_fst"),)),)), OVar("x"),))
            results.append((rhs, "Mathlib: CategoryTheory_OverPresheafAux_YonedaCollection_mk_snd"))
    except Exception:
        pass
    return results


def _r0200_map_1_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.OverPresheafAux.YonedaCollection.map₁_comp
    # YonedaCollection.map₁ (η ≫ μ) (X := X) =       YonedaCollection.map₁ μ (X := X) ∘ YonedaCollection.map₁ η (X := X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "YonedaCollection_map_1", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("YonedaCollection_map_1", (OVar("mu"), OOp("X", (OVar("colon_eq"), OVar("X"),)),)), OOp("YonedaCollection_map_1", (OVar("eta"), OOp("X", (OVar("colon_eq"), OVar("X"),)),))))
            results.append((rhs, "Mathlib: CategoryTheory_OverPresheafAux_YonedaCollection_map_1_comp"))
        except Exception:
            pass
    return results


def _r0201_map_2_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.OverPresheafAux.YonedaCollection.map₂_comp
    # YonedaCollection.map₂ F (f ≫ g) = YonedaCollection.map₂ F f ∘ YonedaCollection.map₂ F g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "YonedaCollection_map_2", 2)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("YonedaCollection_map_2", (args[0], OVar("f"),)), OOp("YonedaCollection_map_2", (args[0], OVar("g"),))))
            results.append((rhs, "Mathlib: CategoryTheory_OverPresheafAux_YonedaCollection_map_2_comp"))
        except Exception:
            pass
    return results


def _r0202_mk_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.StructuredArrow.mk_right
    # (mk f).right = Y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mk_f_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Y")
            results.append((rhs, "Mathlib: CategoryTheory_StructuredArrow_mk_right"))
    except Exception:
        pass
    return results


def _r0203_mk_hom_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.StructuredArrow.mk_hom_eq_self
    # (mk f).hom = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mk_f_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CategoryTheory_StructuredArrow_mk_hom_eq_self"))
    except Exception:
        pass
    return results


def _r0204_w(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.StructuredArrow.w
    # A.hom ≫ T.map f.right = B.hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "A_hom", 3)
    if args is not None:
        try:
            rhs = OVar("B_hom")
            results.append((rhs, "Mathlib: CategoryTheory_StructuredArrow_w"))
        except Exception:
            pass
    return results


def _r0205_comp_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.StructuredArrow.comp_right
    # (f ≫ g).right = f.right ≫ g.right
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_right", (OVar("_unknown"), OVar("g_right"),))
            results.append((rhs, "Mathlib: CategoryTheory_StructuredArrow_comp_right"))
    except Exception:
        pass
    return results


def _r0206_id_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.StructuredArrow.id_right
    # (𝟙 X : X ⟶ X).right = 𝟙 X.right
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_X_colon_X_X_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("X_right"),))
            results.append((rhs, "Mathlib: CategoryTheory_StructuredArrow_id_right"))
    except Exception:
        pass
    return results


def _r0207_eqToHom_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.StructuredArrow.eqToHom_right
    # (eqToHom h).right = eqToHom (by rw [h])
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("eqToHom_h_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("eqToHom", (OOp("by", (OVar("rw"), OSeq((OVar("h"),)),)),))
            results.append((rhs, "Mathlib: CategoryTheory_StructuredArrow_eqToHom_right"))
    except Exception:
        pass
    return results


def _r0208_mk_surjective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.StructuredArrow.mk_surjective
    # ∃ (Y : C) (g : S ⟶ T.obj Y), f = mk g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 3)
    if args is not None:
        try:
            rhs = OOp("pair", (OVar("g"),))
            results.append((rhs, "Mathlib: CategoryTheory_StructuredArrow_mk_surjective"))
        except Exception:
            pass
    return results


def _r0209_map_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.StructuredArrow.map_mk
    # (map g).obj (mk f) = mk (g ≫ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_g_obj", 1)
    if args is not None:
        try:
            rhs = OOp("pair", (OOp("g", (OVar("_unknown"), OVar("f"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_StructuredArrow_map_mk"))
        except Exception:
            pass
    return results


def _r0210_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.StructuredArrow.map_id
    # (map (𝟙 S)).obj f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_1_S_obj", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CategoryTheory_StructuredArrow_map_id"))
        except Exception:
            pass
    return results


def _r0211_obj_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.Precomp.obj_one
    # obj F X 1 = F.obj' 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "obj", 3)
    if args is not None:
        try:
            rhs = OOp("F_obj_prime", (OLit(0),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_Precomp_obj_one"))
        except Exception:
            pass
    return results


def _r0212_obj_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.Precomp.obj_succ
    # obj F X ⟨i + 1, hi⟩ = F.obj' i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "obj", 3)
    if args is not None:
        try:
            rhs = OOp("F_obj_prime", (OVar("i"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_Precomp_obj_succ"))
        except Exception:
            pass
    return results


def _r0213_map_one_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.Precomp.map_one_one
    # map F f 1 1 (by simp) = F.map (𝟙 _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 5)
    if args is not None:
        try:
            rhs = OOp("F_map", (OOp("_1", (OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_Precomp_map_one_one"))
        except Exception:
            pass
    return results


def _r0214_map_zero_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.Precomp.map_zero_one
    # map F f 0 1 (by simp) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 5)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_Precomp_map_zero_one"))
        except Exception:
            pass
    return results


def _r0215_map_zero_succ_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.Precomp.map_zero_succ_succ
    # map F f 0 ⟨j + 2, hj⟩ (by simp) = f ≫ F.map' 0 (j + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 5)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("_unknown"), OVar("F_map_prime"), OLit(0), OOp("+", (OVar("j"), OLit(1))),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_Precomp_map_zero_succ_succ"))
        except Exception:
            pass
    return results


def _r0216_map_succ_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.Precomp.map_succ_succ
    # map F f ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ hij = F.map' i j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 5)
    if args is not None:
        try:
            rhs = OOp("F_map_prime", (OVar("i"), OVar("j"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_Precomp_map_succ_succ"))
        except Exception:
            pass
    return results


def _r0217_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.Precomp.map_id
    # map F f i i (by simp) = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 5)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_Precomp_map_id"))
        except Exception:
            pass
    return results


def _r0218_homMkSucc_app_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.homMkSucc_app_succ
    # (homMkSucc α β w).app ⟨i + 1, hi⟩ = app' β i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homMkSucc_a_b_w_app", 1)
    if args is not None:
        try:
            rhs = OOp("app_prime", (OVar("b"), OVar("i"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_homMkSucc_app_succ"))
        except Exception:
            pass
    return results


def _r0219_homMk_2_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.homMk₂_app_one
    # (homMk₂ app₀ app₁ app₂ w₀ w₁).app 1 = app₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homMk_2_app_0_app_1_app_2_w_0_w_1_app", 1)
    if args is not None:
        try:
            rhs = OVar("app_1")
            results.append((rhs, "Mathlib: CategoryTheory_homMk_2_app_one"))
        except Exception:
            pass
    return results


def _r0220_homMk_2_app_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.homMk₂_app_two
    # (homMk₂ app₀ app₁ app₂ w₀ w₁).app 2 = app₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homMk_2_app_0_app_1_app_2_w_0_w_1_app", 1)
    if args is not None:
        try:
            rhs = OVar("app_2")
            results.append((rhs, "Mathlib: CategoryTheory_homMk_2_app_two"))
        except Exception:
            pass
    return results


def _r0221_homMk_3_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.homMk₃_app_one
    # (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 1 = app₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homMk_3_app_0_app_1_app_2_app_3_w_0_w_1_w_2_app", 1)
    if args is not None:
        try:
            rhs = OVar("app_1")
            results.append((rhs, "Mathlib: CategoryTheory_homMk_3_app_one"))
        except Exception:
            pass
    return results


def _r0222_homMk_4_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.homMk₄_app_one
    # (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 1 = app₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homMk_4_app_0_app_1_app_2_app_3_app_4_w_0_w_1_w_2_w_3_app", 1)
    if args is not None:
        try:
            rhs = OVar("app_1")
            results.append((rhs, "Mathlib: CategoryTheory_homMk_4_app_one"))
        except Exception:
            pass
    return results


def _r0223_homMk_5_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.homMk₅_app_one
    # (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 1 = app₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homMk_5_app_0_app_1_app_2_app_3_app_4_app_5_w_0_w_1_w_2_w_3_w_4_app", 1)
    if args is not None:
        try:
            rhs = OVar("app_1")
            results.append((rhs, "Mathlib: CategoryTheory_homMk_5_app_one"))
        except Exception:
            pass
    return results


def _r0224_mkOfObjOfMapSucc_map_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.mkOfObjOfMapSucc_map_succ
    # (mkOfObjOfMapSucc obj mapSucc).map' i (i + 1) = mapSucc ⟨i, hi⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mkOfObjOfMapSucc_obj_mapSucc_map_prime", 2)
    if args is not None:
        try:
            rhs = OOp("mapSucc", (OVar("i_hi"),))
            results.append((rhs, "Mathlib: CategoryTheory_mkOfObjOfMapSucc_map_succ"))
        except Exception:
            pass
    return results


def _r0225_fourd_4Tod_3_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₄Toδ₃_app_one
    # (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 1 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_4Tod_3_f_1_f_2_f_3_f_4_f_3_4_h_3_4_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_4Tod_3_app_one"))
        except Exception:
            pass
    return results


def _r0226_fourd_4Tod_3_app_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₄Toδ₃_app_two
    # (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 2 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_4Tod_3_f_1_f_2_f_3_f_4_f_3_4_h_3_4_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_4Tod_3_app_two"))
        except Exception:
            pass
    return results


def _r0227_fourd_4Tod_3_app_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₄Toδ₃_app_three
    # (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 3 = f₄
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_4Tod_3_f_1_f_2_f_3_f_4_f_3_4_h_3_4_app", 1)
    if args is not None:
        try:
            rhs = OVar("f_4")
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_4Tod_3_app_three"))
        except Exception:
            pass
    return results


def _r0228_fourd_3Tod_2_app_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₃Toδ₂_app_zero
    # (fourδ₃Toδ₂ f₁ f₂ f₃ f₄ f₂₃ f₃₄ h₂₃ h₃₄).app 0 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_3Tod_2_f_1_f_2_f_3_f_4_f_2_3_f_3_4_h_2_3_h_3_4_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_3Tod_2_app_zero"))
        except Exception:
            pass
    return results


def _r0229_fourd_3Tod_2_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₃Toδ₂_app_one
    # (fourδ₃Toδ₂ f₁ f₂ f₃ f₄ f₂₃ f₃₄ h₂₃ h₃₄).app 1 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_3Tod_2_f_1_f_2_f_3_f_4_f_2_3_f_3_4_h_2_3_h_3_4_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_3Tod_2_app_one"))
        except Exception:
            pass
    return results


def _r0230_fourd_3Tod_2_app_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₃Toδ₂_app_two
    # (fourδ₃Toδ₂ f₁ f₂ f₃ f₄ f₂₃ f₃₄ h₂₃ h₃₄).app 2 = f₃
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_3Tod_2_f_1_f_2_f_3_f_4_f_2_3_f_3_4_h_2_3_h_3_4_app", 1)
    if args is not None:
        try:
            rhs = OVar("f_3")
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_3Tod_2_app_two"))
        except Exception:
            pass
    return results


def _r0231_fourd_3Tod_2_app_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₃Toδ₂_app_three
    # (fourδ₃Toδ₂ f₁ f₂ f₃ f₄ f₂₃ f₃₄ h₂₃ h₃₄).app 3 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_3Tod_2_f_1_f_2_f_3_f_4_f_2_3_f_3_4_h_2_3_h_3_4_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_3Tod_2_app_three"))
        except Exception:
            pass
    return results


def _r0232_fourd_2Tod_1_app_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₂Toδ₁_app_zero
    # (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ f₂₃ h₁₂ h₂₃).app 0 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_2Tod_1_f_1_f_2_f_3_f_4_f_1_2_f_2_3_h_1_2_h_2_3_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_2Tod_1_app_zero"))
        except Exception:
            pass
    return results


def _r0233_fourd_2Tod_1_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₂Toδ₁_app_one
    # (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ f₂₃ h₁₂ h₂₃).app 1 = f₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_2Tod_1_f_1_f_2_f_3_f_4_f_1_2_f_2_3_h_1_2_h_2_3_app", 1)
    if args is not None:
        try:
            rhs = OVar("f_2")
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_2Tod_1_app_one"))
        except Exception:
            pass
    return results


def _r0234_fourd_2Tod_1_app_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₂Toδ₁_app_two
    # (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ f₂₃ h₁₂ h₂₃).app 2 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_2Tod_1_f_1_f_2_f_3_f_4_f_1_2_f_2_3_h_1_2_h_2_3_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_2Tod_1_app_two"))
        except Exception:
            pass
    return results


def _r0235_fourd_2Tod_1_app_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₂Toδ₁_app_three
    # (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ f₂₃ h₁₂ h₂₃).app 3 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_2Tod_1_f_1_f_2_f_3_f_4_f_1_2_f_2_3_h_1_2_h_2_3_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_2Tod_1_app_three"))
        except Exception:
            pass
    return results


def _r0236_fourd_1Tod_0_app_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₁Toδ₀_app_zero
    # (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 0 = f₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_1Tod_0_f_1_f_2_f_3_f_4_f_1_2_h_1_2_app", 1)
    if args is not None:
        try:
            rhs = OVar("f_1")
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_1Tod_0_app_zero"))
        except Exception:
            pass
    return results


def _r0237_fourd_1Tod_0_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₁Toδ₀_app_one
    # (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 1 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_1Tod_0_f_1_f_2_f_3_f_4_f_1_2_h_1_2_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_1Tod_0_app_one"))
        except Exception:
            pass
    return results


def _r0238_fourd_1Tod_0_app_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₁Toδ₀_app_two
    # (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 2 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_1Tod_0_f_1_f_2_f_3_f_4_f_1_2_h_1_2_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_1Tod_0_app_two"))
        except Exception:
            pass
    return results


def _r0239_fourd_1Tod_0_app_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.fourδ₁Toδ₀_app_three
    # (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 3 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fourd_1Tod_0_f_1_f_2_f_3_f_4_f_1_2_h_1_2_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_fourd_1Tod_0_app_three"))
        except Exception:
            pass
    return results


def _r0240_threed_3Tod_2_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.threeδ₃Toδ₂_app_one
    # (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 1 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "threed_3Tod_2_f_1_f_2_f_3_f_2_3_h_2_3_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_threed_3Tod_2_app_one"))
        except Exception:
            pass
    return results


def _r0241_threed_3Tod_2_app_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.threeδ₃Toδ₂_app_two
    # (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 2 = f₃
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "threed_3Tod_2_f_1_f_2_f_3_f_2_3_h_2_3_app", 1)
    if args is not None:
        try:
            rhs = OVar("f_3")
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_threed_3Tod_2_app_two"))
        except Exception:
            pass
    return results


def _r0242_threed_2Tod_1_app_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.threeδ₂Toδ₁_app_zero
    # (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).app 0 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "threed_2Tod_1_f_1_f_2_f_3_f_1_2_f_2_3_h_1_2_h_2_3_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_threed_2Tod_1_app_zero"))
        except Exception:
            pass
    return results


def _r0243_threed_2Tod_1_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.threeδ₂Toδ₁_app_one
    # (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).app 1 = f₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "threed_2Tod_1_f_1_f_2_f_3_f_1_2_f_2_3_h_1_2_h_2_3_app", 1)
    if args is not None:
        try:
            rhs = OVar("f_2")
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_threed_2Tod_1_app_one"))
        except Exception:
            pass
    return results


def _r0244_threed_2Tod_1_app_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.threeδ₂Toδ₁_app_two
    # (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).app 2 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "threed_2Tod_1_f_1_f_2_f_3_f_1_2_f_2_3_h_1_2_h_2_3_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_threed_2Tod_1_app_two"))
        except Exception:
            pass
    return results


def _r0245_threed_1Tod_0_app_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.threeδ₁Toδ₀_app_zero
    # (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 0 = f₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "threed_1Tod_0_f_1_f_2_f_3_f_1_2_h_1_2_app", 1)
    if args is not None:
        try:
            rhs = OVar("f_1")
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_threed_1Tod_0_app_zero"))
        except Exception:
            pass
    return results


def _r0246_threed_1Tod_0_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.threeδ₁Toδ₀_app_one
    # (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 1 = (𝟙 _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "threed_1Tod_0_f_1_f_2_f_3_f_1_2_h_1_2_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_threed_1Tod_0_app_one"))
        except Exception:
            pass
    return results


def _r0247_threed_1Tod_0_app_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.threeδ₁Toδ₀_app_two
    # (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 2 = (𝟙 _)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "threed_1Tod_0_f_1_f_2_f_3_f_1_2_h_1_2_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_threed_1Tod_0_app_two"))
        except Exception:
            pass
    return results


def _r0248_twod_2Tod_1_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.twoδ₂Toδ₁_app_one
    # (twoδ₂Toδ₁ f g fg h).app 1 = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "twod_2Tod_1_f_g_fg_h_app", 1)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_twod_2Tod_1_app_one"))
        except Exception:
            pass
    return results


def _r0249_twod_1Tod_0_app_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.twoδ₁Toδ₀_app_zero
    # (twoδ₁Toδ₀ f g fg h).app 0 = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "twod_1Tod_0_f_g_fg_h_app", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_twod_1Tod_0_app_zero"))
        except Exception:
            pass
    return results


def _r0250_twod_1Tod_0_app_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ComposableArrows.twoδ₁Toδ₀_app_one
    # (twoδ₁Toδ₀ f g fg h).app 1 = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "twod_1Tod_0_f_g_fg_h_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_ComposableArrows_twod_1Tod_0_app_one"))
        except Exception:
            pass
    return results


def _r0251_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.comp_apply
    # (f ≫ g) x = g (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: CategoryTheory_comp_apply"))
        except Exception:
            pass
    return results


def _r0252_naturality_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.NatTrans.naturality_apply
    # φ.app Y (F.map f x) = G.map f (φ.app X x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi_app", 2)
    if args is not None:
        try:
            rhs = OOp("G_map", (OVar("f"), OOp("phi_app", (OVar("X"), OVar("x"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_NatTrans_naturality_apply"))
        except Exception:
            pass
    return results


def _r0253_conj_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.conj_id
    # α.conj (𝟙 X) = 𝟙 Y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_conj", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("Y"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_conj_id"))
        except Exception:
            pass
    return results


def _r0254_refl_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.refl_conj
    # (Iso.refl X).conj f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_refl_X_conj", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CategoryTheory_Iso_refl_conj"))
        except Exception:
            pass
    return results


def _r0255_trans_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.trans_conj
    # (α ≪≫ β).conj f = β.conj (α.conj f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_b_conj", 1)
    if args is not None:
        try:
            rhs = OOp("b_conj", (OOp("a_conj", (args[0],)),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_trans_conj"))
        except Exception:
            pass
    return results


def _r0256_symm_self_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.symm_self_conj
    # α.symm.conj (α.conj f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_symm_conj", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CategoryTheory_Iso_symm_self_conj"))
        except Exception:
            pass
    return results


def _r0257_self_symm_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.self_symm_conj
    # α.conj (α.symm.conj f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_conj", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CategoryTheory_Iso_self_symm_conj"))
        except Exception:
            pass
    return results


def _r0258_conj_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.conj_pow
    # α.conj (f ^ n) = α.conj f ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_conj", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("a_conj", (OVar("f"),)), OVar("n")))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_conj_pow"))
        except Exception:
            pass
    return results


def _r0259_trans_conjAut(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.trans_conjAut
    # (α ≪≫ β).conjAut f = β.conjAut (α.conjAut f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_b_conjAut", 1)
    if args is not None:
        try:
            rhs = OOp("b_conjAut", (OOp("a_conjAut", (args[0],)),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_trans_conjAut"))
        except Exception:
            pass
    return results


def _r0260_conjAut_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.conjAut_trans
    # α.conjAut (f ≪≫ g) = α.conjAut f ≪≫ α.conjAut g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_conjAut", 1)
    if args is not None:
        try:
            rhs = OOp("a_conjAut", (OVar("f"), OVar("_unknown"), OVar("a_conjAut"), OVar("g"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_conjAut_trans"))
        except Exception:
            pass
    return results


def _r0261_conjAut_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.conjAut_pow
    # α.conjAut (f ^ n) = α.conjAut f ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_conjAut", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("a_conjAut", (OVar("f"),)), OVar("n")))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_conjAut_pow"))
        except Exception:
            pass
    return results


def _r0262_conjAut_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.conjAut_zpow
    # α.conjAut (f ^ n) = α.conjAut f ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_conjAut", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("a_conjAut", (OVar("f"),)), OVar("n")))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_conjAut_zpow"))
        except Exception:
            pass
    return results


def _r0263_inclusion_comp_decomposedTo(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.inclusion_comp_decomposedTo
    # inclusion j ⋙ decomposedTo J = ConnectedComponents.ι j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inclusion", 4)
    if args is not None:
        try:
            rhs = OOp("ConnectedComponents_i", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_inclusion_comp_decomposedTo"))
        except Exception:
            pass
    return results


def _r0264_coreId(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.coreId
    # (Iso.refl F).core = Iso.refl F.core
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Iso_refl_F_core")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Iso_refl", (OVar("F_core"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_coreId"))
    except Exception:
        pass
    return results


def _r0265_coreWhiskerLeft(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.coreWhiskerLeft
    # (isoWhiskerLeft F η).core =     F.coreComp G ≪≫ isoWhiskerLeft F.core η.core ≪≫ (F.coreComp H).symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("isoWhiskerLeft_F_eta_core")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("F_coreComp", (OVar("G"), OVar("_unknown"), OVar("isoWhiskerLeft"), OVar("F_core"), OVar("eta_core"), OVar("_unknown"), OVar("F_coreComp_H_symm"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_coreWhiskerLeft"))
    except Exception:
        pass
    return results


def _r0266_comp_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.DifferentialObject.comp_f
    # (f ≫ g).f = f.f ≫ g.f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_f", (OVar("_unknown"), OVar("g_f"),))
            results.append((rhs, "Mathlib: CategoryTheory_DifferentialObject_comp_f"))
    except Exception:
        pass
    return results


def _r0267_isoApp_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.DifferentialObject.isoApp_symm
    # isoApp f.symm = (isoApp f).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "isoApp", 1)
    if args is not None:
        try:
            rhs = OVar("isoApp_f_symm")
            results.append((rhs, "Mathlib: CategoryTheory_DifferentialObject_isoApp_symm"))
        except Exception:
            pass
    return results


def _r0268_isoApp_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.DifferentialObject.isoApp_trans
    # isoApp (f ≪≫ g) = isoApp f ≪≫ isoApp g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "isoApp", 1)
    if args is not None:
        try:
            rhs = OOp("isoApp", (OVar("f"), OVar("_unknown"), OVar("isoApp"), OVar("g"),))
            results.append((rhs, "Mathlib: CategoryTheory_DifferentialObject_isoApp_trans"))
        except Exception:
            pass
    return results


def _r0269_map_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.CategoryOfElements.map_snd
    # (F.map f.val) p.2 = q.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_map_f_val", 1)
    if args is not None:
        try:
            rhs = OVar("q_2")
            results.append((rhs, "Mathlib: CategoryTheory_CategoryOfElements_map_snd"))
        except Exception:
            pass
    return results


def _r0270_fromStructuredArrow_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.CategoryOfElements.fromStructuredArrow_map
    # (fromStructuredArrow F).map f = ⟨f.right, congr_fun f.w.symm PUnit.unit⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fromStructuredArrow_F_map", 1)
    if args is not None:
        try:
            rhs = OVar("f_right_congr_fun_f_w_symm_PUnit_unit")
            results.append((rhs, "Mathlib: CategoryTheory_CategoryOfElements_fromStructuredArrow_map"))
        except Exception:
            pass
    return results


def _r0271_id_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Endofunctor.Algebra.id_f
    # (𝟙 _ : A ⟶ A).1 = 𝟙 A.1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_A_A_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("A_1"),))
            results.append((rhs, "Mathlib: CategoryTheory_Endofunctor_Algebra_id_f"))
    except Exception:
        pass
    return results


def _r0272_comp_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Endofunctor.Algebra.comp_f
    # (f ≫ g).1 = f.1 ≫ g.1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_1", (OVar("_unknown"), OVar("g_1"),))
            results.append((rhs, "Mathlib: CategoryTheory_Endofunctor_Algebra_comp_f"))
    except Exception:
        pass
    return results


def _r0273_id_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Endofunctor.Coalgebra.id_f
    # (𝟙 _ : V ⟶ V).1 = 𝟙 V.1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_V_V_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("V_1"),))
            results.append((rhs, "Mathlib: CategoryTheory_Endofunctor_Coalgebra_id_f"))
    except Exception:
        pass
    return results


def _r0274_comp_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Endofunctor.Coalgebra.comp_f
    # (f ≫ g).1 = f.1 ≫ g.1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_1", (OVar("_unknown"), OVar("g_1"),))
            results.append((rhs, "Mathlib: CategoryTheory_Endofunctor_Coalgebra_comp_f"))
    except Exception:
        pass
    return results


def _r0275_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.End.ext
    # x = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("y")
            results.append((rhs, "Mathlib: CategoryTheory_End_ext"))
    except Exception:
        pass
    return results


def _r0276_of_to(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ForgetEnrichment.of_to
    # ForgetEnrichment.of W (ForgetEnrichment.to W X) = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ForgetEnrichment_of", 2)
    if args is not None:
        try:
            rhs = OVar("X")
            results.append((rhs, "Mathlib: CategoryTheory_ForgetEnrichment_of_to"))
        except Exception:
            pass
    return results


def _r0277_eHomEquiv_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.eHomEquiv_comp
    # eHomEquiv V (f ≫ g) = (λ_ _).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V g) ≫ eComp V X Y Z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eHomEquiv", 2)
    if args is not None:
        try:
            rhs = OOp("lam_inv", (OVar("_unknown"), OOp("eHomEquiv", (args[0], OVar("f"), OVar("_unknown"), OVar("eHomEquiv"), args[0], OVar("g"),)), OVar("_unknown"), OVar("eComp"), args[0], OVar("X"), OVar("Y"), OVar("Z"),))
            results.append((rhs, "Mathlib: CategoryTheory_eHomEquiv_comp"))
        except Exception:
            pass
    return results


def _r0278_eHomWhiskerRight_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.eHomWhiskerRight_comp
    # eHomWhiskerRight V (f ≫ f') Y = eHomWhiskerRight V f' Y ≫ eHomWhiskerRight V f Y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eHomWhiskerRight", 3)
    if args is not None:
        try:
            rhs = OOp("eHomWhiskerRight", (args[0], OVar("f_prime"), args[2], OVar("_unknown"), OVar("eHomWhiskerRight"), args[0], OVar("f"), args[2],))
            results.append((rhs, "Mathlib: CategoryTheory_eHomWhiskerRight_comp"))
        except Exception:
            pass
    return results


def _r0279_eHomWhiskerLeft_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.eHomWhiskerLeft_comp
    # eHomWhiskerLeft V X (g ≫ g') = eHomWhiskerLeft V X g ≫ eHomWhiskerLeft V X g'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eHomWhiskerLeft", 3)
    if args is not None:
        try:
            rhs = OOp("eHomWhiskerLeft", (args[0], args[1], OVar("g"), OVar("_unknown"), OVar("eHomWhiskerLeft"), args[0], args[1], OVar("g_prime"),))
            results.append((rhs, "Mathlib: CategoryTheory_eHomWhiskerLeft_comp"))
        except Exception:
            pass
    return results


def _r0280_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.eqToIso.inv
    # (eqToIso p).inv = eqToHom p.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("eqToIso_p_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("eqToHom", (OVar("p_symm"),))
            results.append((rhs, "Mathlib: CategoryTheory_eqToIso_inv"))
    except Exception:
        pass
    return results


def _r0281_eqToIso_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.eqToIso_refl
    # eqToIso p = Iso.refl X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eqToIso", 1)
    if args is not None:
        try:
            rhs = OOp("Iso_refl", (OVar("X"),))
            results.append((rhs, "Mathlib: CategoryTheory_eqToIso_refl"))
        except Exception:
            pass
    return results


def _r0282_eqToIso_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.eqToIso_trans
    # eqToIso p ≪≫ eqToIso q = eqToIso (p.trans q)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eqToIso", 4)
    if args is not None:
        try:
            rhs = OOp("eqToIso", (OOp("p_trans", (args[3],)),))
            results.append((rhs, "Mathlib: CategoryTheory_eqToIso_trans"))
        except Exception:
            pass
    return results


def _r0283_eqToHom_op(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.eqToHom_op
    # (eqToHom h).op = eqToHom (congr_arg op h.symm)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("eqToHom_h_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("eqToHom", (OOp("congr_arg", (OVar("op"), OVar("h_symm"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_eqToHom_op"))
    except Exception:
        pass
    return results


def _r0284_comp_asNatTrans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Equivalence.comp_asNatTrans
    # asNatTrans (α ≫ β) = asNatTrans α ≫ asNatTrans β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "asNatTrans", 1)
    if args is not None:
        try:
            rhs = OOp("asNatTrans", (OVar("a"), OVar("_unknown"), OVar("asNatTrans"), OVar("b"),))
            results.append((rhs, "Mathlib: CategoryTheory_Equivalence_comp_asNatTrans"))
        except Exception:
            pass
    return results


def _r0285_mkHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Equivalence.mkHom_comp
    # mkHom (α ≫ β) = mkHom α ≫ mkHom β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mkHom", 1)
    if args is not None:
        try:
            rhs = OOp("mkHom", (OVar("a"), OVar("_unknown"), OVar("mkHom"), OVar("b"),))
            results.append((rhs, "Mathlib: CategoryTheory_Equivalence_mkHom_comp"))
        except Exception:
            pass
    return results


def _r0286_essImage_i_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.essImage_ι_comp
    # (P.ι ⋙ F).essImage = P.map F
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("P_i_F_essImage")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("P_map", (OVar("F"),))
            results.append((rhs, "Mathlib: CategoryTheory_essImage_i_comp"))
    except Exception:
        pass
    return results


def _r0287_from_to(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ShrinkHoms.from_to
    # toShrinkHoms (fromShrinkHoms X) = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toShrinkHoms", 1)
    if args is not None:
        try:
            rhs = OVar("X")
            results.append((rhs, "Mathlib: CategoryTheory_ShrinkHoms_from_to"))
        except Exception:
            pass
    return results


def _r0288_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.BasedFunctor.id_comp
    # 𝟭 𝒳 ⋙ F = F
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: CategoryTheory_BasedFunctor_id_comp"))
        except Exception:
            pass
    return results


def _r0289_comp_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.BasedFunctor.comp_assoc
    # (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_G", 2)
    if args is not None:
        try:
            rhs = OOp("F", (args[0], OOp("G", (args[0], args[1],)),))
            results.append((rhs, "Mathlib: CategoryTheory_BasedFunctor_comp_assoc"))
        except Exception:
            pass
    return results


def _r0290_inducedFunctor_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.Fiber.inducedFunctor_comp
    # (inducedFunctor hF) ⋙ fiberInclusion = F
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inducedFunctor_hF", 2)
    if args is not None:
        try:
            rhs = OVar("F")
            results.append((rhs, "Mathlib: CategoryTheory_Functor_Fiber_inducedFunctor_comp"))
        except Exception:
            pass
    return results


def _r0291_inducedFunctor_comp_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.Fiber.inducedFunctor_comp_map
    # fiberInclusion.map ((inducedFunctor hF).map f) = F.map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fiberInclusion_map", 1)
    if args is not None:
        try:
            rhs = OOp("F_map", (OVar("f"),))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_Fiber_inducedFunctor_comp_map"))
        except Exception:
            pass
    return results


def _r0292_id_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.id_map
    # (𝟭 C).map f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_C_map", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CategoryTheory_Functor_id_map"))
        except Exception:
            pass
    return results


def _r0293_congr_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.congr_map
    # F.map f = F.map g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_map", 1)
    if args is not None:
        try:
            rhs = OOp("F_map", (OVar("g"),))
            results.append((rhs, "Mathlib: CategoryTheory_congr_map"))
        except Exception:
            pass
    return results


def _r0294_toPrefunctor_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.toPrefunctor_injective
    # F = G
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("F")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("G")
            results.append((rhs, "Mathlib: CategoryTheory_toPrefunctor_injective"))
    except Exception:
        pass
    return results


def _r0295_comp_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.NatTrans.comp_app
    # (α ≫ β).app X = α.app X ≫ β.app X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_b_app", 1)
    if args is not None:
        try:
            rhs = OOp("a_app", (args[0], OVar("_unknown"), OVar("b_app"), args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_NatTrans_comp_app"))
        except Exception:
            pass
    return results


def _r0296_app_naturality(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.NatTrans.app_naturality
    # (F.obj X).map f ≫ (T.app X).app Z = (T.app X).app Y ≫ (G.obj X).map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_obj_X_map", 4)
    if args is not None:
        try:
            rhs = OOp("T_app_X_app", (OVar("Y"), args[1], OVar("G_obj_X_map"), args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_NatTrans_app_naturality"))
        except Exception:
            pass
    return results


def _r0297_opObjUnop_inv_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.const.opObjUnop_inv_app
    # (opObjUnop.{v₁, v₂} X).inv.app j = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "opObjUnop_v_1_v_2_X_inv_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_const_opObjUnop_inv_app"))
        except Exception:
            pass
    return results


def _r0298_unop_functor_op_obj_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.const.unop_functor_op_obj_map
    # (unop ((Functor.op (const J)).obj X)).map f = 𝟙 (unop X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop_Functor_op_const_J_obj_X_map", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("unop", (OVar("X"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_const_unop_functor_op_obj_map"))
        except Exception:
            pass
    return results


def _r0299_comp_flip_uncurry_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.comp_flip_uncurry_eq
    # uncurry.obj (F ⋙ G).flip = (𝟭 C).prod F ⋙ uncurry.obj G.flip
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "uncurry_obj", 1)
    if args is not None:
        try:
            rhs = OOp("_1_C_prod", (OVar("F"), OVar("_unknown"), OVar("uncurry_obj"), OVar("G_flip"),))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_comp_flip_uncurry_eq"))
        except Exception:
            pass
    return results


def _r0300_curry_obj_comp_flip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.curry_obj_comp_flip
    # (curry.obj (F ⋙ G)).flip =       (curry.obj F).flip ⋙ (whiskeringRight _ _ _).obj G
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("curry_obj_F_G_flip")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("curry_obj_F_flip", (OVar("_unknown"), OVar("whiskeringRight_obj"), OVar("G"),))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_curry_obj_comp_flip"))
    except Exception:
        pass
    return results


def _r0301_preimage_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.preimage_comp
    # F.preimage (f ≫ g) = F.preimage f ≫ F.preimage g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_preimage", 1)
    if args is not None:
        try:
            rhs = OOp("F_preimage", (OVar("f"), OVar("_unknown"), OVar("F_preimage"), OVar("g"),))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_preimage_comp"))
        except Exception:
            pass
    return results


def _r0302_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.TwoSquare.ext
    # w = w'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("w")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("w_prime")
            results.append((rhs, "Mathlib: CategoryTheory_TwoSquare_ext"))
    except Exception:
        pass
    return results


def _r0303_autMap_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.PreGaloisCategory.autMap_comp
    # autMap (f ≫ g) = autMap g ∘ autMap f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "autMap", 1)
    if args is not None:
        try:
            rhs = OOp("comp", (OOp("autMap", (OVar("g"),)), OOp("autMap", (OVar("f"),))))
            results.append((rhs, "Mathlib: CategoryTheory_PreGaloisCategory_autMap_comp"))
        except Exception:
            pass
    return results


def _r0304_toAutHomeo_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.toAutHomeo_apply
    # toAutHomeo F G g = toAut F G g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAutHomeo", 3)
    if args is not None:
        try:
            rhs = OOp("toAut", (args[0], args[1], args[2],))
            results.append((rhs, "Mathlib: CategoryTheory_toAutHomeo_apply"))
        except Exception:
            pass
    return results


def _r0305_comp_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.PreGaloisCategory.PointedGaloisObject.comp_val
    # (f ≫ g).val = f.val ≫ g.val
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_val", (OVar("_unknown"), OVar("g_val"),))
            results.append((rhs, "Mathlib: CategoryTheory_PreGaloisCategory_PointedGaloisObject_comp_val"))
    except Exception:
        pass
    return results


def _r0306_incl_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.PreGaloisCategory.PointedGaloisObject.incl_map
    # (incl F).map f = f.val
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "incl_F_map", 1)
    if args is not None:
        try:
            rhs = OVar("f_val")
            results.append((rhs, "Mathlib: CategoryTheory_PreGaloisCategory_PointedGaloisObject_incl_map"))
        except Exception:
            pass
    return results


def _r0307_diagram_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.GlueData.diagram_snd
    # D.diagram.snd ⟨i, j⟩ = D.t i j ≫ D.f j i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D_diagram_snd", 1)
    if args is not None:
        try:
            rhs = OOp("D_t", (OVar("i"), OVar("j"), OVar("_unknown"), OVar("D_f"), OVar("j"), OVar("i"),))
            results.append((rhs, "Mathlib: CategoryTheory_GlueData_diagram_snd"))
        except Exception:
            pass
    return results


def _r0308_diagram_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.GlueData.diagram_left
    # D.diagram.left = D.V
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("D_diagram_left")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("D_V")
            results.append((rhs, "Mathlib: CategoryTheory_GlueData_diagram_left"))
    except Exception:
        pass
    return results


def _r0309_diagram_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.GlueData.diagram_right
    # D.diagram.right = D.U
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("D_diagram_right")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("D_U")
            results.append((rhs, "Mathlib: CategoryTheory_GlueData_diagram_right"))
    except Exception:
        pass
    return results


def _r0310_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.GradedObject.hom_ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: CategoryTheory_GradedObject_hom_ext"))
    except Exception:
        pass
    return results


def _r0311_fiber_eqToHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Grothendieck.fiber_eqToHom
    # (eqToHom h).fiber = eqToHom (by subst h; simp)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("eqToHom_h_fiber")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("eqToHom", (OOp("by", (OVar("subst"), OVar("h"), OVar("simp"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Grothendieck_fiber_eqToHom"))
    except Exception:
        pass
    return results


def _r0312_eqToHom_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Grothendieck.eqToHom_eq
    # eqToHom hF = { base := eqToHom (by subst hF; rfl), fiber := eqToHom (by subst hF; simp) }
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "eqToHom", 1)
    if args is not None:
        try:
            rhs = OVar("base_colon_eq_eqToHom_by_subst_hF_rfl_fiber_colon_eq_eqToHom_by_subst_hF_simp")
            results.append((rhs, "Mathlib: CategoryTheory_Grothendieck_eqToHom_eq"))
        except Exception:
            pass
    return results


def _r0313_lift_map_homMk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.FreeGroupoid.lift_map_homMk
    # (lift φ).map (homMk f) = φ.map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_phi_map", 1)
    if args is not None:
        try:
            rhs = OOp("phi_map", (OVar("f"),))
            results.append((rhs, "Mathlib: CategoryTheory_FreeGroupoid_lift_map_homMk"))
        except Exception:
            pass
    return results


def _r0314_mapId_inv_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.mapId_inv_app
    # (mapId C).inv.app X = 𝟙 X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapId_C_inv_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_mapId_inv_app"))
        except Exception:
            pass
    return results


def _r0315_mapComp_inv_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.mapComp_inv_app
    # (mapComp φ φ').inv.app X = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapComp_phi_phi_prime_inv_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_mapComp_inv_app"))
        except Exception:
            pass
    return results


def _r0316_map_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.map_comp
    # map (φ ⋙ φ') = map φ ⋙ map φ'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 1)
    if args is not None:
        try:
            rhs = OOp("map", (OVar("phi"), OVar("_unknown"), OVar("map"), OVar("phi_prime"),))
            results.append((rhs, "Mathlib: CategoryTheory_map_comp"))
        except Exception:
            pass
    return results


def _r0317_map_map_homMk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.map_map_homMk
    # (map φ).map (homMk f) = homMk (φ.map f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_phi_map", 1)
    if args is not None:
        try:
            rhs = OOp("homMk", (OOp("phi_map", (OVar("f"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_map_map_homMk"))
        except Exception:
            pass
    return results


def _r0318_mapCompLift_inv_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.mapCompLift_inv_app
    # (mapCompLift F G).inv.app X = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapCompLift_F_G_inv_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_mapCompLift_inv_app"))
        except Exception:
            pass
    return results


def _r0319_app_comp_p(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.app_comp_p
    # f.f.app X ≫ Q.p.app X = f.f.app X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_f_app", 4)
    if args is not None:
        try:
            rhs = OOp("f_f_app", (args[3],))
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_app_comp_p"))
        except Exception:
            pass
    return results


def _r0320_app_p_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.app_p_comm
    # P.p.app X ≫ f.f.app X = f.f.app X ≫ Q.p.app X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "P_p_app", 4)
    if args is not None:
        try:
            rhs = OOp("f_f_app", (args[3], args[1], OVar("Q_p_app"), args[3],))
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_app_p_comm"))
        except Exception:
            pass
    return results


def _r0321_karoubiUniversal_2_functor_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.karoubiUniversal₂_functor_eq
    # (karoubiUniversal₂ C D).functor = functorExtension₂ C D
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("karoubiUniversal_2_C_D_functor")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("functorExtension_2", (OVar("C"), OVar("D"),))
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_karoubiUniversal_2_functor_eq"))
    except Exception:
        pass
    return results


def _r0322_karoubiUniversal_functor_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.karoubiUniversal_functor_eq
    # (karoubiUniversal C D).functor = functorExtension C D
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("karoubiUniversal_C_D_functor")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("functorExtension", (OVar("C"), OVar("D"),))
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_karoubiUniversal_functor_eq"))
    except Exception:
        pass
    return results


def _r0323_comp_p_d(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.Karoubi.HomologicalComplex.comp_p_d
    # f.f.f n ≫ Q.p.f n = f.f.f n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_f_f", 4)
    if args is not None:
        try:
            rhs = OOp("f_f_f", (args[3],))
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_Karoubi_HomologicalComplex_comp_p_d"))
        except Exception:
            pass
    return results


def _r0324_p_comm_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comm_f
    # P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "P_p_f", 4)
    if args is not None:
        try:
            rhs = OOp("f_f_f", (args[3], args[1], OVar("Q_p_f"), args[3],))
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_Karoubi_HomologicalComplex_p_comm_f"))
        except Exception:
            pass
    return results


def _r0325_comp_p(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.Karoubi.comp_p
    # f.f ≫ Q.p = f.f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_f", 2)
    if args is not None:
        try:
            rhs = OVar("f_f")
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_Karoubi_comp_p"))
        except Exception:
            pass
    return results


def _r0326_p_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.Karoubi.p_comm
    # P.p ≫ f.f = f.f ≫ Q.p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "P_p", 2)
    if args is not None:
        try:
            rhs = OOp("f_f", (args[0], OVar("Q_p"),))
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_Karoubi_p_comm"))
        except Exception:
            pass
    return results


def _r0327_id_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.Karoubi.id_f
    # Hom.f (𝟙 P) = P.p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_f", 1)
    if args is not None:
        try:
            rhs = OVar("P_p")
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_Karoubi_id_f"))
        except Exception:
            pass
    return results


def _r0328_eqToHom_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.Karoubi.eqToHom_f
    # Karoubi.Hom.f (eqToHom h) = P.p ≫ eqToHom (congr_arg Karoubi.X h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Karoubi_Hom_f", 1)
    if args is not None:
        try:
            rhs = OOp("P_p", (OVar("_unknown"), OVar("eqToHom"), OOp("congr_arg", (OVar("Karoubi_X"), OVar("h"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_Karoubi_eqToHom_f"))
        except Exception:
            pass
    return results


def _r0329_p_comm_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Idempotents.KaroubiKaroubi.p_comm_f
    # P.p.f ≫ f.f.f = f.f.f ≫ Q.p.f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "P_p_f", 2)
    if args is not None:
        try:
            rhs = OOp("f_f_f", (args[0], OVar("Q_p_f"),))
            results.append((rhs, "Mathlib: CategoryTheory_Idempotents_KaroubiKaroubi_p_comm_f"))
        except Exception:
            pass
    return results


def _r0330_symm_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.symm_mk
    # Iso.symm { hom, inv, hom_inv_id := hom_inv_id, inv_hom_id := inv_hom_id } =       { hom := inv, inv := hom, hom_inv_id :
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iso_symm", 1)
    if args is not None:
        try:
            rhs = OVar("hom_colon_eq_inv_inv_colon_eq_hom_hom_inv_id_colon_eq_inv_hom_id_inv_hom_id_colon_eq_hom_inv_id")
            results.append((rhs, "Mathlib: CategoryTheory_Iso_symm_mk"))
        except Exception:
            pass
    return results


def _r0331_trans_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.trans_assoc
    # (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_b", 2)
    if args is not None:
        try:
            rhs = OOp("a", (args[0], OVar("b"), args[0], args[1],))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_trans_assoc"))
        except Exception:
            pass
    return results


def _r0332_trans_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.trans_refl
    # α ≪≫ Iso.refl Y = α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 3)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: CategoryTheory_Iso_trans_refl"))
        except Exception:
            pass
    return results


def _r0333_symm_self_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.symm_self_id
    # α.symm ≪≫ α = Iso.refl Y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_symm", 2)
    if args is not None:
        try:
            rhs = OOp("Iso_refl", (OVar("Y"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_symm_self_id"))
        except Exception:
            pass
    return results


def _r0334_self_symm_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.self_symm_id
    # α ≪≫ α.symm = Iso.refl X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("Iso_refl", (OVar("X"),))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_self_symm_id"))
        except Exception:
            pass
    return results


def _r0335_symm_self_id_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.symm_self_id_assoc
    # α.symm ≪≫ α ≪≫ β = β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_symm", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: CategoryTheory_Iso_symm_self_id_assoc"))
        except Exception:
            pass
    return results


def _r0336_self_symm_id_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.self_symm_id_assoc
    # α ≪≫ α.symm ≪≫ β = β
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: CategoryTheory_Iso_self_symm_id_assoc"))
        except Exception:
            pass
    return results


def _r0337_inv_comp_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.inv_comp_eq
    # α.inv ≫ f = g ↔ f = α.hom ≫ g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_inv", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("g"), args[1])), OOp("a_hom", (args[0], OVar("g"),))))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_inv_comp_eq"))
        except Exception:
            pass
    return results


def _r0338_asIso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.asIso_inv
    # (asIso f).inv = inv f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("asIso_f_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inv", (OVar("f"),))
            results.append((rhs, "Mathlib: CategoryTheory_asIso_inv"))
    except Exception:
        pass
    return results


def _r0339_eq_inv_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.IsIso.eq_inv_comp
    # g = inv α ≫ f ↔ α ≫ g = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("inv", (OVar("a"), OVar("_unknown"), OVar("f"),)), OOp("a", (OVar("_unknown"), OVar("g"),)))), OVar("f")))
            results.append((rhs, "Mathlib: CategoryTheory_IsIso_eq_inv_comp"))
    except Exception:
        pass
    return results


def _r0340_map_inv_hom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Iso.map_inv_hom_id
    # F.map e.inv ≫ F.map e.hom = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_map", 4)
    if args is not None:
        try:
            rhs = OOp("_1", (args[1],))
            results.append((rhs, "Mathlib: CategoryTheory_Iso_map_inv_hom_id"))
        except Exception:
            pass
    return results


def _r0341_mapIso_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.mapIso_trans
    # F.mapIso (i ≪≫ j) = F.mapIso i ≪≫ F.mapIso j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "F_mapIso", 1)
    if args is not None:
        try:
            rhs = OOp("F_mapIso", (OVar("i"), OVar("_unknown"), OVar("F_mapIso"), OVar("j"),))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_mapIso_trans"))
        except Exception:
            pass
    return results


def _r0342_fromSum_map_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Join.fromSum_map_inl
    # (fromSum C D).map ((Sum.inl_ C D).map f) = (inclLeft C D).map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fromSum_C_D_map", 1)
    if args is not None:
        try:
            rhs = OOp("inclLeft_C_D_map", (OVar("f"),))
            results.append((rhs, "Mathlib: CategoryTheory_Join_fromSum_map_inl"))
        except Exception:
            pass
    return results


def _r0343_isoMap_inv_hom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Functor.IsEventuallyConstantTo.isoMap_inv_hom_id
    # (h.isoMap φ hφ).inv ≫ F.map φ = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_isoMap_phi_hphi_inv", 3)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Functor_IsEventuallyConstantTo_isoMap_inv_hom_id"))
        except Exception:
            pass
    return results


def _r0344_isoMap_inv_hom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.IsEventuallyConstantFrom.isoMap_inv_hom_id
    # (h.isoMap φ hφ).inv ≫ F.map φ = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_isoMap_phi_hphi_inv", 3)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_IsEventuallyConstantFrom_isoMap_inv_hom_id"))
        except Exception:
            pass
    return results


def _r0345_pullbackZeroZeroIso_hom_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.pullbackZeroZeroIso_hom_snd
    # (pullbackZeroZeroIso X Y).hom ≫ prod.snd = pullback.snd 0 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pullbackZeroZeroIso_X_Y_hom", 2)
    if args is not None:
        try:
            rhs = OOp("pullback_snd", (OLit(0), OLit(0),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_pullbackZeroZeroIso_hom_snd"))
        except Exception:
            pass
    return results


def _r0346_inr_pushoutZeroZeroIso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.inr_pushoutZeroZeroIso_inv
    # coprod.inr ≫ (pushoutZeroZeroIso X Y).inv = pushout.inr _ _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coprod_inr", 2)
    if args is not None:
        try:
            rhs = OOp("pushout_inr", (args[0], args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_inr_pushoutZeroZeroIso_inv"))
        except Exception:
            pass
    return results


def _r0347_forget_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.RightExactFunctor.forget_obj
    # (RightExactFunctor.forget C D).obj F = F.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "RightExactFunctor_forget_C_D_obj", 1)
    if args is not None:
        try:
            rhs = OVar("F_1")
            results.append((rhs, "Mathlib: CategoryTheory_RightExactFunctor_forget_obj"))
        except Exception:
            pass
    return results


def _r0348_forget_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ExactFunctor.forget_obj
    # (ExactFunctor.forget C D).obj F = F.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ExactFunctor_forget_C_D_obj", 1)
    if args is not None:
        try:
            rhs = OVar("F_1")
            results.append((rhs, "Mathlib: CategoryTheory_ExactFunctor_forget_obj"))
        except Exception:
            pass
    return results


def _r0349_forget_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.LeftExactFunctor.forget_map
    # (LeftExactFunctor.forget C D).map α = α.hom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LeftExactFunctor_forget_C_D_map", 1)
    if args is not None:
        try:
            rhs = OVar("a_hom")
            results.append((rhs, "Mathlib: CategoryTheory_LeftExactFunctor_forget_map"))
        except Exception:
            pass
    return results


def _r0350_cofan_inj_f_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.cofan_inj_f_snd
    # (((cofan 𝒜 f).inj i).f x).2 = x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cofan_f_inj_i_f_x_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_cofan_inj_f_snd"))
    except Exception:
        pass
    return results


def _r0351_cofan_inj_phi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.cofan_inj_φ
    # ((cofan 𝒜 f).inj i).φ x = 𝟙 ((f i).obj x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cofan_f_inj_i_phi", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("f_i_obj", (args[0],)),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_cofan_inj_phi"))
        except Exception:
            pass
    return results


def _r0352_i_comp_coproductIsoSelf_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.ι_comp_coproductIsoSelf_hom
    # Sigma.ι _ i ≫ (coproductIsoSelf X).hom = .fromIncl i (𝟙 (X.obj i))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Sigma_i", 4)
    if args is not None:
        try:
            rhs = OOp("fromIncl", (args[1], OOp("_1", (OOp("X_obj", (args[1],)),)),))
            results.append((rhs, "Mathlib: CategoryTheory_i_comp_coproductIsoSelf_hom"))
        except Exception:
            pass
    return results


def _r0353_fromIncl_comp_coproductIsoSelf_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.fromIncl_comp_coproductIsoSelf_inv
    # Hom.fromIncl i (𝟙 (X.obj i)) ≫ (coproductIsoSelf X).inv = Sigma.ι X.toFun i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Hom_fromIncl", 4)
    if args is not None:
        try:
            rhs = OOp("Sigma_i", (OVar("X_toFun"), args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_fromIncl_comp_coproductIsoSelf_inv"))
        except Exception:
            pass
    return results


def _r0354_cone_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.limit.cone_π
    # (limit.cone F).π.app = limit.π _
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("limit_cone_F_pi_app")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("limit_pi", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_limit_cone_pi"))
    except Exception:
        pass
    return results


def _r0355_w(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.limit.w
    # limit.π F j ≫ F.map f = limit.π F j'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "limit_pi", 5)
    if args is not None:
        try:
            rhs = OOp("limit_pi", (args[0], OVar("j_prime"),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_limit_w"))
        except Exception:
            pass
    return results


def _r0356_uniq_cone_morphism(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.IsLimit.uniq_cone_morphism
    # f = f'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_prime")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_IsLimit_uniq_cone_morphism"))
    except Exception:
        pass
    return results


def _r0357_iso_inv_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.PreservesLimitPair.iso_inv_fst
    # (PreservesLimitPair.iso G X Y).inv ≫ G.map prod.fst = prod.fst
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "PreservesLimitPair_iso_G_X_Y_inv", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: CategoryTheory_Limits_PreservesLimitPair_iso_inv_fst"))
        except Exception:
            pass
    return results


def _r0358_toCone_pi_app_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryBicone.toCone_π_app_left
    # c.toCone.π.app ⟨WalkingPair.left⟩ = c.fst
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_toCone_pi_app", 1)
    if args is not None:
        try:
            rhs = OVar("c_fst")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryBicone_toCone_pi_app_left"))
        except Exception:
            pass
    return results


def _r0359_toCone_pi_app_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryBicone.toCone_π_app_right
    # c.toCone.π.app ⟨WalkingPair.right⟩ = c.snd
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_toCone_pi_app", 1)
    if args is not None:
        try:
            rhs = OVar("c_snd")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryBicone_toCone_pi_app_right"))
        except Exception:
            pass
    return results


def _r0360_binary_fan_fst_toCone(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryBicone.binary_fan_fst_toCone
    # BinaryFan.fst c.toCone = c.fst
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BinaryFan_fst", 1)
    if args is not None:
        try:
            rhs = OVar("c_fst")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryBicone_binary_fan_fst_toCone"))
        except Exception:
            pass
    return results


def _r0361_binary_fan_snd_toCone(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryBicone.binary_fan_snd_toCone
    # BinaryFan.snd c.toCone = c.snd
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BinaryFan_snd", 1)
    if args is not None:
        try:
            rhs = OVar("c_snd")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryBicone_binary_fan_snd_toCone"))
        except Exception:
            pass
    return results


def _r0362_toCocone_i_app_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryBicone.toCocone_ι_app_left
    # c.toCocone.ι.app ⟨WalkingPair.left⟩ = c.inl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_toCocone_i_app", 1)
    if args is not None:
        try:
            rhs = OVar("c_inl")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryBicone_toCocone_i_app_left"))
        except Exception:
            pass
    return results


def _r0363_toCocone_i_app_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryBicone.toCocone_ι_app_right
    # c.toCocone.ι.app ⟨WalkingPair.right⟩ = c.inr
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_toCocone_i_app", 1)
    if args is not None:
        try:
            rhs = OVar("c_inr")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryBicone_toCocone_i_app_right"))
        except Exception:
            pass
    return results


def _r0364_binary_cofan_inl_toCocone(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryBicone.binary_cofan_inl_toCocone
    # BinaryCofan.inl c.toCocone = c.inl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BinaryCofan_inl", 1)
    if args is not None:
        try:
            rhs = OVar("c_inl")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryBicone_binary_cofan_inl_toCocone"))
        except Exception:
            pass
    return results


def _r0365_binary_cofan_inr_toCocone(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryBicone.binary_cofan_inr_toCocone
    # BinaryCofan.inr c.toCocone = c.inr
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BinaryCofan_inr", 1)
    if args is not None:
        try:
            rhs = OVar("c_inr")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryBicone_binary_cofan_inr_toCocone"))
        except Exception:
            pass
    return results


def _r0366_swap_apply_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.WalkingPair.swap_apply_right
    # WalkingPair.swap right = left
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WalkingPair_swap", 1)
    if args is not None:
        try:
            rhs = OVar("left")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_WalkingPair_swap_apply_right"))
        except Exception:
            pass
    return results


def _r0367_swap_symm_apply_tt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.WalkingPair.swap_symm_apply_tt
    # WalkingPair.swap.symm left = right
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WalkingPair_swap_symm", 1)
    if args is not None:
        try:
            rhs = OVar("right")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_WalkingPair_swap_symm_apply_tt"))
        except Exception:
            pass
    return results


def _r0368_swap_symm_apply_ff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.WalkingPair.swap_symm_apply_ff
    # WalkingPair.swap.symm right = left
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WalkingPair_swap_symm", 1)
    if args is not None:
        try:
            rhs = OVar("left")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_WalkingPair_swap_symm_apply_ff"))
        except Exception:
            pass
    return results


def _r0369_equivBool_apply_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.WalkingPair.equivBool_apply_right
    # WalkingPair.equivBool right = false
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WalkingPair_equivBool", 1)
    if args is not None:
        try:
            rhs = OLit(False)
            results.append((rhs, "Mathlib: CategoryTheory_Limits_WalkingPair_equivBool_apply_right"))
        except Exception:
            pass
    return results


def _r0370_equivBool_symm_apply_true(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.WalkingPair.equivBool_symm_apply_true
    # WalkingPair.equivBool.symm true = left
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WalkingPair_equivBool_symm", 1)
    if args is not None:
        try:
            rhs = OVar("left")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_WalkingPair_equivBool_symm_apply_true"))
        except Exception:
            pass
    return results


def _r0371_equivBool_symm_apply_false(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.WalkingPair.equivBool_symm_apply_false
    # WalkingPair.equivBool.symm false = right
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "WalkingPair_equivBool_symm", 1)
    if args is not None:
        try:
            rhs = OVar("right")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_WalkingPair_equivBool_symm_apply_false"))
        except Exception:
            pass
    return results


def _r0372_pairFunction_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.pairFunction_right
    # pairFunction X Y right = Y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pairFunction", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: CategoryTheory_Limits_pairFunction_right"))
        except Exception:
            pass
    return results


def _r0373_pair_obj_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.pair_obj_right
    # (pair X Y).obj ⟨right⟩ = Y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair_X_Y_obj", 1)
    if args is not None:
        try:
            rhs = OVar("Y")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_pair_obj_right"))
        except Exception:
            pass
    return results


def _r0374_mapPair_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.mapPair_right
    # (mapPair f g).app ⟨right⟩ = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapPair_f_g_app", 1)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: CategoryTheory_Limits_mapPair_right"))
        except Exception:
            pass
    return results


def _r0375_unop_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryFan.unop_mk
    # BinaryFan.unop (mk π₁ π₂) = .mk π₁.unop π₂.unop
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BinaryFan_unop", 1)
    if args is not None:
        try:
            rhs = OOp("mk", (OVar("pi_1_unop"), OVar("pi_2_unop"),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryFan_unop_mk"))
        except Exception:
            pass
    return results


def _r0376_op_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryCofan.op_mk
    # BinaryCofan.op (mk ι₁ ι₂) = .mk ι₁.op ι₂.op
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BinaryCofan_op", 1)
    if args is not None:
        try:
            rhs = OOp("mk", (OVar("i_1_op"), OVar("i_2_op"),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryCofan_op_mk"))
        except Exception:
            pass
    return results


def _r0377_unop_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.BinaryCofan.unop_mk
    # BinaryCofan.unop (mk ι₁ ι₂) = .mk ι₁.unop ι₂.unop
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "BinaryCofan_unop", 1)
    if args is not None:
        try:
            rhs = OOp("mk", (OVar("i_1_unop"), OVar("i_2_unop"),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_BinaryCofan_unop_mk"))
        except Exception:
            pass
    return results


def _r0378_bicone_i_pi_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.bicone_ι_π_ne
    # B.ι j ≫ B.π j' = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "B_i", 4)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CategoryTheory_Limits_bicone_i_pi_ne"))
        except Exception:
            pass
    return results


def _r0379_toCone_pi_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.Bicone.toCone_π_app
    # B.toCone.π.app j = B.π j.as
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "B_toCone_pi_app", 1)
    if args is not None:
        try:
            rhs = OOp("B_pi", (OVar("j_as"),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_Bicone_toCone_pi_app"))
        except Exception:
            pass
    return results


def _r0380_toCone_pi_app_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.Bicone.toCone_π_app_mk
    # B.toCone.π.app ⟨j⟩ = B.π j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "B_toCone_pi_app", 1)
    if args is not None:
        try:
            rhs = OOp("B_pi", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_Bicone_toCone_pi_app_mk"))
        except Exception:
            pass
    return results


def _r0381_toCone_proj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.Bicone.toCone_proj
    # Fan.proj B.toCone j = B.π j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fan_proj", 2)
    if args is not None:
        try:
            rhs = OOp("B_pi", (args[1],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_Bicone_toCone_proj"))
        except Exception:
            pass
    return results


def _r0382_toCocone_i_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.Bicone.toCocone_ι_app
    # B.toCocone.ι.app j = B.ι j.as
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "B_toCocone_i_app", 1)
    if args is not None:
        try:
            rhs = OOp("B_i", (OVar("j_as"),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_Bicone_toCocone_i_app"))
        except Exception:
            pass
    return results


def _r0383_toCocone_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.Bicone.toCocone_inj
    # Cofan.inj B.toCocone j = B.ι j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Cofan_inj", 2)
    if args is not None:
        try:
            rhs = OOp("B_i", (args[1],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_Bicone_toCocone_inj"))
        except Exception:
            pass
    return results


def _r0384_toCocone_i_app_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.Bicone.toCocone_ι_app_mk
    # B.toCocone.ι.app ⟨j⟩ = B.ι j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "B_toCocone_i_app", 1)
    if args is not None:
        try:
            rhs = OOp("B_i", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_Bicone_toCocone_i_app_mk"))
        except Exception:
            pass
    return results


def _r0385_diagonal_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.pullback.diagonal_snd
    # diagonal f ≫ pullback.snd _ _ = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "diagonal", 5)
    if args is not None:
        try:
            rhs = OOp("_1", (args[4],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_pullback_diagonal_snd"))
        except Exception:
            pass
    return results


def _r0386_mk_i(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.Wedge.mk_ι
    # (mk pt π hπ).ι j = π j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mk_pt_pi_hpi_i", 1)
    if args is not None:
        try:
            rhs = OOp("pi", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_Wedge_mk_i"))
        except Exception:
            pass
    return results


def _r0387_mk_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Cowedge.mk_π
    # (mk pt ι hι).π j = ι j
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mk_pt_i_hi_pi", 1)
    if args is not None:
        try:
            rhs = OOp("i", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Cowedge_mk_pi"))
        except Exception:
            pass
    return results


def _r0388_walkingParallelPairOp_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOp_one
    # walkingParallelPairOp.obj one = op zero
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOp_obj", 1)
    if args is not None:
        try:
            rhs = OOp("op", (OVar("zero"),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOp_one"))
        except Exception:
            pass
    return results


def _r0389_walkingParallelPairOp_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOp_left
    # walkingParallelPairOp.map left = @Quiver.Hom.op _ _ zero one left
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOp_map", 1)
    if args is not None:
        try:
            rhs = OOp("at_Quiver_Hom_op", (OVar("_unknown"), OVar("_unknown"), OVar("zero"), OVar("one"), args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOp_left"))
        except Exception:
            pass
    return results


def _r0390_walkingParallelPairOp_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOp_right
    # walkingParallelPairOp.map right = @Quiver.Hom.op _ _ zero one right
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOp_map", 1)
    if args is not None:
        try:
            rhs = OOp("at_Quiver_Hom_op", (OVar("_unknown"), OVar("_unknown"), OVar("zero"), OVar("one"), args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOp_right"))
        except Exception:
            pass
    return results


def _r0391_walkingParallelPairOpEquiv_unitIso_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_one
    # walkingParallelPairOpEquiv.unitIso.app one = Iso.refl one
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOpEquiv_unitIso_app", 1)
    if args is not None:
        try:
            rhs = OOp("Iso_refl", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOpEquiv_unitIso_one"))
        except Exception:
            pass
    return results


def _r0392_walkingParallelPairOpEquiv_counitIso_zer(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_zero
    # walkingParallelPairOpEquiv.counitIso.app (op zero) = Iso.refl (op zero)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOpEquiv_counitIso_app", 1)
    if args is not None:
        try:
            rhs = OOp("Iso_refl", (OOp("op", (OVar("zero"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOpEquiv_counitIso_zero"))
        except Exception:
            pass
    return results


def _r0393_walkingParallelPairOpEquiv_counitIso_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_one
    # walkingParallelPairOpEquiv.counitIso.app (op one) = Iso.refl (op one)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOpEquiv_counitIso_app", 1)
    if args is not None:
        try:
            rhs = OOp("Iso_refl", (OOp("op", (OVar("one"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOpEquiv_counitIso_one"))
        except Exception:
            pass
    return results


def _r0394_walkingParallelPairOpEquiv_unitIso_hom_a(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_hom_app_one
    # walkingParallelPairOpEquiv.unitIso.hom.app one = 𝟙 one
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOpEquiv_unitIso_hom_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOpEquiv_unitIso_hom_app_one"))
        except Exception:
            pass
    return results


def _r0395_walkingParallelPairOpEquiv_unitIso_inv_a(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_inv_app_zero
    # walkingParallelPairOpEquiv.unitIso.inv.app zero = 𝟙 zero
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOpEquiv_unitIso_inv_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOpEquiv_unitIso_inv_app_zero"))
        except Exception:
            pass
    return results


def _r0396_walkingParallelPairOpEquiv_unitIso_inv_a(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_inv_app_one
    # walkingParallelPairOpEquiv.unitIso.inv.app one = 𝟙 one
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOpEquiv_unitIso_inv_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0],))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOpEquiv_unitIso_inv_app_one"))
        except Exception:
            pass
    return results


def _r0397_walkingParallelPairOpEquiv_counitIso_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_hom_app_op_zero
    # walkingParallelPairOpEquiv.counitIso.hom.app (op zero) = 𝟙 (op zero)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOpEquiv_counitIso_hom_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("op", (OVar("zero"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOpEquiv_counitIso_hom_app_op_zero"))
        except Exception:
            pass
    return results


def _r0398_walkingParallelPairOpEquiv_counitIso_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_hom_app_op_one
    # walkingParallelPairOpEquiv.counitIso.hom.app (op one) = 𝟙 (op one)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOpEquiv_counitIso_hom_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("op", (OVar("one"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOpEquiv_counitIso_hom_app_op_one"))
        except Exception:
            pass
    return results


def _r0399_walkingParallelPairOpEquiv_counitIso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_inv_app_op_one
    # walkingParallelPairOpEquiv.counitIso.inv.app (op one) = 𝟙 (op one)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "walkingParallelPairOpEquiv_counitIso_inv_app", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("op", (OVar("one"),)),))
            results.append((rhs, "Mathlib: CategoryTheory_Limits_walkingParallelPairOpEquiv_counitIso_inv_app_op_one"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_category rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("**", "+", "-", "A_hom", "Arrow_Hom_right", "B_i", "B_toCocone_i_app", "B_toCone_pi_app", "BinaryCofan_inl", "BinaryCofan_inr", "BinaryCofan_op", "BinaryCofan_unop", "BinaryFan_fst", "BinaryFan_snd", "BinaryFan_unop", "Cat_of", "Cofan_inj", "CommaMorphism_left", "ComposableArrows_mk_0", "D", "D_diagram_snd", "ExactFunctor_forget_C_D_obj", "F", "F_G", "F_G_toFunctor_obj", "F_eta_toNatTrans_app", "F_fromLeftDerivedZero", "F_map", "F_mapExtAddHom", "F_mapHomologicalComplex_ComplexShape_up_commShiftIso_n_inv_app_K_f", "F_mapIso", "F_map_f_val", "F_obj_X_map", "F_preimage", "F_rightDerivedZeroIsoSelf_hom", "Fan_proj", "ForgetEnrichment_of", "ForgetEnrichment_to", "FunctorCategoryEquivalence_functor", "Functor_comp", "G", "G_map", "Hom_2_associator", "Hom_2_associator_inv", "Hom_2_left_unitor", "Hom_2_left_unitor_inv", "Hom_2_right_unitor", "Hom_2_right_unitor_inv", "Hom_f", "Hom_f_1",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_category axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_category rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_toBialgEquiv_refl(term, ctx))
    results.extend(_r0001_toBialgEquiv_symm(term, ctx))
    results.extend(_r0002_toBialgEquiv_trans(term, ctx))
    results.extend(_r0003_toCoalgEquiv_refl(term, ctx))
    results.extend(_r0004_toCoalgEquiv_symm(term, ctx))
    results.extend(_r0005_toCoalgEquiv_trans(term, ctx))
    results.extend(_r0006_toHopfAlgEquiv_refl(term, ctx))
    results.extend(_r0007_toHopfAlgEquiv_symm(term, ctx))
    results.extend(_r0008_toHopfAlgEquiv_trans(term, ctx))
    results.extend(_r0009_toLinearEquiv_symm(term, ctx))
    results.extend(_r0010_toLinearMap_toLinearEquiv(term, ctx))
    results.extend(_r0011_mk_0_homEquiv_0_apply(term, ctx))
    results.extend(_r0012_mk_0_add(term, ctx))
    results.extend(_r0013_mapExtAddHom_apply(term, ctx))
    results.extend(_r0014_mapExtLinearMap_coe(term, ctx))
    results.extend(_r0015_mapToComposableArrows_app_1(term, ctx))
    results.extend(_r0016_mapToComposableArrows_app_2(term, ctx))
    results.extend(_r0017_mapToComposableArrows_id(term, ctx))
    results.extend(_r0018_comp_d(term, ctx))
    results.extend(_r0019_mapHomotopyCategory_comp(term, ctx))
    results.extend(_r0020_mapHomologicalComplex_commShiftIso_inv_a(term, ctx))
    results.extend(_r0021_id_tau_2(term, ctx))
    results.extend(_r0022_id_tau_3(term, ctx))
    results.extend(_r0023_comp_tau_1(term, ctx))
    results.extend(_r0024_comp_tau_2(term, ctx))
    results.extend(_r0025_zero_tau_2(term, ctx))
    results.extend(_r0026_zero_tau_3(term, ctx))
    results.extend(_r0027_pi_1Topi_2_comp_pi_2Topi_3(term, ctx))
    results.extend(_r0028_map_id(term, ctx))
    results.extend(_r0029_map_comp(term, ctx))
    results.extend(_r0030_liftK_pi_eq_zero_of_boundary(term, ctx))
    results.extend(_r0031_toCycles_i(term, ctx))
    results.extend(_r0032_cyclesIsoX_2_inv_hom_id(term, ctx))
    results.extend(_r0033_smul_tau_2(term, ctx))
    results.extend(_r0034_smul_tau_3(term, ctx))
    results.extend(_r0035_cyclesMap_smul(term, ctx))
    results.extend(_r0036_moduleCat_exact_iff(term, ctx))
    results.extend(_r0037_moduleCatLeftHomologyData_descH_hom(term, ctx))
    results.extend(_r0038_add_tau_2(term, ctx))
    results.extend(_r0039_add_tau_3(term, ctx))
    results.extend(_r0040_sub_tau_1(term, ctx))
    results.extend(_r0041_sub_tau_2(term, ctx))
    results.extend(_r0042_sub_tau_3(term, ctx))
    results.extend(_r0043_neg_tau_1(term, ctx))
    results.extend(_r0044_neg_tau_2(term, ctx))
    results.extend(_r0045_neg_tau_3(term, ctx))
    results.extend(_r0046_cyclesMap_neg(term, ctx))
    results.extend(_r0047_leftHomologyMap_add(term, ctx))
    results.extend(_r0048_cyclesMap_add(term, ctx))
    results.extend(_r0049_leftHomologyMap_sub(term, ctx))
    results.extend(_r0050_cyclesMap_sub(term, ctx))
    results.extend(_r0051_i_descQ_eq_zero_of_boundary(term, ctx))
    results.extend(_r0052_p_fromOpcycles(term, ctx))
    results.extend(_r0053_opcyclesIsoX_2_hom_inv_id(term, ctx))
    results.extend(_r0054_w_0_2_tau_2(term, ctx))
    results.extend(_r0055_w_0_2_tau_3(term, ctx))
    results.extend(_r0056_w_1_3_tau_1(term, ctx))
    results.extend(_r0057_w_1_3_tau_2(term, ctx))
    results.extend(_r0058_w_1_3_tau_3(term, ctx))
    results.extend(_r0059_L_0X_2ToP_comp_pullback_snd(term, ctx))
    results.extend(_r0060_id_f_1(term, ctx))
    results.extend(_r0061_id_f_2(term, ctx))
    results.extend(_r0062_id_f_3(term, ctx))
    results.extend(_r0063_comp_f_1(term, ctx))
    results.extend(_r0064_comp_f_2(term, ctx))
    results.extend(_r0065_comp_f_3(term, ctx))
    results.extend(_r0066_equivalence_inverse(term, ctx))
    results.extend(_r0067_whiskering_obj_obj_d(term, ctx))
    results.extend(_r0068_whiskering_obj_obj_sig(term, ctx))
    results.extend(_r0069_nerveMap_app_mk_0(term, ctx))
    results.extend(_r0070_edgeMk_id(term, ctx))
    results.extend(_r0071_i_snd(term, ctx))
    results.extend(_r0072_inr_phi_fst(term, ctx))
    results.extend(_r0073_phi_snd(term, ctx))
    results.extend(_r0074_inr_pi(term, ctx))
    results.extend(_r0075_i_phi(term, ctx))
    results.extend(_r0076_homotopyEquiv_inv_i(term, ctx))
    results.extend(_r0077_leftDerivedToHomotopyCategory_comp(term, ctx))
    results.extend(_r0078_leftDerivedZeroIsoSelf_hom_inv_id(term, ctx))
    results.extend(_r0079_pi_op(term, ctx))
    results.extend(_r0080_i_unop(term, ctx))
    results.extend(_r0081_homotopyEquiv_inv_pi(term, ctx))
    results.extend(_r0082_rightDerivedToHomotopyCategory_comp(term, ctx))
    results.extend(_r0083_rightDerivedZeroIsoSelf_hom_inv_id(term, ctx))
    results.extend(_r0084_pi_obj(term, ctx))
    results.extend(_r0085_back_coe(term, ctx))
    results.extend(_r0086_comp_val(term, ctx))
    results.extend(_r0087_functor_eta(term, ctx))
    results.extend(_r0088_functor_mu(term, ctx))
    results.extend(_r0089_functor_d(term, ctx))
    results.extend(_r0090_mapAction_mu_hom(term, ctx))
    results.extend(_r0091_mapAction_d_hom(term, ctx))
    results.extend(_r0092_homAddEquiv_symm_apply(term, ctx))
    results.extend(_r0093_homAddEquiv_zero(term, ctx))
    results.extend(_r0094_homAddEquiv_add(term, ctx))
    results.extend(_r0095_homAddEquiv_symm_zero(term, ctx))
    results.extend(_r0096_homAddEquiv_symm_add(term, ctx))
    results.extend(_r0097_homEquiv_naturality_left_symm(term, ctx))
    results.extend(_r0098_right_triangle(term, ctx))
    results.extend(_r0099_counit_naturality(term, ctx))
    results.extend(_r0100_conjugateEquiv_leftAdjointIdIso_hom(term, ctx))
    results.extend(_r0101_op_rightTriple(term, ctx))
    results.extend(_r0102_comp_left_triangle_aux(term, ctx))
    results.extend(_r0103_rightZigzagIso_hom(term, ctx))
    results.extend(_r0104_leftZigzagIso_inv(term, ctx))
    results.extend(_r0105_rightZigzagIso_inv(term, ctx))
    results.extend(_r0106_leftZigzagIso_symm(term, ctx))
    results.extend(_r0107_rightZigzagIso_symm(term, ctx))
    results.extend(_r0108_mateEquiv_eq_iff(term, ctx))
    results.extend(_r0109_hom_inv_whiskerRight(term, ctx))
    results.extend(_r0110_whiskerLeft_inv_hom(term, ctx))
    results.extend(_r0111_inv_hom_whiskerRight(term, ctx))
    results.extend(_r0112_whiskerLeft_whiskerLeft_hom_inv(term, ctx))
    results.extend(_r0113_triangle_assoc_comp_right_inv(term, ctx))
    results.extend(_r0114_eqToHom_hComp_eqToHom(term, ctx))
    results.extend(_r0115_preinclusion_map_2(term, ctx))
    results.extend(_r0116_mk_associator_hom(term, ctx))
    results.extend(_r0117_mk_associator_inv(term, ctx))
    results.extend(_r0118_mk_left_unitor_hom(term, ctx))
    results.extend(_r0119_mk_left_unitor_inv(term, ctx))
    results.extend(_r0120_mk_right_unitor_hom(term, ctx))
    results.extend(_r0121_mk_right_unitor_inv(term, ctx))
    results.extend(_r0122_map_comp_forget(term, ctx))
    results.extend(_r0123_uniqueUpToIso_inv_right(term, ctx))
    results.extend(_r0124_uniqueUpToIso_inv_right(term, ctx))
    results.extend(_r0125_comp_as(term, ctx))
    results.extend(_r0126_comp_of(term, ctx))
    results.extend(_r0127_comp_2_iso_inv(term, ctx))
    results.extend(_r0128_id_2_iso_hom(term, ctx))
    results.extend(_r0129_id_2_iso_inv(term, ctx))
    results.extend(_r0130_comul_counit(term, ctx))
    results.extend(_r0131_comul_assoc(term, ctx))
    results.extend(_r0132_comul_assoc_flip(term, ctx))
    results.extend(_r0133_toLax(term, ctx))
    results.extend(_r0134_unop2_op2(term, ctx))
    results.extend(_r0135_iso_hom_naturality(term, ctx))
    results.extend(_r0136_toNatTrans_comp(term, ctx))
    results.extend(_r0137_ext(term, ctx))
    results.extend(_r0138_toNatIso_isoMk(term, ctx))
    results.extend(_r0139_id_obj(term, ctx))
    results.extend(_r0140_id_map(term, ctx))
    results.extend(_r0141_comp_toFunctor(term, ctx))
    results.extend(_r0142_comp_obj(term, ctx))
    results.extend(_r0143_eqToHom_toNatTrans(term, ctx))
    results.extend(_r0144_eqToHom_app(term, ctx))
    results.extend(_r0145_whiskerLeft_app(term, ctx))
    results.extend(_r0146_whiskerRight_toNatTrans(term, ctx))
    results.extend(_r0147_whiskerRight_app(term, ctx))
    results.extend(_r0148_toNatIso_leftUnitor(term, ctx))
    results.extend(_r0149_leftUnitor_hom_toNatTrans(term, ctx))
    results.extend(_r0150_leftUnitor_inv_toNatTrans(term, ctx))
    results.extend(_r0151_leftUnitor_hom_app(term, ctx))
    results.extend(_r0152_rightUnitor_hom_toNatTrans(term, ctx))
    results.extend(_r0153_rightUnitor_inv_toNatTrans(term, ctx))
    results.extend(_r0154_rightUnitor_hom_app(term, ctx))
    results.extend(_r0155_coe_of(term, ctx))
    results.extend(_r0156_comp_def(term, ctx))
    results.extend(_r0157_homOfLE_comp(term, ctx))
    results.extend(_r0158_toOrderIso_symm_apply(term, ctx))
    results.extend(_r0159_of_toQuivHom(term, ctx))
    results.extend(_r0160_freeMap_id(term, ctx))
    results.extend(_r0161_hom_obj_inv_obj_of_iso(term, ctx))
    results.extend(_r0162_hom_map_inv_map_of_iso(term, ctx))
    results.extend(_r0163_id_map(term, ctx))
    results.extend(_r0164_comp_obj(term, ctx))
    results.extend(_r0165_comp_map(term, ctx))
    results.extend(_r0166_quotientFunctor_map_nil(term, ctx))
    results.extend(_r0167_lift_map(term, ctx))
    results.extend(_r0168_rel_comp(term, ctx))
    results.extend(_r0169_rel_id_apply_2(term, ctx))
    results.extend(_r0170_unopFunctor_comp_opFunctor_eq(term, ctx))
    results.extend(_r0171_objUp_objDown(term, ctx))
    results.extend(_r0172_app_sub(term, ctx))
    results.extend(_r0173_app_neg(term, ctx))
    results.extend(_r0174_fac_right(term, ctx))
    results.extend(_r0175_id_right(term, ctx))
    results.extend(_r0176_comp_left(term, ctx))
    results.extend(_r0177_comp_right(term, ctx))
    results.extend(_r0178_w(term, ctx))
    results.extend(_r0179_inv_right(term, ctx))
    results.extend(_r0180_left_hom_inv_right(term, ctx))
    results.extend(_r0181_inv_hom_id_left(term, ctx))
    results.extend(_r0182_hom_inv_id_right(term, ctx))
    results.extend(_r0183_inv_hom_id_right(term, ctx))
    results.extend(_r0184_id_right(term, ctx))
    results.extend(_r0185_comp_left(term, ctx))
    results.extend(_r0186_comp_right(term, ctx))
    results.extend(_r0187_eqToHom_left(term, ctx))
    results.extend(_r0188_id_left(term, ctx))
    results.extend(_r0189_comp_left(term, ctx))
    results.extend(_r0190_w(term, ctx))
    results.extend(_r0191_homMk_eta(term, ctx))
    results.extend(_r0192_forget_map(term, ctx))
    results.extend(_r0193_map_obj_hom(term, ctx))
    results.extend(_r0194_map_map_left(term, ctx))
    results.extend(_r0195_mapIso_inverse(term, ctx))
    results.extend(_r0196_asOverHom_comp(term, ctx))
    results.extend(_r0197_asOverHom_inv(term, ctx))
    results.extend(_r0198_forgetAdjStar_unit_app_left(term, ctx))
    results.extend(_r0199_mk_snd(term, ctx))
    results.extend(_r0200_map_1_comp(term, ctx))
    results.extend(_r0201_map_2_comp(term, ctx))
    results.extend(_r0202_mk_right(term, ctx))
    results.extend(_r0203_mk_hom_eq_self(term, ctx))
    results.extend(_r0204_w(term, ctx))
    results.extend(_r0205_comp_right(term, ctx))
    results.extend(_r0206_id_right(term, ctx))
    results.extend(_r0207_eqToHom_right(term, ctx))
    results.extend(_r0208_mk_surjective(term, ctx))
    results.extend(_r0209_map_mk(term, ctx))
    results.extend(_r0210_map_id(term, ctx))
    results.extend(_r0211_obj_one(term, ctx))
    results.extend(_r0212_obj_succ(term, ctx))
    results.extend(_r0213_map_one_one(term, ctx))
    results.extend(_r0214_map_zero_one(term, ctx))
    results.extend(_r0215_map_zero_succ_succ(term, ctx))
    results.extend(_r0216_map_succ_succ(term, ctx))
    results.extend(_r0217_map_id(term, ctx))
    results.extend(_r0218_homMkSucc_app_succ(term, ctx))
    results.extend(_r0219_homMk_2_app_one(term, ctx))
    results.extend(_r0220_homMk_2_app_two(term, ctx))
    results.extend(_r0221_homMk_3_app_one(term, ctx))
    results.extend(_r0222_homMk_4_app_one(term, ctx))
    results.extend(_r0223_homMk_5_app_one(term, ctx))
    results.extend(_r0224_mkOfObjOfMapSucc_map_succ(term, ctx))
    results.extend(_r0225_fourd_4Tod_3_app_one(term, ctx))
    results.extend(_r0226_fourd_4Tod_3_app_two(term, ctx))
    results.extend(_r0227_fourd_4Tod_3_app_three(term, ctx))
    results.extend(_r0228_fourd_3Tod_2_app_zero(term, ctx))
    results.extend(_r0229_fourd_3Tod_2_app_one(term, ctx))
    results.extend(_r0230_fourd_3Tod_2_app_two(term, ctx))
    results.extend(_r0231_fourd_3Tod_2_app_three(term, ctx))
    results.extend(_r0232_fourd_2Tod_1_app_zero(term, ctx))
    results.extend(_r0233_fourd_2Tod_1_app_one(term, ctx))
    results.extend(_r0234_fourd_2Tod_1_app_two(term, ctx))
    results.extend(_r0235_fourd_2Tod_1_app_three(term, ctx))
    results.extend(_r0236_fourd_1Tod_0_app_zero(term, ctx))
    results.extend(_r0237_fourd_1Tod_0_app_one(term, ctx))
    results.extend(_r0238_fourd_1Tod_0_app_two(term, ctx))
    results.extend(_r0239_fourd_1Tod_0_app_three(term, ctx))
    results.extend(_r0240_threed_3Tod_2_app_one(term, ctx))
    results.extend(_r0241_threed_3Tod_2_app_two(term, ctx))
    results.extend(_r0242_threed_2Tod_1_app_zero(term, ctx))
    results.extend(_r0243_threed_2Tod_1_app_one(term, ctx))
    results.extend(_r0244_threed_2Tod_1_app_two(term, ctx))
    results.extend(_r0245_threed_1Tod_0_app_zero(term, ctx))
    results.extend(_r0246_threed_1Tod_0_app_one(term, ctx))
    results.extend(_r0247_threed_1Tod_0_app_two(term, ctx))
    results.extend(_r0248_twod_2Tod_1_app_one(term, ctx))
    results.extend(_r0249_twod_1Tod_0_app_zero(term, ctx))
    results.extend(_r0250_twod_1Tod_0_app_one(term, ctx))
    results.extend(_r0251_comp_apply(term, ctx))
    results.extend(_r0252_naturality_apply(term, ctx))
    results.extend(_r0253_conj_id(term, ctx))
    results.extend(_r0254_refl_conj(term, ctx))
    results.extend(_r0255_trans_conj(term, ctx))
    results.extend(_r0256_symm_self_conj(term, ctx))
    results.extend(_r0257_self_symm_conj(term, ctx))
    results.extend(_r0258_conj_pow(term, ctx))
    results.extend(_r0259_trans_conjAut(term, ctx))
    results.extend(_r0260_conjAut_trans(term, ctx))
    results.extend(_r0261_conjAut_pow(term, ctx))
    results.extend(_r0262_conjAut_zpow(term, ctx))
    results.extend(_r0263_inclusion_comp_decomposedTo(term, ctx))
    results.extend(_r0264_coreId(term, ctx))
    results.extend(_r0265_coreWhiskerLeft(term, ctx))
    results.extend(_r0266_comp_f(term, ctx))
    results.extend(_r0267_isoApp_symm(term, ctx))
    results.extend(_r0268_isoApp_trans(term, ctx))
    results.extend(_r0269_map_snd(term, ctx))
    results.extend(_r0270_fromStructuredArrow_map(term, ctx))
    results.extend(_r0271_id_f(term, ctx))
    results.extend(_r0272_comp_f(term, ctx))
    results.extend(_r0273_id_f(term, ctx))
    results.extend(_r0274_comp_f(term, ctx))
    results.extend(_r0275_ext(term, ctx))
    results.extend(_r0276_of_to(term, ctx))
    results.extend(_r0277_eHomEquiv_comp(term, ctx))
    results.extend(_r0278_eHomWhiskerRight_comp(term, ctx))
    results.extend(_r0279_eHomWhiskerLeft_comp(term, ctx))
    results.extend(_r0280_inv(term, ctx))
    results.extend(_r0281_eqToIso_refl(term, ctx))
    results.extend(_r0282_eqToIso_trans(term, ctx))
    results.extend(_r0283_eqToHom_op(term, ctx))
    results.extend(_r0284_comp_asNatTrans(term, ctx))
    results.extend(_r0285_mkHom_comp(term, ctx))
    results.extend(_r0286_essImage_i_comp(term, ctx))
    results.extend(_r0287_from_to(term, ctx))
    results.extend(_r0288_id_comp(term, ctx))
    results.extend(_r0289_comp_assoc(term, ctx))
    results.extend(_r0290_inducedFunctor_comp(term, ctx))
    results.extend(_r0291_inducedFunctor_comp_map(term, ctx))
    results.extend(_r0292_id_map(term, ctx))
    results.extend(_r0293_congr_map(term, ctx))
    results.extend(_r0294_toPrefunctor_injective(term, ctx))
    results.extend(_r0295_comp_app(term, ctx))
    results.extend(_r0296_app_naturality(term, ctx))
    results.extend(_r0297_opObjUnop_inv_app(term, ctx))
    results.extend(_r0298_unop_functor_op_obj_map(term, ctx))
    results.extend(_r0299_comp_flip_uncurry_eq(term, ctx))
    results.extend(_r0300_curry_obj_comp_flip(term, ctx))
    results.extend(_r0301_preimage_comp(term, ctx))
    results.extend(_r0302_ext(term, ctx))
    results.extend(_r0303_autMap_comp(term, ctx))
    results.extend(_r0304_toAutHomeo_apply(term, ctx))
    results.extend(_r0305_comp_val(term, ctx))
    results.extend(_r0306_incl_map(term, ctx))
    results.extend(_r0307_diagram_snd(term, ctx))
    results.extend(_r0308_diagram_left(term, ctx))
    results.extend(_r0309_diagram_right(term, ctx))
    results.extend(_r0310_hom_ext(term, ctx))
    results.extend(_r0311_fiber_eqToHom(term, ctx))
    results.extend(_r0312_eqToHom_eq(term, ctx))
    results.extend(_r0313_lift_map_homMk(term, ctx))
    results.extend(_r0314_mapId_inv_app(term, ctx))
    results.extend(_r0315_mapComp_inv_app(term, ctx))
    results.extend(_r0316_map_comp(term, ctx))
    results.extend(_r0317_map_map_homMk(term, ctx))
    results.extend(_r0318_mapCompLift_inv_app(term, ctx))
    results.extend(_r0319_app_comp_p(term, ctx))
    results.extend(_r0320_app_p_comm(term, ctx))
    results.extend(_r0321_karoubiUniversal_2_functor_eq(term, ctx))
    results.extend(_r0322_karoubiUniversal_functor_eq(term, ctx))
    results.extend(_r0323_comp_p_d(term, ctx))
    results.extend(_r0324_p_comm_f(term, ctx))
    results.extend(_r0325_comp_p(term, ctx))
    results.extend(_r0326_p_comm(term, ctx))
    results.extend(_r0327_id_f(term, ctx))
    results.extend(_r0328_eqToHom_f(term, ctx))
    results.extend(_r0329_p_comm_f(term, ctx))
    results.extend(_r0330_symm_mk(term, ctx))
    results.extend(_r0331_trans_assoc(term, ctx))
    results.extend(_r0332_trans_refl(term, ctx))
    results.extend(_r0333_symm_self_id(term, ctx))
    results.extend(_r0334_self_symm_id(term, ctx))
    results.extend(_r0335_symm_self_id_assoc(term, ctx))
    results.extend(_r0336_self_symm_id_assoc(term, ctx))
    results.extend(_r0337_inv_comp_eq(term, ctx))
    results.extend(_r0338_asIso_inv(term, ctx))
    results.extend(_r0339_eq_inv_comp(term, ctx))
    results.extend(_r0340_map_inv_hom_id(term, ctx))
    results.extend(_r0341_mapIso_trans(term, ctx))
    results.extend(_r0342_fromSum_map_inl(term, ctx))
    results.extend(_r0343_isoMap_inv_hom_id(term, ctx))
    results.extend(_r0344_isoMap_inv_hom_id(term, ctx))
    results.extend(_r0345_pullbackZeroZeroIso_hom_snd(term, ctx))
    results.extend(_r0346_inr_pushoutZeroZeroIso_inv(term, ctx))
    results.extend(_r0347_forget_obj(term, ctx))
    results.extend(_r0348_forget_obj(term, ctx))
    results.extend(_r0349_forget_map(term, ctx))
    results.extend(_r0350_cofan_inj_f_snd(term, ctx))
    results.extend(_r0351_cofan_inj_phi(term, ctx))
    results.extend(_r0352_i_comp_coproductIsoSelf_hom(term, ctx))
    results.extend(_r0353_fromIncl_comp_coproductIsoSelf_inv(term, ctx))
    results.extend(_r0354_cone_pi(term, ctx))
    results.extend(_r0355_w(term, ctx))
    results.extend(_r0356_uniq_cone_morphism(term, ctx))
    results.extend(_r0357_iso_inv_fst(term, ctx))
    results.extend(_r0358_toCone_pi_app_left(term, ctx))
    results.extend(_r0359_toCone_pi_app_right(term, ctx))
    results.extend(_r0360_binary_fan_fst_toCone(term, ctx))
    results.extend(_r0361_binary_fan_snd_toCone(term, ctx))
    results.extend(_r0362_toCocone_i_app_left(term, ctx))
    results.extend(_r0363_toCocone_i_app_right(term, ctx))
    results.extend(_r0364_binary_cofan_inl_toCocone(term, ctx))
    results.extend(_r0365_binary_cofan_inr_toCocone(term, ctx))
    results.extend(_r0366_swap_apply_right(term, ctx))
    results.extend(_r0367_swap_symm_apply_tt(term, ctx))
    results.extend(_r0368_swap_symm_apply_ff(term, ctx))
    results.extend(_r0369_equivBool_apply_right(term, ctx))
    results.extend(_r0370_equivBool_symm_apply_true(term, ctx))
    results.extend(_r0371_equivBool_symm_apply_false(term, ctx))
    results.extend(_r0372_pairFunction_right(term, ctx))
    results.extend(_r0373_pair_obj_right(term, ctx))
    results.extend(_r0374_mapPair_right(term, ctx))
    results.extend(_r0375_unop_mk(term, ctx))
    results.extend(_r0376_op_mk(term, ctx))
    results.extend(_r0377_unop_mk(term, ctx))
    results.extend(_r0378_bicone_i_pi_ne(term, ctx))
    results.extend(_r0379_toCone_pi_app(term, ctx))
    results.extend(_r0380_toCone_pi_app_mk(term, ctx))
    results.extend(_r0381_toCone_proj(term, ctx))
    results.extend(_r0382_toCocone_i_app(term, ctx))
    results.extend(_r0383_toCocone_inj(term, ctx))
    results.extend(_r0384_toCocone_i_app_mk(term, ctx))
    results.extend(_r0385_diagonal_snd(term, ctx))
    results.extend(_r0386_mk_i(term, ctx))
    results.extend(_r0387_mk_pi(term, ctx))
    results.extend(_r0388_walkingParallelPairOp_one(term, ctx))
    results.extend(_r0389_walkingParallelPairOp_left(term, ctx))
    results.extend(_r0390_walkingParallelPairOp_right(term, ctx))
    results.extend(_r0391_walkingParallelPairOpEquiv_unitIso_one(term, ctx))
    results.extend(_r0392_walkingParallelPairOpEquiv_counitIso_zer(term, ctx))
    results.extend(_r0393_walkingParallelPairOpEquiv_counitIso_one(term, ctx))
    results.extend(_r0394_walkingParallelPairOpEquiv_unitIso_hom_a(term, ctx))
    results.extend(_r0395_walkingParallelPairOpEquiv_unitIso_inv_a(term, ctx))
    results.extend(_r0396_walkingParallelPairOpEquiv_unitIso_inv_a(term, ctx))
    results.extend(_r0397_walkingParallelPairOpEquiv_counitIso_hom(term, ctx))
    results.extend(_r0398_walkingParallelPairOpEquiv_counitIso_hom(term, ctx))
    results.extend(_r0399_walkingParallelPairOpEquiv_counitIso_inv(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_category rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("CategoryTheory_Iso_toBialgEquiv_toBialgHom", "i_toBialgEquiv_colon_X_to_c_R_Y_eq_i_hom_1", "Not an equality or iff proposition"),
    ("CategoryTheory_Iso_toHopfAlgEquiv_toBialgHom", "i_toHopfAlgEquiv_colon_X_to_c_R_Y_eq_i_hom_1", "Not an equality or iff proposition"),
    ("CategoryTheory_isCompatible_map_smul", "r_0_smul_m_0_map_whiskerRight_phi_forget_Compatible", "Not an equality or iff proposition"),
    ("CategoryTheory_Limits_IsColimit_i_smul", "letI", "Not an equality or iff proposition"),
    ("CategoryTheory_Iso_semiRingCatIsoToRingEquiv_toRingHom", "e_semiRingCatIsoToRingEquiv_colon_R_to_plus_star_S_eq_e_hom_hom", "Not an equality or iff proposition"),
    ("CategoryTheory_Iso_ringCatIsoToRingEquiv_toRingHom", "e_ringCatIsoToRingEquiv_colon_R_to_plus_star_S_eq_e_hom_hom", "Not an equality or iff proposition"),
    ("CategoryTheory_Iso_commSemiRingCatIsoToRingEquiv_toRingHom", "e_commSemiRingCatIsoToRingEquiv_colon_R_to_plus_star_S_eq_e_hom_hom", "Not an equality or iff proposition"),
    ("CategoryTheory_Iso_commRingCatIsoToRingEquiv_toRingHom", "e_commRingCatIsoToRingEquiv_colon_R_to_plus_star_S_eq_e_hom_hom", "Not an equality or iff proposition"),
    ("CategoryTheory_IsPushout_epi_shortComplex_g", "Epi_h_shortComplex_g", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_d_apply", "_unknown", "Empty proposition"),
    ("CategoryTheory_hasExt_of_hasDerivedCategory", "HasExt_w_C", "Not an equality or iff proposition"),
    ("CategoryTheory_HasExt_standard", "HasExt_max_u_v_C", "Not an equality or iff proposition"),
    ("CategoryTheory_Abelian_mk_0_bijective", "Function_Bijective_mk_0_X_colon_eq_X_Y_colon_eq_Y", "Not an equality or iff proposition"),
    ("CategoryTheory_Abelian_add_hom", "_unknown", "Empty proposition"),
    ("CategoryTheory_Abelian_neg_hom", "_unknown", "Empty proposition"),
    ("CategoryTheory_Abelian_zero_hom", "_unknown", "Empty proposition"),
    ("CategoryTheory_Abelian_Ext_subsingleton_of_injective", "Subsingleton_Ext_w_X_I_n_plus_1", "Not an equality or iff proposition"),
    ("CategoryTheory_hasExt_of_enoughInjectives", "HasExt_w_C", "Not an equality or iff proposition"),
    ("CategoryTheory_Abelian_Ext_subsingleton_of_projective", "Subsingleton_Ext_w_P_Y_n_plus_1", "Not an equality or iff proposition"),
    ("CategoryTheory_hasExt_of_enoughProjectives", "HasExt_w_C", "Not an equality or iff proposition"),
    ("CategoryTheory_Abelian_Ext_covariant_sequence_exact_2", "_unknown", "Empty proposition"),
    ("CategoryTheory_Abelian_Ext_covariant_sequence_exact_3", "_unknown", "Empty proposition"),
    ("CategoryTheory_Abelian_Ext_covariant_sequence_exact_1", "_unknown", "Empty proposition"),
    ("CategoryTheory_Abelian_Ext_covariantSequence_exact", "covariantSequence_X_hS_n_0_n_1_h_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_Abelian_postcomp_mk_0_injective_of_mono", "Function_Injective_Ext_mk_0_f_postcomp_L_add_zero_0", "Not an equality or iff proposition"),
    ("CategoryTheory_Abelian_mono_postcomp_mk_0_of_mono", "Mono_AddCommGrpCat_ofHom_lt_pipe_Ext_mk_0_f_postcomp_L_add_zero_0", "Not an equality or iff proposition"),
    ("CategoryTheory_contravariant_sequence_exact_2", "_unknown", "Empty proposition"),
    ("CategoryTheory_contravariant_sequence_exact_1", "_unknown", "Empty proposition"),
    ("CategoryTheory_contravariant_sequence_exact_3", "_unknown", "Empty proposition"),
    ("CategoryTheory_contravariantSequence_exact", "contravariantSequence_hS_Y_n_0_n_1_h_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_hasSmallLocalizedHom_S", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_hasSmallLocalizedShiftedHom_K_S", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_mapShiftedHom_singled", "_unknown", "Empty proposition"),
    ("CategoryTheory_HasExt_hasSmallLocalizedShiftedHom_of_isLE_of_isGE", "HasSmallLocalizedShiftedHom_w_HomologicalComplex_quasiIso_C_ComplexSha", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_singleTriangle_distinguished", "hS_singleTriangle_in_distTriang_DerivedCategory_C", "Not an equality or iff proposition"),
    ("CategoryTheory_DifferentialObject_eqToHom_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_ComposableArrows_IsComplex_zero", "_unknown", "Empty proposition"),
    ("CategoryTheory_ComposableArrows_isComplex_of_iso", "S_2_IsComplex", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_isComplex_0", "S_IsComplex", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_isComplex_1", "S_IsComplex", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_Exact_exact", "_unknown", "Empty proposition"),
    ("CategoryTheory_ComposableArrows_exact_of_iso", "S_2_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_exact_0", "S_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_exact_1", "S_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_isComplex_2_mk", "S_IsComplex", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_isComplex_toComposableArrows", "S_toComposableArrows_IsComplex", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_exact_2_mk", "S_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_Exact_exact_toComposableArrows", "S_toComposableArrows_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_Exact_d_0", "S_d_0_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_exact_of_d_0", "S_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_Exact_dlast", "S_dlast_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_exact_of_dlast", "S_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ComposableArrows_Exact_isIso_map", "_unknown", "Empty proposition"),
    ("CategoryTheory_ComposableArrows_IsComplex_cokerToKer", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_homology_exact_1", "ShortComplex_mk_d_comp_hS_i_j_hij_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_homology_exact_2", "ShortComplex_mk_HomologicalComplex_homologyMap_S_f_i_HomologicalComplex", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_homology_exact_3", "ShortComplex_mk_comp_d_hS_i_j_hij_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_d_eq", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_mono_d", "Mono_hS_d_i_j_hij", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_epi_d", "Epi_hS_d_i_j_hij", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_isIso_d", "IsIso_hS_d_i_j_hij", "Not an equality or iff proposition"),
    ("CategoryTheory_Abelian_LeftResolution_exactAt_map_chainComplex_succ", "i_mapHomologicalComplex_obj_chainComplex_X_ExactAt_n_plus_1", "Not an equality or iff proposition"),
    ("CategoryTheory_Functor_mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso", "HomologicalComplex_quasiIso_C_c_IsInvertedBy_F_mapHomologicalComplex_c", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_abLeftHomologyData_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_Exact_ab_finite", "Finite_S_X_2", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_ab_injective_f", "Function_Injective_S_f", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_ab_surjective_g", "Function_Surjective_S_g", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_HomologyData_ofEpiMonoFactorisation_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_HomologyData_ofEpiMonoFactorisation_g", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_isIso_of_isIso", "IsIso_f", "Not an equality or iff proposition"),
    ("CategoryTheory_Preadditive_mono_iff_injective", "_unknown", "Empty proposition"),
    ("CategoryTheory_Preadditive_epi_iff_surjective", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_Exact_hasHomology", "S_HasHomology", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_Exact_hasZeroObject", "HasZeroObject_C", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_HomologyData_exact_iff", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_exact_of_iso", "S_2_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_exact_of_isZero_X_2", "S_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_Exact_op", "S_op_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_Exact_unop", "S_unop_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_Exact_map_of_preservesLeftHomologyOf", "S_map_F_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_Exact_map_of_preservesRightHomologyOf", "S_map_F_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_Exact_map", "S_map_F_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_Exact_isZero_of_both_zeros", "IsZero_S_X_2", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_epi_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_Exact_mono_g", "_unknown", "Empty proposition"),
    ("CategoryTheory_Exact_epi_toCycles", "Epi_S_toCycles", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_mono_fromOpcycles", "Mono_S_fromOpcycles", "Not an equality or iff proposition"),
    ("CategoryTheory_LeftHomologyData_exact_iff_epi_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_RightHomologyData_exact_iff_mono_g", "_unknown", "Empty proposition"),
    ("CategoryTheory_Exact_mono_cokernelDesc", "Mono_Limits_cokernel_desc_S_f_S_g_S_zero", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_epi_kernelLift", "Epi_Limits_kernel_lift_S_g_S_f_S_zero", "Not an equality or iff proposition"),
    ("CategoryTheory_exact_of_f_is_kernel", "S_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_exact_of_g_is_cokernel", "S_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_mono_g", "Mono_S_g", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_epi_f", "Epi_S_f", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_isZero_X_2", "IsZero_S_X_2", "Not an equality or iff proposition"),
    ("CategoryTheory_Splitting_isSplitMono_f", "IsSplitMono_S_f", "Not an equality or iff proposition"),
    ("CategoryTheory_Splitting_mono_f", "Mono_S_f", "Not an equality or iff proposition"),
    ("CategoryTheory_Splitting_isSplitEpi_g", "IsSplitEpi_S_g", "Not an equality or iff proposition"),
    ("CategoryTheory_Splitting_epi_g", "Epi_S_g", "Not an equality or iff proposition"),
    ("CategoryTheory_Splitting_exact", "S_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_isIso_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_Exact_isIso_toCycles", "IsIso_S_toCycles", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_isIso_g", "_unknown", "Empty proposition"),
    ("CategoryTheory_Exact_isIso_fromOpcycles", "IsIso_S_fromOpcycles", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_map_of_mono_of_preservesKernel", "S_map_F_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_map_of_epi_of_preservesCokernel", "S_map_F_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_Exact_lift", "_unknown", "Empty proposition"),
    ("CategoryTheory_Exact_desc", "_unknown", "Empty proposition"),
    ("CategoryTheory_mono_tau_2_of_exact_of_mono", "Mono_phi_tau_2", "Not an equality or iff proposition"),
    ("CategoryTheory_epi_tau_2_of_exact_of_epi", "Epi_phi_tau_2", "Not an equality or iff proposition"),
    ("CategoryTheory_Functor_preservesFiniteLimits_of_preservesHomology", "PreservesFiniteLimits_F", "Not an equality or iff proposition"),
    ("CategoryTheory_Functor_preservesFiniteColimits_of_preservesHomology", "PreservesFiniteColimits_F", "Not an equality or iff proposition"),
    ("CategoryTheory_preservesMonomorphisms_of_preserves_shortExact_left", "F_PreservesMonomorphisms", "Not an equality or iff proposition"),
    ("CategoryTheory_preservesFiniteLimits_tfae", "List_TFAE_forall_S_colon_ShortComplex_C_S_ShortExact_to_S_map_F_Exact_and_M", "Not an equality or iff proposition"),
    ("CategoryTheory_preservesEpimorphisms_of_preserves_shortExact_right", "F_PreservesEpimorphisms", "Not an equality or iff proposition"),
    ("CategoryTheory_preservesFiniteColimits_tfae", "List_TFAE_forall_S_colon_ShortComplex_C_S_ShortExact_to_S_map_F_Exact_and_E", "Not an equality or iff proposition"),
    ("CategoryTheory_exact_tfae", "List_TFAE_forall_S_colon_ShortComplex_C_S_ShortExact_to_S_map_F_ShortExac", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_HasHomology_mk", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_hasHomology_of_epi_of_isIso_of_mono", "HasHomology_S_2", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_hasHomology_of_epi_of_isIso_of_mono", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_hasHomology_of_iso", "HasHomology_S_2", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_HomologyMapData_homologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_HomologyMapData_cyclesMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_HomologyMapData_opcyclesMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_homologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_homologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_homologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_leftRightHomologyComparison", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_pi_leftRightHomologyComparison", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_leftRightHomologyComparison", "_unknown", "Empty proposition"),
    ("CategoryTheory_leftRightHomologyComparison", "_unknown", "Empty proposition"),
    ("CategoryTheory_leftRightHomologyComparison", "_unknown", "Empty proposition"),
    ("CategoryTheory_HomologyData_leftRightHomologyComparison", "_unknown", "Empty proposition"),
    ("CategoryTheory_leftRightHomologyComparison", "_unknown", "Empty proposition"),
    ("CategoryTheory_leftRightHomologyComparison", "_unknown", "Empty proposition"),
    ("CategoryTheory_hasHomology_of_isIso_leftRightHomologyComparison", "_unknown", "Empty proposition"),
    ("CategoryTheory_hasHomology_of_isIsoLeftRightHomologyComparison", "S_HasHomology", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_isIso_i", "IsIso_h_i", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_isIso_pi", "IsIso_h_pi", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_ofIsColimitCokernelCofork_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_ofIsLimitKernelFork_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_ofZeros_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_HasLeftHomology_mk", "_unknown", "Empty proposition"),
    ("CategoryTheory_isIso_iCycles", "IsIso_S_iCycles", "Not an equality or iff proposition"),
    ("CategoryTheory_isIso_leftHomologypi", "IsIso_S_leftHomologypi", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_leftHomologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_cyclesMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_moduleCat_injective_f", "Function_Injective_S_f", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_ShortExact_moduleCat_surjective_g", "Function_Surjective_S_g", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_Exact_moduleCat_of_range_eq_ker", "moduleCatMkOfKerLERange_f_g_by_rw_hfg_Exact", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_moduleCatLeftHomologyData_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_leftHomologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_cyclesMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_leftHomologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_cyclesMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_leftHomologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_cyclesMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_Functor_PreservesHomology_preservesKernel", "PreservesLimit_parallelPair_f_0_F", "Not an equality or iff proposition"),
    ("CategoryTheory_Functor_PreservesHomology_preservesCokernel", "PreservesColimit_parallelPair_f_0_F", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_IsPreservedBy_hg", "PreservesLimit_parallelPair_S_g_0_F", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_IsPreservedBy_hf", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_map_f", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_IsPreservedBy_hf", "PreservesColimit_parallelPair_S_f_0_F", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_IsPreservedBy_hg", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_map_g", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_map_leftRightHomologyComparison", "_unknown", "Empty proposition"),
    ("CategoryTheory_Functor_PreservesLeftHomologyOf_mk", "_unknown", "Empty proposition"),
    ("CategoryTheory_Functor_PreservesRightHomologyOf_mk", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_map_cyclesMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_LeftHomologyData_map_leftHomologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_map_opcyclesMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_map_rightHomologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_HomologyData_map_homologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_mapHomologyIso", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_mapHomologyIso", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_mapHomologyIso", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_mapHomologyIso", "_unknown", "Empty proposition"),
    ("Functor_preservesLeftHomology_of_zero_f", "F_PreservesLeftHomologyOf_S", "Not an equality or iff proposition"),
    ("Functor_preservesRightHomology_of_zero_g", "F_PreservesRightHomologyOf_S", "Not an equality or iff proposition"),
    ("Functor_preservesLeftHomology_of_zero_g", "F_PreservesLeftHomologyOf_S", "Not an equality or iff proposition"),
    ("Functor_preservesRightHomology_of_zero_f", "F_PreservesRightHomologyOf_S", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_quasiIso_of_comp_left", "QuasiIso_phi_prime", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_quasiIso_of_comp_right", "QuasiIso_phi", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_quasiIso_of_arrow_mk_iso", "QuasiIso_phi_prime", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_quasiIso_iff_isIso_leftHomologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_quasiIso_iff_isIso_rightHomologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_quasiIso_iff_isIso_homologyMap", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_quasiIso_of_epi_of_isIso_of_mono", "QuasiIso_phi", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_quasiIso_opMap", "QuasiIso_opMap_phi", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_quasiIso_unopMap", "QuasiIso_unopMap_phi", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_quasiIso_of_retract", "QuasiIso_f_1", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_p_g", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_i_g", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_isIso_p", "IsIso_h_p", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_isIso_i", "IsIso_h_i", "Not an equality or iff proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_ofIsLimitKernelFork_g", "_unknown", "Empty proposition"),
    ("CategoryTheory_ShortComplex_RightHomologyData_ofIsColimitCokernelCofork_g", "_unknown", "Empty proposition"),
]
