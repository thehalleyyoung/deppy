"""Mathlib: Topology — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 2242 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_topology"
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

def _r0000_hom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.hom_comp
    # (f ≫ g).hom = g.hom.comp f.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g_hom_comp", (OVar("f_hom"),))
            results.append((rhs, "Mathlib: TopModuleCat_hom_comp"))
    except Exception:
        pass
    return results


def _r0001_hom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.hom_id
    # hom (𝟙 X) = .id _ _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hom", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("_unknown"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: TopModuleCat_hom_id"))
        except Exception:
            pass
    return results


def _r0002_hom_zero_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.hom_zero_apply
    # (0 : M₁ ⟶ M₂).hom m = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_M_1_M_2_hom", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: TopModuleCat_hom_zero_apply"))
        except Exception:
            pass
    return results


def _r0003_hom_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.hom_add
    # (φ₁ + φ₂).hom = φ₁.hom + φ₂.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_1_plus_phi_2_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("phi_1_hom"), OVar("phi_2_hom")))
            results.append((rhs, "Mathlib: TopModuleCat_hom_add"))
    except Exception:
        pass
    return results


def _r0004_hom_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.hom_neg
    # (-φ).hom = -φ.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_phi_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_phi_hom")
            results.append((rhs, "Mathlib: TopModuleCat_hom_neg"))
    except Exception:
        pass
    return results


def _r0005_hom_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.hom_sub
    # (φ₁ - φ₂).hom = φ₁.hom - φ₂.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_1_minus_phi_2_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("phi_1_hom"), OVar("phi_2_hom")))
            results.append((rhs, "Mathlib: TopModuleCat_hom_sub"))
    except Exception:
        pass
    return results


def _r0006_hom_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.hom_nsmul
    # (n • φ).hom = n • φ.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_phi_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n", (OVar("_unknown"), OVar("phi_hom"),))
            results.append((rhs, "Mathlib: TopModuleCat_hom_nsmul"))
    except Exception:
        pass
    return results


def _r0007_hom_zsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.hom_zsmul
    # (n • φ).hom = n • φ.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_phi_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n", (OVar("_unknown"), OVar("phi_hom"),))
            results.append((rhs, "Mathlib: TopModuleCat_hom_zsmul"))
    except Exception:
        pass
    return results


def _r0008_forget_2_TopCat_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: forget₂_TopCat_obj
    # ((forget₂ _ TopCat).obj X : Type _) = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_2_TopCat_obj", 4)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: forget_2_TopCat_obj"))
        except Exception:
            pass
    return results


def _r0009_keri_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.kerι_apply
    # kerι φ x = x.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "keri", 2)
    if args is not None:
        try:
            rhs = OVar("x_1")
            results.append((rhs, "Mathlib: TopModuleCat_keri_apply"))
        except Exception:
            pass
    return results


def _r0010_lift_uniq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.lift_uniq
    # l = lift f g H'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("lift", (OVar("f"), OVar("g"), OVar("H_prime"),))
            results.append((rhs, "Mathlib: IsOpenImmersion_lift_uniq"))
    except Exception:
        pass
    return results


def _r0011_toNNReal_add_add_neg_add_neg_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.toNNReal_add_add_neg_add_neg_eq
    # (f + g).toNNReal + (-f).toNNReal + (-g).toNNReal =       (-(f + g)).toNNReal + f.toNNReal + g.toNNReal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("minus_f_plus_g_toNNReal"), OOp("+", (OVar("f_toNNReal"), OVar("g_toNNReal")))))
            results.append((rhs, "Mathlib: ContinuousMap_toNNReal_add_add_neg_add_neg_eq"))
        except Exception:
            pass
    return results


def _r0012_toNNReal_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.toNNReal_one
    # (1 : C(X, ℝ)).toNNReal = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_C_X_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ContinuousMap_toNNReal_one"))
    except Exception:
        pass
    return results


def _r0013_toNNReal_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.toNNReal_neg_one
    # (-1 : C(X, ℝ)).toNNReal = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_1_colon_C_X_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousMap_toNNReal_neg_one"))
    except Exception:
        pass
    return results


def _r0014_toNNReal_mul_add_neg_mul_add_mul_neg_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMapZero.toNNReal_mul_add_neg_mul_add_mul_neg_eq
    # ((f * g).toNNReal + (-f).toNNReal * g.toNNReal + f.toNNReal * (-g).toNNReal) =     ((-(f * g)).toNNReal + f.toNNReal * g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("minus_f_star_g_toNNReal"), OOp("+", (OOp("*", (OVar("f_toNNReal"), OVar("g_toNNReal"))), OOp("*", (OVar("minus_f_toNNReal"), OVar("minus_g_toNNReal")))))))
            results.append((rhs, "Mathlib: ContinuousMapZero_toNNReal_mul_add_neg_mul_add_mul_neg_eq"))
        except Exception:
            pass
    return results


def _r0015_derivWithin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.derivWithin
    # derivWithin e s x = e 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "derivWithin", 3)
    if args is not None:
        try:
            rhs = OOp("e", (OLit(1),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_derivWithin"))
        except Exception:
            pass
    return results


def _r0016_fderivWithin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAffineMap.fderivWithin
    # fderivWithin 𝕜 f s x = f.contLinear
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderivWithin", 4)
    if args is not None:
        try:
            rhs = OVar("f_contLinear")
            results.append((rhs, "Mathlib: ContinuousAffineMap_fderivWithin"))
        except Exception:
            pass
    return results


def _r0017_fderivWithin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fderivWithin
    # fderivWithin 𝕜 f s x = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderivWithin", 4)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: ContinuousLinearMap_fderivWithin"))
        except Exception:
            pass
    return results


def _r0018_rankOne_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: InnerProductSpace.rankOne_comp
    # rankOne 𝕜 x y ∘L f = rankOne 𝕜 x (adjoint f y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rankOne", 5)
    if args is not None:
        try:
            rhs = OOp("rankOne", (args[0], args[1], OOp("adjoint", (args[4], args[2],)),))
            results.append((rhs, "Mathlib: InnerProductSpace_rankOne_comp"))
        except Exception:
            pass
    return results


def _r0019_rayleighQuotient_apply_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.rayleighQuotient_apply_zero
    # rayleighQuotient T 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rayleighQuotient", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousLinearMap_rayleighQuotient_apply_zero"))
        except Exception:
            pass
    return results


def _r0020_rayleighQuotient_neg_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.rayleighQuotient_neg_apply
    # rayleighQuotient (-T) x = -rayleighQuotient T x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rayleighQuotient", 2)
    if args is not None:
        try:
            rhs = OOp("minus_rayleighQuotient", (OVar("T"), args[1],))
            results.append((rhs, "Mathlib: ContinuousLinearMap_rayleighQuotient_neg_apply"))
        except Exception:
            pass
    return results


def _r0021_rayleighQuotient_apply_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.rayleighQuotient_apply_neg
    # rayleighQuotient T (-x) = rayleighQuotient T x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rayleighQuotient", 2)
    if args is not None:
        try:
            rhs = OOp("rayleighQuotient", (args[0], OVar("x"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_rayleighQuotient_apply_neg"))
        except Exception:
            pass
    return results


def _r0022_image_rayleigh_eq_image_rayleigh_sphere(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.image_rayleigh_eq_image_rayleigh_sphere
    # rayleighQuotient T '' {0}ᶜ = rayleighQuotient T '' sphere 0 r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rayleighQuotient", 3)
    if args is not None:
        try:
            rhs = OOp("rayleighQuotient", (args[0], args[1], OVar("sphere"), OLit(0), OVar("r"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_image_rayleigh_eq_image_rayleigh_sphere"))
        except Exception:
            pass
    return results


def _r0023_add_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMapWOT.add_apply
    # (f + g) x = f x + g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_plus_g", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: ContinuousLinearMapWOT_add_apply"))
        except Exception:
            pass
    return results


def _r0024_sub_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMapWOT.sub_apply
    # (f - g) x = f x - g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_minus_g", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: ContinuousLinearMapWOT_sub_apply"))
        except Exception:
            pass
    return results


def _r0025_neg_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMapWOT.neg_apply
    # (-f) x = -(f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_f", 1)
    if args is not None:
        try:
            rhs = OVar("minus_f_x")
            results.append((rhs, "Mathlib: ContinuousLinearMapWOT_neg_apply"))
        except Exception:
            pass
    return results


def _r0026_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMapWOT.smul_apply
    # (c • f) x = c • (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_f", 1)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: ContinuousLinearMapWOT_smul_apply"))
        except Exception:
            pass
    return results


def _r0027_nnnorm_toContinuousMultilinearMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlternatingMap.nnnorm_toContinuousMultilinearMap
    # ‖f.1‖₊ = ‖f‖₊
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousAlternatingMap_nnnorm_toContinuousMultilinearMap"))
    except Exception:
        pass
    return results


def _r0028_enorm_toContinuousMultilinearMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlternatingMap.enorm_toContinuousMultilinearMap
    # ‖f.1‖ₑ = ‖f‖ₑ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousAlternatingMap_enorm_toContinuousMultilinearMap"))
    except Exception:
        pass
    return results


def _r0029_nnnorm_ofSubsingleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlternatingMap.nnnorm_ofSubsingleton
    # ‖ofSubsingleton 𝕜 E F i f‖₊ = ‖f‖₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofSubsingleton", 5)
    if args is not None:
        try:
            rhs = args[4]
            results.append((rhs, "Mathlib: ContinuousAlternatingMap_nnnorm_ofSubsingleton"))
        except Exception:
            pass
    return results


def _r0030_nnnorm_constOfIsEmpty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlternatingMap.nnnorm_constOfIsEmpty
    # ‖constOfIsEmpty 𝕜 E ι x‖₊ = ‖x‖₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "constOfIsEmpty", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: ContinuousAlternatingMap_nnnorm_constOfIsEmpty"))
        except Exception:
            pass
    return results


def _r0031_curryLeft_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlternatingMap.curryLeft_apply_apply
    # curryLeft f x v = f (Matrix.vecCons x v)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "curryLeft", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("Matrix_vecCons", (args[1], args[2],)),))
            results.append((rhs, "Mathlib: ContinuousAlternatingMap_curryLeft_apply_apply"))
        except Exception:
            pass
    return results


def _r0032_curryLeft_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlternatingMap.curryLeft_add
    # curryLeft (f + g) = curryLeft f + curryLeft g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "curryLeft", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("curryLeft", (OVar("f"),)), OOp("curryLeft", (OVar("g"),))))
            results.append((rhs, "Mathlib: ContinuousAlternatingMap_curryLeft_add"))
        except Exception:
            pass
    return results


def _r0033_coe_unitBall_apply_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.coe_unitBall_apply_zero
    # (Homeomorph.unitBall (0 : E) : E) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Homeomorph_unitBall", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Homeomorph_coe_unitBall_apply_zero"))
        except Exception:
            pass
    return results


def _r0034_flipMultilinear_flipLinear(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMultilinearMap.flipMultilinear_flipLinear
    # f.flipLinear.flipMultilinear = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_flipLinear_flipMultilinear")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousMultilinearMap_flipMultilinear_flipLinear"))
    except Exception:
        pass
    return results


def _r0035_apply_zero_uncurry0(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMultilinearMap.apply_zero_uncurry0
    # ContinuousMultilinearMap.uncurry0 𝕜 G (f x) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ContinuousMultilinearMap_uncurry0", 3)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousMultilinearMap_apply_zero_uncurry0"))
        except Exception:
            pass
    return results


def _r0036_flip_flip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.flip_flip
    # f.flip.flip = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_flip_flip")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousLinearMap_flip_flip"))
    except Exception:
        pass
    return results


def _r0037_flip_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.flip_add
    # (f + g).flip = f.flip + g.flip
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_plus_g_flip")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("f_flip"), OVar("g_flip")))
            results.append((rhs, "Mathlib: ContinuousLinearMap_flip_add"))
    except Exception:
        pass
    return results


def _r0038_flip_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.flip_smul
    # (c • f).flip = c • f.flip
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("c_f_flip")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("c", (OVar("_unknown"), OVar("f_flip"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_flip_smul"))
    except Exception:
        pass
    return results


def _r0039_coe_flip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.coe_flipₗᵢ
    # ⇑(flipₗᵢ 𝕜 E Fₗ Gₗ) = flip
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("flip_E_F_G")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("flip")
            results.append((rhs, "Mathlib: ContinuousLinearMap_coe_flip"))
    except Exception:
        pass
    return results


def _r0040_norm_toSpanSingleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.norm_toSpanSingleton
    # ‖toSpanSingleton 𝕜 x‖ = ‖x‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toSpanSingleton", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: ContinuousLinearMap_norm_toSpanSingleton"))
        except Exception:
            pass
    return results


def _r0041_nnnorm_toSpanSingleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.nnnorm_toSpanSingleton
    # ‖toSpanSingleton 𝕜 x‖₊ = ‖x‖₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toSpanSingleton", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: ContinuousLinearMap_nnnorm_toSpanSingleton"))
        except Exception:
            pass
    return results


def _r0042_norm_bilinearRestrictScalars(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.norm_bilinearRestrictScalars
    # ‖B.bilinearRestrictScalars 𝕜‖ = ‖B‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "B_bilinearRestrictScalars", 1)
    if args is not None:
        try:
            rhs = OVar("B")
            results.append((rhs, "Mathlib: ContinuousLinearMap_norm_bilinearRestrictScalars"))
        except Exception:
            pass
    return results


def _r0043_symm_toDiffeomorph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.symm_toDiffeomorph
    # e.symm.toDiffeomorph = e.toDiffeomorph.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_toDiffeomorph")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_toDiffeomorph_symm")
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_symm_toDiffeomorph"))
    except Exception:
        pass
    return results


def _r0044_coe_toDiffeomorph_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.coe_toDiffeomorph_symm
    # ⇑e.toDiffeomorph.symm = e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toDiffeomorph_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm")
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_coe_toDiffeomorph_symm"))
    except Exception:
        pass
    return results


def _r0045_lift_uniq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LocallyRingedSpace.IsOpenImmersion.lift_uniq
    # l = lift f g H'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("l")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("lift", (OVar("f"), OVar("g"), OVar("H_prime"),))
            results.append((rhs, "Mathlib: LocallyRingedSpace_IsOpenImmersion_lift_uniq"))
    except Exception:
        pass
    return results


def _r0046_coe_toOrderHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OmegaCompletePartialOrder.ContinuousHom.coe_toOrderHom
    # ⇑f.1 = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OmegaCompletePartialOrder_ContinuousHom_coe_toOrderHom"))
    except Exception:
        pass
    return results


def _r0047_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OmegaCompletePartialOrder.ContinuousHom.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: OmegaCompletePartialOrder_ContinuousHom_ext"))
    except Exception:
        pass
    return results


def _r0048_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OmegaCompletePartialOrder.ContinuousHom.id_comp
    # id.comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "id_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: OmegaCompletePartialOrder_ContinuousHom_id_comp"))
        except Exception:
            pass
    return results


def _r0049_comp_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OmegaCompletePartialOrder.ContinuousHom.comp_assoc
    # f.comp (g.comp h) = (f.comp g).comp h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp", 1)
    if args is not None:
        try:
            rhs = OOp("f_comp_g_comp", (OVar("h"),))
            results.append((rhs, "Mathlib: OmegaCompletePartialOrder_ContinuousHom_comp_assoc"))
        except Exception:
            pass
    return results


def _r0050_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgHom.copy_eq
    # f.copy f' h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_copy", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousAlgHom_copy_eq"))
        except Exception:
            pass
    return results


def _r0051_coe_toAlgEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.coe_toAlgEquiv
    # ⇑e.toAlgEquiv = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toAlgEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_coe_toAlgEquiv"))
    except Exception:
        pass
    return results


def _r0052_coe_coeCLE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.coe_coeCLE
    # ⇑(e : A ≃L[R] B) = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_colon_A_L_R_B")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_coe_coeCLE"))
    except Exception:
        pass
    return results


def _r0053_toContinuousLinearEquiv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.toContinuousLinearEquiv_apply
    # e.toContinuousLinearEquiv a = e a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_toContinuousLinearEquiv", 1)
    if args is not None:
        try:
            rhs = OOp("e", (args[0],))
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_toContinuousLinearEquiv_apply"))
        except Exception:
            pass
    return results


def _r0054_toContinuousLinearMap_toContinuousLinear(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.toContinuousLinearMap_toContinuousLinearEquiv_eq
    # e.toContinuousLinearEquiv.toContinuousLinearMap     = e.toContinuousAlgHom.toContinuousLinearMap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toContinuousLinearEquiv_toContinuousLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_toContinuousAlgHom_toContinuousLinearMap")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_toContinuousLinearMap_toContinuousLinearEquiv_eq"))
    except Exception:
        pass
    return results


def _r0055_map_nhds_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.map_nhds_eq
    # Filter.map e (𝓝 a) = 𝓝 (e a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OOp("e", (OVar("a"),)),))
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_map_nhds_eq"))
        except Exception:
            pass
    return results


def _r0056_coe_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.coe_refl
    # refl R A = ContinuousAlgHom.id R A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "refl", 2)
    if args is not None:
        try:
            rhs = OOp("ContinuousAlgHom_id", (args[0], args[1],))
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_coe_refl"))
        except Exception:
            pass
    return results


def _r0057_coeCLE_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.coeCLE_refl
    # (refl R A).toContinuousLinearEquiv = ContinuousLinearEquiv.refl R A
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("refl_R_A_toContinuousLinearEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ContinuousLinearEquiv_refl", (OVar("R"), OVar("A"),))
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_coeCLE_refl"))
    except Exception:
        pass
    return results


def _r0058_refl_toContinuousLinearEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.refl_toContinuousLinearEquiv
    # (refl R A).toContinuousLinearEquiv = .refl R A
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("refl_R_A_toContinuousLinearEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("refl", (OVar("R"), OVar("A"),))
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_refl_toContinuousLinearEquiv"))
    except Exception:
        pass
    return results


def _r0059_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.symm_apply_apply
    # e.symm (e a) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0060_symm_image_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.symm_image_image
    # e.symm '' (e '' S) = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm", 2)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_symm_image_image"))
        except Exception:
            pass
    return results


def _r0061_image_symm_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.image_symm_image
    # e '' (e.symm '' S) = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 2)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_image_symm_image"))
        except Exception:
            pass
    return results


def _r0062_symm_toAlgEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.symm_toAlgEquiv
    # e.symm.toAlgEquiv = e.toAlgEquiv.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_toAlgEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_toAlgEquiv_symm")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_symm_toAlgEquiv"))
    except Exception:
        pass
    return results


def _r0063_symm_toHomeomorph(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.symm_toHomeomorph
    # e.symm.toHomeomorph = e.toHomeomorph.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_toHomeomorph")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_toHomeomorph_symm")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_symm_toHomeomorph"))
    except Exception:
        pass
    return results


def _r0064_toContinuousLinearEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.toContinuousLinearEquiv_symm
    # e.symm.toContinuousLinearEquiv = e.toContinuousLinearEquiv.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_toContinuousLinearEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_toContinuousLinearEquiv_symm")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_toContinuousLinearEquiv_symm"))
    except Exception:
        pass
    return results


def _r0065_symm_map_nhds_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.symm_map_nhds_eq
    # Filter.map e.symm (𝓝 (e a)) = 𝓝 a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Filter_map", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("a"),))
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_symm_map_nhds_eq"))
        except Exception:
            pass
    return results


def _r0066_symm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.symm_symm
    # e.symm.symm = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_symm_symm"))
    except Exception:
        pass
    return results


def _r0067_symm_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.symm_symm_apply
    # e.symm.symm a = e a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm_symm", 1)
    if args is not None:
        try:
            rhs = OOp("e", (args[0],))
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_symm_symm_apply"))
        except Exception:
            pass
    return results


def _r0068_preimage_symm_preimage(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgEquiv.preimage_symm_preimage
    # e ⁻¹' (e.symm ⁻¹' S) = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 2)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: ContinuousAlgEquiv_preimage_symm_preimage"))
        except Exception:
            pass
    return results


def _r0069_smulOfNeZero_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.smulOfNeZero_symm_apply
    # ⇑(Homeomorph.smulOfNeZero c hc).symm = (c⁻¹ • · : α → α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Homeomorph_smulOfNeZero_c_hc_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("implies", (OOp("cinv", (OVar("_unknown"), OVar("_unknown"), OVar("colon"), OVar("a"),)), OVar("a")))
            results.append((rhs, "Mathlib: Homeomorph_smulOfNeZero_symm_apply"))
    except Exception:
        pass
    return results


def _r0070_coe_toEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAffineEquiv.coe_toEquiv
    # ⇑e.toEquiv = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: ContinuousAffineEquiv_coe_toEquiv"))
    except Exception:
        pass
    return results


def _r0071_to_continuousMap_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAffineMap.to_continuousMap_injective
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: ContinuousAffineMap_to_continuousMap_injective"))
    except Exception:
        pass
    return results


def _r0072_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAffineMap.comp_apply
    # f.comp g p = f (g p)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("g", (args[1],)),))
            results.append((rhs, "Mathlib: ContinuousAffineMap_comp_apply"))
        except Exception:
            pass
    return results


def _r0073_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAffineMap.id_comp
    # (id R Q).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "id_R_Q_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ContinuousAffineMap_id_comp"))
        except Exception:
            pass
    return results


def _r0074_contLinear_map_vsub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAffineMap.contLinear_map_vsub
    # f.contLinear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_contLinear", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("p_1"), OVar("minus"), OVar("f"), OVar("p_2"),))
            results.append((rhs, "Mathlib: ContinuousAffineMap_contLinear_map_vsub"))
        except Exception:
            pass
    return results


def _r0075_const_contLinear(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAffineMap.const_contLinear
    # (const R P q).contLinear = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("const_R_P_q_contLinear")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousAffineMap_const_contLinear"))
    except Exception:
        pass
    return results


def _r0076_contLinear_eq_zero_iff_exists_const(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAffineMap.contLinear_eq_zero_iff_exists_const
    # f.contLinear = 0 ↔ ∃ q, f = const R P q
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_contLinear")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("exists", (OVar("q"), OVar("f"),)))), OOp("const", (OVar("R"), OVar("P"), OVar("q"),))))
            results.append((rhs, "Mathlib: ContinuousAffineMap_contLinear_eq_zero_iff_exists_const"))
    except Exception:
        pass
    return results


def _r0077_toContinuousAffineMap_map_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.toContinuousAffineMap_map_zero
    # f.toContinuousAffineMap 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toContinuousAffineMap", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousLinearMap_toContinuousAffineMap_map_zero"))
        except Exception:
            pass
    return results


def _r0078_coe_toContinuousMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMonoidHom.coe_toContinuousMap
    # f.toContinuousMap = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toContinuousMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousMonoidHom_coe_toContinuousMap"))
    except Exception:
        pass
    return results


def _r0079_coe_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMonoidHom.coe_comp
    # ⇑(g.comp f) = ⇑g ∘ ⇑f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_comp_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("g"), OVar("f")))
            results.append((rhs, "Mathlib: ContinuousMonoidHom_coe_comp"))
    except Exception:
        pass
    return results


def _r0080_coe_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMonoidHom.coe_id
    # ⇑(ContinuousMonoidHom.id A) = _root_.id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ContinuousMonoidHom_id_A")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("root_id")
            results.append((rhs, "Mathlib: ContinuousMonoidHom_coe_id"))
    except Exception:
        pass
    return results


def _r0081_pow_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMonoidHom.pow_apply
    # (f ^ n) a = (f a) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_pow_n", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("f", (args[0],)), OVar("n")))
            results.append((rhs, "Mathlib: ContinuousMonoidHom_pow_apply"))
        except Exception:
            pass
    return results


def _r0082_toEquiv_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMulEquiv.toEquiv_eq_coe
    # f.toEquiv = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousMulEquiv_toEquiv_eq_coe"))
    except Exception:
        pass
    return results


def _r0083_toHomeomorph_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMulEquiv.toHomeomorph_eq_coe
    # f.toHomeomorph = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toHomeomorph")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousMulEquiv_toHomeomorph_eq_coe"))
    except Exception:
        pass
    return results


def _r0084_mulLeft_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.mulLeft_symm
    # (Homeomorph.mulLeft a).symm = Homeomorph.mulLeft a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Homeomorph_mulLeft_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Homeomorph_mulLeft", (OVar("ainv"),))
            results.append((rhs, "Mathlib: Homeomorph_mulLeft_symm"))
    except Exception:
        pass
    return results


def _r0085_mulRight_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.mulRight_symm
    # (Homeomorph.mulRight a).symm = Homeomorph.mulRight a⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Homeomorph_mulRight_a_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Homeomorph_mulRight", (OVar("ainv"),))
            results.append((rhs, "Mathlib: Homeomorph_mulRight_symm"))
    except Exception:
        pass
    return results


def _r0086_coe_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.coe_inv
    # ⇑(Homeomorph.inv G) = Inv.inv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Homeomorph_inv_G")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Inv_inv")
            results.append((rhs, "Mathlib: Homeomorph_coe_inv"))
    except Exception:
        pass
    return results


def _r0087_coe_completion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.coe_completion
    # f.completion = Completion.map f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_completion")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Completion_map", (OVar("f"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_coe_completion"))
    except Exception:
        pass
    return results


def _r0088_coe_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlternatingMap.coe_mk
    # ⇑(mk f h) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mk_f_h")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousAlternatingMap_coe_mk"))
    except Exception:
        pass
    return results


def _r0089_map_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlternatingMap.map_zero
    # f 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousAlternatingMap_map_zero"))
        except Exception:
            pass
    return results


def _r0090_map_eq_zero_of_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlternatingMap.map_eq_zero_of_eq
    # f v = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousAlternatingMap_map_eq_zero_of_eq"))
        except Exception:
            pass
    return results


def _r0091_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlternatingMap.smul_apply
    # (c • f) v = c • f v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_f", 1)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OVar("f"), args[0],))
            results.append((rhs, "Mathlib: ContinuousAlternatingMap_smul_apply"))
        except Exception:
            pass
    return results


def _r0092_map_nhds_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.map_nhds_eq
    # map e (𝓝 x) = 𝓝 (e x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OOp("e", (OVar("x"),)),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_map_nhds_eq"))
        except Exception:
            pass
    return results


def _r0093_map_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.map_smul
    # e (c • x) = c • e x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OVar("e"), OVar("x"),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_map_smul"))
        except Exception:
            pass
    return results


def _r0094_symm_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.symm_smul_apply
    # (α • e).symm x = (↑α⁻¹ : S) • e.symm x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_e_symm", 1)
    if args is not None:
        try:
            rhs = OOp("ainv_colon_S", (OVar("_unknown"), OVar("e_symm"), args[0],))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_symm_smul_apply"))
        except Exception:
            pass
    return results


def _r0095_toLinearEquiv_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.toLinearEquiv_smul
    # (α • e).toLinearEquiv = α • e.toLinearEquiv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_e_toLinearEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a", (OVar("_unknown"), OVar("e_toLinearEquiv"),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_toLinearEquiv_smul"))
    except Exception:
        pass
    return results


def _r0096_smul_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.smul_trans
    # (α • e).trans f = α • (e.trans f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_e_trans", 1)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OOp("e_trans", (args[0],)),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_smul_trans"))
        except Exception:
            pass
    return results


def _r0097_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.copy_eq
    # f.copy f' h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_copy", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousLinearMap_copy_eq"))
        except Exception:
            pass
    return results


def _r0098_map_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.map_smul
    # f (c • x) = c • f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OVar("f"), OVar("x"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_map_smul"))
        except Exception:
            pass
    return results


def _r0099_inr_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.inr_apply
    # inr R M₁ M₂ x = (0, x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inr", 4)
    if args is not None:
        try:
            rhs = OOp("_0", (args[3],))
            results.append((rhs, "Mathlib: ContinuousLinearMap_inr_apply"))
        except Exception:
            pass
    return results


def _r0100_comp_inl_add_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.comp_inl_add_comp_inr
    # L.comp (.inl R M₁ M₂) v.1 + L.comp (.inr R M₁ M₂) v.2 = L v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("L", (OVar("v"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_comp_inl_add_comp_inr"))
        except Exception:
            pass
    return results


def _r0101_coe_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.coe_snd
    # ↑(snd R M₁ M₂) = LinearMap.snd R M₁ M₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("snd_R_M_1_M_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("LinearMap_snd", (OVar("R"), OVar("M_1"), OVar("M_2"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_coe_snd"))
    except Exception:
        pass
    return results


def _r0102_fst_prod_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fst_prod_snd
    # (fst R M₁ M₂).prod (snd R M₁ M₂) = .id R (M₁ × M₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_R_M_1_M_2_prod", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("R"), OOp("product", (OVar("M_1"), OVar("M_2"))),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_fst_prod_snd"))
        except Exception:
            pass
    return results


def _r0103_fst_comp_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fst_comp_prod
    # (fst R M₂ M₃).comp (f.prod g) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_R_M_2_M_3_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousLinearMap_fst_comp_prod"))
        except Exception:
            pass
    return results


def _r0104_fst_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fst_comp_inr
    # fst R M₁ M₂ ∘L inr R M₁ M₂ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst", 8)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousLinearMap_fst_comp_inr"))
        except Exception:
            pass
    return results


def _r0105_snd_comp_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.snd_comp_inl
    # snd R M₁ M₂ ∘L inl R M₁ M₂ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd", 8)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousLinearMap_snd_comp_inl"))
        except Exception:
            pass
    return results


def _r0106_snd_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.snd_comp_inr
    # snd R M₁ M₂ ∘L inr R M₁ M₂ = .id R M₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd", 8)
    if args is not None:
        try:
            rhs = OOp("id", (args[5], args[7],))
            results.append((rhs, "Mathlib: ContinuousLinearMap_snd_comp_inr"))
        except Exception:
            pass
    return results


def _r0107_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMultilinearMap.ext
    # f = f'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_prime")
            results.append((rhs, "Mathlib: ContinuousMultilinearMap_ext"))
    except Exception:
        pass
    return results


def _r0108_toMultilinearMap_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMultilinearMap.toMultilinearMap_zero
    # (0 : ContinuousMultilinearMap R M₁ M₂).toMultilinearMap = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_ContinuousMultilinearMap_R_M_1_M_2_toMultilinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousMultilinearMap_toMultilinearMap_zero"))
    except Exception:
        pass
    return results


def _r0109_toUniformConvergenceCLM_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.toUniformConvergenceCLM_symm_apply
    # (ContinuousLinearMap.toUniformConvergenceCLM σ F 𝔖).symm A x = A x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ContinuousLinearMap_toUniformConvergenceCLM_sig_F_symm", 2)
    if args is not None:
        try:
            rhs = OOp("A", (args[1],))
            results.append((rhs, "Mathlib: ContinuousLinearMap_toUniformConvergenceCLM_symm_apply"))
        except Exception:
            pass
    return results


def _r0110_toLinearMap_intrinsicStar(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.toLinearMap_intrinsicStar
    # (star f).ofConv.toLinearMap = (star (toConv f.ofConv.toLinearMap)).ofConv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("star_f_ofConv_toLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("star_toConv_f_ofConv_toLinearMap_ofConv")
            results.append((rhs, "Mathlib: ContinuousLinearMap_toLinearMap_intrinsicStar"))
    except Exception:
        pass
    return results


def _r0111_isSelfAdjoint_iff_map_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star
    # IsSelfAdjoint f ↔ ∀ x, f (star x) = star (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("star", (OOp("f", (OVar("x"),)),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_IntrinsicStar_isSelfAdjoint_iff_map_star"))
        except Exception:
            pass
    return results


def _r0112_intrinsicStar_smulRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.intrinsicStar_smulRight
    # star (toConv (f.ofConv.smulRight x)) = toConv ((star f).ofConv.smulRight (star x))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "star", 1)
    if args is not None:
        try:
            rhs = OOp("toConv", (OOp("star_f_ofConv_smulRight", (OOp("star", (OVar("x"),)),)),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_intrinsicStar_smulRight"))
        except Exception:
            pass
    return results


def _r0113_ext_iff_isClosed(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.ext_iff_isClosed
    # t₁ = t₂ ↔ ∀ s, IsClosed[t₁] s ↔ IsClosed[t₂] s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("t_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("t_2"), OOp("iff", (OOp("forall", (OVar("s"), OVar("IsClosed_t_1"), OVar("s"),)), OOp("IsClosed_t_2", (OVar("s"),))))))
            results.append((rhs, "Mathlib: TopologicalSpace_ext_iff_isClosed"))
    except Exception:
        pass
    return results


def _r0114_val_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.OpenNhds.val_apply
    # (f y : X) = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: TopologicalSpace_OpenNhds_val_apply"))
        except Exception:
            pass
    return results


def _r0115_coe_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.OpenNhds.coe_id
    # ⇑f = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: TopologicalSpace_OpenNhds_coe_id"))
    except Exception:
        pass
    return results


def _r0116_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.OpenNhds.id_apply
    # f y = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: TopologicalSpace_OpenNhds_id_apply"))
        except Exception:
            pass
    return results


def _r0117_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.OpenNhds.comp_apply
    # (f ≫ g) x = g (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: TopologicalSpace_OpenNhds_comp_apply"))
        except Exception:
            pass
    return results


def _r0118_map_id_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.OpenNhds.map_id_obj
    # (map (𝟙 X) x).obj U = U
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_1_X_x_obj", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: TopologicalSpace_OpenNhds_map_id_obj"))
        except Exception:
            pass
    return results


def _r0119_map_id_obj_unop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.OpenNhds.map_id_obj_unop
    # (map (𝟙 X) x).obj (unop U) = unop U
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_1_X_x_obj", 1)
    if args is not None:
        try:
            rhs = OOp("unop", (OVar("U"),))
            results.append((rhs, "Mathlib: TopologicalSpace_OpenNhds_map_id_obj_unop"))
        except Exception:
            pass
    return results


def _r0120_op_map_id_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.OpenNhds.op_map_id_obj
    # (map (𝟙 X) x).op.obj U = U
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_1_X_x_op_obj", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: TopologicalSpace_OpenNhds_op_map_id_obj"))
        except Exception:
            pass
    return results


def _r0121_inclusionMapIso_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.OpenNhds.inclusionMapIso_hom
    # (inclusionMapIso f x).hom = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inclusionMapIso_f_x_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: TopologicalSpace_OpenNhds_inclusionMapIso_hom"))
    except Exception:
        pass
    return results


def _r0122_inclusionMapIso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.OpenNhds.inclusionMapIso_inv
    # (inclusionMapIso f x).inv = 𝟙 _
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inclusionMapIso_f_x_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: TopologicalSpace_OpenNhds_inclusionMapIso_inv"))
    except Exception:
        pass
    return results


def _r0123_val_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.val_apply
    # (f x : X) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_val_apply"))
        except Exception:
            pass
    return results


def _r0124_coe_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_id
    # ⇑f = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_id"))
    except Exception:
        pass
    return results


def _r0125_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.id_apply
    # f x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_id_apply"))
        except Exception:
            pass
    return results


def _r0126_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.comp_apply
    # (f ≫ g) x = g (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_comp_apply"))
        except Exception:
            pass
    return results


def _r0127_map_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.map_obj
    # (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.hom.continuous⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_f_obj", 1)
    if args is not None:
        try:
            rhs = OVar("f_inv_prime_U_p_preimage_f_hom_continuous")
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_map_obj"))
        except Exception:
            pass
    return results


def _r0128_map_homOfLE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.map_homOfLE
    # (TopologicalSpace.Opens.map f).map (homOfLE e) =       homOfLE (show (Opens.map f).obj U ≤ (Opens.map f).obj V from fun 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "TopologicalSpace_Opens_map_f_map", 1)
    if args is not None:
        try:
            rhs = OOp("homOfLE", (OOp("<=", (OOp("show", (OVar("Opens_map_f_obj"), OVar("U"),)), OOp("Opens_map_f_obj", (OVar("V"), OVar("from"), OVar("fun"), OVar("_unknown"), OVar("hx"), OVar("_unknown"), OVar("e"), OVar("hx"),)))),))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_map_homOfLE"))
        except Exception:
            pass
    return results


def _r0129_map_id_obj_unop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.map_id_obj_unop
    # (map (𝟙 X)).obj (unop U) = unop U
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map_1_X_obj", 1)
    if args is not None:
        try:
            rhs = OOp("unop", (OVar("U"),))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_map_id_obj_unop"))
        except Exception:
            pass
    return results


def _r0130_mapIso_hom_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.mapIso_hom_app
    # (mapIso f g h).hom.app U = eqToHom (by rw [h])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mapIso_f_g_h_hom_app", 1)
    if args is not None:
        try:
            rhs = OOp("eqToHom", (OOp("by", (OVar("rw"), OSeq((OVar("h"),)),)),))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_mapIso_hom_app"))
        except Exception:
            pass
    return results


def _r0131_continuousMapOfUnique_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.continuousMapOfUnique_symm_apply
    # continuousMapOfUnique.symm f = f default
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "continuousMapOfUnique_symm", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("default"),))
            results.append((rhs, "Mathlib: Homeomorph_continuousMapOfUnique_symm_apply"))
        except Exception:
            pass
    return results


def _r0132_equivOfIsClopen_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ConnectedComponents.equivOfIsClopen_mk
    # equivOfIsClopen hclopen hdisj hunion (.mk x) = ⟨i, .mk ⟨x, hx⟩⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "equivOfIsClopen", 4)
    if args is not None:
        try:
            rhs = OVar("i_mk_x_hx")
            results.append((rhs, "Mathlib: ConnectedComponents_equivOfIsClopen_mk"))
        except Exception:
            pass
    return results


def _r0133_coe_prodComm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.coe_prodComm
    # ⇑(prodComm X Y) = Prod.swap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("prodComm_X_Y")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Prod_swap")
            results.append((rhs, "Mathlib: Homeomorph_coe_prodComm"))
    except Exception:
        pass
    return results


def _r0134_sumCongr_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.sumCongr_refl
    # sumCongr (.refl X) (.refl Y) = .refl (X ⊕ Y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sumCongr", 2)
    if args is not None:
        try:
            rhs = OOp("refl", (OOp("X", (OVar("_unknown"), OVar("Y"),)),))
            results.append((rhs, "Mathlib: Homeomorph_sumCongr_refl"))
        except Exception:
            pass
    return results


def _r0135_coe_sumComm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.coe_sumComm
    # ⇑(sumComm X Y) = Sum.swap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sumComm_X_Y")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Sum_swap")
            results.append((rhs, "Mathlib: Homeomorph_coe_sumComm"))
    except Exception:
        pass
    return results


def _r0136_sumSumSumComm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.sumSumSumComm_symm
    # (sumSumSumComm X Y W Z).symm = (sumSumSumComm X W Y Z)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sumSumSumComm_X_Y_W_Z_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sumSumSumComm", (OVar("X"), OVar("W"), OVar("Y"), OVar("Z"),))
            results.append((rhs, "Mathlib: Homeomorph_sumSumSumComm_symm"))
    except Exception:
        pass
    return results


def _r0137_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.mul_apply
    # (f * g) x = f x * g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_star_g", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: ContinuousMap_mul_apply"))
        except Exception:
            pass
    return results


def _r0138_mul_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.mul_comp
    # (f₁ * f₂).comp g = f₁.comp g * f₂.comp g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_1_star_f_2_comp", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f_1_comp", (args[0],)), OOp("f_2_comp", (args[0],))))
            results.append((rhs, "Mathlib: ContinuousMap_mul_comp"))
        except Exception:
            pass
    return results


def _r0139_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.one_apply
    # (1 : C(α, β)) x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_C_a_b", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ContinuousMap_one_apply"))
        except Exception:
            pass
    return results


def _r0140_one_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.one_comp
    # (1 : C(β, γ)).comp g = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_C_b_g_comp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ContinuousMap_one_comp"))
        except Exception:
            pass
    return results


def _r0141_comp_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.comp_one
    # g.comp (1 : C(α, β)) = const α (g 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("const", (OVar("a"), OOp("g", (OLit(1),)),))
            results.append((rhs, "Mathlib: ContinuousMap_comp_one"))
        except Exception:
            pass
    return results


def _r0142_const_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.const_one
    # const α (1 : β) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "const", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: ContinuousMap_const_one"))
        except Exception:
            pass
    return results


def _r0143_natCast_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.natCast_apply
    # (n : C(α, β)) x = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_colon_C_a_b", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ContinuousMap_natCast_apply"))
        except Exception:
            pass
    return results


def _r0144_intCast_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.intCast_apply
    # (n : C(α, β)) x = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_colon_C_a_b", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ContinuousMap_intCast_apply"))
        except Exception:
            pass
    return results


def _r0145_inv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.inv_apply
    # f⁻¹ x = (f x)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finv", 1)
    if args is not None:
        try:
            rhs = OVar("f_x_inv")
            results.append((rhs, "Mathlib: ContinuousMap_inv_apply"))
        except Exception:
            pass
    return results


def _r0146_inv_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.inv_comp
    # f⁻¹.comp g = (f.comp g)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finv_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f_comp_g_inv")
            results.append((rhs, "Mathlib: ContinuousMap_inv_comp"))
        except Exception:
            pass
    return results


def _r0147_div_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.div_apply
    # (f / g) x = f x / g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_slash_g", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: ContinuousMap_div_apply"))
        except Exception:
            pass
    return results


def _r0148_div_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.div_comp
    # (f / g).comp h = f.comp h / g.comp h
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_slash_g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("f_comp", (args[0],)), OOp("g_comp", (args[0],))))
            results.append((rhs, "Mathlib: ContinuousMap_div_comp"))
        except Exception:
            pass
    return results


def _r0149_smul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.smul_apply
    # (c • f) a = c • f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c_f", 1)
    if args is not None:
        try:
            rhs = OOp("c", (OVar("_unknown"), OVar("f"), args[0],))
            results.append((rhs, "Mathlib: ContinuousMap_smul_apply"))
        except Exception:
            pass
    return results


def _r0150_equivFnOfDiscrete_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.equivFnOfDiscrete_symm_apply
    # equivFnOfDiscrete.symm f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "equivFnOfDiscrete_symm", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ContinuousMap_equivFnOfDiscrete_symm_apply"))
        except Exception:
            pass
    return results


def _r0151_coe_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.coe_trans
    # (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_trans", 3)
    if args is not None:
        try:
            rhs = OOp("g_colon_C_b_g_comp", (OVar("f"),))
            results.append((rhs, "Mathlib: Homeomorph_coe_trans"))
        except Exception:
            pass
    return results


def _r0152_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CompactlySupportedContinuousMap.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: CompactlySupportedContinuousMap_ext"))
    except Exception:
        pass
    return results


def _r0153_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CompactlySupportedContinuousMap.copy_eq
    # f.copy f' h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_copy", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CompactlySupportedContinuousMap_copy_eq"))
        except Exception:
            pass
    return results


def _r0154_nnrealPart_neg_eq_zero_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CompactlySupportedContinuousMap.nnrealPart_neg_eq_zero_of_nonneg
    # (-f).nnrealPart = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_f_nnrealPart")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CompactlySupportedContinuousMap_nnrealPart_neg_eq_zero_of_nonneg"))
    except Exception:
        pass
    return results


def _r0155_toReal_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CompactlySupportedContinuousMap.toReal_add
    # (f + g).toReal = f.toReal + g.toReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_plus_g_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("f_toReal"), OVar("g_toReal")))
            results.append((rhs, "Mathlib: CompactlySupportedContinuousMap_toReal_add"))
    except Exception:
        pass
    return results


def _r0156_toReal_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CompactlySupportedContinuousMap.toReal_smul
    # (r • f).toReal = r • f.toReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_f_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("r", (OVar("_unknown"), OVar("f_toReal"),))
            results.append((rhs, "Mathlib: CompactlySupportedContinuousMap_toReal_smul"))
    except Exception:
        pass
    return results


def _r0157_nnrealPart_sub_nnrealPart_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg
    # (nnrealPart f).toReal - (nnrealPart (-f)).toReal = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CompactlySupportedContinuousMap_nnrealPart_sub_nnrealPart_neg"))
        except Exception:
            pass
    return results


def _r0158_toRealLinearMap_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CompactlySupportedContinuousMap.toRealLinearMap_apply
    # toRealLinearMap f = f.toReal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toRealLinearMap", 1)
    if args is not None:
        try:
            rhs = OVar("f_toReal")
            results.append((rhs, "Mathlib: CompactlySupportedContinuousMap_toRealLinearMap_apply"))
        except Exception:
            pass
    return results


def _r0159_nnrealPart_neg_toReal_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CompactlySupportedContinuousMap.nnrealPart_neg_toReal_eq
    # nnrealPart (-toReal f) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nnrealPart", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: CompactlySupportedContinuousMap_nnrealPart_neg_toReal_eq"))
        except Exception:
            pass
    return results


def _r0160_toNNRealLinear_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CompactlySupportedContinuousMap.toNNRealLinear_inj
    # toNNRealLinear Λ₁ = toNNRealLinear Λ₂ ↔ Λ₁ = Λ₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toNNRealLinear", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("toNNRealLinear", (OVar("_2"),)), args[0])), OVar("_2")))
            results.append((rhs, "Mathlib: CompactlySupportedContinuousMap_toNNRealLinear_inj"))
        except Exception:
            pass
    return results


def _r0161_toContinuousMap_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMapZero.toContinuousMap_id
    # (ContinuousMapZero.id s : C(s, R)) = .restrict s (.id R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ContinuousMapZero_id", 3)
    if args is not None:
        try:
            rhs = OOp("restrict", (args[0], OOp("id", (OVar("R"),)),))
            results.append((rhs, "Mathlib: ContinuousMapZero_toContinuousMap_id"))
        except Exception:
            pass
    return results


def _r0162_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.copy_eq
    # f.copy f' h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_copy", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousMap_copy_eq"))
        except Exception:
            pass
    return results


def _r0163_setOfTop_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.setOfTop_eq_univ
    # setOfIdeal (⊤ : Ideal C(X, R)) = Set.univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "setOfIdeal", 1)
    if args is not None:
        try:
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: ContinuousMap_setOfTop_eq_univ"))
        except Exception:
            pass
    return results


def _r0164_idealOfEmpty_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.idealOfEmpty_eq_bot
    # idealOfSet R (∅ : Set X) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "idealOfSet", 2)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: ContinuousMap_idealOfEmpty_eq_bot"))
        except Exception:
            pass
    return results


def _r0165_mabs_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.mabs_apply
    # |f|ₘ x = |f x|ₘ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pipe_fpipe", 1)
    if args is not None:
        try:
            rhs = OOp("pipe_f", (OVar("xpipe"),))
            results.append((rhs, "Mathlib: ContinuousMap_mabs_apply"))
        except Exception:
            pass
    return results


def _r0166_sup_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.sup_apply
    # (f ⊔ g) a = f a ⊔ g a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0], OVar("_unknown"), OVar("g"), args[0],))
            results.append((rhs, "Mathlib: ContinuousMap_sup_apply"))
        except Exception:
            pass
    return results


def _r0167_star_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.star_apply
    # star f x = star (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "star", 2)
    if args is not None:
        try:
            rhs = OOp("star", (OOp("f", (args[1],)),))
            results.append((rhs, "Mathlib: ContinuousMap_star_apply"))
        except Exception:
            pass
    return results


def _r0168_closedEBall_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.closedEBall_zero
    # closedEBall x 0 = {x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closedEBall", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Metric_closedEBall_zero"))
        except Exception:
            pass
    return results


def _r0169_ediam_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.ediam_one
    # ediam (1 : Set X) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ediam", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Metric_ediam_one"))
        except Exception:
            pass
    return results


def _r0170_ediam_iUnion_mem_option(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.ediam_iUnion_mem_option
    # ediam (⋃ i ∈ o, s i) = ⨆ i ∈ o, ediam (s i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ediam", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("o", (OVar("ediam"), OOp("s", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: Metric_ediam_iUnion_mem_option"))
        except Exception:
            pass
    return results


def _r0171_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOpenMap.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: ContinuousOpenMap_ext"))
    except Exception:
        pass
    return results


def _r0172_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOpenMap.copy_eq
    # f.copy f' h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_copy", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousOpenMap_copy_eq"))
        except Exception:
            pass
    return results


def _r0173_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOpenMap.comp_apply
    # (f.comp g) a = f (g a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp_g", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("g", (args[0],)),))
            results.append((rhs, "Mathlib: ContinuousOpenMap_comp_apply"))
        except Exception:
            pass
    return results


def _r0174_comp_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOpenMap.comp_assoc
    # (f.comp g).comp h = f.comp (g.comp h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp_g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("f_comp", (OOp("g_comp", (args[0],)),))
            results.append((rhs, "Mathlib: ContinuousOpenMap_comp_assoc"))
        except Exception:
            pass
    return results


def _r0175_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOpenMap.id_comp
    # (ContinuousOpenMap.id β).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ContinuousOpenMap_id_b_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ContinuousOpenMap_id_comp"))
        except Exception:
            pass
    return results


def _r0176_cancel_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOpenMap.cancel_right
    # g₁.comp f = g₂.comp f ↔ g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_1_comp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("g_2_comp", (args[0],)), OVar("g_1"))), OVar("g_2")))
            results.append((rhs, "Mathlib: ContinuousOpenMap_cancel_right"))
        except Exception:
            pass
    return results


def _r0177_coe_symm_toEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.coe_symm_toEquiv
    # ⇑h.toEquiv.symm = h.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h_toEquiv_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("h_symm")
            results.append((rhs, "Mathlib: Homeomorph_coe_symm_toEquiv"))
    except Exception:
        pass
    return results


def _r0178_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.ext
    # h = h'
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("h_prime")
            results.append((rhs, "Mathlib: Homeomorph_ext"))
    except Exception:
        pass
    return results


def _r0179_symm_trans_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.symm_trans_apply
    # (f.trans g).symm z = f.symm (g.symm z)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_trans_g_symm", 1)
    if args is not None:
        try:
            rhs = OOp("f_symm", (OOp("g_symm", (args[0],)),))
            results.append((rhs, "Mathlib: Homeomorph_symm_trans_apply"))
        except Exception:
            pass
    return results


def _r0180_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.symm_apply_apply
    # h.symm (h x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Homeomorph_symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0181_symm_apply_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.symm_apply_eq
    # h.symm y = x ↔ y = h x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h_symm", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("x"), args[0])), OOp("h", (OVar("x"),))))
            results.append((rhs, "Mathlib: Homeomorph_symm_apply_eq"))
        except Exception:
            pass
    return results


def _r0182_self_comp_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.self_comp_symm
    # h ∘ h.symm = id
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OVar("id")
            results.append((rhs, "Mathlib: Homeomorph_self_comp_symm"))
        except Exception:
            pass
    return results


def _r0183_range_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.range_coe
    # range h = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Homeomorph_range_coe"))
        except Exception:
            pass
    return results


def _r0184_preimage_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.preimage_image
    # h ⁻¹' (h '' s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Homeomorph_preimage_image"))
        except Exception:
            pass
    return results


def _r0185_image_eq_preimage_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.image_eq_preimage_symm
    # h '' s = h.symm ⁻¹' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "h", 2)
    if args is not None:
        try:
            rhs = OOp("h_symm", (OVar("inv_prime"), args[1],))
            results.append((rhs, "Mathlib: Homeomorph_image_eq_preimage_symm"))
        except Exception:
            pass
    return results


def _r0186_map_nhds_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.map_nhds_eq
    # map h (𝓝 x) = 𝓝 (h x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OOp("h", (OVar("x"),)),))
            results.append((rhs, "Mathlib: Homeomorph_map_nhds_eq"))
        except Exception:
            pass
    return results


def _r0187_symm_map_nhds_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.symm_map_nhds_eq
    # map h.symm (𝓝 (h x)) = 𝓝 x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "map", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("x"),))
            results.append((rhs, "Mathlib: Homeomorph_symm_map_nhds_eq"))
        except Exception:
            pass
    return results


def _r0188_trans_toHomotopyEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.trans_toHomotopyEquiv
    # (h₀.trans h₁).toHomotopyEquiv = h₀.toHomotopyEquiv.trans h₁.toHomotopyEquiv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("h_0_trans_h_1_toHomotopyEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("h_0_toHomotopyEquiv_trans", (OVar("h_1_toHomotopyEquiv"),))
            results.append((rhs, "Mathlib: Homeomorph_trans_toHomotopyEquiv"))
    except Exception:
        pass
    return results


def _r0189_isCover_empty_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.isCover_empty_right
    # IsCover ε s ∅ ↔ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Metric_isCover_empty_right"))
        except Exception:
            pass
    return results


def _r0190_sphere_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.sphere_zero
    # sphere x 0 = {x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sphere", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Metric_sphere_zero"))
        except Exception:
            pass
    return results


def _r0191_dimH_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.dimH_univ
    # dimH (univ : Set E) = dimH (univ : Set F)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dimH", 1)
    if args is not None:
        try:
            rhs = OOp("dimH", (OOp("univ_set", (OVar("colon"), OVar("Set"), OVar("F"),)),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_dimH_univ"))
        except Exception:
            pass
    return results


def _r0192_infEDist_iUnion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.infEDist_iUnion
    # infEDist x (⋃ i, f i) = ⨅ i, infEDist x (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "infEDist", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("infEDist"), args[0], OOp("f", (OVar("i"),)),))
            results.append((rhs, "Mathlib: Metric_infEDist_iUnion"))
        except Exception:
            pass
    return results


def _r0193_infEDist_biUnion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.infEDist_biUnion
    # infEDist x (⋃ i ∈ I, f i) = ⨅ i ∈ I, infEDist x (f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "infEDist", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("I", (OVar("infEDist"), args[0], OOp("f", (OVar("i"),)),))))
            results.append((rhs, "Mathlib: Metric_infEDist_biUnion"))
        except Exception:
            pass
    return results


def _r0194_hausdorffDist_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.hausdorffDist_comm
    # hausdorffDist s t = hausdorffDist t s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hausdorffDist", 2)
    if args is not None:
        try:
            rhs = OOp("hausdorffDist", (args[1], args[0],))
            results.append((rhs, "Mathlib: Metric_hausdorffDist_comm"))
        except Exception:
            pass
    return results


def _r0195_hausdorffDist_closure_1(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.hausdorffDist_closure₁
    # hausdorffDist (closure s) t = hausdorffDist s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hausdorffDist", 2)
    if args is not None:
        try:
            rhs = OOp("hausdorffDist", (OVar("s"), args[1],))
            results.append((rhs, "Mathlib: Metric_hausdorffDist_closure_1"))
        except Exception:
            pass
    return results


def _r0196_preimage_smul_ball(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.preimage_smul_ball
    # (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c", 4)
    if args is not None:
        try:
            rhs = OOp("ball", (OOp("cinv", (OVar("_unknown"), args[2],)), args[3],))
            results.append((rhs, "Mathlib: Metric_preimage_smul_ball"))
        except Exception:
            pass
    return results


def _r0197_smul_closedBall(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.smul_closedBall
    # c • closedBall x r = closedBall (c • x) r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c", 4)
    if args is not None:
        try:
            rhs = OOp("closedBall", (OOp("c", (args[0], args[2],)), args[3],))
            results.append((rhs, "Mathlib: Metric_smul_closedBall"))
        except Exception:
            pass
    return results


def _r0198_preimage_smul_closedBall(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.preimage_smul_closedBall
    # (c • ·) ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c", 4)
    if args is not None:
        try:
            rhs = OOp("closedBall", (OOp("cinv", (OVar("_unknown"), args[2],)), args[3],))
            results.append((rhs, "Mathlib: Metric_preimage_smul_closedBall"))
        except Exception:
            pass
    return results


def _r0199_smul_sphere(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.smul_sphere
    # c • sphere x r = sphere (c • x) r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c", 4)
    if args is not None:
        try:
            rhs = OOp("sphere", (OOp("c", (args[0], args[2],)), args[3],))
            results.append((rhs, "Mathlib: Metric_smul_sphere"))
        except Exception:
            pass
    return results


def _r0200_preimage_smul_sphere(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.preimage_smul_sphere
    # (c • ·) ⁻¹' sphere x r = sphere (c⁻¹ • x) r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "c", 4)
    if args is not None:
        try:
            rhs = OOp("sphere", (OOp("cinv", (OVar("_unknown"), args[2],)), args[3],))
            results.append((rhs, "Mathlib: Metric_preimage_smul_sphere"))
        except Exception:
            pass
    return results


def _r0201_ball_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.ball_eq_empty
    # ball x ε = ∅ ↔ ε ≤ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ball", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OVar("empty"), args[1])), OLit(0)))
            results.append((rhs, "Mathlib: Metric_ball_eq_empty"))
        except Exception:
            pass
    return results


def _r0202_ball_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.ball_zero
    # ball x 0 = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ball", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Metric_ball_zero"))
        except Exception:
            pass
    return results


def _r0203_iUnion_ball_nat_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.iUnion_ball_nat_succ
    # ⋃ n : ℕ, ball x (n + 1) = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 6)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: Metric_iUnion_ball_nat_succ"))
        except Exception:
            pass
    return results


def _r0204_sphere_eq_empty_of_subsingleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.sphere_eq_empty_of_subsingleton
    # sphere x ε = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sphere", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Metric_sphere_eq_empty_of_subsingleton"))
        except Exception:
            pass
    return results


def _r0205_closedBall_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.closedBall_eq_empty
    # closedBall x ε = ∅ ↔ ε < 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closedBall", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("iff", (OVar("empty"), args[1])), OLit(0)))
            results.append((rhs, "Mathlib: Metric_closedBall_eq_empty"))
        except Exception:
            pass
    return results


def _r0206_closedBall_eq_sphere_of_nonpos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.closedBall_eq_sphere_of_nonpos
    # closedBall x ε = sphere x ε
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closedBall", 2)
    if args is not None:
        try:
            rhs = OOp("sphere", (args[0], args[1],))
            results.append((rhs, "Mathlib: Metric_closedBall_eq_sphere_of_nonpos"))
        except Exception:
            pass
    return results


def _r0207_sphere_union_ball(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.sphere_union_ball
    # sphere x ε ∪ ball x ε = closedBall x ε
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "union", 2)
    if args is not None:
        try:
            rhs = OOp("closedBall", (OVar("x"), OVar("e"),))
            results.append((rhs, "Mathlib: Metric_sphere_union_ball"))
        except Exception:
            pass
    return results


def _r0208_closedBall_diff_sphere(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.closedBall_diff_sphere
    # closedBall x ε \\ sphere x ε = ball x ε
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closedBall", 6)
    if args is not None:
        try:
            rhs = OOp("ball", (args[4], args[5],))
            results.append((rhs, "Mathlib: Metric_closedBall_diff_sphere"))
        except Exception:
            pass
    return results


def _r0209_closedBall_diff_ball(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.closedBall_diff_ball
    # closedBall x ε \\ ball x ε = sphere x ε
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closedBall", 6)
    if args is not None:
        try:
            rhs = OOp("sphere", (args[4], args[5],))
            results.append((rhs, "Mathlib: Metric_closedBall_diff_ball"))
        except Exception:
            pass
    return results


def _r0210_iUnion_inter_closedBall_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.iUnion_inter_closedBall_nat
    # ⋃ n : ℕ, s ∩ closedBall x n = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: Metric_iUnion_inter_closedBall_nat"))
        except Exception:
            pass
    return results


def _r0211_closure_sphere(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.closure_sphere
    # closure (sphere x ε) = sphere x ε
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("sphere", (OVar("x"), OVar("e"),))
            results.append((rhs, "Mathlib: Metric_closure_sphere"))
        except Exception:
            pass
    return results


def _r0212_symm_toSnowflaking(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.Snowflaking.symm_toSnowflaking
    # (toSnowflaking : X ≃ Snowflaking X α hα₀ hα₁).symm = ofSnowflaking
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toSnowflaking_colon_X_Snowflaking_X_a_ha_0_ha_1_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("ofSnowflaking")
            results.append((rhs, "Mathlib: Metric_Snowflaking_symm_toSnowflaking"))
    except Exception:
        pass
    return results


def _r0213_thickening_of_nonpos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.thickening_of_nonpos
    # thickening δ s = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "thickening", 2)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Metric_thickening_of_nonpos"))
        except Exception:
            pass
    return results


def _r0214_nhdsWithin_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpen.nhdsWithin_eq
    # 𝓝[s] a = 𝓝 a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (args[0],))
            results.append((rhs, "Mathlib: IsOpen_nhdsWithin_eq"))
        except Exception:
            pass
    return results


def _r0215_toFun_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOrderHom.toFun_eq_coe
    # f.toFun = (f : α → β)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("implies", (OOp("f", (OVar("colon"), OVar("a"),)), OVar("b")))
            results.append((rhs, "Mathlib: ContinuousOrderHom_toFun_eq_coe"))
    except Exception:
        pass
    return results


def _r0216_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOrderHom.ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: ContinuousOrderHom_ext"))
    except Exception:
        pass
    return results


def _r0217_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOrderHom.copy_eq
    # f.copy f' h = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_copy", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ContinuousOrderHom_copy_eq"))
        except Exception:
            pass
    return results


def _r0218_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOrderHom.comp_apply
    # (f.comp g) a = f (g a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp_g", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("g", (args[0],)),))
            results.append((rhs, "Mathlib: ContinuousOrderHom_comp_apply"))
        except Exception:
            pass
    return results


def _r0219_comp_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOrderHom.comp_assoc
    # (f.comp g).comp h = f.comp (g.comp h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp_g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("f_comp", (OOp("g_comp", (args[0],)),))
            results.append((rhs, "Mathlib: ContinuousOrderHom_comp_assoc"))
        except Exception:
            pass
    return results


def _r0220_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOrderHom.id_comp
    # (ContinuousOrderHom.id β).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ContinuousOrderHom_id_b_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ContinuousOrderHom_id_comp"))
        except Exception:
            pass
    return results


def _r0221_cancel_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOrderHom.cancel_right
    # g₁.comp f = g₂.comp f ↔ g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_1_comp", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("g_2_comp", (args[0],)), OVar("g_1"))), OVar("g_2")))
            results.append((rhs, "Mathlib: ContinuousOrderHom_cancel_right"))
        except Exception:
            pass
    return results


def _r0222_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.ext
    # s = t
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("t")
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_ext"))
    except Exception:
        pass
    return results


def _r0223_coe_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.coe_inf
    # (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_t", 3)
    if args is not None:
        try:
            rhs = OOp("inter", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_coe_inf"))
        except Exception:
            pass
    return results


def _r0224_coe_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.coe_top
    # (↑(⊤ : Closeds α) : Set α) = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Closeds_a", 3)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_coe_top"))
        except Exception:
            pass
    return results


def _r0225_coe_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.coe_eq_univ
    # (s : Set α) = univ ↔ s = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("univ"), OVar("s"))), OVar("top")))
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_coe_eq_univ"))
        except Exception:
            pass
    return results


def _r0226_coe_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.coe_bot
    # (↑(⊥ : Closeds α) : Set α) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_Closeds_a", 3)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_coe_bot"))
        except Exception:
            pass
    return results


def _r0227_coe_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.coe_eq_empty
    # (s : Set α) = ∅ ↔ s = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("s"))), OVar("bot")))
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_coe_eq_empty"))
        except Exception:
            pass
    return results


def _r0228_coe_sSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.coe_sSup
    # ((sSup S : Closeds α) : Set α) =     closure (⋃₀ ((↑) '' S))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sSup_S_colon_Closeds_a", 3)
    if args is not None:
        try:
            rhs = OOp("closure", (OOp("_0", (OOp("_unknown", (OVar("prime_prime"), OVar("S"),)),)),))
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_coe_sSup"))
        except Exception:
            pass
    return results


def _r0229_coe_finset_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.coe_finset_sup
    # (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sup_f", 3)
    if args is not None:
        try:
            rhs = OOp("s_sup", (OOp("comp", (OVar("_unknown"), OVar("f"))),))
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_coe_finset_sup"))
        except Exception:
            pass
    return results


def _r0230_coe_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.coe_iInf
    # ((⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_s_i_colon_Closeds_a", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("s"), OVar("i"),))
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_coe_iInf"))
        except Exception:
            pass
    return results


def _r0231_iInf_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.iInf_def
    # ⨅ i, s i = ⟨⋂ i, s i, isClosed_iInter fun i => (s i).2⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OVar("i_s_i_isClosed_iInter_fun_i_eq_gt_s_i_2")
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_iInf_def"))
        except Exception:
            pass
    return results


def _r0232_singleton_prod_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.singleton_prod_singleton
    # ({x} ×ˢ {y} : Closeds (α × β)) = {(x, y)}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 5)
    if args is not None:
        try:
            rhs = OVar("x_y")
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_singleton_prod_singleton"))
        except Exception:
            pass
    return results


def _r0233_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Clopens.ext
    # s = t
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("t")
            results.append((rhs, "Mathlib: TopologicalSpace_Clopens_ext"))
    except Exception:
        pass
    return results


def _r0234_coe_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Clopens.coe_inf
    # ↑(s ⊓ t) = (s ∩ t : Set α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("inter", (OVar("s"), OOp("t", (OVar("colon"), OVar("Set"), OVar("a"),))))
            results.append((rhs, "Mathlib: TopologicalSpace_Clopens_coe_inf"))
    except Exception:
        pass
    return results


def _r0235_coe_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Clopens.coe_top
    # (↑(⊤ : Clopens α) : Set α) = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Clopens_a", 3)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: TopologicalSpace_Clopens_coe_top"))
        except Exception:
            pass
    return results


def _r0236_coe_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Clopens.coe_bot
    # (↑(⊥ : Clopens α) : Set α) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_Clopens_a", 3)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: TopologicalSpace_Clopens_coe_bot"))
        except Exception:
            pass
    return results


def _r0237_coe_sdiff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Clopens.coe_sdiff
    # ↑(s \\ t) = (s \\ t : Set α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_bsl_t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s", (OVar("bsl"), OVar("t"), OVar("colon"), OVar("Set"), OVar("a"),))
            results.append((rhs, "Mathlib: TopologicalSpace_Clopens_coe_sdiff"))
    except Exception:
        pass
    return results


def _r0238_coe_himp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Clopens.coe_himp
    # ↑(s ⇨ t) = (s ⇨ t : Set α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_t")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s", (OVar("_unknown"), OVar("t"), OVar("colon"), OVar("Set"), OVar("a"),))
            results.append((rhs, "Mathlib: TopologicalSpace_Clopens_coe_himp"))
    except Exception:
        pass
    return results


def _r0239_coe_compl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Clopens.coe_compl
    # (↑sᶜ : Set α) = (↑s)ᶜ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 3)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: TopologicalSpace_Clopens_coe_compl"))
        except Exception:
            pass
    return results


def _r0240_coe_finset_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Clopens.coe_finset_sup
    # (↑(s.sup U) : Set α) = ⋃ i ∈ s, U i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sup_U", 3)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("U"), OVar("i"),))))
            results.append((rhs, "Mathlib: TopologicalSpace_Clopens_coe_finset_sup"))
        except Exception:
            pass
    return results


def _r0241_carrier_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.carrier_eq_coe
    # s.carrier = s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_carrier")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s")
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_carrier_eq_coe"))
    except Exception:
        pass
    return results


def _r0242_coe_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.coe_inf
    # (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_t", 3)
    if args is not None:
        try:
            rhs = OOp("inter", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_coe_inf"))
        except Exception:
            pass
    return results


def _r0243_coe_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.coe_top
    # (↑(⊤ : Compacts α) : Set α) = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Compacts_a", 3)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_coe_top"))
        except Exception:
            pass
    return results


def _r0244_coe_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.coe_bot
    # (↑(⊥ : Compacts α) : Set α) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_Compacts_a", 3)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_coe_bot"))
        except Exception:
            pass
    return results


def _r0245_coe_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.coe_eq_empty
    # (s : Set α) = ∅ ↔ s = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("s"))), OVar("bot")))
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_coe_eq_empty"))
        except Exception:
            pass
    return results


def _r0246_coe_finset_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.coe_finset_sup
    # (↑(s.sup f) : Set α) = s.sup fun i => ↑(f i)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sup_f", 3)
    if args is not None:
        try:
            rhs = OOp("s_sup", (OVar("fun"), OVar("i"), OVar("eq_gt"), OVar("f_i"),))
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_coe_finset_sup"))
        except Exception:
            pass
    return results


def _r0247_mem_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.mem_singleton
    # x ∈ ({y} : Compacts α) ↔ x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_mem_singleton"))
        except Exception:
            pass
    return results


def _r0248_toCloseds_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.toCloseds_singleton
    # toCloseds {x} = {x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCloseds", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_toCloseds_singleton"))
        except Exception:
            pass
    return results


def _r0249_map_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.map_id
    # K.map id continuous_id = K
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "K_map", 2)
    if args is not None:
        try:
            rhs = OVar("K")
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_map_id"))
        except Exception:
            pass
    return results


def _r0250_map_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.map_comp
    # K.map (f ∘ g) (hf.comp hg) = (K.map g hg).map f hf
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "K_map", 2)
    if args is not None:
        try:
            rhs = OOp("K_map_g_hg_map", (OVar("f"), OVar("hf"),))
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_map_comp"))
        except Exception:
            pass
    return results


def _r0251_equiv_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.equiv_trans
    # Compacts.equiv (f.trans g) = (Compacts.equiv f).trans (Compacts.equiv g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Compacts_equiv", 1)
    if args is not None:
        try:
            rhs = OOp("Compacts_equiv_f_trans", (OOp("Compacts_equiv", (OVar("g"),)),))
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_equiv_trans"))
        except Exception:
            pass
    return results


def _r0252_toCloseds_toCompacts(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.NonemptyCompacts.toCloseds_toCompacts
    # s.toCompacts.toCloseds = s.toCloseds
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_toCompacts_toCloseds")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_toCloseds")
            results.append((rhs, "Mathlib: TopologicalSpace_NonemptyCompacts_toCloseds_toCompacts"))
    except Exception:
        pass
    return results


def _r0253_carrier_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.NonemptyCompacts.carrier_eq_coe
    # s.carrier = s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_carrier")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s")
            results.append((rhs, "Mathlib: TopologicalSpace_NonemptyCompacts_carrier_eq_coe"))
    except Exception:
        pass
    return results


def _r0254_toCompacts_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.NonemptyCompacts.toCompacts_sup
    # (s ⊔ t).toCompacts = s.toCompacts ⊔ t.toCompacts
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_t_toCompacts")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s_toCompacts", (OVar("_unknown"), OVar("t_toCompacts"),))
            results.append((rhs, "Mathlib: TopologicalSpace_NonemptyCompacts_toCompacts_sup"))
    except Exception:
        pass
    return results


def _r0255_mem_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.NonemptyCompacts.mem_singleton
    # x ∈ ({y} : NonemptyCompacts α) ↔ x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: TopologicalSpace_NonemptyCompacts_mem_singleton"))
        except Exception:
            pass
    return results


def _r0256_toCloseds_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.NonemptyCompacts.toCloseds_singleton
    # toCloseds {x} = {x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCloseds", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: TopologicalSpace_NonemptyCompacts_toCloseds_singleton"))
        except Exception:
            pass
    return results


def _r0257_coe_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.NonemptyCompacts.coe_map
    # (s.map f hf : Set β) = f '' s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_map", 5)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("prime_prime"), OVar("s"),))
            results.append((rhs, "Mathlib: TopologicalSpace_NonemptyCompacts_coe_map"))
        except Exception:
            pass
    return results


def _r0258_carrier_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.PositiveCompacts.carrier_eq_coe
    # s.carrier = s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_carrier")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s")
            results.append((rhs, "Mathlib: TopologicalSpace_PositiveCompacts_carrier_eq_coe"))
    except Exception:
        pass
    return results


def _r0259_coe_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.PositiveCompacts.coe_top
    # (↑(⊤ : PositiveCompacts α) : Set α) = univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_PositiveCompacts_a", 3)
    if args is not None:
        try:
            rhs = OVar("univ")
            results.append((rhs, "Mathlib: TopologicalSpace_PositiveCompacts_coe_top"))
        except Exception:
            pass
    return results


def _r0260_map_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.PositiveCompacts.map_comp
    # K.map (f ∘ g) (hf.comp hg) (hf'.comp hg') = (K.map g hg hg').map f hf hf'
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "K_map", 3)
    if args is not None:
        try:
            rhs = OOp("K_map_g_hg_hg_prime_map", (OVar("f"), OVar("hf"), OVar("hf_prime"),))
            results.append((rhs, "Mathlib: TopologicalSpace_PositiveCompacts_map_comp"))
        except Exception:
            pass
    return results


def _r0261_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.CompactOpens.ext
    # s = t
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("t")
            results.append((rhs, "Mathlib: TopologicalSpace_CompactOpens_ext"))
    except Exception:
        pass
    return results


def _r0262_coe_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.CompactOpens.coe_bot
    # ↑(⊥ : CompactOpens α) = (∅ : Set α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_CompactOpens_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("empty", (OVar("colon"), OVar("Set"), OVar("a"),))
            results.append((rhs, "Mathlib: TopologicalSpace_CompactOpens_coe_bot"))
    except Exception:
        pass
    return results


def _r0263_coe_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_mk
    # ↑(⟨U, hU⟩ : Opens α) = U
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("U_hU_colon_Opens_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("U")
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_mk"))
    except Exception:
        pass
    return results


def _r0264_coe_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_sup
    # (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_t", 3)
    if args is not None:
        try:
            rhs = OOp("union", (OVar("s"), OVar("t")))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_sup"))
        except Exception:
            pass
    return results


def _r0265_coe_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_bot
    # ((⊥ : Opens α) : Set α) = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_Opens_a", 3)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_bot"))
        except Exception:
            pass
    return results


def _r0266_mk_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.mk_empty
    # (⟨∅, isOpen_empty⟩ : Opens α) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "empty_isOpen_empty", 3)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_mk_empty"))
        except Exception:
            pass
    return results


def _r0267_coe_eq_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_eq_empty
    # (U : Set α) = ∅ ↔ U = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "U", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("empty"), OVar("U"))), OVar("bot")))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_eq_empty"))
        except Exception:
            pass
    return results


def _r0268_coe_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_top
    # ((⊤ : Opens α) : Set α) = Set.univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Opens_a", 3)
    if args is not None:
        try:
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_top"))
        except Exception:
            pass
    return results


def _r0269_mk_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.mk_univ
    # (⟨univ, isOpen_univ⟩ : Opens α) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "univ_isOpen_univ", 3)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_mk_univ"))
        except Exception:
            pass
    return results


def _r0270_coe_eq_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_eq_univ
    # (U : Set α) = univ ↔ U = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "U", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("univ"), OVar("U"))), OVar("top")))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_eq_univ"))
        except Exception:
            pass
    return results


def _r0271_coe_sSup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_sSup
    # (↑(sSup S) : Set α) = ⋃ i ∈ S, ↑i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sSup_S", 3)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("S", (OVar("i"),))))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_sSup"))
        except Exception:
            pass
    return results


def _r0272_coe_finset_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_finset_sup
    # (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_sup_f", 3)
    if args is not None:
        try:
            rhs = OOp("s_sup", (OOp("comp", (OVar("_unknown"), OVar("f"))),))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_finset_sup"))
        except Exception:
            pass
    return results


def _r0273_coe_finset_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_finset_inf
    # (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_inf_f", 3)
    if args is not None:
        try:
            rhs = OOp("s_inf", (OOp("comp", (OVar("_unknown"), OVar("f"))),))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_finset_inf"))
        except Exception:
            pass
    return results


def _r0274_iSup_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.iSup_def
    # ⨆ i, s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OVar("i_s_i_isOpen_iUnion_fun_i_eq_gt_s_i_2")
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_iSup_def"))
        except Exception:
            pass
    return results


def _r0275_comap_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.comap_comp
    # comap (g.comp f) = (comap f).comp (comap g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 1)
    if args is not None:
        try:
            rhs = OOp("comap_f_comp", (OOp("comap", (OVar("g"),)),))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_comap_comp"))
        except Exception:
            pass
    return results


def _r0276_range_toUniformOnFunIsCompact(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.range_toUniformOnFunIsCompact
    # range (toUniformOnFunIsCompact) = {f : UniformOnFun α β {K | IsCompact K} | Continuous f}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "range", 1)
    if args is not None:
        try:
            rhs = OVar("f_colon_UniformOnFun_a_b_K_pipe_IsCompact_K_pipe_Continuous_f")
            results.append((rhs, "Mathlib: ContinuousMap_range_toUniformOnFunIsCompact"))
        except Exception:
            pass
    return results


def _r0277_inc_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsClosedSubgraph.inc_congr
    # H.Inc e x ↔ G.Inc e x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_Inc", 2)
    if args is not None:
        try:
            rhs = OOp("G_Inc", (args[0], args[1],))
            results.append((rhs, "Mathlib: IsClosedSubgraph_inc_congr"))
        except Exception:
            pass
    return results


def _r0278_coe_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAlgHom.coe_inj
    # (f : A →ₐ[R] B) = g ↔ f = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("f"), args[1]))
            results.append((rhs, "Mathlib: ContinuousAlgHom_coe_inj"))
        except Exception:
            pass
    return results


def _r0279_isInvertible_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.isInvertible_zero_iff
    # IsInvertible (0 : M →L[R] M₂) ↔ Subsingleton M ∧ Subsingleton M₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsInvertible", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("Subsingleton", (OVar("M"),)), OOp("Subsingleton", (OVar("M_2"),))))
            results.append((rhs, "Mathlib: ContinuousLinearMap_isInvertible_zero_iff"))
        except Exception:
            pass
    return results


def _r0280_mem_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.mem_map
    # x ∈ (map f).obj U ↔ f.hom x ∈ U
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("f_hom", (args[0],)), OVar("U")))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_mem_map"))
        except Exception:
            pass
    return results


def _r0281_nonempty_iff_nonempty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ConnectedComponents.nonempty_iff_nonempty
    # Nonempty (ConnectedComponents α) ↔ Nonempty α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Nonempty", 1)
    if args is not None:
        try:
            rhs = OOp("Nonempty", (OVar("a"),))
            results.append((rhs, "Mathlib: ConnectedComponents_nonempty_iff_nonempty"))
        except Exception:
            pass
    return results


def _r0282_isOpen_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.isOpen_image
    # IsOpen (h '' s) ↔ IsOpen s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsOpen", 1)
    if args is not None:
        try:
            rhs = OOp("IsOpen", (OVar("s"),))
            results.append((rhs, "Mathlib: Homeomorph_isOpen_image"))
        except Exception:
            pass
    return results


def _r0283_isClosed_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.isClosed_image
    # IsClosed (h '' s) ↔ IsClosed s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsClosed", 1)
    if args is not None:
        try:
            rhs = OOp("IsClosed", (OVar("s"),))
            results.append((rhs, "Mathlib: Homeomorph_isClosed_image"))
        except Exception:
            pass
    return results


def _r0284_comp_continuousAt_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.comp_continuousAt_iff
    # ContinuousAt (h ∘ f) z ↔ ContinuousAt f z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ContinuousAt", 2)
    if args is not None:
        try:
            rhs = OOp("ContinuousAt", (OVar("f"), args[1],))
            results.append((rhs, "Mathlib: Homeomorph_comp_continuousAt_iff"))
        except Exception:
            pass
    return results


def _r0285_tendsto_dist_right_atTop_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.tendsto_dist_right_atTop_iff
    # Tendsto (fun x ↦ dist (f x) c) l atTop ↔ Tendsto f l (cobounded α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Tendsto", 3)
    if args is not None:
        try:
            rhs = OOp("Tendsto", (OVar("f"), args[1], OOp("cobounded", (OVar("a"),)),))
            results.append((rhs, "Mathlib: Metric_tendsto_dist_right_atTop_iff"))
        except Exception:
            pass
    return results


def _r0286_le_infEDist(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.le_infEDist
    # d ≤ infEDist x s ↔ ∀ y ∈ s, d ≤ edist x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("in", (OOp("forall", (OVar("y"),)), OOp("s", (args[0],)))), OOp("edist", (OVar("x"), OVar("y"),))))
            results.append((rhs, "Mathlib: Metric_le_infEDist"))
        except Exception:
            pass
    return results


def _r0287_mem_ball_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Metric.mem_ball_comm
    # x ∈ ball y ε ↔ y ∈ ball x ε
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OVar("y"), OOp("ball", (args[0], OVar("e"),))))
            results.append((rhs, "Mathlib: Metric_mem_ball_comm"))
        except Exception:
            pass
    return results


def _r0288_inseparable_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.IsTopologicalBasis.inseparable_iff
    # Inseparable x y ↔ ∀ s ∈ b, (x ∈ s ↔ y ∈ s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Inseparable", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("s"),)), OOp("b", (OOp("iff", (OOp("in", (args[0], OVar("s"))), OOp("in", (args[1], OVar("s"))))),))))
            results.append((rhs, "Mathlib: TopologicalSpace_IsTopologicalBasis_inseparable_iff"))
        except Exception:
            pass
    return results


def _r0289_mem_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.mem_mk
    # x ∈ (⟨s, hs⟩ : Closeds α) ↔ x ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("s")))
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_mem_mk"))
        except Exception:
            pass
    return results


def _r0290_mem_closure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.mem_closure
    # x ∈ Closeds.closure s ↔ x ∈ closure s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OOp("closure", (OVar("s"),))))
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_mem_closure"))
        except Exception:
            pass
    return results


def _r0291_coe_nonempty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.coe_nonempty
    # (s : Set α).Nonempty ↔ s ≠ ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_colon_Set_a_Nonempty")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("!=", (OVar("s"), OVar("bot")))
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_coe_nonempty"))
    except Exception:
        pass
    return results


def _r0292_mem_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Closeds.mem_iInf
    # x ∈ iInf s ↔ ∀ i, x ∈ s i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("forall", (OVar("i"), args[0],)), OOp("s", (OVar("i"),))))
            results.append((rhs, "Mathlib: TopologicalSpace_Closeds_mem_iInf"))
        except Exception:
            pass
    return results


def _r0293_mem_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Clopens.mem_mk
    # x ∈ mk s h ↔ x ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("s")))
            results.append((rhs, "Mathlib: TopologicalSpace_Clopens_mem_mk"))
        except Exception:
            pass
    return results


def _r0294_mem_toCloseds(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.mem_toCloseds
    # x ∈ s.toCloseds ↔ x ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("s")))
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_mem_toCloseds"))
        except Exception:
            pass
    return results


def _r0295_coe_nonempty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.coe_nonempty
    # (s : Set α).Nonempty ↔ s ≠ ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_colon_Set_a_Nonempty")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("!=", (OVar("s"), OVar("bot")))
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_coe_nonempty"))
    except Exception:
        pass
    return results


def _r0296_map_injective_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Compacts.map_injective_iff
    # Function.Injective (Compacts.map f hf) ↔ Function.Injective f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "injective", 1)
    if args is not None:
        try:
            rhs = OOp("injective", (OVar("f"),))
            results.append((rhs, "Mathlib: TopologicalSpace_Compacts_map_injective_iff"))
        except Exception:
            pass
    return results


def _r0297_mem_toCompacts(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.NonemptyCompacts.mem_toCompacts
    # x ∈ s.toCompacts ↔ x ∈ s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("s")))
            results.append((rhs, "Mathlib: TopologicalSpace_NonemptyCompacts_mem_toCompacts"))
        except Exception:
            pass
    return results


def _r0298_mem_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.mem_mk
    # x ∈ mk U h ↔ x ∈ U
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OVar("U")))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_mem_mk"))
        except Exception:
            pass
    return results


def _r0299_nonempty_coeSort(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.nonempty_coeSort
    # Nonempty U ↔ (U : Set α).Nonempty
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Nonempty", 1)
    if args is not None:
        try:
            rhs = OVar("U_colon_Set_a_Nonempty")
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_nonempty_coeSort"))
        except Exception:
            pass
    return results


def _r0300_mem_interior(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.mem_interior
    # x ∈ Opens.interior s ↔ x ∈ _root_.interior s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (args[0], OOp("root_interior", (OVar("s"),))))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_mem_interior"))
        except Exception:
            pass
    return results


def _r0301_mem_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.mem_inf
    # x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("and", (OOp("in", (args[0], OVar("s"))), OOp("in", (args[0], OVar("t")))))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_mem_inf"))
        except Exception:
            pass
    return results


def _r0302_mem_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.mem_sup
    # x ∈ (s ⊔ t) ↔ x ∈ s ∨ x ∈ t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("or", (OOp("in", (args[0], OVar("s"))), OOp("in", (args[0], OVar("t")))))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_mem_sup"))
        except Exception:
            pass
    return results


def _r0303_mem_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.mem_bot
    # x ∈ (⊥ : Opens α) ↔ False
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OLit(False)
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_mem_bot"))
        except Exception:
            pass
    return results


def _r0304_coe_disjoint(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.coe_disjoint
    # Disjoint (s : Set α) t ↔ Disjoint s t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Disjoint", 2)
    if args is not None:
        try:
            rhs = OOp("Disjoint", (OVar("s"), args[1],))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_coe_disjoint"))
        except Exception:
            pass
    return results


def _r0305_mem_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopologicalSpace.Opens.mem_comap
    # x ∈ comap f U ↔ f x ∈ U
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("f", (args[0],)), OVar("U")))
            results.append((rhs, "Mathlib: TopologicalSpace_Opens_mem_comap"))
        except Exception:
            pass
    return results


def _r0306_Iobj_rho_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousCohomology.Iobj_ρ_apply
    # ((Iobj rep).ρ g).hom f x = (rep.ρ g).hom (f (g⁻¹ * x))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Iobj_rep_rho_g_hom", 2)
    if args is not None:
        try:
            rhs = OOp("rep_rho_g_hom", (OOp("f", (OOp("*", (OVar("ginv"), args[1])),)),))
            results.append((rhs, "Mathlib: ContinuousCohomology_Iobj_rho_apply"))
        except Exception:
            pass
    return results


def _r0307_d_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousCohomology.MultiInd.d_zero
    # d R G 0 = const R G
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d", 3)
    if args is not None:
        try:
            rhs = OOp("const", (args[0], args[1],))
            results.append((rhs, "Mathlib: ContinuousCohomology_MultiInd_d_zero"))
        except Exception:
            pass
    return results


def _r0308_d_succ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousCohomology.MultiInd.d_succ
    # d R G (n + 1) = whiskerLeft (functor R G (n + 1)) (const R G) -       (by exact whiskerRight (d R G n) (I R G))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d", 3)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("whiskerLeft", (OOp("functor", (args[0], args[1], OOp("+", (OVar("n"), OLit(1))),)), OOp("const", (args[0], args[1],)),)), OOp("by", (OVar("exact"), OVar("whiskerRight"), OOp("d", (args[0], args[1], OVar("n"),)), OOp("I", (args[0], args[1],)),))))
            results.append((rhs, "Mathlib: ContinuousCohomology_MultiInd_d_succ"))
        except Exception:
            pass
    return results


def _r0309_d_comp_d(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousCohomology.MultiInd.d_comp_d
    # d R G n ≫ d R G (n + 1) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "d", 8)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousCohomology_MultiInd_d_comp_d"))
        except Exception:
            pass
    return results


def _r0310_coe_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.coe_of
    # (of R M) = M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "of", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: TopModuleCat_coe_of"))
        except Exception:
            pass
    return results


def _r0311_hom_ofHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.hom_ofHom
    # (ofHom f).hom = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofHom_f_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: TopModuleCat_hom_ofHom"))
    except Exception:
        pass
    return results


def _r0312_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.ofHom_hom
    # ofHom f.hom = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: TopModuleCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0313_hom_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.hom_zero
    # (0 : M₁ ⟶ M₂).hom = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_M_1_M_2_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: TopModuleCat_hom_zero"))
    except Exception:
        pass
    return results


def _r0314_hom_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: hom_smul
    # (s • φ).hom = s • φ.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_phi_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s", (OVar("_unknown"), OVar("phi_hom"),))
            results.append((rhs, "Mathlib: hom_smul"))
    except Exception:
        pass
    return results


def _r0315_hom_forget_2_TopCat_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: hom_forget₂_TopCat_map
    # ((forget₂ _ TopCat).map f).hom = f.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("forget_2_TopCat_map_f_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_hom")
            results.append((rhs, "Mathlib: hom_forget_2_TopCat_map"))
    except Exception:
        pass
    return results


def _r0316_coe_freeObj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_freeObj
    # freeObj R X = (X →₀ R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "freeObj", 2)
    if args is not None:
        try:
            rhs = OOp("X", (OVar("to_0"), args[0],))
            results.append((rhs, "Mathlib: coe_freeObj"))
        except Exception:
            pass
    return results


def _r0317_keri_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TopModuleCat.kerι_comp
    # kerι φ ≫ φ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "keri", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: TopModuleCat_keri_comp"))
        except Exception:
            pass
    return results


def _r0318_hom_cokerpi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: hom_cokerπ
    # (cokerπ φ).hom x = Submodule.mkQ _ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cokerpi_phi_hom", 1)
    if args is not None:
        try:
            rhs = OOp("Submodule_mkQ", (OVar("_unknown"), args[0],))
            results.append((rhs, "Mathlib: hom_cokerpi"))
        except Exception:
            pass
    return results


def _r0319_comp_cokerpi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: comp_cokerπ
    # φ ≫ cokerπ φ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: comp_cokerpi"))
        except Exception:
            pass
    return results


def _r0320_range_pullbackSnd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.range_pullbackSnd
    # Set.range (pullback.snd f g) = g ⁻¹ᵁ f.opensRange
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("inv"), OVar("f_opensRange"),))
            results.append((rhs, "Mathlib: IsOpenImmersion_range_pullbackSnd"))
        except Exception:
            pass
    return results


def _r0321_opensRange_pullbackSnd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgebraicGeometry.Scheme.Hom.opensRange_pullbackSnd
    # (pullback.snd f g).opensRange = g ⁻¹ᵁ f.opensRange
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pullback_snd_f_g_opensRange")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g", (OVar("inv"), OVar("f_opensRange"),))
            results.append((rhs, "Mathlib: AlgebraicGeometry_Scheme_Hom_opensRange_pullbackSnd"))
    except Exception:
        pass
    return results


def _r0322_range_pullbackFst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.range_pullbackFst
    # Set.range (pullback.fst g f) = g ⁻¹ᵁ f.opensRange
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("inv"), OVar("f_opensRange"),))
            results.append((rhs, "Mathlib: IsOpenImmersion_range_pullbackFst"))
        except Exception:
            pass
    return results


def _r0323_opensRange_pullbackFst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgebraicGeometry.Scheme.Hom.opensRange_pullbackFst
    # (pullback.fst g f).opensRange = g ⁻¹ᵁ f.opensRange
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pullback_fst_g_f_opensRange")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g", (OVar("inv"), OVar("f_opensRange"),))
            results.append((rhs, "Mathlib: AlgebraicGeometry_Scheme_Hom_opensRange_pullbackFst"))
    except Exception:
        pass
    return results


def _r0324_range_pullback_to_base_of_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.range_pullback_to_base_of_left
    # Set.range (pullback.fst f g ≫ f) = Set.range f ∩ Set.range g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("Set_range", (OVar("f"),)), OOp("Set_range", (OVar("g"),))))
            results.append((rhs, "Mathlib: IsOpenImmersion_range_pullback_to_base_of_left"))
        except Exception:
            pass
    return results


def _r0325_range_pullback_to_base_of_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.range_pullback_to_base_of_right
    # Set.range (pullback.fst g f ≫ g) = Set.range g ∩ Set.range f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Set_range", 1)
    if args is not None:
        try:
            rhs = OOp("inter", (OOp("Set_range", (OVar("g"),)), OOp("Set_range", (OVar("f"),))))
            results.append((rhs, "Mathlib: IsOpenImmersion_range_pullback_to_base_of_right"))
        except Exception:
            pass
    return results


def _r0326_image_preimage_eq_preimage_image_of_isPu(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    # iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV ''ᵁ W
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iU", 4)
    if args is not None:
        try:
            rhs = OOp("f", (args[2], OVar("iV"), args[0], args[3],))
            results.append((rhs, "Mathlib: IsOpenImmersion_image_preimage_eq_preimage_image_of_isPullback"))
        except Exception:
            pass
    return results


def _r0327_lift_fac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.lift_fac
    # lift f g H' ≫ f = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 5)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: IsOpenImmersion_lift_fac"))
        except Exception:
            pass
    return results


def _r0328_comp_lift(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.comp_lift
    # g' ≫ lift f g H = lift f (g' ≫ g) (.trans (by simp [Set.range_comp_subset_range]) H)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_prime", 5)
    if args is not None:
        try:
            rhs = OOp("lift", (args[2], OOp("g_prime", (args[0], args[3],)), OOp("trans", (OOp("by", (OVar("simp"), OSeq((OVar("Set_range_comp_subset_range"),)),)), args[4],)),))
            results.append((rhs, "Mathlib: IsOpenImmersion_comp_lift"))
        except Exception:
            pass
    return results


def _r0329_isoOfRangeEq_hom_fac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.isoOfRangeEq_hom_fac
    # (isoOfRangeEq f g e).hom ≫ g = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "isoOfRangeEq_f_g_e_hom", 2)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: IsOpenImmersion_isoOfRangeEq_hom_fac"))
        except Exception:
            pass
    return results


def _r0330_isoOfRangeEq_inv_fac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.isoOfRangeEq_inv_fac
    # (isoOfRangeEq f g e).inv ≫ f = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "isoOfRangeEq_f_g_e_inv", 2)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: IsOpenImmersion_isoOfRangeEq_inv_fac"))
        except Exception:
            pass
    return results


def _r0331_app_eq_invApp_app_of_comp_eq_aux(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux
    # f ⁻¹ᵁ V = fg ⁻¹ᵁ (g ''ᵁ V)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("fg", (args[0], OOp("g", (OVar("prime_prime"), args[1],)),))
            results.append((rhs, "Mathlib: IsOpenImmersion_app_eq_invApp_app_of_comp_eq_aux"))
        except Exception:
            pass
    return results


def _r0332_app_eq_appIso_inv_app_of_comp_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq
    # f.app V = (g.appIso V).inv ≫ fg.app (g ''ᵁ V) ≫ Y.presheaf.map       (eqToHom <| IsOpenImmersion.app_eq_invApp_app_of_co
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_app", 1)
    if args is not None:
        try:
            rhs = OOp("g_appIso_V_inv", (OVar("_unknown"), OVar("fg_app"), OOp("g", (OVar("prime_prime"), args[0],)), OVar("_unknown"), OVar("Y_presheaf_map"), OVar("eqToHom_lt_pipe_IsOpenImmersion_app_eq_invApp_app_of_comp_eq_aux_f_g_fg_H_V_op"),))
            results.append((rhs, "Mathlib: IsOpenImmersion_app_eq_appIso_inv_app_of_comp_eq"))
        except Exception:
            pass
    return results


def _r0333_lift_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.lift_app
    # (lift f g H).app V = (f.appIso V).inv ≫ g.app (f ''ᵁ V) ≫       X.presheaf.map (eqToHom <| app_eq_invApp_app_of_comp_eq_
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift_f_g_H_app", 1)
    if args is not None:
        try:
            rhs = OOp("f_appIso_V_inv", (OVar("_unknown"), OVar("g_app"), OOp("f", (OVar("prime_prime"), args[0],)), OVar("_unknown"), OVar("X_presheaf_map"), OVar("eqToHom_lt_pipe_app_eq_invApp_app_of_comp_eq_aux_lift_fac_symm_V_op"),))
            results.append((rhs, "Mathlib: IsOpenImmersion_lift_app"))
        except Exception:
            pass
    return results


def _r0334_GIso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.ΓIso_inv
    # (ΓIso f U).inv = f.appLE (f.opensRange ⊓ U) (f ⁻¹ᵁ U)       (by rw [← f.image_preimage_eq_opensRange_inf, f.preimage_ima
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("GIso_f_U_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_appLE", (OOp("f_opensRange", (OVar("_unknown"), OVar("U"),)), OOp("f", (OVar("inv"), OVar("U"),)), OOp("by", (OVar("rw"), OVar("from_f_image_preimage_eq_opensRange_inf_f_preimage_image_eq"),)),))
            results.append((rhs, "Mathlib: IsOpenImmersion_GIso_inv"))
    except Exception:
        pass
    return results


def _r0335_map_GIso_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.map_ΓIso_inv
    # Y.presheaf.map (homOfLE inf_le_right).op ≫ (ΓIso f U).inv = f.app U
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Y_presheaf_map", 3)
    if args is not None:
        try:
            rhs = OOp("f_app", (OVar("U"),))
            results.append((rhs, "Mathlib: IsOpenImmersion_map_GIso_inv"))
        except Exception:
            pass
    return results


def _r0336_app_GIso_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpenImmersion.app_ΓIso_hom
    # f.app U ≫ (ΓIso f U).hom = Y.presheaf.map (homOfLE inf_le_right).op
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_app", 3)
    if args is not None:
        try:
            rhs = OOp("Y_presheaf_map", (OVar("homOfLE_inf_le_right_op"),))
            results.append((rhs, "Mathlib: IsOpenImmersion_app_GIso_hom"))
        except Exception:
            pass
    return results


def _r0337_hcast_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.Homotopy.hcast_def
    # hcast hx₀ = eqToHom (FundamentalGroupoid.ext hx₀)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hcast", 1)
    if args is not None:
        try:
            rhs = OOp("eqToHom", (OOp("FundamentalGroupoid_ext", (args[0],)),))
            results.append((rhs, "Mathlib: ContinuousMap_Homotopy_hcast_def"))
        except Exception:
            pass
    return results


def _r0338_start_path(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.Homotopy.start_path
    # f x₀ = g x₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("x_2"),))
            results.append((rhs, "Mathlib: ContinuousMap_Homotopy_start_path"))
        except Exception:
            pass
    return results


def _r0339_end_path(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.Homotopy.end_path
    # f x₁ = g x₃
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("x_3"),))
            results.append((rhs, "Mathlib: ContinuousMap_Homotopy_end_path"))
        except Exception:
            pass
    return results


def _r0340_eq_path_of_eq_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.Homotopy.eq_path_of_eq_image
    # (πₘ (TopCat.ofHom f)).map ⟦p⟧ =         hcast (start_path hfg) ≫ (πₘ (TopCat.ofHom g)).map ⟦q⟧ ≫ hcast (end_path hfg).sy
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pi_TopCat_ofHom_f_map", 1)
    if args is not None:
        try:
            rhs = OOp("hcast", (OOp("start_path", (OVar("hfg"),)), OVar("_unknown"), OVar("pi_TopCat_ofHom_g_map"), OVar("q"), OVar("_unknown"), OVar("hcast"), OVar("end_path_hfg_symm"),))
            results.append((rhs, "Mathlib: ContinuousMap_Homotopy_eq_path_of_eq_image"))
        except Exception:
            pass
    return results


def _r0341_compAlongComposition_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMultilinearMap.compAlongComposition_apply
    # (f.compAlongComposition p c) v = f (p.applyComposition c v)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_compAlongComposition_p_c", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("p_applyComposition", (OVar("c"), args[0],)),))
            results.append((rhs, "Mathlib: ContinuousMultilinearMap_compAlongComposition_apply"))
        except Exception:
            pass
    return results


def _r0342_iteratedFDeriv_comp_diagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal
    # iteratedFDeriv 𝕜 n (fun x ↦ f (fun _ ↦ x)) x v = ∑ σ : Perm (Fin n), f (fun i ↦ v (σ i))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iteratedFDeriv", 5)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("sig"), OVar("colon"), OVar("Perm"), OVar("Fin_n"), OVar("f"), OOp("fun", (OVar("i"), args[0], args[4], OOp("sig", (OVar("i"),)),)),))
            results.append((rhs, "Mathlib: ContinuousMultilinearMap_iteratedFDeriv_comp_diagonal"))
        except Exception:
            pass
    return results


def _r0343_fpowerSeries_radius(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fpowerSeries_radius
    # (f.fpowerSeries x).radius = ∞
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_fpowerSeries_x_radius")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("inf")
            results.append((rhs, "Mathlib: ContinuousLinearMap_fpowerSeries_radius"))
    except Exception:
        pass
    return results


def _r0344_uncurryBilinear_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.uncurryBilinear_apply
    # f.uncurryBilinear m = f (m 0).1 (m 1).2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_uncurryBilinear", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("m_0_1"), OVar("m_1_2"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_uncurryBilinear_apply"))
        except Exception:
            pass
    return results


def _r0345_fpowerSeriesBilinear_apply_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fpowerSeriesBilinear_apply_zero
    # fpowerSeriesBilinear f x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ (f x.1 x.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpowerSeriesBilinear", 3)
    if args is not None:
        try:
            rhs = OOp("ContinuousMultilinearMap_uncurry0", (OVar("_unknown"), OVar("_unknown"), OOp("f", (OVar("x_1"), OVar("x_2"),)),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_fpowerSeriesBilinear_apply_zero"))
        except Exception:
            pass
    return results


def _r0346_fpowerSeriesBilinear_apply_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fpowerSeriesBilinear_apply_one
    # fpowerSeriesBilinear f x 1 = (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpowerSeriesBilinear", 3)
    if args is not None:
        try:
            rhs = OOp("continuousMultilinearCurryFin1_E_times_F_G_symm", (OOp("f_deriv_2", (args[1],)),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_fpowerSeriesBilinear_apply_one"))
        except Exception:
            pass
    return results


def _r0347_fpowerSeriesBilinear_apply_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fpowerSeriesBilinear_apply_two
    # fpowerSeriesBilinear f x 2 = f.uncurryBilinear
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpowerSeriesBilinear", 3)
    if args is not None:
        try:
            rhs = OVar("f_uncurryBilinear")
            results.append((rhs, "Mathlib: ContinuousLinearMap_fpowerSeriesBilinear_apply_two"))
        except Exception:
            pass
    return results


def _r0348_fpowerSeriesBilinear_apply_add_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fpowerSeriesBilinear_apply_add_three
    # fpowerSeriesBilinear f x (n + 3) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fpowerSeriesBilinear", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousLinearMap_fpowerSeriesBilinear_apply_add_three"))
        except Exception:
            pass
    return results


def _r0349_fpowerSeriesBilinear_radius(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fpowerSeriesBilinear_radius
    # (f.fpowerSeriesBilinear x).radius = ∞
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_fpowerSeriesBilinear_x_radius")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("inf")
            results.append((rhs, "Mathlib: ContinuousLinearMap_fpowerSeriesBilinear_radius"))
    except Exception:
        pass
    return results


def _r0350_isBigO_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.isBigO_congr
    # f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("O_b", (OVar("g"),)), OOp("f_comp_e", (OVar("eq_O_e_symm_b"), OOp("comp", (OVar("g"), OVar("e"))),))))
            results.append((rhs, "Mathlib: Homeomorph_isBigO_congr"))
    except Exception:
        pass
    return results


def _r0351_isLittleO_congr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Homeomorph.isLittleO_congr
    # f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("o_b", (OVar("g"),)), OOp("f_comp_e", (OVar("eq_o_e_symm_b"), OOp("comp", (OVar("g"), OVar("e"))),))))
            results.append((rhs, "Mathlib: Homeomorph_isLittleO_congr"))
    except Exception:
        pass
    return results


def _r0352_isBigOWith_principal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOn.isBigOWith_principal
    # IsBigOWith (sSup (Norm.norm '' (f '' s)) / ‖c‖) (𝓟 s) f fun _ => c
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "IsBigOWith", 5)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("c"),))
            results.append((rhs, "Mathlib: ContinuousOn_isBigOWith_principal"))
        except Exception:
            pass
    return results


def _r0353_isBigO_principal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOn.isBigO_principal
    # f =O[𝓟 s] fun _ => c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("O_s", (OVar("fun"), OVar("_unknown"), OVar("eq_gt"), OVar("c"),))
            results.append((rhs, "Mathlib: ContinuousOn_isBigO_principal"))
    except Exception:
        pass
    return results


def _r0354_isBigOTVS_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.isBigOTVS_id
    # f =O[𝕜; l] id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("O_l", (OVar("id"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_isBigOTVS_id"))
    except Exception:
        pass
    return results


def _r0355_isBigOTVS_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.isBigOTVS_comp
    # (g ∘ f) =O[𝕜; l] f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("O_l", (args[1],))
            results.append((rhs, "Mathlib: ContinuousLinearMap_isBigOTVS_comp"))
        except Exception:
            pass
    return results


def _r0356_isBigOTVS_fun_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.isBigOTVS_fun_comp
    # (g <| f ·) =O[𝕜; l] f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g", 3)
    if args is not None:
        try:
            rhs = OOp("O_l", (args[1],))
            results.append((rhs, "Mathlib: ContinuousLinearMap_isBigOTVS_fun_comp"))
        except Exception:
            pass
    return results


def _r0357_isThetaTVS_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.isThetaTVS_comp
    # (g ∘ f) =Θ[𝕜; l] f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = OOp("l", (args[1],))
            results.append((rhs, "Mathlib: ContinuousLinearMap_isThetaTVS_comp"))
        except Exception:
            pass
    return results


def _r0358_isTheta_principal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousOn.isTheta_principal
    # f =Θ[𝓟 s] fun _ => c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s", (OVar("fun"), OVar("_unknown"), OVar("eq_gt"), OVar("c"),))
            results.append((rhs, "Mathlib: ContinuousOn_isTheta_principal"))
    except Exception:
        pass
    return results


def _r0359_toNNReal_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.toNNReal_apply
    # f.toNNReal x = (f x).toNNReal
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toNNReal", 1)
    if args is not None:
        try:
            rhs = OVar("f_x_toNNReal")
            results.append((rhs, "Mathlib: ContinuousMap_toNNReal_apply"))
        except Exception:
            pass
    return results


def _r0360_toNNReal_mul_add_neg_mul_add_mul_neg_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.toNNReal_mul_add_neg_mul_add_mul_neg_eq
    # (f * g).toNNReal + (-f).toNNReal * g.toNNReal + f.toNNReal * (-g).toNNReal =       (-(f * g)).toNNReal + f.toNNReal * g.
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("minus_f_star_g_toNNReal"), OOp("+", (OOp("*", (OVar("f_toNNReal"), OVar("g_toNNReal"))), OOp("*", (OVar("minus_f_toNNReal"), OVar("minus_g_toNNReal")))))))
            results.append((rhs, "Mathlib: ContinuousMap_toNNReal_mul_add_neg_mul_add_mul_neg_eq"))
        except Exception:
            pass
    return results


def _r0361_toNNReal_algebraMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.toNNReal_algebraMap
    # (algebraMap ℝ C(X, ℝ) r).toNNReal = algebraMap ℝ≥0 C(X, ℝ≥0) r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("algebraMap_C_X_r_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("algebraMap", (OVar("ge_0"), OVar("C_X_ge_0"), OVar("r"),))
            results.append((rhs, "Mathlib: ContinuousMap_toNNReal_algebraMap"))
    except Exception:
        pass
    return results


def _r0362_toNNReal_neg_algebraMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMap.toNNReal_neg_algebraMap
    # (- algebraMap ℝ C(X, ℝ) r).toNNReal = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_algebraMap_C_X_r_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousMap_toNNReal_neg_algebraMap"))
    except Exception:
        pass
    return results


def _r0363_toNNReal_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMapZero.toNNReal_apply
    # f.toNNReal x = Real.toNNReal (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toNNReal", 1)
    if args is not None:
        try:
            rhs = OOp("Real_toNNReal", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: ContinuousMapZero_toNNReal_apply"))
        except Exception:
            pass
    return results


def _r0364_toContinuousMapHom_toNNReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMapZero.toContinuousMapHom_toNNReal
    # (toContinuousMapHom (X := X) (R := ℝ) f).toNNReal =       toContinuousMapHom (X := X) (R := ℝ≥0) f.toNNReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toContinuousMapHom_X_colon_eq_X_R_colon_eq_f_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("toContinuousMapHom", (OOp("X", (OVar("colon_eq"), OVar("X"),)), OOp("R", (OVar("colon_eq"), OVar("ge_0"),)), OVar("f_toNNReal"),))
            results.append((rhs, "Mathlib: ContinuousMapZero_toContinuousMapHom_toNNReal"))
    except Exception:
        pass
    return results


def _r0365_toNNReal_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMapZero.toNNReal_smul
    # (r • f).toNNReal = r • f.toNNReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_f_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("r", (OVar("_unknown"), OVar("f_toNNReal"),))
            results.append((rhs, "Mathlib: ContinuousMapZero_toNNReal_smul"))
    except Exception:
        pass
    return results


def _r0366_toNNReal_neg_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMapZero.toNNReal_neg_smul
    # (-(r • f)).toNNReal = r • (-f).toNNReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_r_f_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("r", (OVar("_unknown"), OVar("minus_f_toNNReal"),))
            results.append((rhs, "Mathlib: ContinuousMapZero_toNNReal_neg_smul"))
    except Exception:
        pass
    return results


def _r0367_toNNReal_add_add_neg_add_neg_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMapZero.toNNReal_add_add_neg_add_neg_eq
    # ((f + g).toNNReal + (-f).toNNReal + (-g).toNNReal) =       ((-(f + g)).toNNReal + f.toNNReal + g.toNNReal)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("minus_f_plus_g_toNNReal"), OOp("+", (OVar("f_toNNReal"), OVar("g_toNNReal")))))
            results.append((rhs, "Mathlib: ContinuousMapZero_toNNReal_add_add_neg_add_neg_eq"))
        except Exception:
            pass
    return results


def _r0368_opNorm_mul_flip_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.opNorm_mul_flip_apply
    # ‖(mul 𝕜 E).flip a‖ = ‖a‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mul_E_flip", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ContinuousLinearMap_opNorm_mul_flip_apply"))
        except Exception:
            pass
    return results


def _r0369_opNNNorm_mul_flip_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.opNNNorm_mul_flip_apply
    # ‖(mul 𝕜 E).flip a‖₊ = ‖a‖₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mul_E_flip", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ContinuousLinearMap_opNNNorm_mul_flip_apply"))
        except Exception:
            pass
    return results


def _r0370_exists_contDiff_support_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IsOpen.exists_contDiff_support_eq
    # ∃ f : E → ℝ, f.support = s ∧ ContDiff ℝ n f ∧ Set.range f ⊆ Set.Icc 0 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 1)
    if args is not None:
        try:
            rhs = OOp("and", (OVar("s"), OOp("and", (OOp("ContDiff", (OVar("_unknown"), OVar("n"), OVar("f"),)), OOp("subset", (OOp("Set_range", (OVar("f"),)), OOp("Set_Icc", (OLit(0), OLit(1),))))))))
            results.append((rhs, "Mathlib: IsOpen_exists_contDiff_support_eq"))
        except Exception:
            pass
    return results


def _r0371_iteratedFDerivWithin_comp_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.iteratedFDerivWithin_comp_left
    # iteratedFDerivWithin 𝕜 i (g ∘ f) s x =       g.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iteratedFDerivWithin", 5)
    if args is not None:
        try:
            rhs = OOp("g_compContinuousMultilinearMap", (OOp("iteratedFDerivWithin", (args[0], args[1], OVar("f"), args[3], args[4],)),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_iteratedFDerivWithin_comp_left"))
        except Exception:
            pass
    return results


def _r0372_iteratedFDeriv_comp_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.iteratedFDeriv_comp_left
    # iteratedFDeriv 𝕜 i (g ∘ f) x = g.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iteratedFDeriv", 4)
    if args is not None:
        try:
            rhs = OOp("g_compContinuousMultilinearMap", (OOp("iteratedFDeriv", (args[0], args[1], OVar("f"), args[3],)),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_iteratedFDeriv_comp_left"))
        except Exception:
            pass
    return results


def _r0373_iteratedFDerivWithin_comp_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.iteratedFDerivWithin_comp_left
    # iteratedFDerivWithin 𝕜 i (g ∘ f) s x =       (g : F →L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iteratedFDerivWithin", 5)
    if args is not None:
        try:
            rhs = OOp("g_colon_F_to_L_G_compContinuousMultilinearMap", (OOp("iteratedFDerivWithin", (args[0], args[1], OVar("f"), args[3], args[4],)),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_iteratedFDerivWithin_comp_left"))
        except Exception:
            pass
    return results


def _r0374_iteratedFDeriv_comp_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.iteratedFDeriv_comp_left
    # iteratedFDeriv 𝕜 i (g ∘ f) x =       g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iteratedFDeriv", 4)
    if args is not None:
        try:
            rhs = OOp("g_toContinuousLinearMap_compContinuousMultilinearMap", (OOp("iteratedFDeriv", (args[0], args[1], OVar("f"), args[3],)),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_iteratedFDeriv_comp_left"))
        except Exception:
            pass
    return results


def _r0375_iteratedFDerivWithin_comp_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.iteratedFDerivWithin_comp_right
    # iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =       (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iteratedFDerivWithin", 5)
    if args is not None:
        try:
            rhs = OOp("iteratedFDerivWithin_i_f_s_g_x_compContinuousLinearMap", (OVar("fun"), args[0], OVar("eq_gt"), OVar("g"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_iteratedFDerivWithin_comp_right"))
        except Exception:
            pass
    return results


def _r0376_iteratedFDerivWithin_comp_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.iteratedFDerivWithin_comp_right
    # iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =       (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ 
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iteratedFDerivWithin", 5)
    if args is not None:
        try:
            rhs = OOp("iteratedFDerivWithin_i_f_s_g_x_compContinuousLinearMap", (OVar("fun"), args[0], OVar("eq_gt"), OVar("g"),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_iteratedFDerivWithin_comp_right"))
        except Exception:
            pass
    return results


def _r0377_iteratedFDeriv_comp_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.iteratedFDeriv_comp_right
    # iteratedFDeriv 𝕜 i (f ∘ g) x =       (iteratedFDeriv 𝕜 i f (g x)).compContinuousLinearMap fun _ => g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iteratedFDeriv", 4)
    if args is not None:
        try:
            rhs = OOp("iteratedFDeriv_i_f_g_x_compContinuousLinearMap", (OVar("fun"), args[0], OVar("eq_gt"), OVar("g"),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_iteratedFDeriv_comp_right"))
        except Exception:
            pass
    return results


def _r0378_fderiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Continuous.fderiv
    # Continuous fun x => fderiv 𝕜 (f x) (g x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Continuous", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("fderiv"), OVar("_unknown"), OOp("f", (args[1],)), OOp("g", (args[1],)),))
            results.append((rhs, "Mathlib: Continuous_fderiv"))
        except Exception:
            pass
    return results


def _r0379_fderiv_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Continuous.fderiv_one
    # Continuous fun x => _root_.fderiv 𝕜 (f x) (g x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Continuous", 2)
    if args is not None:
        try:
            rhs = OOp("gt", (OVar("root_fderiv"), OVar("_unknown"), OOp("f", (args[1],)), OOp("g", (args[1],)),))
            results.append((rhs, "Mathlib: Continuous_fderiv_one"))
        except Exception:
            pass
    return results


def _r0380_dslope_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.dslope_comp
    # dslope (f ∘ g) a b = f (dslope g a b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dslope", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("dslope", (OVar("g"), args[1], args[2],)),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_dslope_comp"))
        except Exception:
            pass
    return results


def _r0381_deriv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.deriv
    # deriv e x = e 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "deriv", 2)
    if args is not None:
        try:
            rhs = OOp("e", (OLit(1),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_deriv"))
        except Exception:
            pass
    return results


def _r0382_derivWithin_of_bilinear(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.derivWithin_of_bilinear
    # derivWithin (fun y => B (u y) (v y)) s x =       B (u x) (derivWithin v s x) + B (derivWithin u s x) (v x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "derivWithin", 3)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("B", (OOp("u", (args[2],)), OOp("derivWithin", (OVar("v"), args[1], args[2],)),)), OOp("B", (OOp("derivWithin", (OVar("u"), args[1], args[2],)), OOp("v", (args[2],)),))))
            results.append((rhs, "Mathlib: ContinuousLinearMap_derivWithin_of_bilinear"))
        except Exception:
            pass
    return results


def _r0383_deriv_of_bilinear(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.deriv_of_bilinear
    # deriv (fun y => B (u y) (v y)) x = B (u x) (deriv v x) + B (deriv u x) (v x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "deriv", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("B", (OOp("u", (args[1],)), OOp("deriv", (OVar("v"), args[1],)),)), OOp("B", (OOp("deriv", (OVar("u"), args[1],)), OOp("v", (args[1],)),))))
            results.append((rhs, "Mathlib: ContinuousLinearMap_deriv_of_bilinear"))
        except Exception:
            pass
    return results


def _r0384_fderiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousAffineMap.fderiv
    # fderiv 𝕜 f x = f.contLinear
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderiv", 3)
    if args is not None:
        try:
            rhs = OVar("f_contLinear")
            results.append((rhs, "Mathlib: ContinuousAffineMap_fderiv"))
        except Exception:
            pass
    return results


def _r0385_changeOriginSeries_support(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMultilinearMap.changeOriginSeries_support
    # f.toFormalMultilinearSeries.changeOriginSeries k l = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toFormalMultilinearSeries_changeOriginSeries", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ContinuousMultilinearMap_changeOriginSeries_support"))
        except Exception:
            pass
    return results


def _r0386_changeOrigin_toFormalMultilinearSeries(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMultilinearMap.changeOrigin_toFormalMultilinearSeries
    # continuousMultilinearCurryFin1 𝕜 (∀ i, E i) F (f.toFormalMultilinearSeries.changeOrigin x 1) =     f.linearDeriv x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "continuousMultilinearCurryFin1", 4)
    if args is not None:
        try:
            rhs = OOp("f_linearDeriv", (OVar("x"),))
            results.append((rhs, "Mathlib: ContinuousMultilinearMap_changeOrigin_toFormalMultilinearSeries"))
        except Exception:
            pass
    return results


def _r0387_succ_embeddingFinSucc_fst_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Equiv.succ_embeddingFinSucc_fst_symm_apply
    # Fin.succ ((Equiv.embeddingFinSucc n ι e).1.toEquivRange.symm ⟨k, h'k⟩)       = e.toEquivRange.symm ⟨k, hk⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Fin_succ", 1)
    if args is not None:
        try:
            rhs = OOp("e_toEquivRange_symm", (OVar("k_hk"),))
            results.append((rhs, "Mathlib: Equiv_succ_embeddingFinSucc_fst_symm_apply"))
        except Exception:
            pass
    return results


def _r0388_iteratedFDeriv_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousMultilinearMap.iteratedFDeriv_eq
    # iteratedFDeriv 𝕜 n f = f.iteratedFDeriv n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iteratedFDeriv", 3)
    if args is not None:
        try:
            rhs = OOp("f_iteratedFDeriv", (args[1],))
            results.append((rhs, "Mathlib: ContinuousMultilinearMap_iteratedFDeriv_eq"))
        except Exception:
            pass
    return results


def _r0389_fderivWithin_of_bilinear(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fderivWithin_of_bilinear
    # fderivWithin 𝕜 (fun y => B (f y) (g y)) s x =       B.precompR G' (f x) (fderivWithin 𝕜 g s x) + B.precompL G' (fderivWi
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderivWithin", 4)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("B_precompR", (OVar("G_prime"), OOp("f", (args[3],)), OOp("fderivWithin", (args[0], OVar("g"), args[2], args[3],)),)), OOp("B_precompL", (OVar("G_prime"), OOp("fderivWithin", (args[0], OVar("f"), args[2], args[3],)), OOp("g", (args[3],)),))))
            results.append((rhs, "Mathlib: ContinuousLinearMap_fderivWithin_of_bilinear"))
        except Exception:
            pass
    return results


def _r0390_fderiv_of_bilinear(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fderiv_of_bilinear
    # fderiv 𝕜 (fun y => B (f y) (g y)) x =       B.precompR G' (f x) (fderiv 𝕜 g x) + B.precompL G' (fderiv 𝕜 f x) (g x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderiv", 3)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("B_precompR", (OVar("G_prime"), OOp("f", (args[2],)), OOp("fderiv", (args[0], OVar("g"), args[2],)),)), OOp("B_precompL", (OVar("G_prime"), OOp("fderiv", (args[0], OVar("f"), args[2],)), OOp("g", (args[2],)),))))
            results.append((rhs, "Mathlib: ContinuousLinearMap_fderiv_of_bilinear"))
        except Exception:
            pass
    return results


def _r0391_fderiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.fderiv
    # fderiv 𝕜 iso x = iso
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderiv", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_fderiv"))
        except Exception:
            pass
    return results


def _r0392_fderivWithin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.fderivWithin
    # fderivWithin 𝕜 iso s x = iso
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderivWithin", 4)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_fderivWithin"))
        except Exception:
            pass
    return results


def _r0393_comp_fderivWithin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.comp_fderivWithin
    # fderivWithin 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderivWithin 𝕜 f s x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderivWithin", 4)
    if args is not None:
        try:
            rhs = OOp("iso_colon_E_to_L_F_comp", (OOp("fderivWithin", (args[0], OVar("f"), args[2], args[3],)),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_comp_fderivWithin"))
        except Exception:
            pass
    return results


def _r0394_comp_fderiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.comp_fderiv
    # fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderiv", 3)
    if args is not None:
        try:
            rhs = OOp("iso_colon_E_to_L_F_comp", (OOp("fderiv", (args[0], OVar("f"), args[2],)),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_comp_fderiv"))
        except Exception:
            pass
    return results


def _r0395_comp_right_fderivWithin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.comp_right_fderivWithin
    # fderivWithin 𝕜 (f ∘ iso) (iso ⁻¹' s) x =       (fderivWithin 𝕜 f s (iso x)).comp (iso : E →L[𝕜] F)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderivWithin", 4)
    if args is not None:
        try:
            rhs = OOp("fderivWithin_f_s_iso_x_comp", (OOp("iso", (OVar("colon"), OVar("E"), OVar("to_L"), OVar("F"),)),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_comp_right_fderivWithin"))
        except Exception:
            pass
    return results


def _r0396_comp_right_fderiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearEquiv.comp_right_fderiv
    # fderiv 𝕜 (f ∘ iso) x = (fderiv 𝕜 f (iso x)).comp (iso : E →L[𝕜] F)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderiv", 3)
    if args is not None:
        try:
            rhs = OOp("fderiv_f_iso_x_comp", (OOp("iso", (OVar("colon"), OVar("E"), OVar("to_L"), OVar("F"),)),))
            results.append((rhs, "Mathlib: ContinuousLinearEquiv_comp_right_fderiv"))
        except Exception:
            pass
    return results


def _r0397_fderiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fderiv
    # fderiv 𝕜 f x = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderiv", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: ContinuousLinearMap_fderiv"))
        except Exception:
            pass
    return results


def _r0398_compFormalMultilinearSeries_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.compFormalMultilinearSeries_apply
    # (f.compFormalMultilinearSeries p) n = f.compContinuousMultilinearMap (p n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_compFormalMultilinearSeries_p", 1)
    if args is not None:
        try:
            rhs = OOp("f_compContinuousMultilinearMap", (OOp("p", (args[0],)),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_compFormalMultilinearSeries_apply"))
        except Exception:
            pass
    return results


def _r0399_fpowerSeries_apply_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ContinuousLinearMap.fpowerSeries_apply_zero
    # f.fpowerSeries x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_fpowerSeries", 2)
    if args is not None:
        try:
            rhs = OOp("ContinuousMultilinearMap_uncurry0", (OVar("_unknown"), OVar("_unknown"), OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: ContinuousLinearMap_fpowerSeries_apply_zero"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_topology rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "+", "-", "//", "<=", "==", "B_bilinearRestrictScalars", "Closeds_closure", "Compacts_equiv", "Compacts_map", "ConnectedComponents", "Continuous", "ContinuousAt", "ContinuousLinearMap_toUniformConvergenceCLM_sig_F_symm", "ContinuousMapZero_id", "ContinuousMultilinearMap_uncurry0", "ContinuousOpenMap_id_b_comp", "ContinuousOrderHom_id_b_comp", "Disjoint", "Equiv_embeddingFinSucc_n_i_e_1_toEquivRange_symm", "Filter_map", "Fin_succ", "H_Inc", "Homeomorph_unitBall", "I", "Inseparable", "Iobj_rep_rho_g_hom", "IsBigOWith", "IsClosed", "IsCover", "IsInvertible", "IsOpen", "IsSelfAdjoint", "K_map", "L_comp", "Nonempty", "Norm_norm", "Opens_interior", "Set_range", "Tendsto", "TopologicalSpace_Opens_map_f_map", "U", "Y_presheaf_map", "_0", "_0_colon_M_1_M_2_hom", "_1", "_1_colon_C_a_b", "_1_colon_C_b_g_comp", "_unknown", "a_e_symm",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_topology axioms."""
    if recognizes(term):
        return 0.6
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_topology rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_hom_comp(term, ctx))
    results.extend(_r0001_hom_id(term, ctx))
    results.extend(_r0002_hom_zero_apply(term, ctx))
    results.extend(_r0003_hom_add(term, ctx))
    results.extend(_r0004_hom_neg(term, ctx))
    results.extend(_r0005_hom_sub(term, ctx))
    results.extend(_r0006_hom_nsmul(term, ctx))
    results.extend(_r0007_hom_zsmul(term, ctx))
    results.extend(_r0008_forget_2_TopCat_obj(term, ctx))
    results.extend(_r0009_keri_apply(term, ctx))
    results.extend(_r0010_lift_uniq(term, ctx))
    results.extend(_r0011_toNNReal_add_add_neg_add_neg_eq(term, ctx))
    results.extend(_r0012_toNNReal_one(term, ctx))
    results.extend(_r0013_toNNReal_neg_one(term, ctx))
    results.extend(_r0014_toNNReal_mul_add_neg_mul_add_mul_neg_eq(term, ctx))
    results.extend(_r0015_derivWithin(term, ctx))
    results.extend(_r0016_fderivWithin(term, ctx))
    results.extend(_r0017_fderivWithin(term, ctx))
    results.extend(_r0018_rankOne_comp(term, ctx))
    results.extend(_r0019_rayleighQuotient_apply_zero(term, ctx))
    results.extend(_r0020_rayleighQuotient_neg_apply(term, ctx))
    results.extend(_r0021_rayleighQuotient_apply_neg(term, ctx))
    results.extend(_r0022_image_rayleigh_eq_image_rayleigh_sphere(term, ctx))
    results.extend(_r0023_add_apply(term, ctx))
    results.extend(_r0024_sub_apply(term, ctx))
    results.extend(_r0025_neg_apply(term, ctx))
    results.extend(_r0026_smul_apply(term, ctx))
    results.extend(_r0027_nnnorm_toContinuousMultilinearMap(term, ctx))
    results.extend(_r0028_enorm_toContinuousMultilinearMap(term, ctx))
    results.extend(_r0029_nnnorm_ofSubsingleton(term, ctx))
    results.extend(_r0030_nnnorm_constOfIsEmpty(term, ctx))
    results.extend(_r0031_curryLeft_apply_apply(term, ctx))
    results.extend(_r0032_curryLeft_add(term, ctx))
    results.extend(_r0033_coe_unitBall_apply_zero(term, ctx))
    results.extend(_r0034_flipMultilinear_flipLinear(term, ctx))
    results.extend(_r0035_apply_zero_uncurry0(term, ctx))
    results.extend(_r0036_flip_flip(term, ctx))
    results.extend(_r0037_flip_add(term, ctx))
    results.extend(_r0038_flip_smul(term, ctx))
    results.extend(_r0039_coe_flip(term, ctx))
    results.extend(_r0040_norm_toSpanSingleton(term, ctx))
    results.extend(_r0041_nnnorm_toSpanSingleton(term, ctx))
    results.extend(_r0042_norm_bilinearRestrictScalars(term, ctx))
    results.extend(_r0043_symm_toDiffeomorph(term, ctx))
    results.extend(_r0044_coe_toDiffeomorph_symm(term, ctx))
    results.extend(_r0045_lift_uniq(term, ctx))
    results.extend(_r0046_coe_toOrderHom(term, ctx))
    results.extend(_r0047_ext(term, ctx))
    results.extend(_r0048_id_comp(term, ctx))
    results.extend(_r0049_comp_assoc(term, ctx))
    results.extend(_r0050_copy_eq(term, ctx))
    results.extend(_r0051_coe_toAlgEquiv(term, ctx))
    results.extend(_r0052_coe_coeCLE(term, ctx))
    results.extend(_r0053_toContinuousLinearEquiv_apply(term, ctx))
    results.extend(_r0054_toContinuousLinearMap_toContinuousLinear(term, ctx))
    results.extend(_r0055_map_nhds_eq(term, ctx))
    results.extend(_r0056_coe_refl(term, ctx))
    results.extend(_r0057_coeCLE_refl(term, ctx))
    results.extend(_r0058_refl_toContinuousLinearEquiv(term, ctx))
    results.extend(_r0059_symm_apply_apply(term, ctx))
    results.extend(_r0060_symm_image_image(term, ctx))
    results.extend(_r0061_image_symm_image(term, ctx))
    results.extend(_r0062_symm_toAlgEquiv(term, ctx))
    results.extend(_r0063_symm_toHomeomorph(term, ctx))
    results.extend(_r0064_toContinuousLinearEquiv_symm(term, ctx))
    results.extend(_r0065_symm_map_nhds_eq(term, ctx))
    results.extend(_r0066_symm_symm(term, ctx))
    results.extend(_r0067_symm_symm_apply(term, ctx))
    results.extend(_r0068_preimage_symm_preimage(term, ctx))
    results.extend(_r0069_smulOfNeZero_symm_apply(term, ctx))
    results.extend(_r0070_coe_toEquiv(term, ctx))
    results.extend(_r0071_to_continuousMap_injective(term, ctx))
    results.extend(_r0072_comp_apply(term, ctx))
    results.extend(_r0073_id_comp(term, ctx))
    results.extend(_r0074_contLinear_map_vsub(term, ctx))
    results.extend(_r0075_const_contLinear(term, ctx))
    results.extend(_r0076_contLinear_eq_zero_iff_exists_const(term, ctx))
    results.extend(_r0077_toContinuousAffineMap_map_zero(term, ctx))
    results.extend(_r0078_coe_toContinuousMap(term, ctx))
    results.extend(_r0079_coe_comp(term, ctx))
    results.extend(_r0080_coe_id(term, ctx))
    results.extend(_r0081_pow_apply(term, ctx))
    results.extend(_r0082_toEquiv_eq_coe(term, ctx))
    results.extend(_r0083_toHomeomorph_eq_coe(term, ctx))
    results.extend(_r0084_mulLeft_symm(term, ctx))
    results.extend(_r0085_mulRight_symm(term, ctx))
    results.extend(_r0086_coe_inv(term, ctx))
    results.extend(_r0087_coe_completion(term, ctx))
    results.extend(_r0088_coe_mk(term, ctx))
    results.extend(_r0089_map_zero(term, ctx))
    results.extend(_r0090_map_eq_zero_of_eq(term, ctx))
    results.extend(_r0091_smul_apply(term, ctx))
    results.extend(_r0092_map_nhds_eq(term, ctx))
    results.extend(_r0093_map_smul(term, ctx))
    results.extend(_r0094_symm_smul_apply(term, ctx))
    results.extend(_r0095_toLinearEquiv_smul(term, ctx))
    results.extend(_r0096_smul_trans(term, ctx))
    results.extend(_r0097_copy_eq(term, ctx))
    results.extend(_r0098_map_smul(term, ctx))
    results.extend(_r0099_inr_apply(term, ctx))
    results.extend(_r0100_comp_inl_add_comp_inr(term, ctx))
    results.extend(_r0101_coe_snd(term, ctx))
    results.extend(_r0102_fst_prod_snd(term, ctx))
    results.extend(_r0103_fst_comp_prod(term, ctx))
    results.extend(_r0104_fst_comp_inr(term, ctx))
    results.extend(_r0105_snd_comp_inl(term, ctx))
    results.extend(_r0106_snd_comp_inr(term, ctx))
    results.extend(_r0107_ext(term, ctx))
    results.extend(_r0108_toMultilinearMap_zero(term, ctx))
    results.extend(_r0109_toUniformConvergenceCLM_symm_apply(term, ctx))
    results.extend(_r0110_toLinearMap_intrinsicStar(term, ctx))
    results.extend(_r0111_isSelfAdjoint_iff_map_star(term, ctx))
    results.extend(_r0112_intrinsicStar_smulRight(term, ctx))
    results.extend(_r0113_ext_iff_isClosed(term, ctx))
    results.extend(_r0114_val_apply(term, ctx))
    results.extend(_r0115_coe_id(term, ctx))
    results.extend(_r0116_id_apply(term, ctx))
    results.extend(_r0117_comp_apply(term, ctx))
    results.extend(_r0118_map_id_obj(term, ctx))
    results.extend(_r0119_map_id_obj_unop(term, ctx))
    results.extend(_r0120_op_map_id_obj(term, ctx))
    results.extend(_r0121_inclusionMapIso_hom(term, ctx))
    results.extend(_r0122_inclusionMapIso_inv(term, ctx))
    results.extend(_r0123_val_apply(term, ctx))
    results.extend(_r0124_coe_id(term, ctx))
    results.extend(_r0125_id_apply(term, ctx))
    results.extend(_r0126_comp_apply(term, ctx))
    results.extend(_r0127_map_obj(term, ctx))
    results.extend(_r0128_map_homOfLE(term, ctx))
    results.extend(_r0129_map_id_obj_unop(term, ctx))
    results.extend(_r0130_mapIso_hom_app(term, ctx))
    results.extend(_r0131_continuousMapOfUnique_symm_apply(term, ctx))
    results.extend(_r0132_equivOfIsClopen_mk(term, ctx))
    results.extend(_r0133_coe_prodComm(term, ctx))
    results.extend(_r0134_sumCongr_refl(term, ctx))
    results.extend(_r0135_coe_sumComm(term, ctx))
    results.extend(_r0136_sumSumSumComm_symm(term, ctx))
    results.extend(_r0137_mul_apply(term, ctx))
    results.extend(_r0138_mul_comp(term, ctx))
    results.extend(_r0139_one_apply(term, ctx))
    results.extend(_r0140_one_comp(term, ctx))
    results.extend(_r0141_comp_one(term, ctx))
    results.extend(_r0142_const_one(term, ctx))
    results.extend(_r0143_natCast_apply(term, ctx))
    results.extend(_r0144_intCast_apply(term, ctx))
    results.extend(_r0145_inv_apply(term, ctx))
    results.extend(_r0146_inv_comp(term, ctx))
    results.extend(_r0147_div_apply(term, ctx))
    results.extend(_r0148_div_comp(term, ctx))
    results.extend(_r0149_smul_apply(term, ctx))
    results.extend(_r0150_equivFnOfDiscrete_symm_apply(term, ctx))
    results.extend(_r0151_coe_trans(term, ctx))
    results.extend(_r0152_ext(term, ctx))
    results.extend(_r0153_copy_eq(term, ctx))
    results.extend(_r0154_nnrealPart_neg_eq_zero_of_nonneg(term, ctx))
    results.extend(_r0155_toReal_add(term, ctx))
    results.extend(_r0156_toReal_smul(term, ctx))
    results.extend(_r0157_nnrealPart_sub_nnrealPart_neg(term, ctx))
    results.extend(_r0158_toRealLinearMap_apply(term, ctx))
    results.extend(_r0159_nnrealPart_neg_toReal_eq(term, ctx))
    results.extend(_r0160_toNNRealLinear_inj(term, ctx))
    results.extend(_r0161_toContinuousMap_id(term, ctx))
    results.extend(_r0162_copy_eq(term, ctx))
    results.extend(_r0163_setOfTop_eq_univ(term, ctx))
    results.extend(_r0164_idealOfEmpty_eq_bot(term, ctx))
    results.extend(_r0165_mabs_apply(term, ctx))
    results.extend(_r0166_sup_apply(term, ctx))
    results.extend(_r0167_star_apply(term, ctx))
    results.extend(_r0168_closedEBall_zero(term, ctx))
    results.extend(_r0169_ediam_one(term, ctx))
    results.extend(_r0170_ediam_iUnion_mem_option(term, ctx))
    results.extend(_r0171_ext(term, ctx))
    results.extend(_r0172_copy_eq(term, ctx))
    results.extend(_r0173_comp_apply(term, ctx))
    results.extend(_r0174_comp_assoc(term, ctx))
    results.extend(_r0175_id_comp(term, ctx))
    results.extend(_r0176_cancel_right(term, ctx))
    results.extend(_r0177_coe_symm_toEquiv(term, ctx))
    results.extend(_r0178_ext(term, ctx))
    results.extend(_r0179_symm_trans_apply(term, ctx))
    results.extend(_r0180_symm_apply_apply(term, ctx))
    results.extend(_r0181_symm_apply_eq(term, ctx))
    results.extend(_r0182_self_comp_symm(term, ctx))
    results.extend(_r0183_range_coe(term, ctx))
    results.extend(_r0184_preimage_image(term, ctx))
    results.extend(_r0185_image_eq_preimage_symm(term, ctx))
    results.extend(_r0186_map_nhds_eq(term, ctx))
    results.extend(_r0187_symm_map_nhds_eq(term, ctx))
    results.extend(_r0188_trans_toHomotopyEquiv(term, ctx))
    results.extend(_r0189_isCover_empty_right(term, ctx))
    results.extend(_r0190_sphere_zero(term, ctx))
    results.extend(_r0191_dimH_univ(term, ctx))
    results.extend(_r0192_infEDist_iUnion(term, ctx))
    results.extend(_r0193_infEDist_biUnion(term, ctx))
    results.extend(_r0194_hausdorffDist_comm(term, ctx))
    results.extend(_r0195_hausdorffDist_closure_1(term, ctx))
    results.extend(_r0196_preimage_smul_ball(term, ctx))
    results.extend(_r0197_smul_closedBall(term, ctx))
    results.extend(_r0198_preimage_smul_closedBall(term, ctx))
    results.extend(_r0199_smul_sphere(term, ctx))
    results.extend(_r0200_preimage_smul_sphere(term, ctx))
    results.extend(_r0201_ball_eq_empty(term, ctx))
    results.extend(_r0202_ball_zero(term, ctx))
    results.extend(_r0203_iUnion_ball_nat_succ(term, ctx))
    results.extend(_r0204_sphere_eq_empty_of_subsingleton(term, ctx))
    results.extend(_r0205_closedBall_eq_empty(term, ctx))
    results.extend(_r0206_closedBall_eq_sphere_of_nonpos(term, ctx))
    results.extend(_r0207_sphere_union_ball(term, ctx))
    results.extend(_r0208_closedBall_diff_sphere(term, ctx))
    results.extend(_r0209_closedBall_diff_ball(term, ctx))
    results.extend(_r0210_iUnion_inter_closedBall_nat(term, ctx))
    results.extend(_r0211_closure_sphere(term, ctx))
    results.extend(_r0212_symm_toSnowflaking(term, ctx))
    results.extend(_r0213_thickening_of_nonpos(term, ctx))
    results.extend(_r0214_nhdsWithin_eq(term, ctx))
    results.extend(_r0215_toFun_eq_coe(term, ctx))
    results.extend(_r0216_ext(term, ctx))
    results.extend(_r0217_copy_eq(term, ctx))
    results.extend(_r0218_comp_apply(term, ctx))
    results.extend(_r0219_comp_assoc(term, ctx))
    results.extend(_r0220_id_comp(term, ctx))
    results.extend(_r0221_cancel_right(term, ctx))
    results.extend(_r0222_ext(term, ctx))
    results.extend(_r0223_coe_inf(term, ctx))
    results.extend(_r0224_coe_top(term, ctx))
    results.extend(_r0225_coe_eq_univ(term, ctx))
    results.extend(_r0226_coe_bot(term, ctx))
    results.extend(_r0227_coe_eq_empty(term, ctx))
    results.extend(_r0228_coe_sSup(term, ctx))
    results.extend(_r0229_coe_finset_sup(term, ctx))
    results.extend(_r0230_coe_iInf(term, ctx))
    results.extend(_r0231_iInf_def(term, ctx))
    results.extend(_r0232_singleton_prod_singleton(term, ctx))
    results.extend(_r0233_ext(term, ctx))
    results.extend(_r0234_coe_inf(term, ctx))
    results.extend(_r0235_coe_top(term, ctx))
    results.extend(_r0236_coe_bot(term, ctx))
    results.extend(_r0237_coe_sdiff(term, ctx))
    results.extend(_r0238_coe_himp(term, ctx))
    results.extend(_r0239_coe_compl(term, ctx))
    results.extend(_r0240_coe_finset_sup(term, ctx))
    results.extend(_r0241_carrier_eq_coe(term, ctx))
    results.extend(_r0242_coe_inf(term, ctx))
    results.extend(_r0243_coe_top(term, ctx))
    results.extend(_r0244_coe_bot(term, ctx))
    results.extend(_r0245_coe_eq_empty(term, ctx))
    results.extend(_r0246_coe_finset_sup(term, ctx))
    results.extend(_r0247_mem_singleton(term, ctx))
    results.extend(_r0248_toCloseds_singleton(term, ctx))
    results.extend(_r0249_map_id(term, ctx))
    results.extend(_r0250_map_comp(term, ctx))
    results.extend(_r0251_equiv_trans(term, ctx))
    results.extend(_r0252_toCloseds_toCompacts(term, ctx))
    results.extend(_r0253_carrier_eq_coe(term, ctx))
    results.extend(_r0254_toCompacts_sup(term, ctx))
    results.extend(_r0255_mem_singleton(term, ctx))
    results.extend(_r0256_toCloseds_singleton(term, ctx))
    results.extend(_r0257_coe_map(term, ctx))
    results.extend(_r0258_carrier_eq_coe(term, ctx))
    results.extend(_r0259_coe_top(term, ctx))
    results.extend(_r0260_map_comp(term, ctx))
    results.extend(_r0261_ext(term, ctx))
    results.extend(_r0262_coe_bot(term, ctx))
    results.extend(_r0263_coe_mk(term, ctx))
    results.extend(_r0264_coe_sup(term, ctx))
    results.extend(_r0265_coe_bot(term, ctx))
    results.extend(_r0266_mk_empty(term, ctx))
    results.extend(_r0267_coe_eq_empty(term, ctx))
    results.extend(_r0268_coe_top(term, ctx))
    results.extend(_r0269_mk_univ(term, ctx))
    results.extend(_r0270_coe_eq_univ(term, ctx))
    results.extend(_r0271_coe_sSup(term, ctx))
    results.extend(_r0272_coe_finset_sup(term, ctx))
    results.extend(_r0273_coe_finset_inf(term, ctx))
    results.extend(_r0274_iSup_def(term, ctx))
    results.extend(_r0275_comap_comp(term, ctx))
    results.extend(_r0276_range_toUniformOnFunIsCompact(term, ctx))
    results.extend(_r0277_inc_congr(term, ctx))
    results.extend(_r0278_coe_inj(term, ctx))
    results.extend(_r0279_isInvertible_zero_iff(term, ctx))
    results.extend(_r0280_mem_map(term, ctx))
    results.extend(_r0281_nonempty_iff_nonempty(term, ctx))
    results.extend(_r0282_isOpen_image(term, ctx))
    results.extend(_r0283_isClosed_image(term, ctx))
    results.extend(_r0284_comp_continuousAt_iff(term, ctx))
    results.extend(_r0285_tendsto_dist_right_atTop_iff(term, ctx))
    results.extend(_r0286_le_infEDist(term, ctx))
    results.extend(_r0287_mem_ball_comm(term, ctx))
    results.extend(_r0288_inseparable_iff(term, ctx))
    results.extend(_r0289_mem_mk(term, ctx))
    results.extend(_r0290_mem_closure(term, ctx))
    results.extend(_r0291_coe_nonempty(term, ctx))
    results.extend(_r0292_mem_iInf(term, ctx))
    results.extend(_r0293_mem_mk(term, ctx))
    results.extend(_r0294_mem_toCloseds(term, ctx))
    results.extend(_r0295_coe_nonempty(term, ctx))
    results.extend(_r0296_map_injective_iff(term, ctx))
    results.extend(_r0297_mem_toCompacts(term, ctx))
    results.extend(_r0298_mem_mk(term, ctx))
    results.extend(_r0299_nonempty_coeSort(term, ctx))
    results.extend(_r0300_mem_interior(term, ctx))
    results.extend(_r0301_mem_inf(term, ctx))
    results.extend(_r0302_mem_sup(term, ctx))
    results.extend(_r0303_mem_bot(term, ctx))
    results.extend(_r0304_coe_disjoint(term, ctx))
    results.extend(_r0305_mem_comap(term, ctx))
    results.extend(_r0306_Iobj_rho_apply(term, ctx))
    results.extend(_r0307_d_zero(term, ctx))
    results.extend(_r0308_d_succ(term, ctx))
    results.extend(_r0309_d_comp_d(term, ctx))
    results.extend(_r0310_coe_of(term, ctx))
    results.extend(_r0311_hom_ofHom(term, ctx))
    results.extend(_r0312_ofHom_hom(term, ctx))
    results.extend(_r0313_hom_zero(term, ctx))
    results.extend(_r0314_hom_smul(term, ctx))
    results.extend(_r0315_hom_forget_2_TopCat_map(term, ctx))
    results.extend(_r0316_coe_freeObj(term, ctx))
    results.extend(_r0317_keri_comp(term, ctx))
    results.extend(_r0318_hom_cokerpi(term, ctx))
    results.extend(_r0319_comp_cokerpi(term, ctx))
    results.extend(_r0320_range_pullbackSnd(term, ctx))
    results.extend(_r0321_opensRange_pullbackSnd(term, ctx))
    results.extend(_r0322_range_pullbackFst(term, ctx))
    results.extend(_r0323_opensRange_pullbackFst(term, ctx))
    results.extend(_r0324_range_pullback_to_base_of_left(term, ctx))
    results.extend(_r0325_range_pullback_to_base_of_right(term, ctx))
    results.extend(_r0326_image_preimage_eq_preimage_image_of_isPu(term, ctx))
    results.extend(_r0327_lift_fac(term, ctx))
    results.extend(_r0328_comp_lift(term, ctx))
    results.extend(_r0329_isoOfRangeEq_hom_fac(term, ctx))
    results.extend(_r0330_isoOfRangeEq_inv_fac(term, ctx))
    results.extend(_r0331_app_eq_invApp_app_of_comp_eq_aux(term, ctx))
    results.extend(_r0332_app_eq_appIso_inv_app_of_comp_eq(term, ctx))
    results.extend(_r0333_lift_app(term, ctx))
    results.extend(_r0334_GIso_inv(term, ctx))
    results.extend(_r0335_map_GIso_inv(term, ctx))
    results.extend(_r0336_app_GIso_hom(term, ctx))
    results.extend(_r0337_hcast_def(term, ctx))
    results.extend(_r0338_start_path(term, ctx))
    results.extend(_r0339_end_path(term, ctx))
    results.extend(_r0340_eq_path_of_eq_image(term, ctx))
    results.extend(_r0341_compAlongComposition_apply(term, ctx))
    results.extend(_r0342_iteratedFDeriv_comp_diagonal(term, ctx))
    results.extend(_r0343_fpowerSeries_radius(term, ctx))
    results.extend(_r0344_uncurryBilinear_apply(term, ctx))
    results.extend(_r0345_fpowerSeriesBilinear_apply_zero(term, ctx))
    results.extend(_r0346_fpowerSeriesBilinear_apply_one(term, ctx))
    results.extend(_r0347_fpowerSeriesBilinear_apply_two(term, ctx))
    results.extend(_r0348_fpowerSeriesBilinear_apply_add_three(term, ctx))
    results.extend(_r0349_fpowerSeriesBilinear_radius(term, ctx))
    results.extend(_r0350_isBigO_congr(term, ctx))
    results.extend(_r0351_isLittleO_congr(term, ctx))
    results.extend(_r0352_isBigOWith_principal(term, ctx))
    results.extend(_r0353_isBigO_principal(term, ctx))
    results.extend(_r0354_isBigOTVS_id(term, ctx))
    results.extend(_r0355_isBigOTVS_comp(term, ctx))
    results.extend(_r0356_isBigOTVS_fun_comp(term, ctx))
    results.extend(_r0357_isThetaTVS_comp(term, ctx))
    results.extend(_r0358_isTheta_principal(term, ctx))
    results.extend(_r0359_toNNReal_apply(term, ctx))
    results.extend(_r0360_toNNReal_mul_add_neg_mul_add_mul_neg_eq(term, ctx))
    results.extend(_r0361_toNNReal_algebraMap(term, ctx))
    results.extend(_r0362_toNNReal_neg_algebraMap(term, ctx))
    results.extend(_r0363_toNNReal_apply(term, ctx))
    results.extend(_r0364_toContinuousMapHom_toNNReal(term, ctx))
    results.extend(_r0365_toNNReal_smul(term, ctx))
    results.extend(_r0366_toNNReal_neg_smul(term, ctx))
    results.extend(_r0367_toNNReal_add_add_neg_add_neg_eq(term, ctx))
    results.extend(_r0368_opNorm_mul_flip_apply(term, ctx))
    results.extend(_r0369_opNNNorm_mul_flip_apply(term, ctx))
    results.extend(_r0370_exists_contDiff_support_eq(term, ctx))
    results.extend(_r0371_iteratedFDerivWithin_comp_left(term, ctx))
    results.extend(_r0372_iteratedFDeriv_comp_left(term, ctx))
    results.extend(_r0373_iteratedFDerivWithin_comp_left(term, ctx))
    results.extend(_r0374_iteratedFDeriv_comp_left(term, ctx))
    results.extend(_r0375_iteratedFDerivWithin_comp_right(term, ctx))
    results.extend(_r0376_iteratedFDerivWithin_comp_right(term, ctx))
    results.extend(_r0377_iteratedFDeriv_comp_right(term, ctx))
    results.extend(_r0378_fderiv(term, ctx))
    results.extend(_r0379_fderiv_one(term, ctx))
    results.extend(_r0380_dslope_comp(term, ctx))
    results.extend(_r0381_deriv(term, ctx))
    results.extend(_r0382_derivWithin_of_bilinear(term, ctx))
    results.extend(_r0383_deriv_of_bilinear(term, ctx))
    results.extend(_r0384_fderiv(term, ctx))
    results.extend(_r0385_changeOriginSeries_support(term, ctx))
    results.extend(_r0386_changeOrigin_toFormalMultilinearSeries(term, ctx))
    results.extend(_r0387_succ_embeddingFinSucc_fst_symm_apply(term, ctx))
    results.extend(_r0388_iteratedFDeriv_eq(term, ctx))
    results.extend(_r0389_fderivWithin_of_bilinear(term, ctx))
    results.extend(_r0390_fderiv_of_bilinear(term, ctx))
    results.extend(_r0391_fderiv(term, ctx))
    results.extend(_r0392_fderivWithin(term, ctx))
    results.extend(_r0393_comp_fderivWithin(term, ctx))
    results.extend(_r0394_comp_fderiv(term, ctx))
    results.extend(_r0395_comp_right_fderivWithin(term, ctx))
    results.extend(_r0396_comp_right_fderiv(term, ctx))
    results.extend(_r0397_fderiv(term, ctx))
    results.extend(_r0398_compFormalMultilinearSeries_apply(term, ctx))
    results.extend(_r0399_fpowerSeries_apply_zero(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_topology rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("freeMap_map", "freeMap_R_f_colon_X_to_0_R_to_Y_to_0_R_v_eq_Finsupp_mapDomain_f_hom_v", "Not an equality or iff proposition"),
    ("cokerpi_surjective", "Function_Surjective_cokerpi_phi_hom", "Not an equality or iff proposition"),
    ("IsClosedImmersion_of_comp", "IsClosedImmersion_f", "Not an equality or iff proposition"),
    ("IsOpenImmersion_isIso", "IsIso_f", "Not an equality or iff proposition"),
    ("IsOpenImmersion_of_isIso_stalkMap", "IsOpenImmersion_f", "Not an equality or iff proposition"),
    ("IsOpenImmersion_of_comp", "IsOpenImmersion_f", "Not an equality or iff proposition"),
    ("IsOpenImmersion_le_monomorphisms", "IsOpenImmersion_le_MorphismProperty_monomorphisms_Scheme_u", "Not an equality or iff proposition"),
    ("IsOpenImmersion_isPullback_lift_id", "IsPullback_IsOpenImmersion_lift_g_f_H_1_g_f", "Not an equality or iff proposition"),
    ("IsOpenImmersion_isPullback", "IsPullback_g_iU_iV_f", "Not an equality or iff proposition"),
    ("ContinuousMap_Homotopy_heq_path_of_eq_image", "pi_TopCat_ofHom_f_map_p_pi_TopCat_ofHom_g_map_q", "Not an equality or iff proposition"),
    ("ContinuousMap_HomotopyEquiv_simplyConnectedSpace", "SimplyConnectedSpace_X", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_comp_hasFPowerSeriesWithinOnBall", "HasFPowerSeriesWithinOnBall_g_comp_f_g_compFormalMultilinearSeries_p_s_x_r", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_comp_hasFPowerSeriesOnBall", "HasFPowerSeriesOnBall_g_comp_f_g_compFormalMultilinearSeries_p_x_r", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_comp_analyticOn", "AnalyticOn_g_comp_f_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_comp_analyticOnNhd", "AnalyticOnNhd_g_comp_f_s", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_hasFiniteFPowerSeriesOnBall", "HasFiniteFPowerSeriesOnBall_f_f_toFormalMultilinearSeries_0_Fintype_card_i_plus_1", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_cpolynomialAt", "CPolynomialAt_f_x", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_cpolynomialOn", "CPolynomialOn_f_s", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticOnNhd", "AnalyticOnNhd_f_s", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticOn", "AnalyticOn_f_s", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticAt", "AnalyticAt_f_x", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticWithinAt", "AnalyticWithinAt_f_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear", "HasFiniteFPowerSeriesOnBall_fun_p_colon_G_times_Pi_i_Em_i_f_p_1_p_2_f_toFo", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_cpolynomialAt_uncurry_of_multilinear", "CPolynomialAt_fun_p_colon_G_times_Pi_i_Em_i_f_p_1_p_2_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_cpolynomialOn_uncurry_of_multilinear", "CPolynomialOn_fun_p_colon_G_times_Pi_i_Em_i_f_p_1_p_2_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticOnNhd_uncurry_of_multilinear", "AnalyticOnNhd_fun_p_colon_G_times_Pi_i_Em_i_f_p_1_p_2_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticOn_uncurry_of_multilinear", "AnalyticOn_fun_p_colon_G_times_Pi_i_Em_i_f_p_1_p_2_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticAt_uncurry_of_multilinear", "AnalyticAt_fun_p_colon_G_times_Pi_i_Em_i_f_p_1_p_2_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticWithinAt_uncurry_of_multilinear", "AnalyticWithinAt_fun_p_colon_G_times_Pi_i_Em_i_f_p_1_p_2_s_x", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_cpolynomialAt_uncurry_of_linear", "CPolynomialAt_fun_p_colon_Pi_i_Em_i_times_G_f_p_1_p_2_x", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_cpolyomialOn_uncurry_of_linear", "CPolynomialOn_fun_p_colon_Pi_i_Em_i_times_G_f_p_1_p_2_s", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticOnNhd_uncurry_of_linear", "AnalyticOnNhd_fun_p_colon_Pi_i_Em_i_times_G_f_p_1_p_2_s", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticOn_uncurry_of_linear", "AnalyticOn_fun_p_colon_Pi_i_Em_i_times_G_f_p_1_p_2_s", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticAt_uncurry_of_linear", "AnalyticAt_fun_p_colon_Pi_i_Em_i_times_G_f_p_1_p_2_x", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticWithinAt_uncurry_of_linear", "AnalyticWithinAt_fun_p_colon_Pi_i_Em_i_times_G_f_p_1_p_2_s_x", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_cpolynomialAt_uncurry_compContinuousLinearMap", "CPolynomialAt_fun_p_colon_Pi_i_Fm_i_to_L_Em_i_times_ContinuousMultilinearMap_E", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_cpolynomialOn_uncurry_compContinuousLinearMap", "CPolynomialOn_fun_p_colon_Pi_i_Fm_i_to_L_Em_i_times_ContinuousMultilinearMap_E", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticOnNhd_uncurry_compContinuousLinearMap", "AnalyticOnNhd_fun_p_colon_Pi_i_Fm_i_to_L_Em_i_times_ContinuousMultilinearMap_E", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticOn_uncurry_compContinuousLinearMap", "AnalyticOn_fun_p_colon_Pi_i_Fm_i_to_L_Em_i_times_ContinuousMultilinearMap_Em_G", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticAt_uncurry_compContinuousLinearMap", "AnalyticAt_fun_p_colon_Pi_i_Fm_i_to_L_Em_i_times_ContinuousMultilinearMap_Em_G", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_analyticWithinAt_uncurry_compContinuousLinearMap", "AnalyticWithinAt_fun_p_colon_Pi_i_Fm_i_to_L_Em_i_times_ContinuousMultilinearMap", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_comp_hasFiniteFPowerSeriesOnBall", "HasFiniteFPowerSeriesOnBall_g_comp_f_g_compFormalMultilinearSeries_p_x_n_r", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_comp_cpolynomialOn", "CPolynomialOn_g_comp_f_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFiniteFPowerSeriesOnBall", "HasFiniteFPowerSeriesOnBall_f_f_fpowerSeries_x_x_2_inf", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFPowerSeriesOnBall", "HasFPowerSeriesOnBall_f_f_fpowerSeries_x_x_inf", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFPowerSeriesAt", "HasFPowerSeriesAt_f_f_fpowerSeries_x_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_cpolynomialAt", "CPolynomialAt_f_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticAt", "AnalyticAt_f_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_cpolynomialOn", "CPolynomialOn_f_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticOnNhd", "AnalyticOnNhd_f_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticWithinAt", "AnalyticWithinAt_f_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticOn", "AnalyticOn_f_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFPowerSeriesOnBall_bilinear", "HasFPowerSeriesOnBall_fun_x_colon_E_times_F_eq_gt_f_x_1_x_2_f_fpowerSeriesBilinear_x_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFPowerSeriesAt_bilinear", "HasFPowerSeriesAt_fun_x_colon_E_times_F_eq_gt_f_x_1_x_2_f_fpowerSeriesBilinear_x_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticAt_bilinear", "AnalyticAt_fun_x_colon_E_times_F_eq_gt_f_x_1_x_2_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticWithinAt_bilinear", "AnalyticWithinAt_fun_x_colon_E_times_F_eq_gt_f_x_1_x_2_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticOnNhd_bilinear", "AnalyticOnNhd_fun_x_colon_E_times_F_eq_gt_f_x_1_x_2_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_analyticOn_bilinear", "AnalyticOn_fun_x_colon_E_times_F_eq_gt_f_x_1_x_2_s", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_analyticAt", "AnalyticAt_f_x", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_analyticOnNhd", "AnalyticOnNhd_f_s", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_analyticWithinAt", "AnalyticWithinAt_f_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_analyticOn", "AnalyticOn_f_s", "Not an equality or iff proposition"),
    ("ContinuousOn_cfc_fun", "ContinuousOn_fun_x_cfc_f_x_a_s", "Not an equality or iff proposition"),
    ("Continuous_cfc_fun", "Continuous_fun_x_cfc_f_x_a", "Not an equality or iff proposition"),
    ("ContinuousAt_cfc", "ContinuousAt_fun_x_cfc_f_a_x_x_0", "Not an equality or iff proposition"),
    ("ContinuousWithinAt_cfc", "ContinuousWithinAt_fun_x_cfc_f_a_x_t_x_0", "Not an equality or iff proposition"),
    ("ContinuousOn_cfc", "ContinuousOn_fun_x_cfc_f_a_x_t", "Not an equality or iff proposition"),
    ("ContinuousOn_cfc", "_unknown", "Empty proposition"),
    ("ContinuousOn_cfc_of_mem_nhdsSet", "ContinuousOn_fun_x_cfc_f_a_x_t", "Not an equality or iff proposition"),
    ("Continuous_cfc", "Continuous_fun_x_cfc_f_a_x", "Not an equality or iff proposition"),
    ("Continuous_cfc", "_unknown", "Empty proposition"),
    ("Continuous_cfc_of_mem_nhdsSet", "Continuous_fun_x_cfc_f_a_x", "Not an equality or iff proposition"),
    ("ContinuousAt_cfc_nnreal", "ContinuousAt_fun_x_cfc_f_a_x_x_0", "Not an equality or iff proposition"),
    ("ContinuousWithinAt_cfc_nnreal", "ContinuousWithinAt_fun_x_cfc_f_a_x_t_x_0", "Not an equality or iff proposition"),
    ("ContinuousOn_cfc_nnreal", "ContinuousOn_fun_x_cfc_f_a_x_t", "Not an equality or iff proposition"),
    ("ContinuousOn_cfc_nnreal", "_unknown", "Empty proposition"),
    ("ContinuousOn_cfc_nnreal_of_mem_nhdsSet", "ContinuousOn_fun_x_cfc_f_a_x_t", "Not an equality or iff proposition"),
    ("Continuous_cfc_nnreal", "Continuous_fun_x_cfc_f_a_x", "Not an equality or iff proposition"),
    ("Continuous_cfc_nnreal", "_unknown", "Empty proposition"),
    ("Continuous_cfc_nnreal_of_mem_nhdsSet", "Continuous_fun_x_cfc_f_a_x", "Not an equality or iff proposition"),
    ("ContinuousOn_cfc_fun", "ContinuousOn_fun_x_cfc_f_x_a_s", "Not an equality or iff proposition"),
    ("Continuous_cfc_fun", "Continuous_fun_x_cfc_f_x_a", "Not an equality or iff proposition"),
    ("ContinuousAt_cfc", "ContinuousAt_fun_x_cfc_f_a_x_x_0", "Not an equality or iff proposition"),
    ("ContinuousWithinAt_cfc", "ContinuousWithinAt_fun_x_cfc_f_a_x_t_x_0", "Not an equality or iff proposition"),
    ("ContinuousOn_cfc", "ContinuousOn_fun_x_cfc_f_a_x_t", "Not an equality or iff proposition"),
    ("ContinuousOn_cfc", "_unknown", "Empty proposition"),
    ("ContinuousOn_cfc_of_mem_nhdsSet", "ContinuousOn_fun_x_cfc_f_a_x_t", "Not an equality or iff proposition"),
    ("Continuous_cfc", "Continuous_fun_x_cfc_f_a_x", "Not an equality or iff proposition"),
    ("Continuous_cfc", "_unknown", "Empty proposition"),
    ("Continuous_cfc_of_mem_nhdsSet", "Continuous_fun_x_cfc_f_a_x", "Not an equality or iff proposition"),
    ("ContinuousAt_cfc_nnreal", "ContinuousAt_fun_x_cfc_f_a_x_x_0", "Not an equality or iff proposition"),
    ("ContinuousWithinAt_cfc_nnreal", "ContinuousWithinAt_fun_x_cfc_f_a_x_t_x_0", "Not an equality or iff proposition"),
    ("ContinuousOn_cfc_nnreal", "ContinuousOn_fun_x_cfc_f_a_x_t", "Not an equality or iff proposition"),
    ("ContinuousOn_cfc_nnreal", "_unknown", "Empty proposition"),
    ("ContinuousOn_cfc_nnreal_of_mem_nhdsSet", "ContinuousOn_fun_x_cfc_f_a_x_t", "Not an equality or iff proposition"),
    ("Continuous_cfc_nnreal", "Continuous_fun_x_cfc_f_a_x", "Not an equality or iff proposition"),
    ("Continuous_cfc_nnreal", "_unknown", "Empty proposition"),
    ("Continuous_cfc_nnreal_of_mem_nhdsSet", "Continuous_fun_x_cfc_f_a_x", "Not an equality or iff proposition"),
    ("ContinuousMap_continuous_toNNReal", "Continuous_toNNReal_X_colon_eq_X", "Not an equality or iff proposition"),
    ("ContinuousMapZero_continuous_toNNReal", "Continuous_toNNReal_X_colon_eq_X", "Not an equality or iff proposition"),
    ("ContinuousFunctionalCalculus_isCompact_spectrum", "IsCompact_spectrum_R_a", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_isometry_mul_flip", "Isometry_mul_E_flip", "Not an equality or iff proposition"),
    ("ContinuousAffineMap_contDiff", "ContDiff_n_f", "Not an equality or iff proposition"),
    ("Continuous_exists_contDiff_dist_le_of_forall_mem_ball_dist_le", "exists_g_colon_E_to_F_ContDiff_inf_g_and_forall_a_forall_d_forall_x_in_ball_a_e_dist_f_x_f_a_le_d_to", "Not an equality or iff proposition"),
    ("ContinuousMap_dense_setOf_contDiff", "Dense_f_colon_C_E_F_pipe_ContDiff_inf_f", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_contDiff", "ContDiff_n_f", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_contDiff", "ContDiff_n_f", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_norm_iteratedFDerivWithin_le_of_bilinear_aux", "iteratedFDerivWithin_n_fun_y_eq_gt_B_f_y_g_y_s_x_le_B_star_i_in_Fins", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_norm_iteratedFDerivWithin_le_of_bilinear", "iteratedFDerivWithin_n_fun_y_eq_gt_B_f_y_g_y_s_x_le_B_star_i_in_Fins", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_norm_iteratedFDeriv_le_of_bilinear", "iteratedFDeriv_n_fun_y_eq_gt_B_f_y_g_y_x_le_B_star_i_in_Finset_range_n_plus", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_norm_iteratedFDerivWithin_le_of_bilinear_of_le_one", "iteratedFDerivWithin_n_fun_y_eq_gt_B_f_y_g_y_s_x_le_i_in_Finset_ran", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_norm_iteratedFDeriv_le_of_bilinear_of_le_one", "iteratedFDeriv_n_fun_y_eq_gt_B_f_y_g_y_x_le_i_in_Finset_range_n_plus", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_norm_iteratedFDerivWithin_comp_left", "iteratedFDerivWithin_n_L_comp_f_s_x_le_L_star_iteratedFDerivWithin_n_f_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_norm_iteratedFDeriv_comp_left", "iteratedFDeriv_n_L_comp_f_x_le_L_star_iteratedFDeriv_n_f_x", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_contDiffAt", "ContDiffAt_n_f_x", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_contDiff", "ContDiff_n_f", "Not an equality or iff proposition"),
    ("ContinuousOn_continuousOn_iteratedFDerivWithin", "ContinuousOn_iteratedFDerivWithin_k_f_s_s", "Not an equality or iff proposition"),
    ("ContinuousOn_continuousOn_iteratedFDeriv", "ContinuousOn_iteratedFDeriv_k_f_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_IsInvertible_contDiffAt_map_inverse", "ContDiffAt_n_inverse_e", "Not an equality or iff proposition"),
    ("Homeomorph_contDiff_symm", "ContDiff_n_f_symm_colon_F_to_E", "Not an equality or iff proposition"),
    ("Homeomorph_contDiff_symm_deriv", "ContDiff_n_f_symm_colon_to", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_contDiffPointwiseHolderAt", "ContDiffPointwiseHolderAt_k_a_f_a", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_contDiffPointwiseHolderAt", "ContDiffPointwiseHolderAt_k_a_f_a", "Not an equality or iff proposition"),
    ("ContinuousWithinAt_of_dslope", "ContinuousWithinAt_f_s_b", "Not an equality or iff proposition"),
    ("ContinuousAt_of_dslope", "ContinuousAt_f_b", "Not an equality or iff proposition"),
    ("ContinuousOn_of_dslope", "ContinuousOn_f_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasDerivAtFilter", "HasDerivAtFilter_e_e_1_L", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasStrictDerivAt", "HasStrictDerivAt_e_e_1_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasDerivAt", "HasDerivAt_e_e_1_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasDerivWithinAt", "HasDerivWithinAt_e_e_1_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasDerivWithinAt_of_bilinear", "HasDerivWithinAt_fun_x_B_u_x_v_x_B_u_x_v_prime_plus_B_u_prime_v_x_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasDerivAt_of_bilinear", "HasDerivAt_fun_x_B_u_x_v_x_B_u_x_v_prime_plus_B_u_prime_v_x_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasStrictDerivAt_of_bilinear", "HasStrictDerivAt_fun_x_B_u_x_v_x_B_u_x_v_prime_plus_B_u_prime_v_x_x", "Not an equality or iff proposition"),
    ("ContinuousAffineMap_hasFDerivAtFilter", "HasFDerivAtFilter_f_f_contLinear_L", "Not an equality or iff proposition"),
    ("ContinuousAffineMap_hasStrictFDerivAt", "HasStrictFDerivAt_f_f_contLinear_x", "Not an equality or iff proposition"),
    ("ContinuousAffineMap_hasFDerivWithinAt", "HasFDerivWithinAt_f_f_contLinear_s_x", "Not an equality or iff proposition"),
    ("ContinuousAffineMap_hasFDerivAt", "HasFDerivAt_f_f_contLinear_x", "Not an equality or iff proposition"),
    ("ContinuousAffineMap_differentiableAt", "DifferentiableAt_f_x", "Not an equality or iff proposition"),
    ("ContinuousAffineMap_differentiableWithinAt", "DifferentiableWithinAt_f_s_x", "Not an equality or iff proposition"),
    ("ContinuousAffineMap_differentiable", "Differentiable_f", "Not an equality or iff proposition"),
    ("ContinuousAffineMap_differentiableOn", "DifferentiableOn_f_s", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_hasStrictFDerivAt", "HasStrictFDerivAt_f_f_linearDeriv_x_x", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_hasFDerivAt", "HasFDerivAt_f_f_linearDeriv_x_x", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_hasStrictFDerivAt_uncurry", "HasStrictFDerivAt_fun_fx_colon_ContinuousMultilinearMap_E_F_times_forall_i_E_i_fx_1_fx", "Not an equality or iff proposition"),
    ("HasStrictFDerivAt_continuousMultilinearMap_apply", "HasStrictFDerivAt_fun_x_f_x_g_x_ContinuousMultilinearMap_apply", "Not an equality or iff proposition"),
    ("HasFDerivWithinAt_continuousMultilinearMap_apply", "HasFDerivWithinAt_fun_x_f_x_g_x_ContinuousMultilinearMap_apply", "Not an equality or iff proposition"),
    ("HasFDerivAt_continuousMultilinearMap_apply", "HasFDerivAt_fun_x_f_x_g_x_ContinuousMultilinearMap_apply_E_F_g", "Not an equality or iff proposition"),
    ("HasFDerivWithinAt_multilinear_comp", "HasFDerivWithinAt_fun_x_f_fun_i_g_i_x_i_colon_i_f_toContinuousLi", "Not an equality or iff proposition"),
    ("HasFDerivAt_multilinear_comp", "HasFDerivAt_fun_x_f_fun_i_g_i_x_i_colon_i_f_toContinuousLinearMa", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_hasFTaylorSeriesUpTo_iteratedFDeriv", "HasFTaylorSeriesUpTo_top_f_fun_v_n_f_iteratedFDeriv_n_v", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_norm_iteratedFDeriv_le", "iteratedFDeriv_n_f_x_le_Nat_descFactorial_Fintype_card_i_n_star_f_star_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFDerivAt_uncurry_of_multilinear", "HasFDerivAt_fun_p_colon_E_times_Pi_i_G_i_f_p_1_p_2_f_flipMultilinear_v_2", "Not an equality or iff proposition"),
    ("HasFDerivWithinAt_linear_multilinear_comp", "HasFDerivWithinAt_fun_y_f_a_y_fun_i_b_i_y_f_flipMultilinear_f", "Not an equality or iff proposition"),
    ("HasFDerivAt_linear_multilinear_comp", "HasFDerivAt_fun_y_f_a_y_fun_i_b_i_y_f_flipMultilinear_fun_i", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFDerivWithinAt_of_bilinear", "HasFDerivWithinAt_fun_y_eq_gt_B_f_y_g_y_B_precompR_G_prime_f_x_g_prime_plus_B_pre", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFDerivAt_of_bilinear", "HasFDerivAt_fun_y_eq_gt_B_f_y_g_y_B_precompR_G_prime_f_x_g_prime_plus_B_precompL_G_prime_f_prime", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasStrictFDerivAt_of_bilinear", "HasStrictFDerivAt_fun_y_eq_gt_B_f_y_g_y_B_precompR_G_prime_f_x_g_prime_plus_B_pre", "Not an equality or iff proposition"),
    ("ContinuousAlternatingMap_hasStrictFDerivAt_compContinuousLinearMap", "HasStrictFDerivAt_fun_fg_colon_G_pow_i_to_L_H_times_F_to_L_G_fg_1_compCont", "Not an equality or iff proposition"),
    ("ContinuousAlternatingMap_hasStrictFDerivAt", "HasStrictFDerivAt_f_f_1_linearDeriv_x_x", "Not an equality or iff proposition"),
    ("ContinuousAlternatingMap_hasFDerivAt", "HasFDerivAt_f_f_1_linearDeriv_x_x", "Not an equality or iff proposition"),
    ("ContinuousAlternatingMap_hasFDerivWithinAt", "HasFDerivWithinAt_f_f_1_linearDeriv_x_s_x", "Not an equality or iff proposition"),
    ("ContinuousAlternatingMap_differentiable", "Differentiable_f", "Not an equality or iff proposition"),
    ("ContinuousMultilinearMap_hasStrictFDerivAt_compContinuousLinearMap", "HasStrictFDerivAt_fun_fg_colon_ContinuousMultilinearMap_G_H_times_forall_i_F_i_to_L", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_hasStrictFDerivAt", "HasStrictFDerivAt_iso_iso_colon_E_to_L_F_x", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_hasFDerivWithinAt", "HasFDerivWithinAt_iso_iso_colon_E_to_L_F_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_hasFDerivAt", "HasFDerivAt_iso_iso_colon_E_to_L_F_x", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_differentiableAt", "DifferentiableAt_iso_x", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_differentiableWithinAt", "DifferentiableWithinAt_iso_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_differentiable", "Differentiable_iso", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_differentiableOn", "DifferentiableOn_iso_s", "Not an equality or iff proposition"),
    ("ContinuousLinearEquiv_comp_hasFDerivWithinAt_iff", "_unknown", "Empty proposition"),
    ("ContinuousLinearEquiv_comp_hasFDerivAt_iff", "_unknown", "Empty proposition"),
    ("fderivWithin_continuousLinearEquiv_comp", "fderivWithin_fun_x_L_colon_G_to_L_G_prime_comp_f_x_s_x_eq_ContinuousLi", "Not an equality or iff proposition"),
    ("fderiv_continuousLinearEquiv_comp", "fderiv_fun_x_L_colon_G_to_L_G_prime_comp_f_x_x_eq_ContinuousLinearEqui", "Not an equality or iff proposition"),
    ("fderiv_continuousLinearEquiv_comp", "_unknown", "Empty proposition"),
    ("ContinuousLinearEquiv_comp_right_hasFDerivWithinAt_iff", "_unknown", "Empty proposition"),
    ("ContinuousLinearEquiv_comp_right_hasFDerivAt_iff", "_unknown", "Empty proposition"),
    ("ContinuousLinearEquiv_uniqueDiffOn_image", "UniqueDiffOn_e_prime_prime_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFDerivAtFilter", "HasFDerivAtFilter_f_f_L", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasStrictFDerivAt", "HasStrictFDerivAt_f_f_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFDerivWithinAt", "HasFDerivWithinAt_f_f_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_hasFDerivAt", "HasFDerivAt_f_f_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_differentiableAt", "DifferentiableAt_f_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_differentiableWithinAt", "DifferentiableWithinAt_f_s_x", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_differentiable", "Differentiable_f", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_differentiableOn", "DifferentiableOn_f_s", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_measurable_apply_2", "Measurable_fun_p_colon_E_to_L_F_times_E_eq_gt_p_1_p_2", "Not an equality or iff proposition"),
    ("ContinuousLinearMap_compFormalMultilinearSeries_apply", "_unknown", "Empty proposition"),
    ("IsOpen_isOpen_inter_preimage_of_fderiv_eq_zero", "IsOpen_s_inter_f_inv_prime_t", "Not an equality or iff proposition"),
    ("IsOpen_exists_eq_add_of_fderiv_eq", "exists_a_s_EqOn_f_g_plus_a", "Not an equality or iff proposition"),
    ("IsOpen_eqOn_of_fderiv_eq", "s_EqOn_f_g", "Not an equality or iff proposition"),
    ("IsOpen_isOpen_inter_preimage_of_deriv_eq_zero", "IsOpen_s_inter_f_inv_prime_t", "Not an equality or iff proposition"),
    ("IsOpen_exists_eq_add_of_deriv_eq", "exists_a_s_EqOn_f_g_plus_a", "Not an equality or iff proposition"),
    ("IsOpen_eqOn_of_deriv_eq", "s_EqOn_f_g", "Not an equality or iff proposition"),
    ("IsOpen_uniqueDiffWithinAt", "UniqueDiffWithinAt_s_x", "Not an equality or iff proposition"),
    ("IsOpen_uniqueDiffOn", "UniqueDiffOn_s", "Not an equality or iff proposition"),
    ("IsOpen_reProdIm", "IsOpen_s_times_t", "Not an equality or iff proposition"),
    ("IsClosed_reProdIm", "IsClosed_s_times_t", "Not an equality or iff proposition"),
    ("Metric_instTietzeExtensionBall", "TietzeExtension_u_w_Metric_ball_0_colon_E_r", "Not an equality or iff proposition"),
    ("Metric_instTietzeExtensionClosedBall", "TietzeExtension_u_w_Metric_closedBall_y_r", "Not an equality or iff proposition"),
]
