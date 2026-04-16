"""Mathlib: Algebra Ring — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 768 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_algebra_ring"
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

def _r0000_toDistribMulActionHom_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgHom.toDistribMulActionHom_eq_coe
    # f.toDistribMulActionHom = ↑f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toDistribMulActionHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: NonUnitalAlgHom_toDistribMulActionHom_eq_coe"))
    except Exception:
        pass
    return results


def _r0001_to_distribMulActionHom_injective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgHom.to_distribMulActionHom_injective
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: NonUnitalAlgHom_to_distribMulActionHom_injective"))
    except Exception:
        pass
    return results


def _r0002_one_eq_span_one_set(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.one_eq_span_one_set
    # (1 : Submodule R A) = span R 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 4)
    if args is not None:
        try:
            rhs = OOp("span", (args[2], OLit(1),))
            results.append((rhs, "Mathlib: Submodule_one_eq_span_one_set"))
        except Exception:
            pass
    return results


def _r0003_one_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: one_mul
    # (1 : Submodule R A) * M = M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: one_mul"))
        except Exception:
            pass
    return results


def _r0004_smul_one_eq_span(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_one_eq_span
    # x • (1 : Submodule R A) = span R {x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("span", (OVar("R"), OVar("x"),))
            results.append((rhs, "Mathlib: smul_one_eq_span"))
        except Exception:
            pass
    return results


def _r0005_one_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: one_eq
    # σ (1 : A) = {1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sig", 1)
    if args is not None:
        try:
            rhs = OVar("_1")
            results.append((rhs, "Mathlib: one_eq"))
        except Exception:
            pass
    return results


def _r0006_unitsFstOne_val_val_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Unitization.unitsFstOne_val_val_fst
    # x.val.val.fst = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_val_val_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Unitization_unitsFstOne_val_val_fst"))
    except Exception:
        pass
    return results


def _r0007_unitsFstOne_val_inv_val_fst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Unitization.unitsFstOne_val_inv_val_fst
    # x.val⁻¹.val.fst = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_valinv_val_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Unitization_unitsFstOne_val_inv_val_fst"))
    except Exception:
        pass
    return results


def _r0008_toSubalgebra_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.toSubalgebra_mk
    # s.toSubalgebra h1 hmul =       Subalgebra.mk ⟨⟨⟨s, @hmul⟩, h1⟩, s.add_mem, s.zero_mem⟩         (by intro r; rw [Algebra.
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_toSubalgebra", 2)
    if args is not None:
        try:
            rhs = OOp("Subalgebra_mk", (OVar("s_at_hmul_h1_s_add_mem_s_zero_mem"), OOp("by", (OVar("intro"), OVar("r"), OVar("rw"), OVar("Algebra_algebraMap_eq_smul_one"), OVar("apply"), OVar("s_smul_mem"), OVar("_unknown"), args[0],)),))
            results.append((rhs, "Mathlib: Submodule_toSubalgebra_mk"))
        except Exception:
            pass
    return results


def _r0009_adjoin_insert_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.adjoin_insert_zero
    # adjoin R (insert 0 s) = adjoin R s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adjoin", 2)
    if args is not None:
        try:
            rhs = OOp("adjoin", (args[0], OVar("s"),))
            results.append((rhs, "Mathlib: Algebra_adjoin_insert_zero"))
        except Exception:
            pass
    return results


def _r0010_adjoin_insert_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.adjoin_insert_one
    # adjoin R (insert 1 s) = adjoin R s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adjoin", 2)
    if args is not None:
        try:
            rhs = OOp("adjoin", (args[0], OVar("s"),))
            results.append((rhs, "Mathlib: Algebra_adjoin_insert_one"))
        except Exception:
            pass
    return results


def _r0011_snd_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: snd_zero
    # (0 : Unitization R A).snd = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Unitization_R_A_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: snd_zero"))
    except Exception:
        pass
    return results


def _r0012_snd_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: snd_one
    # (1 : Unitization R A).snd = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Unitization_R_A_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: snd_one"))
    except Exception:
        pass
    return results


def _r0013_hom_add_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.hom_add_apply
    # (f + g) x = f x + g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_plus_g", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: AddCommGrpCat_hom_add_apply"))
        except Exception:
            pass
    return results


def _r0014_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.id_apply
    # (𝟙 R : R ⟶ R) r = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_R_colon_R_R", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CommRingCat_id_apply"))
        except Exception:
            pass
    return results


def _r0015_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CommRingCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0016_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.ofHom_id
    # ofHom (RingHom.id R) = 𝟙 (of R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("R"),)),))
            results.append((rhs, "Mathlib: CommRingCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0017_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: CommRingCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0018_quot_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingCat.Colimits.quot_one
    # Quot.mk Setoid.r one = (1 : ColimitType F)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("colon"), OVar("ColimitType"), OVar("F"),))
            results.append((rhs, "Mathlib: RingCat_Colimits_quot_one"))
        except Exception:
            pass
    return results


def _r0019_quot_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.Colimits.quot_one
    # Quot.mk Setoid.r one = (1 : ColimitType F)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("colon"), OVar("ColimitType"), OVar("F"),))
            results.append((rhs, "Mathlib: CommRingCat_Colimits_quot_one"))
        except Exception:
            pass
    return results


def _r0020_quot_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.Colimits.quot_neg
    # Quot.mk Setoid.r (neg x) = -(show ColimitType F from Quot.mk Setoid.r x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OVar("minus_show_ColimitType_F_from_Quot_mk_Setoid_r_x")
            results.append((rhs, "Mathlib: CommRingCat_Colimits_quot_neg"))
        except Exception:
            pass
    return results


def _r0021_toAlgHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.toAlgHom_comp
    # toAlgHom (f ≫ g) = (toAlgHom g).comp (toAlgHom f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAlgHom", 1)
    if args is not None:
        try:
            rhs = OOp("toAlgHom_g_comp", (OOp("toAlgHom", (OVar("f"),)),))
            results.append((rhs, "Mathlib: CommRingCat_toAlgHom_comp"))
        except Exception:
            pass
    return results


def _r0022_toAlgHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.toAlgHom_apply
    # toAlgHom f a = f.right a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAlgHom", 2)
    if args is not None:
        try:
            rhs = OOp("f_right", (args[1],))
            results.append((rhs, "Mathlib: CommRingCat_toAlgHom_apply"))
        except Exception:
            pass
    return results


def _r0023_mkUnder_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.mkUnder_ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: CommRingCat_mkUnder_ext"))
    except Exception:
        pass
    return results


def _r0024_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.coe_zero
    # ((0 : s) : K) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_s", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Subfield_coe_zero"))
        except Exception:
            pass
    return results


def _r0025_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.coe_one
    # ((1 : s) : K) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_s", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Subfield_coe_one"))
        except Exception:
            pass
    return results


def _r0026_normalize_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommGroupWithZero.normalize_eq_one
    # normalize a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: CommGroupWithZero_normalize_eq_one"))
        except Exception:
            pass
    return results


def _r0027_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.coe_zero
    # ⇑(0 : AddChar A M) = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_AddChar_A_M")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: AddChar_coe_zero"))
    except Exception:
        pass
    return results


def _r0028_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.one_apply
    # (1 : AddChar A M) a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_AddChar_A_M", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: AddChar_one_apply"))
        except Exception:
            pass
    return results


def _r0029_zero_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.zero_apply
    # (0 : AddChar A M) a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_AddChar_A_M", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: AddChar_zero_apply"))
        except Exception:
            pass
    return results


def _r0030_one_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.one_eq_zero
    # (1 : AddChar A M) = (0 : AddChar A M)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 4)
    if args is not None:
        try:
            rhs = OOp("_0", (args[0], args[1], args[2], args[3],))
            results.append((rhs, "Mathlib: AddChar_one_eq_zero"))
        except Exception:
            pass
    return results


def _r0031_coe_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.coe_eq_one
    # ⇑ψ = 1 ↔ ψ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("psi")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("psi"))), OLit(0)))
            results.append((rhs, "Mathlib: AddChar_coe_eq_one"))
    except Exception:
        pass
    return results


def _r0032_toMonoidHomEquiv_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.toMonoidHomEquiv_zero
    # toMonoidHomEquiv (0 : AddChar A M) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toMonoidHomEquiv", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: AddChar_toMonoidHomEquiv_zero"))
        except Exception:
            pass
    return results


def _r0033_toAddMonoidHomEquiv_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.toAddMonoidHomEquiv_zero
    # toAddMonoidHomEquiv (0 : AddChar A M) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAddMonoidHomEquiv", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: AddChar_toAddMonoidHomEquiv_zero"))
        except Exception:
            pass
    return results


def _r0034_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.coe_one
    # ⇑(1 : MulAut M) = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_MulAut_M")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: MulAut_coe_one"))
    except Exception:
        pass
    return results


def _r0035_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.one_apply
    # (1 : MulAut M) m = m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_MulAut_M", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MulAut_one_apply"))
        except Exception:
            pass
    return results


def _r0036_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.coe_one
    # ⇑(1 : AddAut A) = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_AddAut_A")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: AddAut_coe_one"))
    except Exception:
        pass
    return results


def _r0037_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.one_apply
    # (1 : AddAut A) a = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_AddAut_A", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: AddAut_one_apply"))
        except Exception:
            pass
    return results


def _r0038_mul_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.mul_comp
    # (g₁ * g₂).comp f = g₁.comp f * g₂.comp f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_1_star_g_2_comp", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("g_1_comp", (args[0],)), OOp("g_2_comp", (args[0],))))
            results.append((rhs, "Mathlib: OneHom_mul_comp"))
        except Exception:
            pass
    return results


def _r0039_inv_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.inv_comp
    # (g⁻¹).comp f = (g.comp f)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ginv_comp", 1)
    if args is not None:
        try:
            rhs = OVar("g_comp_f_inv")
            results.append((rhs, "Mathlib: OneHom_inv_comp"))
        except Exception:
            pass
    return results


def _r0040_div_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.div_comp
    # (g₁ / g₂).comp f = g₁.comp f / g₂.comp f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_1_slash_g_2_comp", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("g_1_comp", (args[0],)), OOp("g_2_comp", (args[0],))))
            results.append((rhs, "Mathlib: OneHom_div_comp"))
        except Exception:
            pass
    return results


def _r0041_toFun_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.toFun_eq_coe
    # f.toFun = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: OneHom_toFun_eq_coe"))
    except Exception:
        pass
    return results


def _r0042_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.comp_apply
    # g.comp f x = g (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 2)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[1],)),))
            results.append((rhs, "Mathlib: OneHom_comp_apply"))
        except Exception:
            pass
    return results


def _r0043_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.id_comp
    # (OneHom.id N).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OneHom_id_N_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: OneHom_id_comp"))
        except Exception:
            pass
    return results


def _r0044_one_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.one_comp
    # (1 : OneHom N P).comp f = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_OneHom_N_P_comp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: OneHom_one_comp"))
        except Exception:
            pass
    return results


def _r0045_comp_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.comp_one
    # f.comp (1 : OneHom M N) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: OneHom_comp_one"))
        except Exception:
            pass
    return results


def _r0046_unop_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOpposite.unop_pow
    # unop (x ^ n) = unop x ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("unop", (OVar("x"),)), OVar("n")))
            results.append((rhs, "Mathlib: MulOpposite_unop_pow"))
        except Exception:
            pass
    return results


def _r0047_unop_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddOpposite.unop_pow
    # unop (a ^ b) = unop a ^ b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("unop", (OVar("a"),)), OVar("b")))
            results.append((rhs, "Mathlib: AddOpposite_unop_pow"))
        except Exception:
            pass
    return results


def _r0048_coe_mulSingle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.coe_mulSingle
    # mulSingle f i = Pi.mulSingle (M := f) i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSingle", 2)
    if args is not None:
        try:
            rhs = OOp("Pi_mulSingle", (OOp("M", (OVar("colon_eq"), args[0],)), args[1],))
            results.append((rhs, "Mathlib: OneHom_coe_mulSingle"))
        except Exception:
            pass
    return results


def _r0049_coe_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SubgroupClass.coe_zpow
    # ((x ^ n : H) : G) = (x : G) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_pow_n_colon_H", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("x", (args[0], args[1],)), OVar("n")))
            results.append((rhs, "Mathlib: SubgroupClass_coe_zpow"))
        except Exception:
            pass
    return results


def _r0050_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_one
    # ((1 : H) : G) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_H", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Subgroup_coe_one"))
        except Exception:
            pass
    return results


def _r0051_coe_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_zpow
    # ((x ^ n : H) : G) = (x : G) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_pow_n_colon_H", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("x", (args[0], args[1],)), OVar("n")))
            results.append((rhs, "Mathlib: Subgroup_coe_zpow"))
        except Exception:
            pass
    return results


def _r0052_coe_zpowers(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_zpowers
    # ↑(zpowers g) = Set.range (g ^ · : ℤ → G)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("zpowers_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Set_range", (OOp("implies", (OOp("**", (OVar("g"), OOp("_unknown", (OVar("colon"), OVar("_unknown"),)))), OVar("G"))),))
            results.append((rhs, "Mathlib: Subgroup_coe_zpowers"))
    except Exception:
        pass
    return results


def _r0053_coe_set_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.coe_set_mk
    # (mk s h_one : Set M) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 5)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Submonoid_coe_set_mk"))
        except Exception:
            pass
    return results


def _r0054_mk_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.mk_eq_top
    # mk toSubsemigroup one_mem' = ⊤ ↔ toSubsemigroup = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OVar("top")))
            results.append((rhs, "Mathlib: Submonoid_mk_eq_top"))
        except Exception:
            pass
    return results


def _r0055_mk_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.mk_eq_bot
    # mk toSubsemigroup one_mem' = ⊥ ↔ (toSubsemigroup : Set M) = {1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("bot"), OOp("toSubsemigroup", (OVar("colon"), OVar("Set"), OVar("M"),)))), OVar("_1")))
            results.append((rhs, "Mathlib: Submonoid_mk_eq_bot"))
        except Exception:
            pass
    return results


def _r0056_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.coe_one
    # ((1 : S) : M) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_S", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Submonoid_coe_one"))
        except Exception:
            pass
    return results


def _r0057_mk_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.mk_eq_one
    # (⟨a, ha⟩ : S) = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_ha", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("a"))), OLit(1)))
            results.append((rhs, "Mathlib: Submonoid_mk_eq_one"))
        except Exception:
            pass
    return results


def _r0058_withOneCongr_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulEquiv.withOneCongr_symm
    # e.withOneCongr.symm = e.symm.withOneCongr
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_withOneCongr_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm_withOneCongr")
            results.append((rhs, "Mathlib: MulEquiv_withOneCongr_symm"))
    except Exception:
        pass
    return results


def _r0059_smul_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ZeroHom.smul_comp
    # (m • g).comp f = m • g.comp f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("m", (OVar("_unknown"), OVar("g_comp"), args[0],))
            results.append((rhs, "Mathlib: ZeroHom_smul_comp"))
        except Exception:
            pass
    return results


def _r0060_toMonoidHom_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidWithZeroHom.toMonoidHom_coe
    # f.toMonoidHom.toFun = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toMonoidHom_toFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MonoidWithZeroHom_toMonoidHom_coe"))
    except Exception:
        pass
    return results


def _r0061_snd_apply_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidWithZeroHom.snd_apply_coe
    # snd G₀ H₀ x = x.snd
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd", 3)
    if args is not None:
        try:
            rhs = OVar("x_snd")
            results.append((rhs, "Mathlib: MonoidWithZeroHom_snd_apply_coe"))
        except Exception:
            pass
    return results


def _r0062_fst_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidWithZeroHom.fst_inl
    # fst _ H₀ (inl _ _ x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst", 3)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: MonoidWithZeroHom_fst_inl"))
        except Exception:
            pass
    return results


def _r0063_eq_zero_or_unit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GroupWithZero.eq_zero_or_unit
    # a = 0 ∨ ∃ u : G₀ˣ, a = u
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("or", (OLit(0), OOp("exists", (OVar("u"), OVar("colon"), OVar("G_0"), OVar("a"),)))), OVar("u")))
            results.append((rhs, "Mathlib: GroupWithZero_eq_zero_or_unit"))
    except Exception:
        pass
    return results


def _r0064_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Module.End.coe_one
    # ⇑(1 : Module.End R M) = _root_.id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Module_End_R_M")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("root_id")
            results.append((rhs, "Mathlib: Module_End_coe_one"))
    except Exception:
        pass
    return results


def _r0065_toMvPolynomial_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.toMvPolynomial_one
    # (1 : Matrix n n R).toMvPolynomial = X
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Matrix_n_n_R_toMvPolynomial")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("X")
            results.append((rhs, "Mathlib: Matrix_toMvPolynomial_one"))
    except Exception:
        pass
    return results


def _r0066_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.coe_zero
    # ((0 : p) : M) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_p", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Submodule_coe_zero"))
        except Exception:
            pass
    return results


def _r0067_coeff_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidAlgebra.coeff_zero
    # coeff (0 : R[M]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coeff", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MonoidAlgebra_coeff_zero"))
        except Exception:
            pass
    return results


def _r0068_ofCoeff_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidAlgebra.ofCoeff_zero
    # (ofCoeff 0 : R[M]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofCoeff", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MonoidAlgebra_ofCoeff_zero"))
        except Exception:
            pass
    return results


def _r0069_coeff_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidAlgebra.coeff_eq_zero
    # coeff x = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coeff", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: MonoidAlgebra_coeff_eq_zero"))
        except Exception:
            pass
    return results


def _r0070_ofCoeff_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidAlgebra.ofCoeff_eq_zero
    # ofCoeff x = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofCoeff", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: MonoidAlgebra_ofCoeff_eq_zero"))
        except Exception:
            pass
    return results


def _r0071_erase_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidAlgebra.erase_zero
    # erase m (0 : R[M]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "erase", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MonoidAlgebra_erase_zero"))
        except Exception:
            pass
    return results


def _r0072_divOf_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddMonoidAlgebra.divOf_zero
    # x /ᵒᶠ 0 = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: AddMonoidAlgebra_divOf_zero"))
        except Exception:
            pass
    return results


def _r0073_C_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.C_pow
    # (C (a ^ n) : MvPolynomial σ R) = C a ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "C", 5)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("C", (OVar("a"),)), OVar("n")))
            results.append((rhs, "Mathlib: MvPolynomial_C_pow"))
        except Exception:
            pass
    return results


def _r0074_monomial_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.monomial_pow
    # monomial s a ^ e = monomial (e • s) (a ^ e)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("monomial", (OOp("e", (OVar("_unknown"), OVar("s"),)), OOp("**", (OVar("a"), args[1])),))
            results.append((rhs, "Mathlib: MvPolynomial_monomial_pow"))
        except Exception:
            pass
    return results


def _r0075_monomial_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.monomial_eq_zero
    # monomial s b = 0 ↔ b = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "monomial", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[1])), OLit(0)))
            results.append((rhs, "Mathlib: MvPolynomial_monomial_eq_zero"))
        except Exception:
            pass
    return results


def _r0076_support_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.support_one
    # (1 : MvPolynomial σ R).support = {0}
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_MvPolynomial_sig_R_support")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: MvPolynomial_support_one"))
    except Exception:
        pass
    return results


def _r0077_degrees_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.degrees_zero
    # degrees (0 : MvPolynomial σ R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "degrees", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MvPolynomial_degrees_zero"))
        except Exception:
            pass
    return results


def _r0078_divMonomial_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.divMonomial_zero
    # x /ᵐᵒⁿᵒᵐⁱᵃˡ 0 = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: MvPolynomial_divMonomial_zero"))
        except Exception:
            pass
    return results


def _r0079_eval_2_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.eval₂_one
    # (1 : MvPolynomial σ R).eval₂ f g = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_MvPolynomial_sig_R_eval_2", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MvPolynomial_eval_2_one"))
        except Exception:
            pass
    return results


def _r0080_eval_2_X_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.eval₂_X_pow
    # ((X s) ^ n).eval₂ f g = (g s) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "X_s_pow_n_eval_2", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("g", (OVar("s"),)), OVar("n")))
            results.append((rhs, "Mathlib: MvPolynomial_eval_2_X_pow"))
        except Exception:
            pass
    return results


def _r0081_pderiv_eq_zero_of_notMem_vars(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.pderiv_eq_zero_of_notMem_vars
    # pderiv i f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pderiv", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MvPolynomial_pderiv_eq_zero_of_notMem_vars"))
        except Exception:
            pass
    return results


def _r0082_rename_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.rename_zero
    # (0 : MvPolynomial σ R).rename f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_MvPolynomial_sig_R_rename", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MvPolynomial_rename_zero"))
        except Exception:
            pass
    return results


def _r0083_unop_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOpposite.unop_zero
    # unop (0 : αᵐᵒᵖ) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: MulOpposite_unop_zero"))
        except Exception:
            pass
    return results


def _r0084_op_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOpposite.op_one
    # op (1 : α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "op", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MulOpposite_op_one"))
        except Exception:
            pass
    return results


def _r0085_unop_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOpposite.unop_one
    # unop (1 : αᵐᵒᵖ) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MulOpposite_unop_one"))
        except Exception:
            pass
    return results


def _r0086_unop_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOpposite.unop_eq_zero_iff
    # a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("_0", (OVar("colon"), OVar("a"),)), OVar("a"))), OOp("_0", (OVar("colon"), OVar("a"),))))
            results.append((rhs, "Mathlib: MulOpposite_unop_eq_zero_iff"))
    except Exception:
        pass
    return results


def _r0087_op_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOpposite.op_eq_zero_iff
    # op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "op", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("_0", (OVar("colon"), args[0],)), args[0])), OOp("_0", (OVar("colon"), args[0],))))
            results.append((rhs, "Mathlib: MulOpposite_op_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0088_unop_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddOpposite.unop_one
    # unop 1 = (1 : α)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OVar("colon"), OVar("a"),))
            results.append((rhs, "Mathlib: AddOpposite_unop_one"))
        except Exception:
            pass
    return results


def _r0089_op_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddOpposite.op_eq_one_iff
    # op a = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "op", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: AddOpposite_op_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0090_unop_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddOpposite.unop_eq_one_iff
    # unop a = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: AddOpposite_unop_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0091_mk_div_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulArchimedeanClass.mk_div_comm
    # mk (a / b) = mk (b / a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 1)
    if args is not None:
        try:
            rhs = OOp("pair", (OOp("//", (OVar("b"), OVar("a"))),))
            results.append((rhs, "Mathlib: MulArchimedeanClass_mk_div_comm"))
        except Exception:
            pass
    return results


def _r0092_coe_oneLE(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GroupCone.coe_oneLE
    # oneLE H = {x : H | 1 ≤ x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "oneLE", 1)
    if args is not None:
        try:
            rhs = OVar("x_colon_H_pipe_1_le_x")
            results.append((rhs, "Mathlib: GroupCone_coe_oneLE"))
        except Exception:
            pass
    return results


def _r0093_nonneg_toAddGroupCone(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingCone.nonneg_toAddGroupCone
    # (nonneg T).toAddGroupCone = .nonneg T
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("nonneg_T_toAddGroupCone")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("nonneg", (OVar("T"),))
            results.append((rhs, "Mathlib: RingCone_nonneg_toAddGroupCone"))
    except Exception:
        pass
    return results


def _r0094_coe_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingCone.coe_nonneg
    # nonneg T = {x : T | 0 ≤ x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nonneg", 1)
    if args is not None:
        try:
            rhs = OVar("x_colon_T_pipe_0_le_x")
            results.append((rhs, "Mathlib: RingCone_coe_nonneg"))
        except Exception:
            pass
    return results


def _r0095_ofFinsupp_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.ofFinsupp_one
    # (⟨1⟩ : R[X]) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Polynomial_ofFinsupp_one"))
        except Exception:
            pass
    return results


def _r0096_toFinsupp_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.toFinsupp_one
    # (1 : R[X]).toFinsupp = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_R_X_toFinsupp")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Polynomial_toFinsupp_one"))
    except Exception:
        pass
    return results


def _r0097_toFinsupp_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.toFinsupp_eq_zero
    # a.toFinsupp = 0 ↔ a = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_toFinsupp")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("a"))), OLit(0)))
            results.append((rhs, "Mathlib: Polynomial_toFinsupp_eq_zero"))
    except Exception:
        pass
    return results


def _r0098_toFinsupp_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.toFinsupp_eq_one
    # a.toFinsupp = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_toFinsupp")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("a"))), OLit(1)))
            results.append((rhs, "Mathlib: Polynomial_toFinsupp_eq_one"))
    except Exception:
        pass
    return results


def _r0099_ofFinsupp_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.ofFinsupp_eq_one
    # (⟨a⟩ : R[X]) = 1 ↔ a = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("a"))), OLit(1)))
            results.append((rhs, "Mathlib: Polynomial_ofFinsupp_eq_one"))
        except Exception:
            pass
    return results


def _r0100_evalEval_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.evalEval_zero
    # (0 : R[X][Y]).evalEval x y = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_R_X_Y_evalEval", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_evalEval_zero"))
        except Exception:
            pass
    return results


def _r0101_evalEval_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.evalEval_one
    # (1 : R[X][Y]).evalEval x y = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_R_X_Y_evalEval", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Polynomial_evalEval_one"))
        except Exception:
            pass
    return results


def _r0102_mul_coeff_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.mul_coeff_one
    # coeff (p * q) 1 = coeff p 0 * coeff q 1 + coeff p 1 * coeff q 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coeff", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (OOp("coeff", (OVar("p"), OLit(0),)), OOp("coeff", (OVar("q"), OLit(1),)))), OOp("*", (OOp("coeff", (OVar("p"), OLit(1),)), OOp("coeff", (OVar("q"), OLit(0),))))))
            results.append((rhs, "Mathlib: Polynomial_mul_coeff_one"))
        except Exception:
            pass
    return results


def _r0103_natDegree_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.natDegree_zero
    # natDegree (0 : R[X]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "natDegree", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_natDegree_zero"))
        except Exception:
            pass
    return results


def _r0104_degree_C_mul_X_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.degree_C_mul_X_pow
    # degree (C a * X ^ n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "degree", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Polynomial_degree_C_mul_X_pow"))
        except Exception:
            pass
    return results


def _r0105_trailingDegree_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.trailingDegree_zero
    # trailingDegree (0 : R[X]) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trailingDegree", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Polynomial_trailingDegree_zero"))
        except Exception:
            pass
    return results


def _r0106_trailingCoeff_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.trailingCoeff_zero
    # trailingCoeff (0 : R[X]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trailingCoeff", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_trailingCoeff_zero"))
        except Exception:
            pass
    return results


def _r0107_natTrailingDegree_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.natTrailingDegree_zero
    # natTrailingDegree (0 : R[X]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "natTrailingDegree", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_natTrailingDegree_zero"))
        except Exception:
            pass
    return results


def _r0108_natTrailingDegree_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.natTrailingDegree_eq_zero
    # natTrailingDegree p = 0 ↔ p = 0 ∨ coeff p 0 ≠ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "natTrailingDegree", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OOp("!=", (OOp("or", (OLit(0), OOp("coeff", (args[0], OLit(0),)))), OLit(0)))))
            results.append((rhs, "Mathlib: Polynomial_natTrailingDegree_eq_zero"))
        except Exception:
            pass
    return results


def _r0109_natTrailingDegree_ne_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.natTrailingDegree_ne_zero
    # natTrailingDegree p ≠ 0 ↔ p ≠ 0 ∧ coeff p 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_natTrailingDegree_ne_zero"))
        except Exception:
            pass
    return results


def _r0110_natTrailingDegree_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.natTrailingDegree_one
    # natTrailingDegree (1 : R[X]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "natTrailingDegree", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_natTrailingDegree_one"))
        except Exception:
            pass
    return results


def _r0111_trailingDegree_C_mul_X_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.trailingDegree_C_mul_X_pow
    # trailingDegree (C a * X ^ n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trailingDegree", 1)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Polynomial_trailingDegree_C_mul_X_pow"))
        except Exception:
            pass
    return results


def _r0112_iterate_derivative_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.iterate_derivative_zero
    # derivative^[k] (0 : R[X]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "derivativepow_k", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_iterate_derivative_zero"))
        except Exception:
            pass
    return results


def _r0113_derivative_of_natDegree_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.derivative_of_natDegree_zero
    # derivative p = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "derivative", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_derivative_of_natDegree_zero"))
        except Exception:
            pass
    return results


def _r0114_derivative_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.derivative_one
    # derivative (1 : R[X]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "derivative", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_derivative_one"))
        except Exception:
            pass
    return results


def _r0115_iterate_derivative_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.iterate_derivative_one
    # derivative^[k] (1 : R[X]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "derivativepow_k", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_iterate_derivative_one"))
        except Exception:
            pass
    return results


def _r0116_natDegree_eq_zero_of_derivative_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.natDegree_eq_zero_of_derivative_eq_zero
    # f.natDegree = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_natDegree")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_natDegree_eq_zero_of_derivative_eq_zero"))
    except Exception:
        pass
    return results


def _r0117_eval_2_X_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.eval₂_X_pow
    # (X ^ n).eval₂ f x = x ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "X_pow_n_eval_2", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[1], OVar("n")))
            results.append((rhs, "Mathlib: Polynomial_eval_2_X_pow"))
        except Exception:
            pass
    return results


def _r0118_expand_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.expand_one
    # expand R 1 f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "expand", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: Polynomial_expand_one"))
        except Exception:
            pass
    return results


def _r0119_hasseDeriv_eq_zero_of_lt_natDegree(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.hasseDeriv_eq_zero_of_lt_natDegree
    # hasseDeriv n p = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hasseDeriv", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_hasseDeriv_eq_zero_of_lt_natDegree"))
        except Exception:
            pass
    return results


def _r0120_homogenize_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.homogenize_one
    # homogenize (1 : R[X]) n = .X 1 ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "homogenize", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("X", (OLit(1),)), args[1]))
            results.append((rhs, "Mathlib: Polynomial_homogenize_one"))
        except Exception:
            pass
    return results


def _r0121_divX_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.divX_eq_zero_iff
    # divX p = 0 ↔ p = C (p.coeff 0)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "divX", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OOp("C", (OOp("p_coeff", (OLit(0),)),))))
            results.append((rhs, "Mathlib: Polynomial_divX_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0122_divX_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.divX_one
    # divX (1 : R[X]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "divX", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_divX_one"))
        except Exception:
            pass
    return results


def _r0123_natDegree_divX_eq_natDegree_tsub_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.natDegree_divX_eq_natDegree_tsub_one
    # p.divX.natDegree = p.natDegree - 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_divX_natDegree")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("p_natDegree"), OLit(1)))
            results.append((rhs, "Mathlib: Polynomial_natDegree_divX_eq_natDegree_tsub_one"))
    except Exception:
        pass
    return results


def _r0124_toLaurent_C_mul_X_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.toLaurent_C_mul_X_pow
    # toLaurent (Polynomial.C r * X ^ n) = C r * T n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toLaurent", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("C", (OVar("r"),)), OOp("T", (OVar("n"),))))
            results.append((rhs, "Mathlib: Polynomial_toLaurent_C_mul_X_pow"))
        except Exception:
            pass
    return results


def _r0125_mirror_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.mirror_eq_zero
    # p.mirror = 0 ↔ p = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_mirror")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("p"))), OLit(0)))
            results.append((rhs, "Mathlib: Polynomial_mirror_eq_zero"))
    except Exception:
        pass
    return results


def _r0126_eq_one_of_isUnit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Monic.eq_one_of_isUnit
    # p = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Polynomial_Monic_eq_one_of_isUnit"))
    except Exception:
        pass
    return results


def _r0127_reflect_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.reflect_zero
    # reflect N (0 : R[X]) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reflect", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_reflect_zero"))
        except Exception:
            pass
    return results


def _r0128_reflect_one_X(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.reflect_one_X
    # reflect 1 (X : R[X]) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "reflect", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Polynomial_reflect_one_X"))
        except Exception:
            pass
    return results


def _r0129_smeval_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.smeval_one
    # (1 : R[X]).smeval x = 1 • x ^ 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_R_X_smeval", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("_1", (OVar("_unknown"), args[0],)), OLit(0)))
            results.append((rhs, "Mathlib: Polynomial_smeval_one"))
        except Exception:
            pass
    return results


def _r0130_taylor_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.taylor_zero
    # taylor 0 f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "taylor", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Polynomial_taylor_zero"))
        except Exception:
            pass
    return results


def _r0131_taylor_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.taylor_one
    # taylor r (1 : R[X]) = C 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "taylor", 2)
    if args is not None:
        try:
            rhs = OOp("C", (OLit(1),))
            results.append((rhs, "Mathlib: Polynomial_taylor_one"))
        except Exception:
            pass
    return results


def _r0132_taylor_coeff_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.taylor_coeff_one
    # (taylor r f).coeff 1 = f.derivative.eval r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "taylor_r_f_coeff", 1)
    if args is not None:
        try:
            rhs = OOp("f_derivative_eval", (OVar("r"),))
            results.append((rhs, "Mathlib: Polynomial_taylor_coeff_one"))
        except Exception:
            pass
    return results


def _r0133_taylor_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.taylor_eq_zero
    # taylor r f = 0 ↔ f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "taylor", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[1])), OLit(0)))
            results.append((rhs, "Mathlib: Polynomial_taylor_eq_zero"))
        except Exception:
            pass
    return results


def _r0134_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingAut.coe_one
    # ⇑(1 : R ≃+* R) = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_R_plus_star_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: RingAut_coe_one"))
    except Exception:
        pass
    return results


def _r0135_closure_mul_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddSubsemigroup.closure_mul_self
    # closure {x * x | x ≠ (0 : R)} = sumNonzeroSq R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("sumNonzeroSq", (OVar("R"),))
            results.append((rhs, "Mathlib: AddSubsemigroup_closure_mul_self"))
        except Exception:
            pass
    return results


def _r0136_fst_comp_coe_prodComm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingEquiv.fst_comp_coe_prodComm
    # (RingHom.fst S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.snd R S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "RingHom_fst_S_R_comp", 1)
    if args is not None:
        try:
            rhs = OOp("RingHom_snd", (OVar("R"), OVar("S"),))
            results.append((rhs, "Mathlib: RingEquiv_fst_comp_coe_prodComm"))
        except Exception:
            pass
    return results


def _r0137_one_eq_closure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddSubmonoid.one_eq_closure
    # (1 : AddSubmonoid R) = closure {1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 3)
    if args is not None:
        try:
            rhs = OOp("closure", (OVar("_1"),))
            results.append((rhs, "Mathlib: AddSubmonoid_one_eq_closure"))
        except Exception:
            pass
    return results


def _r0138_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subring.coe_zero
    # ((0 : s) : R) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_s", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Subring_coe_zero"))
        except Exception:
            pass
    return results


def _r0139_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subring.coe_one
    # ((1 : s) : R) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_s", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Subring_coe_one"))
        except Exception:
            pass
    return results


def _r0140_coe_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subring.coe_eq_zero_iff
    # (x : R) = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("x"))), OLit(0)))
            results.append((rhs, "Mathlib: Subring_coe_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0141_closure_insert_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subsemiring.closure_insert_one
    # closure (insert 1 s) = closure s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("closure", (OVar("s"),))
            results.append((rhs, "Mathlib: Subsemiring_closure_insert_one"))
        except Exception:
            pass
    return results


def _r0142_coe_set_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subsemiring.coe_set_mk
    # (mk toSubmonoid add_mem zero_mem : Set R) = toSubmonoid
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 6)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Subsemiring_coe_set_mk"))
        except Exception:
            pass
    return results


def _r0143_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subsemiring.coe_zero
    # ((0 : s) : R) = (0 : R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_s", 2)
    if args is not None:
        try:
            rhs = OOp("_0", (args[0], args[1],))
            results.append((rhs, "Mathlib: Subsemiring_coe_zero"))
        except Exception:
            pass
    return results


def _r0144_zmod_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.zmod_zero
    # zmod n 0 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zmod", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: AddChar_zmod_zero"))
        except Exception:
            pass
    return results


def _r0145_doubleDualEmb_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.doubleDualEmb_eq_zero
    # (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) = 0 ↔ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "doubleDualEmb", 5)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: AddChar_doubleDualEmb_eq_zero"))
        except Exception:
            pass
    return results


def _r0146_inner_comm_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TensorProduct.inner_comm_comm
    # inner 𝕜 (TensorProduct.comm 𝕜 E F x) (TensorProduct.comm 𝕜 E F y) = inner 𝕜 x y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inner", 3)
    if args is not None:
        try:
            rhs = OOp("inner", (args[0], OVar("x"), OVar("y"),))
            results.append((rhs, "Mathlib: TensorProduct_inner_comm_comm"))
        except Exception:
            pass
    return results


def _r0147_commIsometry_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TensorProduct.commIsometry_symm
    # (commIsometry 𝕜 E F).symm = commIsometry 𝕜 F E
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("commIsometry_E_F_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("commIsometry", (OVar("_unknown"), OVar("F"), OVar("E"),))
            results.append((rhs, "Mathlib: TensorProduct_commIsometry_symm"))
    except Exception:
        pass
    return results


def _r0148_norm_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TensorProduct.norm_comm
    # ‖TensorProduct.comm 𝕜 E F x‖ = ‖x‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "TensorProduct_comm", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: TensorProduct_norm_comm"))
        except Exception:
            pass
    return results


def _r0149_nnnorm_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TensorProduct.nnnorm_comm
    # ‖TensorProduct.comm 𝕜 E F x‖₊ = ‖x‖₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "TensorProduct_comm", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: TensorProduct_nnnorm_comm"))
        except Exception:
            pass
    return results


def _r0150_enorm_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TensorProduct.enorm_comm
    # ‖TensorProduct.comm 𝕜 E F x‖ₑ = ‖x‖ₑ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "TensorProduct_comm", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: TensorProduct_enorm_comm"))
        except Exception:
            pass
    return results


def _r0151_zero_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GroupSeminorm.zero_apply
    # (0 : GroupSeminorm E) x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_GroupSeminorm_E", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: GroupSeminorm_zero_apply"))
        except Exception:
            pass
    return results


def _r0152_zero_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GroupSeminorm.zero_comp
    # (0 : GroupSeminorm E).comp f = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_GroupSeminorm_E_comp", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: GroupSeminorm_zero_comp"))
        except Exception:
            pass
    return results


def _r0153_toLpLin_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.toLpLin_pow
    # toLpLin p p (A ^ k) = toLpLin p p A ^ k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toLpLin", 3)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("toLpLin", (args[1], args[1], OVar("A"),)), OVar("k")))
            results.append((rhs, "Mathlib: Matrix_toLpLin_pow"))
        except Exception:
            pass
    return results


def _r0154_toLpLin_symm_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.toLpLin_symm_pow
    # (toLpLin p p).symm (A ^ k) = (toLpLin p p).symm A ^ k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toLpLin_p_p_symm", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("toLpLin_p_p_symm", (OVar("A"),)), OVar("k")))
            results.append((rhs, "Mathlib: Matrix_toLpLin_symm_pow"))
        except Exception:
            pass
    return results


def _r0155_norm_smul_one_eq_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.norm_smul_one_eq_norm
    # ‖x • (1 : 𝕜')‖ = ‖x‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Algebra_norm_smul_one_eq_norm"))
        except Exception:
            pass
    return results


def _r0156_cauchyBound_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.cauchyBound_zero
    # cauchyBound (0 : K[X]) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cauchyBound", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Polynomial_cauchyBound_zero"))
        except Exception:
            pass
    return results


def _r0157_cauchyBound_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.cauchyBound_one
    # cauchyBound (1 : K[X]) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cauchyBound", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Polynomial_cauchyBound_one"))
        except Exception:
            pass
    return results


def _r0158_logMahlerMeasure_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.logMahlerMeasure_one
    # (1 : ℂ[X]).logMahlerMeasure = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_X_logMahlerMeasure")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_logMahlerMeasure_one"))
    except Exception:
        pass
    return results


def _r0159_mahlerMeasure_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.mahlerMeasure_one
    # (1 : ℂ[X]).mahlerMeasure = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_X_mahlerMeasure")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Polynomial_mahlerMeasure_one"))
    except Exception:
        pass
    return results


def _r0160_apply_ne_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.IsAdjMatrix.apply_ne_one_iff
    # ¬A i j = 1 ↔ A i j = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not_A", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OOp("A", (args[0], args[1],)))), OLit(0)))
            results.append((rhs, "Mathlib: Matrix_IsAdjMatrix_apply_ne_one_iff"))
        except Exception:
            pass
    return results


def _r0161_apply_ne_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.IsAdjMatrix.apply_ne_zero_iff
    # ¬A i j = 0 ↔ A i j = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "not_A", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("A", (args[0], args[1],)))), OLit(1)))
            results.append((rhs, "Mathlib: Matrix_IsAdjMatrix_apply_ne_zero_iff"))
        except Exception:
            pass
    return results


def _r0162_diagonal_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.diagonal_eq_zero
    # diagonal d = 0 ↔ d = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "diagonal", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Matrix_diagonal_eq_zero"))
        except Exception:
            pass
    return results


def _r0163_diagonal_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.diagonal_eq_one
    # diagonal d = 1 ↔ d = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "diagonal", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OLit(1)))
            results.append((rhs, "Mathlib: Matrix_diagonal_eq_one"))
        except Exception:
            pass
    return results


def _r0164_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.one_apply
    # (1 : Matrix n n α) i j = if i = j then 1 else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_Matrix_n_n_a", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0],)), OOp("j", (OVar("then"), OLit(1), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: Matrix_one_apply"))
        except Exception:
            pass
    return results


def _r0165_one_apply_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.one_apply_ne
    # i ≠ j → (1 : Matrix n n α) i j = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_Matrix_n_n_a", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Matrix_one_apply_ne"))
        except Exception:
            pass
    return results


def _r0166_transpose_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.transpose_eq_one
    # Mᵀ = 1 ↔ M = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("M")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("M"))), OLit(1)))
            results.append((rhs, "Mathlib: Matrix_transpose_eq_one"))
    except Exception:
        pass
    return results


def _r0167_valuation_X_eq_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.valuation_X_eq_neg_one
    # (idealX K).valuation K⟮X⟯ RatFunc.X = exp (-1 : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "idealX_K_valuation", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (OOp("minus_1", (OVar("colon"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: Polynomial_valuation_X_eq_neg_one"))
        except Exception:
            pass
    return results


def _r0168_natSepDegree_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.natSepDegree_zero
    # (0 : F[X]).natSepDegree = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_F_X_natSepDegree")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_natSepDegree_zero"))
    except Exception:
        pass
    return results


def _r0169_natSepDegree_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.natSepDegree_one
    # (1 : F[X]).natSepDegree = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_F_X_natSepDegree")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_natSepDegree_one"))
    except Exception:
        pass
    return results


def _r0170_toConvexCone_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.toConvexCone_bot
    # (⊥ : Submodule R M).toConvexCone = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Submodule_R_M_toConvexCone")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Submodule_toConvexCone_bot"))
    except Exception:
        pass
    return results


def _r0171_toConvexCone_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.toConvexCone_top
    # (⊤ : Submodule R M).toConvexCone = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_Submodule_R_M_toConvexCone")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Submodule_toConvexCone_top"))
    except Exception:
        pass
    return results


def _r0172_toConvexCone_inf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.toConvexCone_inf
    # (C₁ ⊓ C₂).toConvexCone = C₁.toConvexCone ⊓ C₂.toConvexCone
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("C_1_C_2_toConvexCone")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("C_1_toConvexCone", (OVar("_unknown"), OVar("C_2_toConvexCone"),))
            results.append((rhs, "Mathlib: Submodule_toConvexCone_inf"))
    except Exception:
        pass
    return results


def _r0173_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LeftInvariantDerivation.coe_zero
    # ⇑(0 : LeftInvariantDerivation I G) = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_LeftInvariantDerivation_I_G")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: LeftInvariantDerivation_coe_zero"))
    except Exception:
        pass
    return results


def _r0174_lift_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LeftInvariantDerivation.lift_zero
    # (↑(0 : LeftInvariantDerivation I G) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_LeftInvariantDerivation_I_G", 9)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: LeftInvariantDerivation_lift_zero"))
        except Exception:
            pass
    return results


def _r0175_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.Commensurable.eq
    # commensurator H = commensurator K
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "commensurator", 1)
    if args is not None:
        try:
            rhs = OOp("commensurator", (OVar("K"),))
            results.append((rhs, "Mathlib: Subgroup_Commensurable_eq"))
        except Exception:
            pass
    return results


def _r0176_commutator_bot_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.commutator_bot_right
    # ⁅H₁, ⊥⁆ = (⊥ : Subgroup G)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_1", 1)
    if args is not None:
        try:
            rhs = OOp("bot", (OVar("colon"), OVar("Subgroup"), OVar("G"),))
            results.append((rhs, "Mathlib: Subgroup_commutator_bot_right"))
        except Exception:
            pass
    return results


def _r0177_swap_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Monoid.Coprod.swap_eq_one
    # swap M N x = 1 ↔ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "swap", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[2])), OLit(1)))
            results.append((rhs, "Mathlib: Monoid_Coprod_swap_eq_one"))
        except Exception:
            pass
    return results


def _r0178_exponent_multiplicative(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Monoid.exponent_multiplicative
    # exponent (Multiplicative G) = AddMonoid.exponent G
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exponent", 1)
    if args is not None:
        try:
            rhs = OOp("AddMonoid_exponent", (OVar("G"),))
            results.append((rhs, "Mathlib: Monoid_exponent_multiplicative"))
        except Exception:
            pass
    return results


def _r0179_pow_exponent_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.pow_exponent_eq_one
    # g ^ Monoid.exponent H = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Subgroup_pow_exponent_eq_one"))
        except Exception:
            pass
    return results


def _r0180_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulDistribMulActionHom.id_comp
    # comp (MulDistribMulActionHom.id N) f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: MulDistribMulActionHom_id_comp"))
        except Exception:
            pass
    return results


def _r0181_comp_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulDistribMulActionHom.comp_id
    # f.comp (MulDistribMulActionHom.id M) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MulDistribMulActionHom_comp_id"))
        except Exception:
            pass
    return results


def _r0182_noncommCoprod_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.noncommCoprod_comp_inr
    # (f.noncommCoprod g comm).comp (inr M N) = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_noncommCoprod_g_comm_comp", 1)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: MonoidHom_noncommCoprod_comp_inr"))
        except Exception:
            pass
    return results


def _r0183_mk_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuotientGroup.mk_pow
    # ((a ^ n : G) : Q) = (a : Q) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_pow_n_colon_G", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("a", (args[0], args[1],)), OVar("n")))
            results.append((rhs, "Mathlib: QuotientGroup_mk_pow"))
        except Exception:
            pass
    return results


def _r0184_mk_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: QuotientGroup.mk_zpow
    # ((a ^ n : G) : Q) = (a : Q) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a_pow_n_colon_G", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("a", (args[0], args[1],)), OVar("n")))
            results.append((rhs, "Mathlib: QuotientGroup_mk_zpow"))
        except Exception:
            pass
    return results


def _r0185_finTwoProd_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Module.Basis.finTwoProd_one
    # Basis.finTwoProd R 1 = (0, 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Basis_finTwoProd", 2)
    if args is not None:
        try:
            rhs = OOp("_0", (OLit(1),))
            results.append((rhs, "Mathlib: Module_Basis_finTwoProd_one"))
        except Exception:
            pass
    return results


def _r0186_repr_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Module.Basis.repr_smul
    # (g • b).repr = (DistribMulAction.toLinearEquiv _ _ g).symm.trans b.repr
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_b_repr")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("DistribMulAction_toLinearEquiv_g_symm_trans", (OVar("b_repr"),))
            results.append((rhs, "Mathlib: Module_Basis_repr_smul"))
    except Exception:
        pass
    return results


def _r0187_cramer_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.cramer_zero
    # cramer (0 : Matrix n n α) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cramer", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Matrix_cramer_zero"))
        except Exception:
            pass
    return results


def _r0188_circulant_col_zero_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.circulant_col_zero_eq
    # circulant v i 0 = v i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "circulant", 3)
    if args is not None:
        try:
            rhs = OOp("v", (args[1],))
            results.append((rhs, "Mathlib: Matrix_circulant_col_zero_eq"))
        except Exception:
            pass
    return results


def _r0189_transpose_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.transpose_zero
    # (0 : Matrix m n α)ᵀ = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Matrix_m_n_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Matrix_transpose_zero"))
    except Exception:
        pass
    return results


def _r0190_transpose_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.transpose_eq_zero
    # Mᵀ = 0 ↔ M = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("M")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("M"))), OLit(0)))
            results.append((rhs, "Mathlib: Matrix_transpose_eq_zero"))
    except Exception:
        pass
    return results


def _r0191_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.coe_one
    # ↑(1 : GL n R) = (1 : Matrix n n R)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_GL_n_R")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_1", (OVar("colon"), OVar("Matrix"), OVar("n"), OVar("n"), OVar("R"),))
            results.append((rhs, "Mathlib: Matrix_coe_one"))
    except Exception:
        pass
    return results


def _r0192_den_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.den_zero
    # (0 : Matrix m n ℚ).den = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Matrix_m_n_den")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Matrix_den_zero"))
    except Exception:
        pass
    return results


def _r0193_num_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.num_zero
    # (0 : Matrix m n ℚ).num = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Matrix_m_n_num")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Matrix_num_zero"))
    except Exception:
        pass
    return results


def _r0194_den_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.den_one
    # (1 : Matrix m m ℚ).den = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Matrix_m_m_den")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Matrix_den_one"))
    except Exception:
        pass
    return results


def _r0195_num_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.num_one
    # (1 : Matrix m m ℚ).num = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Matrix_m_m_num")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Matrix_num_one"))
    except Exception:
        pass
    return results


def _r0196_vecMulVec_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.vecMulVec_one
    # vecMulVec x 1 = replicateCol m x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "vecMulVec", 2)
    if args is not None:
        try:
            rhs = OOp("replicateCol", (OVar("m"), args[0],))
            results.append((rhs, "Mathlib: Matrix_vecMulVec_one"))
        except Exception:
            pass
    return results


def _r0197_replicateCol_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.replicateCol_eq_zero
    # replicateCol ι v = 0 ↔ v = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicateCol", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[1])), OLit(0)))
            results.append((rhs, "Mathlib: Matrix_replicateCol_eq_zero"))
        except Exception:
            pass
    return results


def _r0198_replicateRow_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.replicateRow_eq_zero
    # replicateRow ι v = 0 ↔ v = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "replicateRow", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[1])), OLit(0)))
            results.append((rhs, "Mathlib: Matrix_replicateRow_eq_zero"))
        except Exception:
            pass
    return results


def _r0199_updateRow_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.updateRow_comm
    # (A.updateRow i x).updateRow i' y = (A.updateRow i' y).updateRow i x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "A_updateRow_i_x_updateRow", 2)
    if args is not None:
        try:
            rhs = OOp("A_updateRow_i_prime_y_updateRow", (OVar("i"), OVar("x"),))
            results.append((rhs, "Mathlib: Matrix_updateRow_comm"))
        except Exception:
            pass
    return results


def _r0200_detp_neg_one_diagonal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.detp_neg_one_diagonal
    # detp (-1) (diagonal d) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "detp", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Matrix_detp_neg_one_diagonal"))
        except Exception:
            pass
    return results


def _r0201_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.coe_one
    # (1 : SpecialLinearGroup n R) = (1 : Matrix n n R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 4)
    if args is not None:
        try:
            rhs = OOp("_1", (args[0], OVar("Matrix"), args[2], args[2], args[3],))
            results.append((rhs, "Mathlib: Matrix_coe_one"))
        except Exception:
            pass
    return results


def _r0202_vec_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.vec_eq_zero_iff
    # vec A = 0 ↔ A = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "vec", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: Matrix_vec_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0203_mk_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.Quotient.mk_eq_zero
    # (mk x : M ⧸ p) = 0 ↔ x ∈ p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 5)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OOp("in", (args[0], args[4]))))
            results.append((rhs, "Mathlib: Submodule_Quotient_mk_eq_zero"))
        except Exception:
            pass
    return results


def _r0204_gradedComm_of_tmul_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TensorProduct.gradedComm_of_tmul_of
    # gradedComm R 𝒜 ℬ (lof R _ 𝒜 i a ⊗ₜ lof R _ ℬ j b) =       (-1 : ℤˣ) ^ (j * i) • (lof R _ ℬ _ b ⊗ₜ lof R _ 𝒜 _ a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "gradedComm", 4)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("minus_1", (OVar("colon"), args[2],)), OOp("j_star_i", (args[2], OOp("lof", (args[0], args[2], args[2], args[2], OVar("b"), args[2], OVar("lof"), args[0], args[2], args[2], args[2], OVar("a"),)),))))
            results.append((rhs, "Mathlib: TensorProduct_gradedComm_of_tmul_of"))
        except Exception:
            pass
    return results


def _r0205_lTensorBot_one_tmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.lTensorBot_one_tmul
    # A.lTensorBot (1 ⊗ₜ[R] a) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "A_lTensorBot", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Subalgebra_lTensorBot_one_tmul"))
        except Exception:
            pass
    return results


def _r0206_rTensorBot_tmul_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.rTensorBot_tmul_one
    # A.rTensorBot (a ⊗ₜ[R] 1) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "A_rTensorBot", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Subalgebra_rTensorBot_tmul_one"))
        except Exception:
            pass
    return results


def _r0207_mulMap_one_left_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.mulMap_one_left_eq
    # mulMap (Subalgebra.toSubmodule ⊥) N = N.subtype ∘ₗ N.lTensorOne.toLinearMap
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulMap", 2)
    if args is not None:
        try:
            rhs = OOp("N_subtype", (OVar("comp"), OVar("N_lTensorOne_toLinearMap"),))
            results.append((rhs, "Mathlib: Submodule_mulMap_one_left_eq"))
        except Exception:
            pass
    return results


def _r0208_mulMap_one_right_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.mulMap_one_right_eq
    # mulMap M (Subalgebra.toSubmodule ⊥) = M.subtype ∘ₗ M.rTensorOne.toLinearMap
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulMap", 2)
    if args is not None:
        try:
            rhs = OOp("M_subtype", (OVar("comp"), OVar("M_rTensorOne_toLinearMap"),))
            results.append((rhs, "Mathlib: Submodule_mulMap_one_right_eq"))
        except Exception:
            pass
    return results


def _r0209_baseChange_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LinearEquiv.baseChange_one
    # (1 : M ≃ₗ[R] M).baseChange R A M M = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_M_R_M_baseChange", 4)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: LinearEquiv_baseChange_one"))
        except Exception:
            pass
    return results


def _r0210_realize_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FirstOrder.Ring.realize_one
    # Term.realize v (1 : ring.Term α) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Term_realize", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: FirstOrder_Ring_realize_one"))
        except Exception:
            pass
    return results


def _r0211_bernoulli_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.bernoulli_one
    # bernoulli 1 = X - C 2⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bernoulli", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("X"), OOp("C", (OVar("_2inv"),))))
            results.append((rhs, "Mathlib: Polynomial_bernoulli_one"))
        except Exception:
            pass
    return results


def _r0212_bernoulli_eval_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.bernoulli_eval_zero
    # (bernoulli n).eval 0 = _root_.bernoulli n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bernoulli_n_eval", 1)
    if args is not None:
        try:
            rhs = OOp("root_bernoulli", (OVar("n"),))
            results.append((rhs, "Mathlib: Polynomial_bernoulli_eval_zero"))
        except Exception:
            pass
    return results


def _r0213_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulChar.one_apply
    # (1 : MulChar R R') x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_MulChar_R_R_prime", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MulChar_one_apply"))
        except Exception:
            pass
    return results


def _r0214_one_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulChar.one_mul
    # (1 : MulChar R R') * χ = χ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: MulChar_one_mul"))
        except Exception:
            pass
    return results


def _r0215_mk_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NumberField.RingOfIntegers.mk_zero
    # (⟨0, zero_mem _⟩ : 𝓞 K) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_zero_mem", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: NumberField_RingOfIntegers_mk_zero"))
        except Exception:
            pass
    return results


def _r0216_comm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: TensorProduct.comm_apply
    # comm ρ σ (v ⊗ₜ w) = w ⊗ₜ v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comm", 3)
    if args is not None:
        try:
            rhs = OOp("w", (OVar("_unknown"), OVar("v"),))
            results.append((rhs, "Mathlib: TensorProduct_comm_apply"))
        except Exception:
            pass
    return results


def _r0217_val_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: GroupLike.val_pow
    # ↑(a ^ n) = (a ^ n : A)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OVar("a"), OOp("n", (OVar("colon"), OVar("A"),))))
            results.append((rhs, "Mathlib: GroupLike_val_pow"))
    except Exception:
        pass
    return results


def _r0218_choose_one_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ring.choose_one_right
    # choose r 1 = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "choose", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Ring_choose_one_right"))
        except Exception:
            pass
    return results


def _r0219_counit_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommSemiring.counit_apply
    # counit r = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "counit", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CommSemiring_counit_apply"))
        except Exception:
            pass
    return results


def _r0220_val_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.H1Cotangent.val_zero
    # (0 : P.H1Cotangent).1 = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_P_H1Cotangent_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Algebra_H1Cotangent_val_zero"))
    except Exception:
        pass
    return results


def _r0221_absNorm_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ideal.absNorm_eq_one_iff
    # absNorm I = 1 ↔ I = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "absNorm", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[0])), OVar("top")))
            results.append((rhs, "Mathlib: Ideal_absNorm_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0222_zero_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ideal.zero_eq_bot
    # (0 : Ideal R) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0", 3)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Ideal_zero_eq_bot"))
        except Exception:
            pass
    return results


def _r0223_primeCompl_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ideal.primeCompl_bot
    # (⊥ : Ideal α).primeCompl = nonZeroDivisors α
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Ideal_a_primeCompl")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("nonZeroDivisors", (OVar("a"),))
            results.append((rhs, "Mathlib: Ideal_primeCompl_bot"))
    except Exception:
        pass
    return results


def _r0224_eq_zero_iff_mem(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ideal.Quotient.eq_zero_iff_mem
    # mk I a = 0 ↔ a ∈ I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OOp("iff", (OLit(0), OOp("in", (args[1], args[0]))))
            results.append((rhs, "Mathlib: Ideal_Quotient_eq_zero_iff_mem"))
        except Exception:
            pass
    return results


def _r0225_span_insert_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ideal.span_insert_zero
    # span (insert (0 : α) s) = span s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "span", 1)
    if args is not None:
        try:
            rhs = OOp("span", (OVar("s"),))
            results.append((rhs, "Mathlib: Ideal_span_insert_zero"))
        except Exception:
            pass
    return results


def _r0226_span_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ideal.span_one
    # span (1 : Set α) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "span", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Ideal_span_one"))
        except Exception:
            pass
    return results


def _r0227_kroneckerTMulStarAlgEquiv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.kroneckerTMulStarAlgEquiv_apply
    # (kroneckerTMulStarAlgEquiv m n R S A B) x =       kroneckerTMulLinearEquiv m m n n R S A B x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kroneckerTMulStarAlgEquiv_m_n_R_S_A_B", 1)
    if args is not None:
        try:
            rhs = OOp("kroneckerTMulLinearEquiv", (OVar("m"), OVar("m"), OVar("n"), OVar("n"), OVar("R"), OVar("S"), OVar("A"), OVar("B"), args[0],))
            results.append((rhs, "Mathlib: Matrix_kroneckerTMulStarAlgEquiv_apply"))
        except Exception:
            pass
    return results


def _r0228_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.coe_one
    # ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_MvPolynomial_sig_R", 4)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MvPolynomial_coe_one"))
        except Exception:
            pass
    return results


def _r0229_coe_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.coe_eq_zero_iff
    # (φ : MvPowerSeries σ R) = 0 ↔ φ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 4)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("phi"))), OLit(0)))
            results.append((rhs, "Mathlib: MvPolynomial_coe_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0230_coe_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.coe_eq_one_iff
    # (φ : MvPowerSeries σ R) = 1 ↔ φ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 4)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("phi"))), OLit(1)))
            results.append((rhs, "Mathlib: MvPolynomial_coe_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0231_monomial_one_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPowerSeries.monomial_one_eq
    # MvPowerSeries.monomial e (1 : R) =       e.prod fun s n ↦ (MvPowerSeries.X s) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MvPowerSeries_monomial", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("e_prod", (OVar("fun"), OVar("s"), OVar("n"), OVar("_unknown"), OOp("MvPowerSeries_X", (OVar("s"),)),)), OVar("n")))
            results.append((rhs, "Mathlib: MvPowerSeries_monomial_one_eq"))
        except Exception:
            pass
    return results


def _r0232_zeroLocus_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MvPolynomial.zeroLocus_top
    # zeroLocus K (⊤ : Ideal (MvPolynomial σ k)) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zeroLocus", 2)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: MvPolynomial_zeroLocus_top"))
        except Exception:
            pass
    return results


def _r0233_T_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.T_one
    # T R 1 = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "T", 2)
    if args is not None:
        try:
            rhs = OVar("X")
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_T_one"))
        except Exception:
            pass
    return results


def _r0234_T_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.T_neg_one
    # T R (-1) = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "T", 2)
    if args is not None:
        try:
            rhs = OVar("X")
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_T_neg_one"))
        except Exception:
            pass
    return results


def _r0235_T_eval_two_mul_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.T_eval_two_mul_zero
    # (T R (2 * n)).eval 0 = n.negOnePow
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "T_R_2_star_n_eval", 1)
    if args is not None:
        try:
            rhs = OVar("n_negOnePow")
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_T_eval_two_mul_zero"))
        except Exception:
            pass
    return results


def _r0236_U_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.U_one
    # U R 1 = 2 * X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "U", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OLit(2), OVar("X")))
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_U_one"))
        except Exception:
            pass
    return results


def _r0237_U_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.U_neg_one
    # U R (-1) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "U", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_U_neg_one"))
        except Exception:
            pass
    return results


def _r0238_U_eval_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.U_eval_one
    # (U R n).eval 1 = n + 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "U_R_n_eval", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("n"), OLit(1)))
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_U_eval_one"))
        except Exception:
            pass
    return results


def _r0239_U_eval_two_mul_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.U_eval_two_mul_zero
    # (U R (2 * n)).eval 0 = n.negOnePow
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "U_R_2_star_n_eval", 1)
    if args is not None:
        try:
            rhs = OVar("n_negOnePow")
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_U_eval_two_mul_zero"))
        except Exception:
            pass
    return results


def _r0240_degree_U_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.degree_U_neg_one
    # (U R (-1)).degree = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("U_R_minus_1_degree")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_degree_U_neg_one"))
    except Exception:
        pass
    return results


def _r0241_C_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.C_one
    # C R 1 = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "C", 2)
    if args is not None:
        try:
            rhs = OVar("X")
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_C_one"))
        except Exception:
            pass
    return results


def _r0242_C_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.C_neg_one
    # C R (-1) = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "C", 2)
    if args is not None:
        try:
            rhs = OVar("X")
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_C_neg_one"))
        except Exception:
            pass
    return results


def _r0243_S_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.S_one
    # S R 1 = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S", 2)
    if args is not None:
        try:
            rhs = OVar("X")
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_S_one"))
        except Exception:
            pass
    return results


def _r0244_S_neg_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.Chebyshev.S_neg_one
    # S R (-1) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_Chebyshev_S_neg_one"))
        except Exception:
            pass
    return results


def _r0245_dickson_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.dickson_one
    # dickson k a 1 = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "dickson", 3)
    if args is not None:
        try:
            rhs = OVar("X")
            results.append((rhs, "Mathlib: Polynomial_dickson_one"))
        except Exception:
            pass
    return results


def _r0246_hermite_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.hermite_one
    # hermite 1 = X
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hermite", 1)
    if args is not None:
        try:
            rhs = OVar("X")
            results.append((rhs, "Mathlib: Polynomial_hermite_one"))
        except Exception:
            pass
    return results


def _r0247_scaleRoots_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.scaleRoots_one
    # p.scaleRoots 1 = p
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_scaleRoots", 1)
    if args is not None:
        try:
            rhs = OVar("p")
            results.append((rhs, "Mathlib: Polynomial_scaleRoots_one"))
        except Exception:
            pass
    return results


def _r0248_scaleRoots_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.scaleRoots_zero
    # p.scaleRoots 0 = p.leadingCoeff • X ^ p.natDegree
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "p_scaleRoots", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("p_leadingCoeff", (OVar("_unknown"), OVar("X"),)), OVar("p_natDegree")))
            results.append((rhs, "Mathlib: Polynomial_scaleRoots_zero"))
        except Exception:
            pass
    return results


def _r0249_wronskian_zero_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.wronskian_zero_left
    # wronskian 0 a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "wronskian", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_wronskian_zero_left"))
        except Exception:
            pass
    return results


def _r0250_wronskian_zero_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.wronskian_zero_right
    # wronskian a 0 = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "wronskian", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_wronskian_zero_right"))
        except Exception:
            pass
    return results


def _r0251_monomial_mul_monomial(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.monomial_mul_monomial
    # monomial m a * monomial n b = monomial (m + n) (a * b)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("monomial", (OOp("+", (OVar("m"), OVar("n"))), OOp("*", (OVar("a"), OVar("b"))),))
            results.append((rhs, "Mathlib: PowerSeries_monomial_mul_monomial"))
        except Exception:
            pass
    return results


def _r0252_coeff_ne_zero_C(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.coeff_ne_zero_C
    # coeff n (C a) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coeff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PowerSeries_coeff_ne_zero_C"))
        except Exception:
            pass
    return results


def _r0253_coeff_one_X(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.coeff_one_X
    # coeff 1 (X : R⟦X⟧) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coeff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PowerSeries_coeff_one_X"))
        except Exception:
            pass
    return results


def _r0254_X_pow_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.X_pow_eq
    # (X : R⟦X⟧) ^ n = monomial n 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("monomial", (args[1], OLit(1),))
            results.append((rhs, "Mathlib: PowerSeries_X_pow_eq"))
        except Exception:
            pass
    return results


def _r0255_coeff_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.coeff_one
    # coeff n (1 : R⟦X⟧) = if n = 0 then 1 else 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coeff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0],)), OOp("_0", (OVar("then"), OLit(1), OVar("else"), OLit(0),))))
            results.append((rhs, "Mathlib: PowerSeries_coeff_one"))
        except Exception:
            pass
    return results


def _r0256_coeff_zero_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.coeff_zero_one
    # coeff 0 (1 : R⟦X⟧) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coeff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: PowerSeries_coeff_zero_one"))
        except Exception:
            pass
    return results


def _r0257_coeff_zero_mul_X(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.coeff_zero_mul_X
    # coeff 0 (φ * X) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "coeff", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PowerSeries_coeff_zero_mul_X"))
        except Exception:
            pass
    return results


def _r0258_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.coe_one
    # ((1 : R[X]) : PowerSeries R) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_R_X", 3)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Polynomial_coe_one"))
        except Exception:
            pass
    return results


def _r0259_coe_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.coe_eq_zero_iff
    # (φ : PowerSeries R) = 0 ↔ φ = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("phi"))), OLit(0)))
            results.append((rhs, "Mathlib: Polynomial_coe_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0260_coe_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.coe_eq_one_iff
    # (φ : PowerSeries R) = 1 ↔ φ = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("phi"))), OLit(1)))
            results.append((rhs, "Mathlib: Polynomial_coe_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0261_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.coe_pow
    # ((φ ^ n : R[X]) : PowerSeries R) = (φ : PowerSeries R) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi_pow_n_colon_R_X", 3)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("phi", (args[0], args[1], args[2],)), OVar("n")))
            results.append((rhs, "Mathlib: Polynomial_coe_pow"))
        except Exception:
            pass
    return results


def _r0262_trunc_derivative(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.trunc_derivative
    # trunc n (d⁄dX R f) = Polynomial.derivative (trunc (n + 1) f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trunc", 2)
    if args is not None:
        try:
            rhs = OOp("Polynomial_derivative", (OOp("trunc", (OOp("+", (args[0], OLit(1))), OVar("f"),)),))
            results.append((rhs, "Mathlib: PowerSeries_trunc_derivative"))
        except Exception:
            pass
    return results


def _r0263_expand_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.expand_one_apply
    # expand 1 one_ne_zero f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "expand", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: PowerSeries_expand_one_apply"))
        except Exception:
            pass
    return results


def _r0264_trunc_one_X(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.trunc_one_X
    # trunc (R := R) 1 X = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trunc", 3)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PowerSeries_trunc_one_X"))
        except Exception:
            pass
    return results


def _r0265_trunc_mul_C(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PowerSeries.trunc_mul_C
    # trunc n (f * C r) = trunc n f * .C r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "trunc", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("trunc", (args[0], OVar("f"),)), OOp("C", (OVar("r"),))))
            results.append((rhs, "Mathlib: PowerSeries_trunc_mul_C"))
        except Exception:
            pass
    return results


def _r0266_numBound_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ChevalleyThm.MvPolynomialC.numBound_zero
    # numBound k D 0 = k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "numBound", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ChevalleyThm_MvPolynomialC_numBound_zero"))
        except Exception:
            pass
    return results


def _r0267_toSpanSingleton_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toSpanSingleton_zero
    # toSpanSingleton R₁ (0 : M₁) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toSpanSingleton", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: toSpanSingleton_zero"))
        except Exception:
            pass
    return results


def _r0268_toSpanSingleton_apply_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toSpanSingleton_apply_one
    # toSpanSingleton R₁ x 1 = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toSpanSingleton", 3)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: toSpanSingleton_apply_one"))
        except Exception:
            pass
    return results


def _r0269_mulSingle_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mulSingle_eq_one_iff
    # mulSingle A i x = 1 ↔ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulSingle", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[2])), OLit(1)))
            results.append((rhs, "Mathlib: mulSingle_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0270_ofVal_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithVal.ofVal_zero
    # ofVal (0 : WithVal v) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofVal", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: WithVal_ofVal_zero"))
        except Exception:
            pass
    return results


def _r0271_toVal_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithVal.toVal_one
    # toVal v 1 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toVal", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: WithVal_toVal_one"))
        except Exception:
            pass
    return results


def _r0272_ofVal_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithVal.ofVal_one
    # ofVal (1 : WithVal v) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofVal", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: WithVal_ofVal_one"))
        except Exception:
            pass
    return results


def _r0273_toVal_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithVal.toVal_pow
    # toVal v (x ^ n) = (toVal v x) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toVal", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("toVal", (args[0], OVar("x"),)), OVar("n")))
            results.append((rhs, "Mathlib: WithVal_toVal_pow"))
        except Exception:
            pass
    return results


def _r0274_ofVal_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithVal.ofVal_pow
    # ofVal (x ^ n) = (ofVal x) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofVal", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("ofVal", (OVar("x"),)), OVar("n")))
            results.append((rhs, "Mathlib: WithVal_ofVal_pow"))
        except Exception:
            pass
    return results


def _r0275_toVal_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithVal.toVal_eq_zero
    # toVal v x = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toVal", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[1])), OLit(0)))
            results.append((rhs, "Mathlib: WithVal_toVal_eq_zero"))
        except Exception:
            pass
    return results


def _r0276_ofVal_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: WithVal.ofVal_eq_zero
    # ofVal x = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofVal", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), args[0])), OLit(0)))
            results.append((rhs, "Mathlib: WithVal_ofVal_eq_zero"))
        except Exception:
            pass
    return results


def _r0277_elim_some(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OnePoint.elim_some
    # (some x).elim y f = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "some_x_elim", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: OnePoint_elim_some"))
        except Exception:
            pass
    return results


def _r0278_compl_infty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OnePoint.compl_infty
    # ({∞}ᶜ : Set (OnePoint X)) = range ((↑) : X → OnePoint X)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inf", 3)
    if args is not None:
        try:
            rhs = OOp("range", (OOp("implies", (OOp("_unknown", (args[0], OVar("X"),)), OOp("OnePoint", (OVar("X"),)))),))
            results.append((rhs, "Mathlib: OnePoint_compl_infty"))
        except Exception:
            pass
    return results


def _r0279_smul_algebra_smul_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_algebra_smul_comm
    # a • r • m = r • a • m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 4)
    if args is not None:
        try:
            rhs = OOp("r", (args[2], OVar("a"), args[2], args[3],))
            results.append((rhs, "Mathlib: smul_algebra_smul_comm"))
        except Exception:
            pass
    return results


def _r0280_pow_mulRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_mulRight
    # mulRight R a ^ n = mulRight R (a ^ n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("mulRight", (OVar("R"), OOp("**", (OVar("a"), args[1])),))
            results.append((rhs, "Mathlib: pow_mulRight"))
        except Exception:
            pass
    return results


def _r0281_mul_smul_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.mul_smul_comm
    # x * s • y = s • (x * y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("s", (OVar("_unknown"), OOp("*", (args[0], OVar("y"))),))
            results.append((rhs, "Mathlib: Algebra_mul_smul_comm"))
        except Exception:
            pass
    return results


def _r0282_isEpi_iff_forall_one_tmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.isEpi_iff_forall_one_tmul_eq
    # Algebra.IsEpi R A ↔ ∀ a : A, 1 ⊗ₜ[R] a = a ⊗ₜ[R] 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("R"), OLit(1),))
            results.append((rhs, "Mathlib: Algebra_isEpi_iff_forall_one_tmul_eq"))
        except Exception:
            pass
    return results


def _r0283_tmul_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: tmul_comm
    # a ⊗ₜ[R] b = b ⊗ₜ[R] a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("b", (args[0], OVar("a"),))
            results.append((rhs, "Mathlib: tmul_comm"))
        except Exception:
            pass
    return results


def _r0284_one_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: one_apply
    # (1 : A₁ ≃ₐ[R] A₁) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_A_1_R_A_1", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: one_apply"))
        except Exception:
            pass
    return results


def _r0285_coe_zpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: algebraMap.coe_zpow
    # ↑(r ^ z) = (r : A) ^ z
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_pow_z")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("**", (OOp("r", (OVar("colon"), OVar("A"),)), OVar("z")))
            results.append((rhs, "Mathlib: algebraMap_coe_zpow"))
    except Exception:
        pass
    return results


def _r0286_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_zero
    # ((0 : S) : A) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_S", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: coe_zero"))
        except Exception:
            pass
    return results


def _r0287_coe_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_eq_zero
    # (x : A) = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("x"))), OLit(0)))
            results.append((rhs, "Mathlib: coe_eq_zero"))
        except Exception:
            pass
    return results


def _r0288_one_eq_span(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.one_eq_span
    # (1 : Submodule R A) = R ∙ 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 4)
    if args is not None:
        try:
            rhs = OOp("R", (OVar("_unknown"), OLit(1),))
            results.append((rhs, "Mathlib: Submodule_one_eq_span"))
        except Exception:
            pass
    return results


def _r0289_toSubMulAction_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.toSubMulAction_one
    # (1 : Submodule R A).toSubMulAction = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Submodule_R_A_toSubMulAction")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Submodule_toSubMulAction_one"))
    except Exception:
        pass
    return results


def _r0290_one_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.one_smul
    # (1 : Submodule R A) • N = N
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_Submodule_R_A", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Submodule_one_smul"))
        except Exception:
            pass
    return results


def _r0291_mul_comm_of_commute(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_comm_of_commute
    # M * N = N * M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (args[1], args[0]))
            results.append((rhs, "Mathlib: mul_comm_of_commute"))
        except Exception:
            pass
    return results


def _r0292_mul_top_eq_top_of_mul_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_top_eq_top_of_mul_eq_one
    # N * ⊤ = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: mul_top_eq_top_of_mul_eq_one"))
        except Exception:
            pass
    return results


def _r0293_pow_eq_npowRec(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_eq_npowRec
    # M ^ n = npowRec n M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("npowRec", (args[1], args[0],))
            results.append((rhs, "Mathlib: pow_eq_npowRec"))
        except Exception:
            pass
    return results


def _r0294_pow_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_zero
    # M ^ 0 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: pow_zero"))
        except Exception:
            pass
    return results


def _r0295_pow_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_add
    # M ^ (m + n) = M ^ m * M ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (args[0], OVar("m"))), OOp("**", (args[0], OVar("n")))))
            results.append((rhs, "Mathlib: pow_add"))
        except Exception:
            pass
    return results


def _r0296_pow_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_one
    # M ^ 1 = M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: pow_one"))
        except Exception:
            pass
    return results


def _r0297_bot_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: bot_pow
    # ∀ {n : ℕ}, n ≠ 0 → (⊥ : Submodule R A) ^ n = ⊥   | 1, _ => Submodule.pow_one _   | n + 2, _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("bot", (OVar("pipe"), OVar("_1"), OVar("_unknown"), OVar("eq_gt"), OVar("Submodule_pow_one"), OVar("_unknown"), OVar("pipe"), args[1],)), OOp("_2", (OVar("_unknown"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: bot_pow"))
        except Exception:
            pass
    return results


def _r0298_restrictScalars_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: restrictScalars_pow
    # ∀ {n : ℕ}, (hn : n ≠ 0) → (I ^ n).restrictScalars A = I.restrictScalars A ^ n   | 1, _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "I_pow_n_restrictScalars", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("I_restrictScalars", (args[0],)), OOp("n", (OVar("pipe"), OVar("_1"), OVar("_unknown"), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: restrictScalars_pow"))
        except Exception:
            pass
    return results


def _r0299_mul_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_one
    # M * 1 = M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: mul_one"))
        except Exception:
            pass
    return results


def _r0300_span_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: span_pow
    # ∀ n : ℕ, span R s ^ n = span R (s ^ n)   | 0 =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("span", (OVar("R"), OOp("**", (OVar("s"), args[1])), OVar("pipe"), OLit(0), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: span_pow"))
        except Exception:
            pass
    return results


def _r0301_pow_eq_span_pow_set(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: pow_eq_span_pow_set
    # M ^ n = span R ((M : Set A) ^ n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("span", (OVar("R"), OOp("**", (OOp("M", (OVar("colon"), OVar("Set"), OVar("A"),)), args[1])),))
            results.append((rhs, "Mathlib: pow_eq_span_pow_set"))
        except Exception:
            pass
    return results


def _r0302_top_mul_eq_top_of_mul_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: top_mul_eq_top_of_mul_eq_one
    # ⊤ * P = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: top_mul_eq_top_of_mul_eq_one"))
        except Exception:
            pass
    return results


def _r0303_mul_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_comm
    # M * N = N * M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (args[1], args[0]))
            results.append((rhs, "Mathlib: mul_comm"))
        except Exception:
            pass
    return results


def _r0304_setOf_isUnit_inter_mul_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: spectrum.setOf_isUnit_inter_mul_comm
    # {r | IsUnit r} ∩ σ (a * b) = {r | IsUnit r} ∩ σ (b * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inter", 2)
    if args is not None:
        try:
            rhs = OOp("inter", (args[0], OOp("sig", (OOp("*", (OVar("b"), OVar("a"))),))))
            results.append((rhs, "Mathlib: spectrum_setOf_isUnit_inter_mul_comm"))
        except Exception:
            pass
    return results


def _r0305_zero_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: zero_eq
    # σ (0 : A) = {0}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sig", 1)
    if args is not None:
        try:
            rhs = OVar("_0")
            results.append((rhs, "Mathlib: zero_eq"))
        except Exception:
            pass
    return results


def _r0306_nonzero_mul_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: nonzero_mul_comm
    # σ (a * b) \\ {0} = σ (b * a) \\ {0}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sig", 3)
    if args is not None:
        try:
            rhs = OOp("sig", (OOp("*", (OVar("b"), OVar("a"))), args[1], args[2],))
            results.append((rhs, "Mathlib: nonzero_mul_comm"))
        except Exception:
            pass
    return results


def _r0307_val_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PreQuasiregular.val_one
    # (1 : PreQuasiregular R).val = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_PreQuasiregular_R_val")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PreQuasiregular_val_one"))
    except Exception:
        pass
    return results


def _r0308_inv_add_add_mul_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PreQuasiregular.inv_add_add_mul_eq_zero
    # u⁻¹.val.val + u.val.val + u.val.val * u⁻¹.val.val = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PreQuasiregular_inv_add_add_mul_eq_zero"))
        except Exception:
            pass
    return results


def _r0309_add_inv_add_mul_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: PreQuasiregular.add_inv_add_mul_eq_zero
    # u.val.val + u⁻¹.val.val + u⁻¹.val.val * u.val.val = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: PreQuasiregular_add_inv_add_mul_eq_zero"))
        except Exception:
            pass
    return results


def _r0310_mem_unitsFstOne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Unitization.mem_unitsFstOne
    # x ∈ unitsFstOne R A ↔ x.val.fst = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Unitization_mem_unitsFstOne"))
        except Exception:
            pass
    return results


def _r0311_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: quasispectrum.coe_zero
    # (0 : quasispectrum R a) = (0 : R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0", 4)
    if args is not None:
        try:
            rhs = OOp("_0", (args[0], args[2],))
            results.append((rhs, "Mathlib: quasispectrum_coe_zero"))
        except Exception:
            pass
    return results


def _r0312_quasispectrum_eq_spectrum_union_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: quasispectrum_eq_spectrum_union_zero
    # quasispectrum R a = spectrum R a ∪ {0}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "quasispectrum", 2)
    if args is not None:
        try:
            rhs = OOp("union", (OOp("spectrum", (args[0], args[1],)), OVar("_0")))
            results.append((rhs, "Mathlib: quasispectrum_eq_spectrum_union_zero"))
        except Exception:
            pass
    return results


def _r0313_mul_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: quasispectrum.mul_comm
    # quasispectrum R (a * b) = quasispectrum R (b * a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "quasispectrum", 2)
    if args is not None:
        try:
            rhs = OOp("quasispectrum", (args[0], OOp("*", (OVar("b"), OVar("a"))),))
            results.append((rhs, "Mathlib: quasispectrum_mul_comm"))
        except Exception:
            pass
    return results


def _r0314_coe_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_zero
    # ((0 : S) : A) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_0_colon_S", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: coe_zero"))
        except Exception:
            pass
    return results


def _r0315_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_one
    # ((1 : S) : A) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_colon_S", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: coe_one"))
        except Exception:
            pass
    return results


def _r0316_coe_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_eq_zero
    # (x : A) = 0 ↔ x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("x"))), OLit(0)))
            results.append((rhs, "Mathlib: coe_eq_zero"))
        except Exception:
            pass
    return results


def _r0317_coe_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_eq_one
    # (x : A) = 1 ↔ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), OVar("x"))), OLit(1)))
            results.append((rhs, "Mathlib: coe_eq_one"))
        except Exception:
            pass
    return results


def _r0318_toNonUnitalSubalgebra_toSubalgebra(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.toNonUnitalSubalgebra_toSubalgebra
    # S.toNonUnitalSubalgebra.toSubalgebra S.one_mem = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_toNonUnitalSubalgebra_toSubalgebra", 1)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: Subalgebra_toNonUnitalSubalgebra_toSubalgebra"))
        except Exception:
            pass
    return results


def _r0319_toProd_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toProd_zero
    # (0 : Unitization R A).toProd = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Unitization_R_A_toProd")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: toProd_zero"))
    except Exception:
        pass
    return results


def _r0320_fst_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fst_zero
    # (0 : Unitization R A).fst = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_Unitization_R_A_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: fst_zero"))
    except Exception:
        pass
    return results


def _r0321_inl_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inl_zero
    # (inl 0 : Unitization R A) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 5)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: inl_zero"))
        except Exception:
            pass
    return results


def _r0322_inr_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inr_zero
    # ↑(0 : A) = (0 : Unitization R A)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_A")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("_0", (OVar("colon"), OVar("Unitization"), OVar("R"), OVar("A"),))
            results.append((rhs, "Mathlib: inr_zero"))
    except Exception:
        pass
    return results


def _r0323_fst_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fst_one
    # (1 : Unitization R A).fst = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_Unitization_R_A_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: fst_one"))
    except Exception:
        pass
    return results


def _r0324_inl_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inl_one
    # (inl 1 : Unitization R A) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 5)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: inl_one"))
        except Exception:
            pass
    return results


def _r0325_free_obj_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.free_obj_coe
    # (free.obj α : Type u) = FreeAbelianGroup α
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "free_obj", 4)
    if args is not None:
        try:
            rhs = OOp("FreeAbelianGroup", (args[0],))
            results.append((rhs, "Mathlib: AddCommGrpCat_free_obj_coe"))
        except Exception:
            pass
    return results


def _r0326_int_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.int_hom_ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: AddCommGrpCat_int_hom_ext"))
    except Exception:
        pass
    return results


def _r0327_binaryProductLimitCone_cone_pi_app_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.binaryProductLimitCone_cone_π_app_left
    # (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.left⟩ = ofHom (AddMonoidHom.fst G H)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "binaryProductLimitCone_G_H_cone_pi_app", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OOp("AddMonoidHom_fst", (OVar("G"), OVar("H"),)),))
            results.append((rhs, "Mathlib: AddCommGrpCat_binaryProductLimitCone_cone_pi_app_left"))
        except Exception:
            pass
    return results


def _r0328_binaryProductLimitCone_cone_pi_app_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.binaryProductLimitCone_cone_π_app_right
    # (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.right⟩ = ofHom (AddMonoidHom.snd G H)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "binaryProductLimitCone_G_H_cone_pi_app", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OOp("AddMonoidHom_snd", (OVar("G"), OVar("H"),)),))
            results.append((rhs, "Mathlib: AddCommGrpCat_binaryProductLimitCone_cone_pi_app_right"))
        except Exception:
            pass
    return results


def _r0329_biproductIsoPi_inv_comp_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.biproductIsoPi_inv_comp_π
    # (biproductIsoPi f).inv ≫ biproduct.π f j = ofHom (Pi.evalAddMonoidHom (fun j => f j) j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "biproductIsoPi_f_inv", 4)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OOp("Pi_evalAddMonoidHom", (OOp("fun", (args[3], OVar("eq_gt"), args[2], args[3],)), args[3],)),))
            results.append((rhs, "Mathlib: AddCommGrpCat_biproductIsoPi_inv_comp_pi"))
        except Exception:
            pass
    return results


def _r0330_tensorObj_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.tensorObj_eq
    # (G ⊗ H) = of (G × H)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "G", 2)
    if args is not None:
        try:
            rhs = OOp("of", (OOp("product", (OVar("G"), args[1])),))
            results.append((rhs, "Mathlib: AddCommGrpCat_tensorObj_eq"))
        except Exception:
            pass
    return results


def _r0331_addMonoidHom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.Colimits.Quot.addMonoidHom_ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: AddCommGrpCat_Colimits_Quot_addMonoidHom_ext"))
    except Exception:
        pass
    return results


def _r0332_i_desc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.Colimits.Quot.ι_desc
    # Quot.desc F c (Quot.ι F j x) = c.ι.app j x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_desc", 3)
    if args is not None:
        try:
            rhs = OOp("c_i_app", (OVar("j"), OVar("x"),))
            results.append((rhs, "Mathlib: AddCommGrpCat_Colimits_Quot_i_desc"))
        except Exception:
            pass
    return results


def _r0333_quotUliftToQuot_i(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.Colimits.quotUliftToQuot_ι
    # quotUliftToQuot F (Quot.ι _ j x) = Quot.ι F j x.down
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "quotUliftToQuot", 2)
    if args is not None:
        try:
            rhs = OOp("Quot_i", (args[0], OVar("j"), OVar("x_down"),))
            results.append((rhs, "Mathlib: AddCommGrpCat_Colimits_quotUliftToQuot_i"))
        except Exception:
            pass
    return results


def _r0334_desc_toCocone_desc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.Colimits.Quot.desc_toCocone_desc
    # (hc.desc (toCocone F f)).hom.comp (Quot.desc F c) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hc_desc_toCocone_F_f_hom_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: AddCommGrpCat_Colimits_Quot_desc_toCocone_desc"))
        except Exception:
            pass
    return results


def _r0335_desc_toCocone_desc_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.Colimits.Quot.desc_toCocone_desc_app
    # hc.desc (toCocone F f) (Quot.desc F c x) = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "hc_desc", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: AddCommGrpCat_Colimits_Quot_desc_toCocone_desc_app"))
        except Exception:
            pass
    return results


def _r0336_desc_colimitCocone(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.Colimits.Quot.desc_colimitCocone
    # Quot.desc F (colimitCocone F) = (Shrink.addEquiv (α := Quot F)).symm.toAddMonoidHom
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_desc", 2)
    if args is not None:
        try:
            rhs = OVar("Shrink_addEquiv_a_colon_eq_Quot_F_symm_toAddMonoidHom")
            results.append((rhs, "Mathlib: AddCommGrpCat_Colimits_Quot_desc_colimitCocone"))
        except Exception:
            pass
    return results


def _r0337_fac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.image.fac
    # factorThruImage f ≫ image.ι f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "factorThruImage", 4)
    if args is not None:
        try:
            rhs = args[3]
            results.append((rhs, "Mathlib: AddCommGrpCat_image_fac"))
        except Exception:
            pass
    return results


def _r0338_lift_fac(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.image.lift_fac
    # image.lift F' ≫ F'.m = image.ι f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image_lift", 3)
    if args is not None:
        try:
            rhs = OOp("image_i", (OVar("f"),))
            results.append((rhs, "Mathlib: AddCommGrpCat_image_lift_fac"))
        except Exception:
            pass
    return results


def _r0339_hom_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.hom_add
    # (f + g).hom = f.hom + g.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_plus_g_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("f_hom"), OVar("g_hom")))
            results.append((rhs, "Mathlib: AddCommGrpCat_hom_add"))
    except Exception:
        pass
    return results


def _r0340_hom_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.hom_zero
    # (0 : M ⟶ N).hom = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_M_N_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: AddCommGrpCat_hom_zero"))
    except Exception:
        pass
    return results


def _r0341_hom_nsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.hom_nsmul
    # (n • f).hom = n • f.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_f_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n", (OVar("_unknown"), OVar("f_hom"),))
            results.append((rhs, "Mathlib: AddCommGrpCat_hom_nsmul"))
    except Exception:
        pass
    return results


def _r0342_hom_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.hom_neg
    # (-f).hom = -f.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_f_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_f_hom")
            results.append((rhs, "Mathlib: AddCommGrpCat_hom_neg"))
    except Exception:
        pass
    return results


def _r0343_hom_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.hom_sub
    # (f - g).hom = f.hom - g.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_minus_g_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("f_hom"), OVar("g_hom")))
            results.append((rhs, "Mathlib: AddCommGrpCat_hom_sub"))
    except Exception:
        pass
    return results


def _r0344_hom_zsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.hom_zsmul
    # (n • f).hom = n • f.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_f_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("n", (OVar("_unknown"), OVar("f_hom"),))
            results.append((rhs, "Mathlib: AddCommGrpCat_hom_zsmul"))
    except Exception:
        pass
    return results


def _r0345_hom_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ModuleCat.hom_zero
    # (0 : M ⟶ N).hom = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_0_colon_M_N_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ModuleCat_hom_zero"))
    except Exception:
        pass
    return results


def _r0346_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.KaehlerDifferential.ext
    # α = β
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("b")
            results.append((rhs, "Mathlib: CommRingCat_KaehlerDifferential_ext"))
    except Exception:
        pass
    return results


def _r0347_desc_d(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ModuleCat.Derivation.desc_d
    # D.desc (CommRingCat.KaehlerDifferential.d b) = D.d b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D_desc", 1)
    if args is not None:
        try:
            rhs = OOp("D_d", (OVar("b"),))
            results.append((rhs, "Mathlib: ModuleCat_Derivation_desc_d"))
        except Exception:
            pass
    return results


def _r0348_free_obj_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.free_obj_coe
    # (free.obj α : Type u) = MvPolynomial α ℤ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "free_obj", 4)
    if args is not None:
        try:
            rhs = OOp("MvPolynomial", (args[0], OVar("_unknown"),))
            results.append((rhs, "Mathlib: CommRingCat_free_obj_coe"))
        except Exception:
            pass
    return results


def _r0349_coe_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.coe_of
    # (of R : Type u) = R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "of", 4)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CommRingCat_coe_of"))
        except Exception:
            pass
    return results


def _r0350_of_carrier(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.of_carrier
    # of R = R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "of", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: CommRingCat_of_carrier"))
        except Exception:
            pass
    return results


def _r0351_hom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.hom_id
    # (𝟙 R : R ⟶ R).hom = RingHom.id R
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_R_colon_R_R_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("RingHom_id", (OVar("R"),))
            results.append((rhs, "Mathlib: CommRingCat_hom_id"))
    except Exception:
        pass
    return results


def _r0352_hom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.hom_comp
    # (f ≫ g).hom = g.hom.comp f.hom
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_g_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("g_hom_comp", (OVar("f_hom"),))
            results.append((rhs, "Mathlib: CommRingCat_hom_comp"))
    except Exception:
        pass
    return results


def _r0353_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.comp_apply
    # (f ≫ g) r = g (f r)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_g", 1)
    if args is not None:
        try:
            rhs = OOp("g", (OOp("f", (args[0],)),))
            results.append((rhs, "Mathlib: CommRingCat_comp_apply"))
        except Exception:
            pass
    return results


def _r0354_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.hom_ext
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: CommRingCat_hom_ext"))
    except Exception:
        pass
    return results


def _r0355_hom_ofHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.hom_ofHom
    # (ofHom f).hom = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofHom_f_hom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: CommRingCat_hom_ofHom"))
    except Exception:
        pass
    return results


def _r0356_ofHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.ofHom_apply
    # ofHom f r = f r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: CommRingCat_ofHom_apply"))
        except Exception:
            pass
    return results


def _r0357_inv_hom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.inv_hom_apply
    # e.inv (e.hom r) = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_inv", 1)
    if args is not None:
        try:
            rhs = OVar("r")
            results.append((rhs, "Mathlib: CommRingCat_inv_hom_apply"))
        except Exception:
            pass
    return results


def _r0358_hom_inv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.hom_inv_apply
    # e.hom (e.inv s) = s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_hom", 1)
    if args is not None:
        try:
            rhs = OVar("s")
            results.append((rhs, "Mathlib: CommRingCat_hom_inv_apply"))
        except Exception:
            pass
    return results


def _r0359_quot_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingCat.Colimits.quot_zero
    # Quot.mk Setoid.r zero = (0 : ColimitType F)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("colon"), OVar("ColimitType"), OVar("F"),))
            results.append((rhs, "Mathlib: RingCat_Colimits_quot_zero"))
        except Exception:
            pass
    return results


def _r0360_quot_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.Colimits.quot_zero
    # Quot.mk Setoid.r zero = (0 : ColimitType F)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OOp("_0", (OVar("colon"), OVar("ColimitType"), OVar("F"),))
            results.append((rhs, "Mathlib: CommRingCat_Colimits_quot_zero"))
        except Exception:
            pass
    return results


def _r0361_quot_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.Colimits.quot_add
    # Quot.mk Setoid.r (add x y) =       (show ColimitType F from Quot.mk _ x) + (show ColimitType F from Quot.mk _ y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("show", (OVar("ColimitType"), OVar("F"), OVar("from"), OVar("Quot_mk"), OVar("_unknown"), OVar("x"),)), OOp("show", (OVar("ColimitType"), OVar("F"), OVar("from"), OVar("Quot_mk"), OVar("_unknown"), OVar("y"),))))
            results.append((rhs, "Mathlib: CommRingCat_Colimits_quot_add"))
        except Exception:
            pass
    return results


def _r0362_quot_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.Colimits.quot_mul
    # Quot.mk Setoid.r (mul x y) =       (show ColimitType F from Quot.mk _ x) * (show ColimitType F from Quot.mk _ y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("show", (OVar("ColimitType"), OVar("F"), OVar("from"), OVar("Quot_mk"), OVar("_unknown"), OVar("x"),)), OOp("show", (OVar("ColimitType"), OVar("F"), OVar("from"), OVar("Quot_mk"), OVar("_unknown"), OVar("y"),))))
            results.append((rhs, "Mathlib: CommRingCat_Colimits_quot_mul"))
        except Exception:
            pass
    return results


def _r0363_pushoutCocone_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.pushoutCocone_inr
    # (pushoutCocone R A B).inr = ofHom (Algebra.TensorProduct.includeRight.toRingHom (A := B))
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pushoutCocone_R_A_B_inr")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ofHom", (OOp("Algebra_TensorProduct_includeRight_toRingHom", (OOp("A", (OVar("colon_eq"), OVar("B"),)),)),))
            results.append((rhs, "Mathlib: CommRingCat_pushoutCocone_inr"))
    except Exception:
        pass
    return results


def _r0364_pushoutCocone_pt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.pushoutCocone_pt
    # (pushoutCocone R A B).pt = CommRingCat.of (A ⊗[R] B)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pushoutCocone_R_A_B_pt")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("CommRingCat_of", (OOp("A", (OVar("R"), OVar("B"),)),))
            results.append((rhs, "Mathlib: CommRingCat_pushoutCocone_pt"))
    except Exception:
        pass
    return results


def _r0365_closure_range_union_range_eq_top_of_isPu(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.closure_range_union_range_eq_top_of_isPushout
    # Subring.closure (Set.range a ∪ Set.range b) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subring_closure", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: CommRingCat_closure_range_union_range_eq_top_of_isPushout"))
        except Exception:
            pass
    return results


def _r0366_toAlgHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.toAlgHom_id
    # toAlgHom (𝟙 A) = AlgHom.id R A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAlgHom", 1)
    if args is not None:
        try:
            rhs = OOp("AlgHom_id", (OVar("R"), OVar("A"),))
            results.append((rhs, "Mathlib: CommRingCat_toAlgHom_id"))
        except Exception:
            pass
    return results


def _r0367_tensorProdIsoPushout_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.tensorProdIsoPushout_app
    # (tensorProdIsoPushout R S).app A = tensorProdObjIsoPushoutObj S A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tensorProdIsoPushout_R_S_app", 1)
    if args is not None:
        try:
            rhs = OOp("tensorProdObjIsoPushoutObj", (OVar("S"), args[0],))
            results.append((rhs, "Mathlib: CommRingCat_tensorProdIsoPushout_app"))
        except Exception:
            pass
    return results


def _r0368_eq_self_iff_eq_zero_of_char_ne_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ring.eq_self_iff_eq_zero_of_char_ne_two
    # -a = a ↔ a = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("a"), OVar("a"))), OLit(0)))
            results.append((rhs, "Mathlib: Ring_eq_self_iff_eq_zero_of_char_ne_two"))
    except Exception:
        pass
    return results


def _r0369_frobenius_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingHom.frobenius_comm
    # g.comp (frobenius R p) = (frobenius S p).comp g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("frobenius_S_p_comp", (OVar("g"),))
            results.append((rhs, "Mathlib: RingHom_frobenius_comm"))
        except Exception:
            pass
    return results


def _r0370_iterateFrobenius_comm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingHom.iterateFrobenius_comm
    # g.comp (iterateFrobenius R p n) = (iterateFrobenius S p n).comp g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("iterateFrobenius_S_p_n_comp", (OVar("g"),))
            results.append((rhs, "Mathlib: RingHom_iterateFrobenius_comm"))
        except Exception:
            pass
    return results


def _r0371_of_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGroup.DirectLimit.of_f
    # of G f j (f i j hij x) = of G f i x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "of", 4)
    if args is not None:
        try:
            rhs = OOp("of", (args[0], args[1], OVar("i"), OVar("x"),))
            results.append((rhs, "Mathlib: AddCommGroup_DirectLimit_of_f"))
        except Exception:
            pass
    return results


def _r0372_zero_exact(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGroup.DirectLimit.of.zero_exact
    # ∃ j hij, f i j hij x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 7)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: AddCommGroup_DirectLimit_of_zero_exact"))
        except Exception:
            pass
    return results


def _r0373_lift_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGroup.DirectLimit.lift_of
    # lift G f P g Hg (of G f i x) = g i x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 6)
    if args is not None:
        try:
            rhs = OOp("g", (OVar("i"), OVar("x"),))
            results.append((rhs, "Mathlib: AddCommGroup_DirectLimit_lift_of"))
        except Exception:
            pass
    return results


def _r0374_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGroup.DirectLimit.hom_ext
    # g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_2")
            results.append((rhs, "Mathlib: AddCommGroup_DirectLimit_hom_ext"))
    except Exception:
        pass
    return results


def _r0375_lift_comp_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGroup.DirectLimit.lift_comp_of
    # lift G f _ (fun i ↦ F.comp <| of G f i) (fun i j hij x ↦ by simp) = F
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "lift", 5)
    if args is not None:
        try:
            rhs = OVar("F")
            results.append((rhs, "Mathlib: AddCommGroup_DirectLimit_lift_comp_of"))
        except Exception:
            pass
    return results


def _r0376_congr_apply_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGroup.DirectLimit.congr_apply_of
    # congr e he (of G f i g) = of G' f' i (e i g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "congr", 3)
    if args is not None:
        try:
            rhs = OOp("of", (OVar("G_prime"), OVar("f_prime"), OVar("i"), OOp("e", (OVar("i"), OVar("g"),)),))
            results.append((rhs, "Mathlib: AddCommGroup_DirectLimit_congr_apply_of"))
        except Exception:
            pass
    return results


def _r0377_congr_symm_apply_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGroup.DirectLimit.congr_symm_apply_of
    # (congr e he).symm (of G' f' i g) = of G f i ((e i).symm g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "congr_e_he_symm", 1)
    if args is not None:
        try:
            rhs = OOp("of", (OVar("G"), OVar("f"), OVar("i"), OOp("e_i_symm", (OVar("g"),)),))
            results.append((rhs, "Mathlib: AddCommGroup_DirectLimit_congr_symm_apply_of"))
        except Exception:
            pass
    return results


def _r0378_zero_exact(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ring.DirectLimit.of.zero_exact
    # ∃ (j : _) (hij : i ≤ j), f' i j hij x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 7)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Ring_DirectLimit_of_zero_exact"))
        except Exception:
            pass
    return results


def _r0379_gcd_zero_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Field.gcd_zero_eq
    # EuclideanDomain.gcd 0 b = b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "EuclideanDomain_gcd", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Field_gcd_zero_eq"))
        except Exception:
            pass
    return results


def _r0380_mul_modEq_mul_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGroup.mul_modEq_mul_right
    # a * c ≡ b * c [PMOD p] ↔ a ≡ b [PMOD (p / c)]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("a", (OVar("_unknown"), OVar("b"), OSeq((OOp("PMOD", (OOp("//", (OVar("p"), OVar("c"))),)),)),))
            results.append((rhs, "Mathlib: AddCommGroup_mul_modEq_mul_right"))
        except Exception:
            pass
    return results


def _r0381_commClosure_eq_closure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.commClosure_eq_closure
    # commClosure s = closure s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "commClosure", 1)
    if args is not None:
        try:
            rhs = OOp("closure", (args[0],))
            results.append((rhs, "Mathlib: Subfield_commClosure_eq_closure"))
        except Exception:
            pass
    return results


def _r0382_coe_normUnit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommGroupWithZero.coe_normUnit
    # (↑(normUnit a) : G₀) = a⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normUnit_a", 2)
    if args is not None:
        try:
            rhs = OVar("ainv")
            results.append((rhs, "Mathlib: CommGroupWithZero_coe_normUnit"))
        except Exception:
            pass
    return results


def _r0383_coe_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.coe_mk
    # AddChar.mk f map_zero_eq_one' map_add_eq_mul' = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "AddChar_mk", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: AddChar_coe_mk"))
        except Exception:
            pass
    return results


def _r0384_map_zero_eq_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.map_zero_eq_one
    # ψ 0 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: AddChar_map_zero_eq_one"))
        except Exception:
            pass
    return results


def _r0385_coe_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.coe_one
    # ⇑(1 : AddChar A M) = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_1_colon_AddChar_A_M")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(1)
            results.append((rhs, "Mathlib: AddChar_coe_one"))
    except Exception:
        pass
    return results


def _r0386_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.eq_one_iff
    # ψ = 1 ↔ ∀ x, ψ x = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("psi")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(1), OOp("forall", (OVar("x"), OVar("psi"), OVar("x"),)))), OLit(1)))
            results.append((rhs, "Mathlib: AddChar_eq_one_iff"))
    except Exception:
        pass
    return results


def _r0387_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.eq_zero_iff
    # ψ = 0 ↔ ∀ x, ψ x = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("psi")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OLit(0), OOp("forall", (OVar("x"), OVar("psi"), OVar("x"),)))), OLit(1)))
            results.append((rhs, "Mathlib: AddChar_eq_zero_iff"))
    except Exception:
        pass
    return results


def _r0388_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOneClass.ext
    # ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("m_2")
            results.append((rhs, "Mathlib: MulOneClass_ext"))
    except Exception:
        pass
    return results


def _r0389_one_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.one_def
    # (1 : MulAut M) = MulEquiv.refl _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 3)
    if args is not None:
        try:
            rhs = OOp("MulEquiv_refl", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: MulAut_one_def"))
        except Exception:
            pass
    return results


def _r0390_one_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.one_def
    # (1 : AddAut A) = AddEquiv.refl _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1", 3)
    if args is not None:
        try:
            rhs = OOp("AddEquiv_refl", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: AddAut_one_def"))
        except Exception:
            pass
    return results


def _r0391_fwdDiff_iter_eq_zero_of_degree_lt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    # Δ_[1]^[n] P.eval = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D_1_pow_n", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_fwdDiff_iter_eq_zero_of_degree_lt"))
        except Exception:
            pass
    return results


def _r0392_fwdDiff_iter_degree_add_one_eq_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Polynomial.fwdDiff_iter_degree_add_one_eq_zero
    # Δ_[1]^[P.natDegree + 1] P.eval = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D_1_pow_P_natDegree_plus_1", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Polynomial_fwdDiff_iter_degree_add_one_eq_zero"))
        except Exception:
            pass
    return results


def _r0393_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.coe_mul
    # ⇑(f * g) = ⇑f * ⇑g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_star_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("f"), OVar("g")))
            results.append((rhs, "Mathlib: OneHom_coe_mul"))
    except Exception:
        pass
    return results


def _r0394_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.mul_apply
    # (f * g) x = f x * g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_star_g", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: OneHom_mul_apply"))
        except Exception:
            pass
    return results


def _r0395_coe_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.coe_inv
    # ⇑(f⁻¹) = (⇑f)⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("finv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_inv")
            results.append((rhs, "Mathlib: OneHom_coe_inv"))
    except Exception:
        pass
    return results


def _r0396_inv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.inv_apply
    # f⁻¹ x = (f x)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finv", 1)
    if args is not None:
        try:
            rhs = OVar("f_x_inv")
            results.append((rhs, "Mathlib: OneHom_inv_apply"))
        except Exception:
            pass
    return results


def _r0397_coe_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.coe_div
    # ⇑(f / g) = ⇑f / ⇑g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_slash_g")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("f"), OVar("g")))
            results.append((rhs, "Mathlib: OneHom_coe_div"))
    except Exception:
        pass
    return results


def _r0398_div_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.div_apply
    # (f / g) x = f x / g x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_slash_g", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("f", (args[0],)), OOp("g", (args[0],))))
            results.append((rhs, "Mathlib: OneHom_div_apply"))
        except Exception:
            pass
    return results


def _r0399_mk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: OneHom.mk_coe
    # OneHom.mk f h1 = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "OneHom_mk", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: OneHom_mk_coe"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_algebra_ring rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "**", "+", "//", "A_lTensorBot", "A_rTensorBot", "A_updateRow_i_x_updateRow", "AddChar", "AddChar_mk", "Algebra_IsEpi", "Basis_finTwoProd", "C", "CommRingCat_KaehlerDifferential_d", "D_1_pow_P_natDegree_plus_1", "D_1_pow_n", "D_desc", "EuclideanDomain_gcd", "G", "H_1", "Hom_hom", "I_pow_n_restrictScalars", "Monoid_exponent", "MulDistribMulActionHom_id", "Multiplicative", "MvPolynomial", "MvPowerSeries_monomial", "OneHom_id_N_comp", "OneHom_mk", "OnePoint", "PMOD", "Polynomial_C", "Quot_desc", "Quot_i", "Quot_mk", "R", "RingHom_fst_S_R_comp", "RingHom_id", "S", "S_toNonUnitalSubalgebra_toSubalgebra", "Set_range", "Subalgebra_toSubmodule", "Subring_closure", "T", "T_R_2_star_n_eval", "TensorProduct_comm", "Term_realize", "U", "U_R_2_star_n_eval", "U_R_n_eval",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_algebra_ring axioms."""
    if recognizes(term):
        return 0.7
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_algebra_ring rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_toDistribMulActionHom_eq_coe(term, ctx))
    results.extend(_r0001_to_distribMulActionHom_injective(term, ctx))
    results.extend(_r0002_one_eq_span_one_set(term, ctx))
    results.extend(_r0003_one_mul(term, ctx))
    results.extend(_r0004_smul_one_eq_span(term, ctx))
    results.extend(_r0005_one_eq(term, ctx))
    results.extend(_r0006_unitsFstOne_val_val_fst(term, ctx))
    results.extend(_r0007_unitsFstOne_val_inv_val_fst(term, ctx))
    results.extend(_r0008_toSubalgebra_mk(term, ctx))
    results.extend(_r0009_adjoin_insert_zero(term, ctx))
    results.extend(_r0010_adjoin_insert_one(term, ctx))
    results.extend(_r0011_snd_zero(term, ctx))
    results.extend(_r0012_snd_one(term, ctx))
    results.extend(_r0013_hom_add_apply(term, ctx))
    results.extend(_r0014_id_apply(term, ctx))
    results.extend(_r0015_ofHom_hom(term, ctx))
    results.extend(_r0016_ofHom_id(term, ctx))
    results.extend(_r0017_ofHom_comp(term, ctx))
    results.extend(_r0018_quot_one(term, ctx))
    results.extend(_r0019_quot_one(term, ctx))
    results.extend(_r0020_quot_neg(term, ctx))
    results.extend(_r0021_toAlgHom_comp(term, ctx))
    results.extend(_r0022_toAlgHom_apply(term, ctx))
    results.extend(_r0023_mkUnder_ext(term, ctx))
    results.extend(_r0024_coe_zero(term, ctx))
    results.extend(_r0025_coe_one(term, ctx))
    results.extend(_r0026_normalize_eq_one(term, ctx))
    results.extend(_r0027_coe_zero(term, ctx))
    results.extend(_r0028_one_apply(term, ctx))
    results.extend(_r0029_zero_apply(term, ctx))
    results.extend(_r0030_one_eq_zero(term, ctx))
    results.extend(_r0031_coe_eq_one(term, ctx))
    results.extend(_r0032_toMonoidHomEquiv_zero(term, ctx))
    results.extend(_r0033_toAddMonoidHomEquiv_zero(term, ctx))
    results.extend(_r0034_coe_one(term, ctx))
    results.extend(_r0035_one_apply(term, ctx))
    results.extend(_r0036_coe_one(term, ctx))
    results.extend(_r0037_one_apply(term, ctx))
    results.extend(_r0038_mul_comp(term, ctx))
    results.extend(_r0039_inv_comp(term, ctx))
    results.extend(_r0040_div_comp(term, ctx))
    results.extend(_r0041_toFun_eq_coe(term, ctx))
    results.extend(_r0042_comp_apply(term, ctx))
    results.extend(_r0043_id_comp(term, ctx))
    results.extend(_r0044_one_comp(term, ctx))
    results.extend(_r0045_comp_one(term, ctx))
    results.extend(_r0046_unop_pow(term, ctx))
    results.extend(_r0047_unop_pow(term, ctx))
    results.extend(_r0048_coe_mulSingle(term, ctx))
    results.extend(_r0049_coe_zpow(term, ctx))
    results.extend(_r0050_coe_one(term, ctx))
    results.extend(_r0051_coe_zpow(term, ctx))
    results.extend(_r0052_coe_zpowers(term, ctx))
    results.extend(_r0053_coe_set_mk(term, ctx))
    results.extend(_r0054_mk_eq_top(term, ctx))
    results.extend(_r0055_mk_eq_bot(term, ctx))
    results.extend(_r0056_coe_one(term, ctx))
    results.extend(_r0057_mk_eq_one(term, ctx))
    results.extend(_r0058_withOneCongr_symm(term, ctx))
    results.extend(_r0059_smul_comp(term, ctx))
    results.extend(_r0060_toMonoidHom_coe(term, ctx))
    results.extend(_r0061_snd_apply_coe(term, ctx))
    results.extend(_r0062_fst_inl(term, ctx))
    results.extend(_r0063_eq_zero_or_unit(term, ctx))
    results.extend(_r0064_coe_one(term, ctx))
    results.extend(_r0065_toMvPolynomial_one(term, ctx))
    results.extend(_r0066_coe_zero(term, ctx))
    results.extend(_r0067_coeff_zero(term, ctx))
    results.extend(_r0068_ofCoeff_zero(term, ctx))
    results.extend(_r0069_coeff_eq_zero(term, ctx))
    results.extend(_r0070_ofCoeff_eq_zero(term, ctx))
    results.extend(_r0071_erase_zero(term, ctx))
    results.extend(_r0072_divOf_zero(term, ctx))
    results.extend(_r0073_C_pow(term, ctx))
    results.extend(_r0074_monomial_pow(term, ctx))
    results.extend(_r0075_monomial_eq_zero(term, ctx))
    results.extend(_r0076_support_one(term, ctx))
    results.extend(_r0077_degrees_zero(term, ctx))
    results.extend(_r0078_divMonomial_zero(term, ctx))
    results.extend(_r0079_eval_2_one(term, ctx))
    results.extend(_r0080_eval_2_X_pow(term, ctx))
    results.extend(_r0081_pderiv_eq_zero_of_notMem_vars(term, ctx))
    results.extend(_r0082_rename_zero(term, ctx))
    results.extend(_r0083_unop_zero(term, ctx))
    results.extend(_r0084_op_one(term, ctx))
    results.extend(_r0085_unop_one(term, ctx))
    results.extend(_r0086_unop_eq_zero_iff(term, ctx))
    results.extend(_r0087_op_eq_zero_iff(term, ctx))
    results.extend(_r0088_unop_one(term, ctx))
    results.extend(_r0089_op_eq_one_iff(term, ctx))
    results.extend(_r0090_unop_eq_one_iff(term, ctx))
    results.extend(_r0091_mk_div_comm(term, ctx))
    results.extend(_r0092_coe_oneLE(term, ctx))
    results.extend(_r0093_nonneg_toAddGroupCone(term, ctx))
    results.extend(_r0094_coe_nonneg(term, ctx))
    results.extend(_r0095_ofFinsupp_one(term, ctx))
    results.extend(_r0096_toFinsupp_one(term, ctx))
    results.extend(_r0097_toFinsupp_eq_zero(term, ctx))
    results.extend(_r0098_toFinsupp_eq_one(term, ctx))
    results.extend(_r0099_ofFinsupp_eq_one(term, ctx))
    results.extend(_r0100_evalEval_zero(term, ctx))
    results.extend(_r0101_evalEval_one(term, ctx))
    results.extend(_r0102_mul_coeff_one(term, ctx))
    results.extend(_r0103_natDegree_zero(term, ctx))
    results.extend(_r0104_degree_C_mul_X_pow(term, ctx))
    results.extend(_r0105_trailingDegree_zero(term, ctx))
    results.extend(_r0106_trailingCoeff_zero(term, ctx))
    results.extend(_r0107_natTrailingDegree_zero(term, ctx))
    results.extend(_r0108_natTrailingDegree_eq_zero(term, ctx))
    results.extend(_r0109_natTrailingDegree_ne_zero(term, ctx))
    results.extend(_r0110_natTrailingDegree_one(term, ctx))
    results.extend(_r0111_trailingDegree_C_mul_X_pow(term, ctx))
    results.extend(_r0112_iterate_derivative_zero(term, ctx))
    results.extend(_r0113_derivative_of_natDegree_zero(term, ctx))
    results.extend(_r0114_derivative_one(term, ctx))
    results.extend(_r0115_iterate_derivative_one(term, ctx))
    results.extend(_r0116_natDegree_eq_zero_of_derivative_eq_zero(term, ctx))
    results.extend(_r0117_eval_2_X_pow(term, ctx))
    results.extend(_r0118_expand_one(term, ctx))
    results.extend(_r0119_hasseDeriv_eq_zero_of_lt_natDegree(term, ctx))
    results.extend(_r0120_homogenize_one(term, ctx))
    results.extend(_r0121_divX_eq_zero_iff(term, ctx))
    results.extend(_r0122_divX_one(term, ctx))
    results.extend(_r0123_natDegree_divX_eq_natDegree_tsub_one(term, ctx))
    results.extend(_r0124_toLaurent_C_mul_X_pow(term, ctx))
    results.extend(_r0125_mirror_eq_zero(term, ctx))
    results.extend(_r0126_eq_one_of_isUnit(term, ctx))
    results.extend(_r0127_reflect_zero(term, ctx))
    results.extend(_r0128_reflect_one_X(term, ctx))
    results.extend(_r0129_smeval_one(term, ctx))
    results.extend(_r0130_taylor_zero(term, ctx))
    results.extend(_r0131_taylor_one(term, ctx))
    results.extend(_r0132_taylor_coeff_one(term, ctx))
    results.extend(_r0133_taylor_eq_zero(term, ctx))
    results.extend(_r0134_coe_one(term, ctx))
    results.extend(_r0135_closure_mul_self(term, ctx))
    results.extend(_r0136_fst_comp_coe_prodComm(term, ctx))
    results.extend(_r0137_one_eq_closure(term, ctx))
    results.extend(_r0138_coe_zero(term, ctx))
    results.extend(_r0139_coe_one(term, ctx))
    results.extend(_r0140_coe_eq_zero_iff(term, ctx))
    results.extend(_r0141_closure_insert_one(term, ctx))
    results.extend(_r0142_coe_set_mk(term, ctx))
    results.extend(_r0143_coe_zero(term, ctx))
    results.extend(_r0144_zmod_zero(term, ctx))
    results.extend(_r0145_doubleDualEmb_eq_zero(term, ctx))
    results.extend(_r0146_inner_comm_comm(term, ctx))
    results.extend(_r0147_commIsometry_symm(term, ctx))
    results.extend(_r0148_norm_comm(term, ctx))
    results.extend(_r0149_nnnorm_comm(term, ctx))
    results.extend(_r0150_enorm_comm(term, ctx))
    results.extend(_r0151_zero_apply(term, ctx))
    results.extend(_r0152_zero_comp(term, ctx))
    results.extend(_r0153_toLpLin_pow(term, ctx))
    results.extend(_r0154_toLpLin_symm_pow(term, ctx))
    results.extend(_r0155_norm_smul_one_eq_norm(term, ctx))
    results.extend(_r0156_cauchyBound_zero(term, ctx))
    results.extend(_r0157_cauchyBound_one(term, ctx))
    results.extend(_r0158_logMahlerMeasure_one(term, ctx))
    results.extend(_r0159_mahlerMeasure_one(term, ctx))
    results.extend(_r0160_apply_ne_one_iff(term, ctx))
    results.extend(_r0161_apply_ne_zero_iff(term, ctx))
    results.extend(_r0162_diagonal_eq_zero(term, ctx))
    results.extend(_r0163_diagonal_eq_one(term, ctx))
    results.extend(_r0164_one_apply(term, ctx))
    results.extend(_r0165_one_apply_ne(term, ctx))
    results.extend(_r0166_transpose_eq_one(term, ctx))
    results.extend(_r0167_valuation_X_eq_neg_one(term, ctx))
    results.extend(_r0168_natSepDegree_zero(term, ctx))
    results.extend(_r0169_natSepDegree_one(term, ctx))
    results.extend(_r0170_toConvexCone_bot(term, ctx))
    results.extend(_r0171_toConvexCone_top(term, ctx))
    results.extend(_r0172_toConvexCone_inf(term, ctx))
    results.extend(_r0173_coe_zero(term, ctx))
    results.extend(_r0174_lift_zero(term, ctx))
    results.extend(_r0175_eq(term, ctx))
    results.extend(_r0176_commutator_bot_right(term, ctx))
    results.extend(_r0177_swap_eq_one(term, ctx))
    results.extend(_r0178_exponent_multiplicative(term, ctx))
    results.extend(_r0179_pow_exponent_eq_one(term, ctx))
    results.extend(_r0180_id_comp(term, ctx))
    results.extend(_r0181_comp_id(term, ctx))
    results.extend(_r0182_noncommCoprod_comp_inr(term, ctx))
    results.extend(_r0183_mk_pow(term, ctx))
    results.extend(_r0184_mk_zpow(term, ctx))
    results.extend(_r0185_finTwoProd_one(term, ctx))
    results.extend(_r0186_repr_smul(term, ctx))
    results.extend(_r0187_cramer_zero(term, ctx))
    results.extend(_r0188_circulant_col_zero_eq(term, ctx))
    results.extend(_r0189_transpose_zero(term, ctx))
    results.extend(_r0190_transpose_eq_zero(term, ctx))
    results.extend(_r0191_coe_one(term, ctx))
    results.extend(_r0192_den_zero(term, ctx))
    results.extend(_r0193_num_zero(term, ctx))
    results.extend(_r0194_den_one(term, ctx))
    results.extend(_r0195_num_one(term, ctx))
    results.extend(_r0196_vecMulVec_one(term, ctx))
    results.extend(_r0197_replicateCol_eq_zero(term, ctx))
    results.extend(_r0198_replicateRow_eq_zero(term, ctx))
    results.extend(_r0199_updateRow_comm(term, ctx))
    results.extend(_r0200_detp_neg_one_diagonal(term, ctx))
    results.extend(_r0201_coe_one(term, ctx))
    results.extend(_r0202_vec_eq_zero_iff(term, ctx))
    results.extend(_r0203_mk_eq_zero(term, ctx))
    results.extend(_r0204_gradedComm_of_tmul_of(term, ctx))
    results.extend(_r0205_lTensorBot_one_tmul(term, ctx))
    results.extend(_r0206_rTensorBot_tmul_one(term, ctx))
    results.extend(_r0207_mulMap_one_left_eq(term, ctx))
    results.extend(_r0208_mulMap_one_right_eq(term, ctx))
    results.extend(_r0209_baseChange_one(term, ctx))
    results.extend(_r0210_realize_one(term, ctx))
    results.extend(_r0211_bernoulli_one(term, ctx))
    results.extend(_r0212_bernoulli_eval_zero(term, ctx))
    results.extend(_r0213_one_apply(term, ctx))
    results.extend(_r0214_one_mul(term, ctx))
    results.extend(_r0215_mk_zero(term, ctx))
    results.extend(_r0216_comm_apply(term, ctx))
    results.extend(_r0217_val_pow(term, ctx))
    results.extend(_r0218_choose_one_right(term, ctx))
    results.extend(_r0219_counit_apply(term, ctx))
    results.extend(_r0220_val_zero(term, ctx))
    results.extend(_r0221_absNorm_eq_one_iff(term, ctx))
    results.extend(_r0222_zero_eq_bot(term, ctx))
    results.extend(_r0223_primeCompl_bot(term, ctx))
    results.extend(_r0224_eq_zero_iff_mem(term, ctx))
    results.extend(_r0225_span_insert_zero(term, ctx))
    results.extend(_r0226_span_one(term, ctx))
    results.extend(_r0227_kroneckerTMulStarAlgEquiv_apply(term, ctx))
    results.extend(_r0228_coe_one(term, ctx))
    results.extend(_r0229_coe_eq_zero_iff(term, ctx))
    results.extend(_r0230_coe_eq_one_iff(term, ctx))
    results.extend(_r0231_monomial_one_eq(term, ctx))
    results.extend(_r0232_zeroLocus_top(term, ctx))
    results.extend(_r0233_T_one(term, ctx))
    results.extend(_r0234_T_neg_one(term, ctx))
    results.extend(_r0235_T_eval_two_mul_zero(term, ctx))
    results.extend(_r0236_U_one(term, ctx))
    results.extend(_r0237_U_neg_one(term, ctx))
    results.extend(_r0238_U_eval_one(term, ctx))
    results.extend(_r0239_U_eval_two_mul_zero(term, ctx))
    results.extend(_r0240_degree_U_neg_one(term, ctx))
    results.extend(_r0241_C_one(term, ctx))
    results.extend(_r0242_C_neg_one(term, ctx))
    results.extend(_r0243_S_one(term, ctx))
    results.extend(_r0244_S_neg_one(term, ctx))
    results.extend(_r0245_dickson_one(term, ctx))
    results.extend(_r0246_hermite_one(term, ctx))
    results.extend(_r0247_scaleRoots_one(term, ctx))
    results.extend(_r0248_scaleRoots_zero(term, ctx))
    results.extend(_r0249_wronskian_zero_left(term, ctx))
    results.extend(_r0250_wronskian_zero_right(term, ctx))
    results.extend(_r0251_monomial_mul_monomial(term, ctx))
    results.extend(_r0252_coeff_ne_zero_C(term, ctx))
    results.extend(_r0253_coeff_one_X(term, ctx))
    results.extend(_r0254_X_pow_eq(term, ctx))
    results.extend(_r0255_coeff_one(term, ctx))
    results.extend(_r0256_coeff_zero_one(term, ctx))
    results.extend(_r0257_coeff_zero_mul_X(term, ctx))
    results.extend(_r0258_coe_one(term, ctx))
    results.extend(_r0259_coe_eq_zero_iff(term, ctx))
    results.extend(_r0260_coe_eq_one_iff(term, ctx))
    results.extend(_r0261_coe_pow(term, ctx))
    results.extend(_r0262_trunc_derivative(term, ctx))
    results.extend(_r0263_expand_one_apply(term, ctx))
    results.extend(_r0264_trunc_one_X(term, ctx))
    results.extend(_r0265_trunc_mul_C(term, ctx))
    results.extend(_r0266_numBound_zero(term, ctx))
    results.extend(_r0267_toSpanSingleton_zero(term, ctx))
    results.extend(_r0268_toSpanSingleton_apply_one(term, ctx))
    results.extend(_r0269_mulSingle_eq_one_iff(term, ctx))
    results.extend(_r0270_ofVal_zero(term, ctx))
    results.extend(_r0271_toVal_one(term, ctx))
    results.extend(_r0272_ofVal_one(term, ctx))
    results.extend(_r0273_toVal_pow(term, ctx))
    results.extend(_r0274_ofVal_pow(term, ctx))
    results.extend(_r0275_toVal_eq_zero(term, ctx))
    results.extend(_r0276_ofVal_eq_zero(term, ctx))
    results.extend(_r0277_elim_some(term, ctx))
    results.extend(_r0278_compl_infty(term, ctx))
    results.extend(_r0279_smul_algebra_smul_comm(term, ctx))
    results.extend(_r0280_pow_mulRight(term, ctx))
    results.extend(_r0281_mul_smul_comm(term, ctx))
    results.extend(_r0282_isEpi_iff_forall_one_tmul_eq(term, ctx))
    results.extend(_r0283_tmul_comm(term, ctx))
    results.extend(_r0284_one_apply(term, ctx))
    results.extend(_r0285_coe_zpow(term, ctx))
    results.extend(_r0286_coe_zero(term, ctx))
    results.extend(_r0287_coe_eq_zero(term, ctx))
    results.extend(_r0288_one_eq_span(term, ctx))
    results.extend(_r0289_toSubMulAction_one(term, ctx))
    results.extend(_r0290_one_smul(term, ctx))
    results.extend(_r0291_mul_comm_of_commute(term, ctx))
    results.extend(_r0292_mul_top_eq_top_of_mul_eq_one(term, ctx))
    results.extend(_r0293_pow_eq_npowRec(term, ctx))
    results.extend(_r0294_pow_zero(term, ctx))
    results.extend(_r0295_pow_add(term, ctx))
    results.extend(_r0296_pow_one(term, ctx))
    results.extend(_r0297_bot_pow(term, ctx))
    results.extend(_r0298_restrictScalars_pow(term, ctx))
    results.extend(_r0299_mul_one(term, ctx))
    results.extend(_r0300_span_pow(term, ctx))
    results.extend(_r0301_pow_eq_span_pow_set(term, ctx))
    results.extend(_r0302_top_mul_eq_top_of_mul_eq_one(term, ctx))
    results.extend(_r0303_mul_comm(term, ctx))
    results.extend(_r0304_setOf_isUnit_inter_mul_comm(term, ctx))
    results.extend(_r0305_zero_eq(term, ctx))
    results.extend(_r0306_nonzero_mul_comm(term, ctx))
    results.extend(_r0307_val_one(term, ctx))
    results.extend(_r0308_inv_add_add_mul_eq_zero(term, ctx))
    results.extend(_r0309_add_inv_add_mul_eq_zero(term, ctx))
    results.extend(_r0310_mem_unitsFstOne(term, ctx))
    results.extend(_r0311_coe_zero(term, ctx))
    results.extend(_r0312_quasispectrum_eq_spectrum_union_zero(term, ctx))
    results.extend(_r0313_mul_comm(term, ctx))
    results.extend(_r0314_coe_zero(term, ctx))
    results.extend(_r0315_coe_one(term, ctx))
    results.extend(_r0316_coe_eq_zero(term, ctx))
    results.extend(_r0317_coe_eq_one(term, ctx))
    results.extend(_r0318_toNonUnitalSubalgebra_toSubalgebra(term, ctx))
    results.extend(_r0319_toProd_zero(term, ctx))
    results.extend(_r0320_fst_zero(term, ctx))
    results.extend(_r0321_inl_zero(term, ctx))
    results.extend(_r0322_inr_zero(term, ctx))
    results.extend(_r0323_fst_one(term, ctx))
    results.extend(_r0324_inl_one(term, ctx))
    results.extend(_r0325_free_obj_coe(term, ctx))
    results.extend(_r0326_int_hom_ext(term, ctx))
    results.extend(_r0327_binaryProductLimitCone_cone_pi_app_left(term, ctx))
    results.extend(_r0328_binaryProductLimitCone_cone_pi_app_right(term, ctx))
    results.extend(_r0329_biproductIsoPi_inv_comp_pi(term, ctx))
    results.extend(_r0330_tensorObj_eq(term, ctx))
    results.extend(_r0331_addMonoidHom_ext(term, ctx))
    results.extend(_r0332_i_desc(term, ctx))
    results.extend(_r0333_quotUliftToQuot_i(term, ctx))
    results.extend(_r0334_desc_toCocone_desc(term, ctx))
    results.extend(_r0335_desc_toCocone_desc_app(term, ctx))
    results.extend(_r0336_desc_colimitCocone(term, ctx))
    results.extend(_r0337_fac(term, ctx))
    results.extend(_r0338_lift_fac(term, ctx))
    results.extend(_r0339_hom_add(term, ctx))
    results.extend(_r0340_hom_zero(term, ctx))
    results.extend(_r0341_hom_nsmul(term, ctx))
    results.extend(_r0342_hom_neg(term, ctx))
    results.extend(_r0343_hom_sub(term, ctx))
    results.extend(_r0344_hom_zsmul(term, ctx))
    results.extend(_r0345_hom_zero(term, ctx))
    results.extend(_r0346_ext(term, ctx))
    results.extend(_r0347_desc_d(term, ctx))
    results.extend(_r0348_free_obj_coe(term, ctx))
    results.extend(_r0349_coe_of(term, ctx))
    results.extend(_r0350_of_carrier(term, ctx))
    results.extend(_r0351_hom_id(term, ctx))
    results.extend(_r0352_hom_comp(term, ctx))
    results.extend(_r0353_comp_apply(term, ctx))
    results.extend(_r0354_hom_ext(term, ctx))
    results.extend(_r0355_hom_ofHom(term, ctx))
    results.extend(_r0356_ofHom_apply(term, ctx))
    results.extend(_r0357_inv_hom_apply(term, ctx))
    results.extend(_r0358_hom_inv_apply(term, ctx))
    results.extend(_r0359_quot_zero(term, ctx))
    results.extend(_r0360_quot_zero(term, ctx))
    results.extend(_r0361_quot_add(term, ctx))
    results.extend(_r0362_quot_mul(term, ctx))
    results.extend(_r0363_pushoutCocone_inr(term, ctx))
    results.extend(_r0364_pushoutCocone_pt(term, ctx))
    results.extend(_r0365_closure_range_union_range_eq_top_of_isPu(term, ctx))
    results.extend(_r0366_toAlgHom_id(term, ctx))
    results.extend(_r0367_tensorProdIsoPushout_app(term, ctx))
    results.extend(_r0368_eq_self_iff_eq_zero_of_char_ne_two(term, ctx))
    results.extend(_r0369_frobenius_comm(term, ctx))
    results.extend(_r0370_iterateFrobenius_comm(term, ctx))
    results.extend(_r0371_of_f(term, ctx))
    results.extend(_r0372_zero_exact(term, ctx))
    results.extend(_r0373_lift_of(term, ctx))
    results.extend(_r0374_hom_ext(term, ctx))
    results.extend(_r0375_lift_comp_of(term, ctx))
    results.extend(_r0376_congr_apply_of(term, ctx))
    results.extend(_r0377_congr_symm_apply_of(term, ctx))
    results.extend(_r0378_zero_exact(term, ctx))
    results.extend(_r0379_gcd_zero_eq(term, ctx))
    results.extend(_r0380_mul_modEq_mul_right(term, ctx))
    results.extend(_r0381_commClosure_eq_closure(term, ctx))
    results.extend(_r0382_coe_normUnit(term, ctx))
    results.extend(_r0383_coe_mk(term, ctx))
    results.extend(_r0384_map_zero_eq_one(term, ctx))
    results.extend(_r0385_coe_one(term, ctx))
    results.extend(_r0386_eq_one_iff(term, ctx))
    results.extend(_r0387_eq_zero_iff(term, ctx))
    results.extend(_r0388_ext(term, ctx))
    results.extend(_r0389_one_def(term, ctx))
    results.extend(_r0390_one_def(term, ctx))
    results.extend(_r0391_fwdDiff_iter_eq_zero_of_degree_lt(term, ctx))
    results.extend(_r0392_fwdDiff_iter_degree_add_one_eq_zero(term, ctx))
    results.extend(_r0393_coe_mul(term, ctx))
    results.extend(_r0394_mul_apply(term, ctx))
    results.extend(_r0395_coe_inv(term, ctx))
    results.extend(_r0396_inv_apply(term, ctx))
    results.extend(_r0397_coe_div(term, ctx))
    results.extend(_r0398_div_apply(term, ctx))
    results.extend(_r0399_mk_coe(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_algebra_ring rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("NeZero_of_faithfulSMul", "NeZero_n_colon_A", "Not an equality or iff proposition"),
    ("Algebra_charZero_of_charZero", "CharZero_A", "Not an equality or iff proposition"),
    ("NoZeroDivisors_of_faithfulSMul", "NoZeroDivisors_R", "Not an equality or iff proposition"),
    ("IsCancelMulZero_of_faithfulSMul", "IsCancelMulZero_R", "Not an equality or iff proposition"),
    ("commute_mulLeft_right", "Commute_mulLeft_R_a_mulRight_R_b", "Not an equality or iff proposition"),
    ("Algebra_commute_algebraMap_left", "Commute_algebraMap_R_A_r_x", "Not an equality or iff proposition"),
    ("Algebra_commute_algebraMap_right", "Commute_x_algebraMap_R_A_r", "Not an equality or iff proposition"),
    ("AlgEquiv_coe_ringHom_commutes", "e_colon_A_1_to_R_A_2_colon_A_1_to_plus_star_A_2_eq_e_colon_A_1_plus_star_A_2_colon_A_1_to_plus_star_A_2", "Not an equality or iff proposition"),
    ("one_apply", "_1_colon_A_to_R_A_x_eq_x", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_to_distribMulActionHom", "f_colon_A_to_plus_phi_B_eq_f", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_distribMulActionHom_mk", "f_h_1_h_2_h_3_h_4_colon_A_to_phi_B_colon_A_to_plus_phi_B_eq_f_h_1_h_2_h_3", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_zero", "_0_colon_A_to_phi_B_eq_0", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_one", "_1_colon_A_to_R_A_colon_A_to_A_eq_id", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_zero_apply", "_0_colon_A_to_phi_B_a_eq_0", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_one_apply", "_1_colon_A_to_R_A_a_eq_a", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_commute_of_mem_adjoin_of_forall_mem_commute", "Commute_a_b", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_commute_of_mem_adjoin_singleton_of_commute", "Commute_a_c", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_commute_of_mem_adjoin_self", "Commute_a_b", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_isMulCommutative_adjoin", "IsMulCommutative_adjoin_R_s", "Not an equality or iff proposition"),
    ("SubMulAction_mem_one", "_unknown", "Empty proposition"),
    ("Submodule_le_one_toAddSubmonoid", "_1_le_1_colon_Submodule_R_A_toAddSubmonoid", "Not an equality or iff proposition"),
    ("pow_induction_on_right", "_unknown", "Empty proposition"),
    ("pow_induction_on_right", "C_x", "Not an equality or iff proposition"),
    ("le_self_mul_one_div", "I_le_I_star_1_slash_I", "Not an equality or iff proposition"),
    ("mul_one_div_le_one", "I_star_1_slash_I_le_1", "Not an equality or iff proposition"),
    ("Units_zero_notMem_spectrum", "_0_notin_spectrum_R_a_colon_A", "Not an equality or iff proposition"),
    ("spectrum_zero_mem_resolventSet_of_unit", "_0_in_resolventSet_R_a_colon_A", "Not an equality or iff proposition"),
    ("spectrum_ne_zero_of_mem_of_unit", "r_ne_0", "Not an equality or iff proposition"),
    ("spectrum_preimage_units_mul_comm", "colon_R_to_R_inv_prime_sig_a_star_b_eq_inv_prime_sig_b_star_a", "Not an equality or iff proposition"),
    ("isQuasiregular_zero", "IsQuasiregular_0", "Not an equality or iff proposition"),
    ("IsQuasiregular_isUnit_one_add", "IsUnit_1_plus_x", "Not an equality or iff proposition"),
    ("quasispectrum_zero_mem", "_0_in_quasispectrum_R_a", "Not an equality or iff proposition"),
    ("Unitization_zero_mem_spectrum_inr", "_0_in_spectrum_R_a_colon_Unitization_S_A", "Not an equality or iff proposition"),
    ("isStrictlyPositive_one", "IsStrictlyPositive_1_colon_A", "Not an equality or iff proposition"),
    ("Subalgebra_one_mem", "_1_colon_A_in_S", "Not an equality or iff proposition"),
    ("Subalgebra_zero_mem", "_0_colon_A_in_S", "Not an equality or iff proposition"),
    ("Subalgebra_one_mem_toNonUnitalSubalgebra", "_1_colon_A_in_S_toNonUnitalSubalgebra", "Not an equality or iff proposition"),
    ("Algebra_isMulCommutative_adjoin", "IsMulCommutative_adjoin_R_s", "Not an equality or iff proposition"),
    ("Algebra_commute_of_mem_adjoin_of_forall_mem_commute", "Commute_a_b", "Not an equality or iff proposition"),
    ("Algebra_commute_of_mem_adjoin_singleton_of_commute", "Commute_a_c", "Not an equality or iff proposition"),
    ("Algebra_commute_of_mem_adjoin_self", "Commute_a_b", "Not an equality or iff proposition"),
    ("Subalgebra_mem_of_finset_sum_eq_one_of_pow_smul_mem", "x_in_S_prime", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_toAlgHom_zero", "_0_colon_A_to_R_R_toAlgHom_eq_fun_x_x_fst", "Not an equality or iff proposition"),
    ("AddCommGrpCat_hasColimit_of_small_quot", "HasColimit_F", "Not an equality or iff proposition"),
    ("CommRingCat_isRegularMono_of_faithfullyFlat", "IsRegularMono_f", "Not an equality or iff proposition"),
    ("CommRingCat_preservesColimit_coyoneda_of_finitePresentation", "PreservesColimit_F_coyoneda_obj_op_S", "Not an equality or iff proposition"),
    ("CommRingCat_isFinitelyPresentable_under", "IsFinitelyPresentable_u_S", "Not an equality or iff proposition"),
    ("CommRingCat_isFinitelyPresentable_hom", "MorphismProperty_isFinitelyPresentable_u_f", "Not an equality or iff proposition"),
    ("CommRingCat_isLocalHom_comp", "IsLocalHom_f_g_hom", "Not an equality or iff proposition"),
    ("CommRingCat_nontrivial_of_isPushout_of_isField", "Nontrivial_D", "Not an equality or iff proposition"),
    ("CommRingCat_HomTopology_isEmbedding_hom", "IsEmbedding_fun_f_colon_A_R_f_hom_colon_A_to_R", "Not an equality or iff proposition"),
    ("CommRingCat_HomTopology_continuous_precomp", "Continuous_f_colon_B_R_to_A_R", "Not an equality or iff proposition"),
    ("CommRingCat_HomTopology_isHomeomorph_precomp", "IsHomeomorph_f_colon_B_R_to_A_R", "Not an equality or iff proposition"),
    ("CommRingCat_HomTopology_isEmbedding_precomp_of_surjective", "Topology_IsEmbedding_f_colon_B_R_to_A_R", "Not an equality or iff proposition"),
    ("CommRingCat_HomTopology_isClosedEmbedding_precomp_of_surjective", "Topology_IsClosedEmbedding_f_colon_B_R_to_A_R", "Not an equality or iff proposition"),
    ("CommRingCat_HomTopology_isClosedEmbedding_hom", "IsClosedEmbedding_fun_f_colon_A_R_f_hom_colon_A_to_R", "Not an equality or iff proposition"),
    ("CommRingCat_HomTopology_isEmbedding_pushout", "IsEmbedding_fun_f_colon_pushout_phi_psi_R_pushout_inl_phi_psi_f_pushout_inr_phi_psi_f", "Not an equality or iff proposition"),
    ("Ring_two_ne_zero", "_2_colon_R_ne_0", "Not an equality or iff proposition"),
    ("Ring_neg_one_ne_one_of_char_ne_two", "minus_1_colon_R_ne_1", "Not an equality or iff proposition"),
    ("AddCommGroup_DirectLimit_induction_on", "C_z", "Not an equality or iff proposition"),
    ("AddCommGroup_DirectLimit_lift_of", "_unknown", "Empty proposition"),
    ("Subfield_one_mem", "_1_colon_K_in_s", "Not an equality or iff proposition"),
    ("Subfield_zero_mem", "_0_colon_K_in_s", "Not an equality or iff proposition"),
    ("Subfield_zpow_mem", "x_pow_n_in_s", "Not an equality or iff proposition"),
    ("FreeAlgebra_i_ne_zero", "i_R_x_ne_0", "Not an equality or iff proposition"),
    ("FreeAlgebra_i_ne_one", "i_R_x_ne_1", "Not an equality or iff proposition"),
    ("AddChar_toMonoidHomEquiv_symm_one", "toMonoidHomEquiv_symm_1_colon_Multiplicative_A_to_star_M_eq_0", "Not an equality or iff proposition"),
    ("AddChar_toAddMonoidHomEquiv_symm_zero", "toAddMonoidHomEquiv_symm_0_colon_A_to_plus_Additive_M_eq_0", "Not an equality or iff proposition"),
    ("CommMonoid_ext", "_unknown", "Empty proposition"),
    ("CommGroup_ext", "_unknown", "Empty proposition"),
    ("OneHom_coe_coe", "f_colon_OneHom_M_N_colon_M_to_N_eq_f", "Not an equality or iff proposition"),
    ("OneHom_coe_mk", "OneHom_mk_f_h1_colon_M_to_N_eq_f", "Not an equality or iff proposition"),
    ("MonoidHom_toOneHom_coe", "f_toOneHom_colon_M_to_N_eq_f", "Not an equality or iff proposition"),
    ("OneHom_ext", "_unknown", "Empty proposition"),
    ("OneHom_coe_id", "OneHom_id_M_colon_M_to_M_eq_root_id", "Not an equality or iff proposition"),
    ("MonoidHom_map_zpow", "_unknown", "Empty proposition"),
    ("Monoid_End_coe_one", "_1_colon_Monoid_End_M_colon_M_to_M_eq_id", "Not an equality or iff proposition"),
    ("MonoidHom_one_apply", "_1_colon_M_to_star_N_x_eq_1", "Not an equality or iff proposition"),
    ("MonoidHom_one_comp", "_1_colon_N_to_star_P_comp_f_eq_1", "Not an equality or iff proposition"),
    ("MonoidHom_comp_one", "f_comp_1_colon_M_to_star_N_eq_1", "Not an equality or iff proposition"),
    ("AddCommGroup_modEq_refl", "a_a_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_modEq_rfl", "a_a_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_ModEq_symm", "b_a_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_ModEq_trans", "a_c_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_self_modEq_zero", "p_0_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_add_nsmul_modEq", "a_plus_n_p_a_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_nsmul_add_modEq", "n_p_plus_a_a_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_ModEq_add", "a_plus_c_b_plus_d_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_ModEq_add_left", "c_plus_a_c_plus_b_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_ModEq_add_right", "a_plus_c_b_plus_c_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_ModEq_of_nsmul", "a_b_PMOD_n_p_to_a_b_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_ModEq_nsmul", "n_a_n_b_PMOD_n_p", "Not an equality or iff proposition"),
    ("AddCommGroup_ModEq_add_nsmul", "a_b_PMOD_p_to_a_plus_n_p_b_PMOD_p", "Not an equality or iff proposition"),
    ("AddCommGroup_ModEq_nsmul_add", "a_b_PMOD_p_to_n_p_plus_a_b_PMOD_p", "Not an equality or iff proposition"),
    ("MonoidHom_commute_inl_inr", "Commute_inl_M_N_m_inr_M_N_n", "Not an equality or iff proposition"),
    ("Subgroup_SubgroupNormal_mem_comm", "b_star_a_in_H", "Not an equality or iff proposition"),
    ("Subgroup_commute_of_normal_of_disjoint", "Commute_x_y", "Not an equality or iff proposition"),
    ("Subgroup_toSubmonoid_mono", "Monotone_toSubmonoid_colon_Subgroup_G_to_Submonoid_G", "Not an equality or iff proposition"),
    ("Subgroup_one_mem", "_1_colon_G_in_H", "Not an equality or iff proposition"),
    ("Subgroup_zpow_mem", "forall_n_colon_x_pow_n_in_K", "Not an equality or iff proposition"),
    ("Subgroup_Normal_mem_comm", "b_star_a_in_H", "Not an equality or iff proposition"),
    ("Subgroup_multiset_noncommProd_mem", "forall_a_in_g_a_in_K_to_g_noncommProd_comm_in_K", "Not an equality or iff proposition"),
    ("Subgroup_noncommProd_mem", "forall_c_in_t_f_c_in_K_to_t_noncommProd_f_comm_in_K", "Not an equality or iff proposition"),
    ("MonoidHom_range_one", "_1_colon_G_to_star_N_range_eq_bot", "Not an equality or iff proposition"),
    ("MonoidHom_ker_one", "_1_colon_G_to_star_M_ker_eq_top", "Not an equality or iff proposition"),
    ("Subgroup_exists_ne_one_of_nontrivial", "exists_x_in_H_x_ne_1", "Not an equality or iff proposition"),
    ("Submonoid_powers_le_zpowers", "Submonoid_powers_g_le_Subgroup_zpowers_g_toSubmonoid", "Not an equality or iff proposition"),
    ("Subgroup_mem_zpowers", "g_in_zpowers_g", "Not an equality or iff proposition"),
    ("Subgroup_zpow_mem_zpowers", "g_pow_k_in_zpowers_g", "Not an equality or iff proposition"),
    ("Subgroup_npow_mem_zpowers", "g_pow_k_in_zpowers_g", "Not an equality or iff proposition"),
    ("Submonoid_multiset_noncommProd_mem", "m_noncommProd_comm_in_S", "Not an equality or iff proposition"),
    ("Submonoid_noncommProd_mem", "t_noncommProd_f_comm_in_S", "Not an equality or iff proposition"),
    ("Submonoid_one_mem", "_1_colon_M_in_S", "Not an equality or iff proposition"),
    ("MonoidHom_mker_one", "mker_1_colon_M_to_star_N_eq_top", "Not an equality or iff proposition"),
    ("Submonoid_units_mono", "Monotone_Submonoid_units_M_colon_eq_M", "Not an equality or iff proposition"),
    ("Subgroup_ofUnits_mono", "Monotone_Subgroup_ofUnits_M_colon_eq_M", "Not an equality or iff proposition"),
    ("MulActionWithZero_nontrivial", "Nontrivial_M_0", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_coe_coe", "f_colon_a_to_star_0_b_colon_a_to_b_eq_f", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_coe_mk", "mk_f_h1_hmul_colon_a_to_b_eq_f_colon_a_to_b", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_toZeroHom_coe", "f_toZeroHom_colon_a_to_b_eq_f", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_ext", "_unknown", "Empty proposition"),
    ("Invertible_ne_zero", "a_ne_0", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_one_apply_apply_eq", "_1_colon_N_0_to_star_0_G_0_f_x_eq_1_colon_M_0_to_star_0_G_0_x", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_one_comp", "_1_colon_N_0_to_star_0_G_0_comp_f_eq_1_colon_M_0_to_star_0_G_0", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_commute_inl_inr", "Commute_inl_G_0_H_0_m_inr_G_0_H_0_n", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_mrange_nontrivial", "Nontrivial_MonoidHom_mrange_f", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_range_nontrivial", "Set_range_f_Nontrivial", "Not an equality or iff proposition"),
    ("MonoidWithZero_coe_inverse", "MonoidWithZero_inverse_colon_M_to_M_eq_Ring_inverse", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_one_apply_val_unit", "_1_colon_M_0_to_star_0_N_0_x_eq_1_colon_N_0", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_apply_one_apply_eq", "f_1_colon_M_0_to_star_0_N_0_x_eq_1_colon_M_0_to_star_0_G_0_x", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_comp_one", "f_comp_1_colon_M_0_to_star_0_N_0_eq_1_colon_M_0_to_star_0_G_0", "Not an equality or iff proposition"),
    ("Module_End_commute_id_left", "Commute_LinearMap_id_f", "Not an equality or iff proposition"),
    ("Module_End_commute_id_right", "Commute_f_LinearMap_id", "Not an equality or iff proposition"),
    ("Algebra_Presentation_differentials_comm_2_3", "_unknown", "Empty proposition"),
    ("Submodule_toAddSubmonoid_mono", "Monotone_toAddSubmonoid_colon_Submodule_R_M_to_AddSubmonoid_M", "Not an equality or iff proposition"),
    ("Submodule_toSubMulAction_mono", "Monotone_toSubMulAction_colon_Submodule_R_M_to_SubMulAction_R_M", "Not an equality or iff proposition"),
    ("Submodule_zero_mem", "_0_colon_M_in_p", "Not an equality or iff proposition"),
    ("Submodule_exists_mem_ne_zero_of_ne_bot", "exists_b_colon_M_b_in_p_and_b_ne_0", "Not an equality or iff proposition"),
    ("Submodule_annihilator_top_inter_nonZeroDivisors", "top_colon_Submodule_R_M_annihilator_inter_R_colon_Set_R_Nonempty", "Not an equality or iff proposition"),
    ("Module_IsTorsionFree_of_smul_eq_zero", "IsTorsionFree_R_M", "Not an equality or iff proposition"),
    ("MvPolynomial_monomial_zero", "_unknown", "Empty proposition"),
    ("MvPolynomial_vars_pow", "phi_pow_n_vars_sub_phi_vars", "Not an equality or iff proposition"),
    ("MulArchimedeanClass_one_lt_of_one_lt_of_mk_lt", "_1_lt_b", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_inl_mono", "Monotone_inl_M_0_N_0", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_inl_strictMono", "StrictMono_inl_M_0_N_0", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_inr_mono", "Monotone_inr_M_0_N_0", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_inr_strictMono", "StrictMono_inr_M_0_N_0", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_fst_mono", "Monotone_fst_M_0_N_0", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_snd_mono", "Monotone_snd_M_0_N_0", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_ValueGroup_0_monoidWithZeroHom_strictMono", "StrictMono_orderMonoidWithZeroHom_f", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_ValueGroup_0_embedding_strictMono", "StrictMono_embedding_f_colon_eq_f", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_ValueGroup_0_embedding_unit_pos", "_0_lt_embedding_a_1", "Not an equality or iff proposition"),
    ("MonoidWithZeroHom_ValueGroup_0_embedding_unit_ne_zero", "embedding_a_1_ne_0", "Not an equality or iff proposition"),
    ("MonoidHom_inl_mono", "Monotone_MonoidHom_inl_a_b", "Not an equality or iff proposition"),
    ("MonoidHom_inr_mono", "Monotone_MonoidHom_inr_a_b", "Not an equality or iff proposition"),
    ("MonoidHom_fst_mono", "Monotone_MonoidHom_fst_a_b", "Not an equality or iff proposition"),
    ("MonoidHom_snd_mono", "Monotone_MonoidHom_snd_a_b", "Not an equality or iff proposition"),
    ("AddMonoidWithOne_toCharZero", "CharZero_R", "Not an equality or iff proposition"),
    ("Polynomial_le_degree_of_ne_zero", "n_colon_WithBot_le_degree_p", "Not an equality or iff proposition"),
    ("Polynomial_degree_one_le", "degree_1_colon_R_X_le_0_colon_WithBot", "Not an equality or iff proposition"),
    ("Polynomial_coeff_ne_zero_of_eq_degree", "coeff_p_n_ne_0", "Not an equality or iff proposition"),
    ("Polynomial_IsMonicOfDegree_pow", "IsMonicOfDegree_p_pow_n_m_star_n", "Not an equality or iff proposition"),
    ("Polynomial_IsMonicOfDegree_ne_zero", "p_ne_0", "Not an equality or iff proposition"),
    ("Polynomial_isMonicOfDegree_X_pow", "IsMonicOfDegree_X_colon_R_X_pow_n_n", "Not an equality or iff proposition"),
    ("Polynomial_isMonicOfDegree_monomial_one", "IsMonicOfDegree_monomial_n_1_colon_R_n", "Not an equality or iff proposition"),
    ("Polynomial_isMonicOfDegree_X_add_one", "IsMonicOfDegree_X_plus_C_r_1", "Not an equality or iff proposition"),
    ("Polynomial_natDegree_pos_of_nextCoeff_ne_zero", "_0_lt_p_natDegree", "Not an equality or iff proposition"),
    ("Polynomial_le_natDegree_of_ne_zero", "n_le_natDegree_p", "Not an equality or iff proposition"),
    ("Polynomial_trailingDegree_le_of_ne_zero", "trailingDegree_p_le_n", "Not an equality or iff proposition"),
    ("Polynomial_natTrailingDegree_le_of_ne_zero", "natTrailingDegree_p_le_n", "Not an equality or iff proposition"),
    ("Polynomial_trailingDegree_one_le", "_0_colon_inf_le_trailingDegree_1_colon_R_X", "Not an equality or iff proposition"),
    ("Polynomial_natTrailingDegree_mem_support_of_nonzero", "p_ne_0_to_natTrailingDegree_p_in_p_support", "Not an equality or iff proposition"),
    ("Polynomial_coeff_coe_units_zero_ne_zero", "coeff_u_colon_R_X_0_ne_0", "Not an equality or iff proposition"),
    ("Polynomial_mkDerivation_one_eq_derivative", "_unknown", "Empty proposition"),
    ("Polynomial_eraseLead_ne_zero", "eraseLead_f_ne_0", "Not an equality or iff proposition"),
    ("Polynomial_card_support_le_one_of_eraseLead_eq_zero", "hash_f_support_le_1", "Not an equality or iff proposition"),
    ("Polynomial_natDegree_pos_of_eraseLead_ne_zero", "_0_lt_f_natDegree", "Not an equality or iff proposition"),
    ("Polynomial_eval_2_pow", "_unknown", "Empty proposition"),
    ("Polynomial_rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero", "p_rootMultiplicity_t_minus_1_le_p_derivative_rootMultiplicity_t", "Not an equality or iff proposition"),
    ("Polynomial_lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors", "n_lt_p_rootMultiplicity_t", "Not an equality or iff proposition"),
    ("Polynomial_lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors", "_unknown", "Empty proposition"),
    ("Polynomial_lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors", "_unknown", "Empty proposition"),
    ("Polynomial_hasseDeriv_zero", "_unknown", "Empty proposition"),
    ("Polynomial_hasseDeriv_one", "_unknown", "Empty proposition"),
    ("Polynomial_natDegree_ne_zero_induction_on", "M_f", "Not an equality or iff proposition"),
    ("Polynomial_toLaurent_one", "Polynomial_toLaurent_colon_R_X_to_R_T_Tinv_1_eq_1", "Not an equality or iff proposition"),
    ("Module_AEval_isTorsion_of_aeval_eq_zero", "IsTorsion_R_X_AEval_R_M_a", "Not an equality or iff proposition"),
    ("Polynomial_monic_C_mul_of_mul_leadingCoeff_eq_one", "Monic_C_b_star_p", "Not an equality or iff proposition"),
    ("Polynomial_monic_mul_C_of_leadingCoeff_mul_eq_one", "Monic_p_star_C_b", "Not an equality or iff proposition"),
    ("Polynomial_monic_X_pow_add", "Monic_X_pow_n_plus_p", "Not an equality or iff proposition"),
    ("Polynomial_monic_X_pow_add_C", "X_pow_n_plus_C_a_Monic", "Not an equality or iff proposition"),
    ("Polynomial_eq_quo_mul_pow_add_sum_rem_mul_pow", "exists_q_colon_R_X_r_colon_Fin_n_to_R_X_forall_i_r_i_degree_lt_g_degree_and_f_eq_q_star", "Not an equality or iff proposition"),
    ("Polynomial_ne_zero_of_mem_roots", "p_ne_0", "Not an equality or iff proposition"),
    ("Polynomial_Sequence_ne_zero", "S_i_ne_0", "Not an equality or iff proposition"),
    ("Polynomial_Splits_zero", "Splits_0_colon_R_X", "Not an equality or iff proposition"),
    ("Polynomial_Splits_one", "Splits_1_colon_R_X", "Not an equality or iff proposition"),
    ("Polynomial_Splits_pow", "Splits_f_pow_n", "Not an equality or iff proposition"),
    ("Polynomial_Splits_X_pow", "Splits_X_pow_n_colon_R_X", "Not an equality or iff proposition"),
    ("Polynomial_Splits_C_mul_X_pow", "Splits_C_a_star_X_pow_n", "Not an equality or iff proposition"),
    ("Polynomial_splits_of_natDegree_eq_zero", "Splits_f", "Not an equality or iff proposition"),
]
