"""Mathlib: Algebra Group — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 7168 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_algebra_group"
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

def _r0000_map_add_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstMapClass.map_add_one
    # f (x + 1) = f x + b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f", (OVar("x"),)), OVar("b")))
            results.append((rhs, "Mathlib: AddConstMapClass_map_add_one"))
        except Exception:
            pass
    return results


def _r0001_mk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstMap.mk_coe
    # mk f f.2 = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: AddConstMap_mk_coe"))
        except Exception:
            pass
    return results


def _r0002_toFun_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstMap.toFun_eq_coe
    # f.toFun = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: AddConstMap_toFun_eq_coe"))
    except Exception:
        pass
    return results


def _r0003_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstMap.id_comp
    # .comp .id f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comp", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: AddConstMap_id_comp"))
        except Exception:
            pass
    return results


def _r0004_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstMap.coe_pow
    # ⇑(f ^ n) = f^[n]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("fpow_n")
            results.append((rhs, "Mathlib: AddConstMap_coe_pow"))
    except Exception:
        pass
    return results


def _r0005_pow_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstMap.pow_apply
    # (f ^ n) x = f^[n] x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_pow_n", 1)
    if args is not None:
        try:
            rhs = OOp("fpow_n", (args[0],))
            results.append((rhs, "Mathlib: AddConstMap_pow_apply"))
        except Exception:
            pass
    return results


def _r0006_coe_toEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstEquiv.coe_toEquiv
    # ⇑e.toEquiv = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: AddConstEquiv_coe_toEquiv"))
    except Exception:
        pass
    return results


def _r0007_refl_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstEquiv.refl_trans
    # (refl a).trans e = e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "refl_a_trans", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: AddConstEquiv_refl_trans"))
        except Exception:
            pass
    return results


def _r0008_self_trans_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstEquiv.self_trans_symm
    # e.trans e.symm = .refl a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_trans", 1)
    if args is not None:
        try:
            rhs = OOp("refl", (OVar("a"),))
            results.append((rhs, "Mathlib: AddConstEquiv_self_trans_symm"))
        except Exception:
            pass
    return results


def _r0009_symm_trans_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstEquiv.symm_trans_self
    # e.symm.trans e = .refl b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm_trans", 1)
    if args is not None:
        try:
            rhs = OOp("refl", (OVar("b"),))
            results.append((rhs, "Mathlib: AddConstEquiv_symm_trans_self"))
        except Exception:
            pass
    return results


def _r0010_coe_symm_toEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstEquiv.coe_symm_toEquiv
    # ⇑e.toEquiv.symm = e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toEquiv_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm")
            results.append((rhs, "Mathlib: AddConstEquiv_coe_symm_toEquiv"))
    except Exception:
        pass
    return results


def _r0011_toEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstEquiv.toEquiv_symm
    # e.symm.toEquiv = e.toEquiv.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_toEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_toEquiv_symm")
            results.append((rhs, "Mathlib: AddConstEquiv_toEquiv_symm"))
    except Exception:
        pass
    return results


def _r0012_toEquiv_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddConstEquiv.toEquiv_trans
    # (e₁.trans e₂).toEquiv = e₁.toEquiv.trans e₂.toEquiv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_1_trans_e_2_toEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("e_1_toEquiv_trans", (OVar("e_2_toEquiv"),))
            results.append((rhs, "Mathlib: AddConstEquiv_toEquiv_trans"))
    except Exception:
        pass
    return results


def _r0013_closure_irreducible(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.closure_irreducible
    # Submonoid.closure {p : M | Irreducible p} = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Submonoid_closure", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Submonoid_closure_irreducible"))
        except Exception:
            pass
    return results


def _r0014_algebraMapSubmonoid_powers(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: algebraMapSubmonoid_powers
    # Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Algebra_algebraMapSubmonoid", 2)
    if args is not None:
        try:
            rhs = OOp("Submonoid_powers", (OOp("algebraMap", (OVar("R"), args[0], OVar("r"),)),))
            results.append((rhs, "Mathlib: algebraMapSubmonoid_powers"))
        except Exception:
            pass
    return results


def _r0015_ker_algebraMap_end(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Module.ker_algebraMap_end
    # LinearMap.ker ((algebraMap K (End K V)) a) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LinearMap_ker", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Module_ker_algebraMap_end"))
        except Exception:
            pass
    return results


def _r0016_algebraMap_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FaithfulSMul.algebraMap_eq_one_iff
    # algebraMap R A r = 1 ↔ r = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "algebraMap", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[2])), OLit(1)))
            results.append((rhs, "Mathlib: FaithfulSMul_algebraMap_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0017_coe_eq_zero_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: algebraMap.coe_eq_zero_iff
    # (↑a : A) = 0 ↔ a = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(0), OVar("a"))), OLit(0)))
            results.append((rhs, "Mathlib: algebraMap_coe_eq_zero_iff"))
        except Exception:
            pass
    return results


def _r0018_extendScalarsOfSurjective_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LinearEquiv.extendScalarsOfSurjective_apply
    # f.extendScalarsOfSurjective h x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_extendScalarsOfSurjective", 2)
    if args is not None:
        try:
            rhs = OOp("f", (args[1],))
            results.append((rhs, "Mathlib: LinearEquiv_extendScalarsOfSurjective_apply"))
        except Exception:
            pass
    return results


def _r0019_extendScalarsOfSurjective_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LinearEquiv.extendScalarsOfSurjective_symm
    # (f.extendScalarsOfSurjective h).symm = f.symm.extendScalarsOfSurjective h
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_extendScalarsOfSurjective_h_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_symm_extendScalarsOfSurjective", (OVar("h"),))
            results.append((rhs, "Mathlib: LinearEquiv_extendScalarsOfSurjective_symm"))
    except Exception:
        pass
    return results


def _r0020_smul_algebraMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: smul_algebraMap
    # a • algebraMap R A r = algebraMap R A r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 5)
    if args is not None:
        try:
            rhs = OOp("algebraMap", (args[2], args[3], args[4],))
            results.append((rhs, "Mathlib: smul_algebraMap"))
        except Exception:
            pass
    return results


def _r0021_coe_linearMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_linearMap
    # ⇑(Algebra.linearMap R A) = algebraMap R A
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Algebra_linearMap_R_A")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("algebraMap", (OVar("R"), OVar("A"),))
            results.append((rhs, "Mathlib: coe_linearMap"))
    except Exception:
        pass
    return results


def _r0022_algebraMap_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: algebraMap_self
    # algebraMap R R = .id _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "algebraMap", 2)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("_unknown"),))
            results.append((rhs, "Mathlib: algebraMap_self"))
        except Exception:
            pass
    return results


def _r0023_algebraMap_self_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: algebraMap_self_apply
    # algebraMap R R x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "algebraMap", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: algebraMap_self_apply"))
        except Exception:
            pass
    return results


def _r0024_coe_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgEquiv.coe_coe
    # ⇑(AlgEquivClass.toAlgEquiv f) = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("AlgEquivClass_toAlgEquiv_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: AlgEquiv_coe_coe"))
    except Exception:
        pass
    return results


def _r0025_toRingEquiv_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgEquiv.toRingEquiv_eq_coe
    # e.toRingEquiv = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toRingEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: AlgEquiv_toRingEquiv_eq_coe"))
    except Exception:
        pass
    return results


def _r0026_toAlgHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgEquiv.toAlgHom_apply
    # e.toAlgHom x = e x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_toAlgHom", 1)
    if args is not None:
        try:
            rhs = OOp("e", (args[0],))
            results.append((rhs, "Mathlib: AlgEquiv_toAlgHom_apply"))
        except Exception:
            pass
    return results


def _r0027_refl_toRingHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: refl_toRingHom
    # (refl : A₁ ≃ₐ[R] A₁) = RingHom.id A₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "refl", 4)
    if args is not None:
        try:
            rhs = OOp("RingHom_id", (args[3],))
            results.append((rhs, "Mathlib: refl_toRingHom"))
        except Exception:
            pass
    return results


def _r0028_coe_refl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_refl
    # ⇑(refl : A₁ ≃ₐ[R] A₁) = id
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("refl_colon_A_1_R_A_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("id")
            results.append((rhs, "Mathlib: coe_refl"))
    except Exception:
        pass
    return results


def _r0029_symm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_symm
    # e.symm.symm = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: symm_symm"))
    except Exception:
        pass
    return results


def _r0030_toRingEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toRingEquiv_symm
    # (e : A₁ ≃+* A₂).symm = e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_colon_A_1_plus_star_A_2_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm")
            results.append((rhs, "Mathlib: toRingEquiv_symm"))
    except Exception:
        pass
    return results


def _r0031_symm_toAddEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_toAddEquiv
    # (e.symm : A₂ ≃+ A₁) = (e : A₁ ≃+ A₂).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm", 4)
    if args is not None:
        try:
            rhs = OVar("e_colon_A_1_plus_A_2_symm")
            results.append((rhs, "Mathlib: symm_toAddEquiv"))
        except Exception:
            pass
    return results


def _r0032_symm_toMulEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_toMulEquiv
    # (e.symm : A₂ ≃* A₁) = (e : A₁ ≃* A₂).symm
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm", 4)
    if args is not None:
        try:
            rhs = OVar("e_colon_A_1_star_A_2_symm")
            results.append((rhs, "Mathlib: symm_toMulEquiv"))
        except Exception:
            pass
    return results


def _r0033_apply_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: apply_symm_apply
    # ∀ x, e (e.symm x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: apply_symm_apply"))
        except Exception:
            pass
    return results


def _r0034_symm_apply_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_apply_apply
    # ∀ x, e.symm (e x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: symm_apply_apply"))
        except Exception:
            pass
    return results


def _r0035_symm_apply_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_apply_eq
    # e.symm x = y ↔ x = e y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("y"), args[0])), OOp("e", (OVar("y"),))))
            results.append((rhs, "Mathlib: symm_apply_eq"))
        except Exception:
            pass
    return results


def _r0036_trans_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: trans_apply
    # (e₁.trans e₂) x = e₂ (e₁ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_1_trans_e_2", 1)
    if args is not None:
        try:
            rhs = OOp("e_2", (OOp("e_1", (args[0],)),))
            results.append((rhs, "Mathlib: trans_apply"))
        except Exception:
            pass
    return results


def _r0037_symm_trans_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_trans_apply
    # (e₁.trans e₂).symm x = e₁.symm (e₂.symm x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_1_trans_e_2_symm", 1)
    if args is not None:
        try:
            rhs = OOp("e_1_symm", (OOp("e_2_symm", (args[0],)),))
            results.append((rhs, "Mathlib: symm_trans_apply"))
        except Exception:
            pass
    return results


def _r0038_symm_trans_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: symm_trans_self
    # e.symm.trans e = refl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_symm_trans", 1)
    if args is not None:
        try:
            rhs = OVar("refl")
            results.append((rhs, "Mathlib: symm_trans_self"))
        except Exception:
            pass
    return results


def _r0039_arrowCongr_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: arrowCongr_trans
    # arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂')
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arrowCongr", 2)
    if args is not None:
        try:
            rhs = OOp("arrowCongr_e_1_e_1_prime_trans", (OOp("arrowCongr", (OVar("e_2"), OVar("e_2_prime"),)),))
            results.append((rhs, "Mathlib: arrowCongr_trans"))
        except Exception:
            pass
    return results


def _r0040_equivCongr_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: equivCongr_symm
    # (equivCongr e e').symm = equivCongr e.symm e'.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("equivCongr_e_e_prime_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("equivCongr", (OVar("e_symm"), OVar("e_prime_symm"),))
            results.append((rhs, "Mathlib: equivCongr_symm"))
    except Exception:
        pass
    return results


def _r0041_toLinearEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toLinearEquiv_symm
    # e.symm.toLinearEquiv = e.toLinearEquiv.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_toLinearEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_toLinearEquiv_symm")
            results.append((rhs, "Mathlib: toLinearEquiv_symm"))
    except Exception:
        pass
    return results


def _r0042_coe_toLinearEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_toLinearEquiv
    # ⇑e.toLinearEquiv = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toLinearEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: coe_toLinearEquiv"))
    except Exception:
        pass
    return results


def _r0043_coe_symm_toLinearEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_symm_toLinearEquiv
    # ⇑e.toLinearEquiv.symm = e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_toLinearEquiv_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm")
            results.append((rhs, "Mathlib: coe_symm_toLinearEquiv"))
    except Exception:
        pass
    return results


def _r0044_toLinearEquiv_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toLinearEquiv_trans
    # (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_1_trans_e_2_toLinearEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("e_1_toLinearEquiv_trans", (OVar("e_2_toLinearEquiv"),))
            results.append((rhs, "Mathlib: toLinearEquiv_trans"))
    except Exception:
        pass
    return results


def _r0045_toLinearMap_ofAlgHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toLinearMap_ofAlgHom
    # (ofAlgHom f g h₁ h₂).toLinearMap = f.toLinearMap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofAlgHom_f_g_h_1_h_2_toLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_toLinearMap")
            results.append((rhs, "Mathlib: toLinearMap_ofAlgHom"))
    except Exception:
        pass
    return results


def _r0046_toLinearMap_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toLinearMap_apply
    # e.toLinearMap x = e x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_toLinearMap", 1)
    if args is not None:
        try:
            rhs = OOp("e", (args[0],))
            results.append((rhs, "Mathlib: toLinearMap_apply"))
        except Exception:
            pass
    return results


def _r0047_linearEquivConj_mulRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: linearEquivConj_mulRight
    # f.toLinearEquiv.conj (.mulRight R x) = .mulRight R (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toLinearEquiv_conj", 1)
    if args is not None:
        try:
            rhs = OOp("mulRight", (OVar("R"), OOp("f", (OVar("x"),)),))
            results.append((rhs, "Mathlib: linearEquivConj_mulRight"))
        except Exception:
            pass
    return results


def _r0048_linearEquivConj_mulLeftRight(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: linearEquivConj_mulLeftRight
    # f.toLinearEquiv.conj (.mulLeftRight R x) = .mulLeftRight R (Prod.map f f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toLinearEquiv_conj", 1)
    if args is not None:
        try:
            rhs = OOp("mulLeftRight", (OVar("R"), OOp("Prod_map", (OVar("f"), OVar("f"), OVar("x"),)),))
            results.append((rhs, "Mathlib: linearEquivConj_mulLeftRight"))
        except Exception:
            pass
    return results


def _r0049_ofBijective_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofBijective_apply
    # (ofBijective f hf) a = f a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofBijective_f_hf", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: ofBijective_apply"))
        except Exception:
            pass
    return results


def _r0050_toAlgHom_ofBijective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toAlgHom_ofBijective
    # AlgHomClass.toAlgHom (ofBijective f hf) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "AlgHomClass_toAlgHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: toAlgHom_ofBijective"))
        except Exception:
            pass
    return results


def _r0051_ofBijective_apply_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ofBijective_apply_symm_apply
    # f ((ofBijective f hf).symm x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: ofBijective_apply_symm_apply"))
        except Exception:
            pass
    return results


def _r0052_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_apply
    # (e₁ * e₂) x = e₁ (e₂ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_1_star_e_2", 1)
    if args is not None:
        try:
            rhs = OOp("e_1", (OOp("e_2", (args[0],)),))
            results.append((rhs, "Mathlib: mul_apply"))
        except Exception:
            pass
    return results


def _r0053_aut_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: aut_inv
    # ϕ⁻¹ = ϕ.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("symm")
            results.append((rhs, "Mathlib: aut_inv"))
    except Exception:
        pass
    return results


def _r0054_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_pow
    # ⇑(e ^ n) = e^[n]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("epow_n")
            results.append((rhs, "Mathlib: coe_pow"))
    except Exception:
        pass
    return results


def _r0055_autCongr_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: autCongr_symm
    # (autCongr ϕ).symm = autCongr ϕ.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("autCongr_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("autCongr", (OVar("symm"),))
            results.append((rhs, "Mathlib: autCongr_symm"))
    except Exception:
        pass
    return results


def _r0056_autCongr_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: autCongr_trans
    # (autCongr ϕ).trans (autCongr ψ) = autCongr (ϕ.trans ψ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "autCongr_trans", 1)
    if args is not None:
        try:
            rhs = OOp("autCongr", (OOp("trans", (OVar("psi"),)),))
            results.append((rhs, "Mathlib: autCongr_trans"))
        except Exception:
            pass
    return results


def _r0057_toRingEquiv_algEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulSemiringAction.toRingEquiv_algEquiv
    # MulSemiringAction.toRingEquiv _ A₁ σ = σ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MulSemiringAction_toRingEquiv", 3)
    if args is not None:
        try:
            rhs = args[2]
            results.append((rhs, "Mathlib: MulSemiringAction_toRingEquiv_algEquiv"))
        except Exception:
            pass
    return results


def _r0058_algebraMap_eq_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: algebraMap_eq_apply
    # algebraMap R A₂ y = e x ↔ algebraMap R A₁ y = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "algebraMap", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("e", (OVar("x"),)), OOp("algebraMap", (args[0], OVar("A_1"), args[2],)))), OVar("x")))
            results.append((rhs, "Mathlib: algebraMap_eq_apply"))
        except Exception:
            pass
    return results


def _r0059_addHomMk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgHom.addHomMk_coe
    # AddHom.mk f (map_add f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "AddHom_mk", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: AlgHom_addHomMk_coe"))
        except Exception:
            pass
    return results


def _r0060_commutes(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgHom.commutes
    # φ (algebraMap R A r) = algebraMap R B r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi", 1)
    if args is not None:
        try:
            rhs = OOp("algebraMap", (OVar("R"), OVar("B"), OVar("r"),))
            results.append((rhs, "Mathlib: AlgHom_commutes"))
        except Exception:
            pass
    return results


def _r0061_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: comp_apply
    # φ₁.comp φ₂ p = φ₁ (φ₂ p)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi_1_comp", 2)
    if args is not None:
        try:
            rhs = OOp("phi_1", (OOp("phi_2", (args[1],)),))
            results.append((rhs, "Mathlib: comp_apply"))
        except Exception:
            pass
    return results


def _r0062_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: id_comp
    # (AlgHom.id R B).comp φ = φ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "AlgHom_id_R_B_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: id_comp"))
        except Exception:
            pass
    return results


def _r0063_comp_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: comp_assoc
    # (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi_1_comp_phi_2_comp", 1)
    if args is not None:
        try:
            rhs = OOp("phi_1_comp", (OOp("phi_2_comp", (args[0],)),))
            results.append((rhs, "Mathlib: comp_assoc"))
        except Exception:
            pass
    return results


def _r0064_coe_toLinearMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_toLinearMap
    # ⇑φ.toLinearMap = φ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_toLinearMap")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("phi")
            results.append((rhs, "Mathlib: coe_toLinearMap"))
    except Exception:
        pass
    return results


def _r0065_linearMapMk_toAddHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: linearMapMk_toAddHom
    # LinearMap.mk f (map_smul f) = f.toLinearMap
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LinearMap_mk", 2)
    if args is not None:
        try:
            rhs = OVar("f_toLinearMap")
            results.append((rhs, "Mathlib: linearMapMk_toAddHom"))
        except Exception:
            pass
    return results


def _r0066_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mul_apply
    # (φ * ψ) x = φ (ψ x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "phi_star_psi", 1)
    if args is not None:
        try:
            rhs = OOp("phi", (OOp("psi", (args[0],)),))
            results.append((rhs, "Mathlib: mul_apply"))
        except Exception:
            pass
    return results


def _r0067_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_pow
    # ⇑(φ ^ n) = φ^[n]
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("phi_pow_n")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("phipow_n")
            results.append((rhs, "Mathlib: coe_pow"))
    except Exception:
        pass
    return results


def _r0068_algebraMap_eq_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: algebraMap_eq_apply
    # algebraMap R B y = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "algebraMap", 3)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("x"),))
            results.append((rhs, "Mathlib: algebraMap_eq_apply"))
        except Exception:
            pass
    return results


def _r0069_toNatAlgHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingHom.toNatAlgHom_apply
    # f.toNatAlgHom x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toNatAlgHom", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: RingHom_toNatAlgHom_apply"))
        except Exception:
            pass
    return results


def _r0070_toIntAlgHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingHom.toIntAlgHom_apply
    # f.toIntAlgHom x = f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_toIntAlgHom", 1)
    if args is not None:
        try:
            rhs = OOp("f", (args[0],))
            results.append((rhs, "Mathlib: RingHom_toIntAlgHom_apply"))
        except Exception:
            pass
    return results


def _r0071_toRingHom_ofId(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.toRingHom_ofId
    # ofId R A = algebraMap R A
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofId", 2)
    if args is not None:
        try:
            rhs = OOp("algebraMap", (args[0], args[1],))
            results.append((rhs, "Mathlib: Algebra_toRingHom_ofId"))
        except Exception:
            pass
    return results


def _r0072_ofId_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.ofId_apply
    # ofId R A r = algebraMap R A r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofId", 3)
    if args is not None:
        try:
            rhs = OOp("algebraMap", (args[0], args[1], args[2],))
            results.append((rhs, "Mathlib: Algebra_ofId_apply"))
        except Exception:
            pass
    return results


def _r0073_addHomMk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgHom.addHomMk_coe
    # AddHom.mk f (map_add f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "AddHom_mk", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: NonUnitalAlgHom_addHomMk_coe"))
        except Exception:
            pass
    return results


def _r0074_toMulHom_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgHom.toMulHom_eq_coe
    # f.toMulHom = ↑f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toMulHom")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: NonUnitalAlgHom_toMulHom_eq_coe"))
    except Exception:
        pass
    return results


def _r0075_map_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgHom.map_add
    # f (x + y) = f x + f y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("f", (OVar("x"),)), OOp("f", (OVar("y"),))))
            results.append((rhs, "Mathlib: NonUnitalAlgHom_map_add"))
        except Exception:
            pass
    return results


def _r0076_comp_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgHom.comp_apply
    # f.comp g x = f (g x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OOp("g", (args[1],)),))
            results.append((rhs, "Mathlib: NonUnitalAlgHom_comp_apply"))
        except Exception:
            pass
    return results


def _r0077_snd_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgHom.snd_prod
    # (snd R B C).comp (prod f g) = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_R_B_C_comp", 1)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: NonUnitalAlgHom_snd_prod"))
        except Exception:
            pass
    return results


def _r0078_prod_fst_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgHom.prod_fst_snd
    # prod (fst R A B) (snd R A B) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: NonUnitalAlgHom_prod_fst_snd"))
        except Exception:
            pass
    return results


def _r0079_inl_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgHom.inl_apply
    # inl R A B x = (x, 0)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 4)
    if args is not None:
        try:
            rhs = OOp("x", (OLit(0),))
            results.append((rhs, "Mathlib: NonUnitalAlgHom_inl_apply"))
        except Exception:
            pass
    return results


def _r0080_inr_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgHom.inr_apply
    # inr R A B x = (0, x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inr", 4)
    if args is not None:
        try:
            rhs = OOp("_0", (args[3],))
            results.append((rhs, "Mathlib: NonUnitalAlgHom_inr_apply"))
        except Exception:
            pass
    return results


def _r0081_map_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_map
    # (S.map f).map g = S.map (g.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_map_f_map", 1)
    if args is not None:
        try:
            rhs = OOp("S_map", (OOp("g_comp", (OVar("f"),)),))
            results.append((rhs, "Mathlib: map_map"))
        except Exception:
            pass
    return results


def _r0082_map_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_toSubmodule
    # (map f S).toSubmodule = Submodule.map (LinearMapClass.linearMap f) S.toSubmodule
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("map_f_S_toSubmodule")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Submodule_map", (OOp("LinearMapClass_linearMap", (OVar("f"),)), OVar("S_toSubmodule"),))
            results.append((rhs, "Mathlib: map_toSubmodule"))
    except Exception:
        pass
    return results


def _r0083_coe_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_comap
    # (comap f S : Set A) = f ⁻¹' (S : Set B)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "comap", 5)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("inv_prime"), OOp("S", (args[2], args[3], OVar("B"),)),))
            results.append((rhs, "Mathlib: coe_comap"))
        except Exception:
            pass
    return results


def _r0084_adjoin_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.adjoin_univ
    # adjoin R (Set.univ : Set A) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adjoin", 2)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: NonUnitalAlgebra_adjoin_univ"))
        except Exception:
            pass
    return results


def _r0085_top_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.top_toSubmodule
    # (⊤ : NonUnitalSubalgebra R A).toSubmodule = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_NonUnitalSubalgebra_R_A_toSubmodule")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: NonUnitalAlgebra_top_toSubmodule"))
    except Exception:
        pass
    return results


def _r0086_top_toNonUnitalSubsemiring(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.top_toNonUnitalSubsemiring
    # (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubsemiring = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_NonUnitalSubalgebra_R_A_toNonUnitalSubsemiring")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: NonUnitalAlgebra_top_toNonUnitalSubsemiring"))
    except Exception:
        pass
    return results


def _r0087_toNonUnitalSubring_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.toNonUnitalSubring_top
    # (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubring = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_NonUnitalSubalgebra_R_A_toNonUnitalSubring")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: NonUnitalAlgebra_toNonUnitalSubring_top"))
    except Exception:
        pass
    return results


def _r0088_toSubmodule_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.toSubmodule_eq_top
    # S.toSubmodule = ⊤ ↔ S = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_toSubmodule")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("S"))), OVar("top")))
            results.append((rhs, "Mathlib: NonUnitalAlgebra_toSubmodule_eq_top"))
    except Exception:
        pass
    return results


def _r0089_inf_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.inf_toSubmodule
    # (S ⊓ T).toSubmodule = S.toSubmodule ⊓ T.toSubmodule
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_T_toSubmodule")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("S_toSubmodule", (OVar("_unknown"), OVar("T_toSubmodule"),))
            results.append((rhs, "Mathlib: NonUnitalAlgebra_inf_toSubmodule"))
    except Exception:
        pass
    return results


def _r0090_sInf_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.sInf_toSubmodule
    # (sInf S).toSubmodule = sInf (NonUnitalSubalgebra.toSubmodule '' S)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sInf_S_toSubmodule")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("sInf", (OOp("NonUnitalSubalgebra_toSubmodule", (OVar("prime_prime"), OVar("S"),)),))
            results.append((rhs, "Mathlib: NonUnitalAlgebra_sInf_toSubmodule"))
    except Exception:
        pass
    return results


def _r0091_map_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.map_iInf
    # ((⨅ i, S i).map f : NonUnitalSubalgebra R B) = ⨅ i, (S i).map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_S_i_map", 5)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("S_i_map"), args[0],))
            results.append((rhs, "Mathlib: NonUnitalAlgebra_map_iInf"))
        except Exception:
            pass
    return results


def _r0092_eq_top_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.eq_top_iff
    # S = ⊤ ↔ ∀ x : A, x ∈ S
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OVar("top"), OOp("in", (OOp("forall", (OVar("x"), OVar("colon"), OVar("A"), OVar("x"),)), OVar("S")))))
            results.append((rhs, "Mathlib: NonUnitalAlgebra_eq_top_iff"))
    except Exception:
        pass
    return results


def _r0093_map_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.map_top
    # (⊤ : NonUnitalSubalgebra R A).map f = NonUnitalAlgHom.range f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_NonUnitalSubalgebra_R_A_map", 1)
    if args is not None:
        try:
            rhs = OOp("NonUnitalAlgHom_range", (args[0],))
            results.append((rhs, "Mathlib: NonUnitalAlgebra_map_top"))
        except Exception:
            pass
    return results


def _r0094_map_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalAlgebra.map_bot
    # (⊥ : NonUnitalSubalgebra R A).map f = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_NonUnitalSubalgebra_R_A_map", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: NonUnitalAlgebra_map_bot"))
        except Exception:
            pass
    return results


def _r0095_prod_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalSubalgebra.prod_toSubmodule
    # (S.prod S₁).toSubmodule = S.toSubmodule.prod S₁.toSubmodule
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_prod_S_1_toSubmodule")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("S_toSubmodule_prod", (OVar("S_1_toSubmodule"),))
            results.append((rhs, "Mathlib: NonUnitalSubalgebra_prod_toSubmodule"))
    except Exception:
        pass
    return results


def _r0096_prod_inf_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalSubalgebra.prod_inf_prod
    # S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_prod", 4)
    if args is not None:
        try:
            rhs = OOp("S_T_prod", (OOp("S_1", (args[1], args[3],)),))
            results.append((rhs, "Mathlib: NonUnitalSubalgebra_prod_inf_prod"))
        except Exception:
            pass
    return results


def _r0097_mem_centralizer_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mem_centralizer_iff
    # z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("z"), OVar("g")))
            results.append((rhs, "Mathlib: mem_centralizer_iff"))
        except Exception:
            pass
    return results


def _r0098_bot_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.bot_smul
    # (⊥ : Submodule R A) • N = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_Submodule_R_A", 2)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Submodule_bot_smul"))
        except Exception:
            pass
    return results


def _r0099_smul_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submodule.smul_sup
    # I • (N ⊔ P) = I • N ⊔ I • P
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "I", 2)
    if args is not None:
        try:
            rhs = OOp("I", (args[0], OVar("N"), args[0], OVar("I"), args[0], OVar("P"),))
            results.append((rhs, "Mathlib: Submodule_smul_sup"))
        except Exception:
            pass
    return results


def _r0100_bot_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: bot_mul
    # ⊥ * M = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: bot_mul"))
        except Exception:
            pass
    return results


def _r0101_algHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Pi.algHom_comp
    # (algHom R A g).comp h = algHom R A (fun i ↦ (g i).comp h)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "algHom_R_A_g_comp", 1)
    if args is not None:
        try:
            rhs = OOp("algHom", (OVar("R"), OVar("A"), OOp("fun", (OVar("i"), OVar("_unknown"), OVar("g_i_comp"), args[0],)),))
            results.append((rhs, "Mathlib: Pi_algHom_comp"))
        except Exception:
            pass
    return results


def _r0102_constAlgHom_eq_algebra_ofId(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Pi.constAlgHom_eq_algebra_ofId
    # constAlgHom R A R = Algebra.ofId R (A → R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "constAlgHom", 3)
    if args is not None:
        try:
            rhs = OOp("Algebra_ofId", (args[2], OOp("implies", (args[1], args[2])),))
            results.append((rhs, "Mathlib: Pi_constAlgHom_eq_algebra_ofId"))
        except Exception:
            pass
    return results


def _r0103_funUnique_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgEquiv.funUnique_symm_apply
    # (funUnique R ι S).symm x = (Equiv.funUnique ι S).symm x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "funUnique_R_i_S_symm", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_funUnique_i_S_symm", (args[0],))
            results.append((rhs, "Mathlib: AlgEquiv_funUnique_symm_apply"))
        except Exception:
            pass
    return results


def _r0104_snd_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgHom.snd_apply
    # snd R A B a = a.2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd", 4)
    if args is not None:
        try:
            rhs = OVar("a_2")
            results.append((rhs, "Mathlib: AlgHom_snd_apply"))
        except Exception:
            pass
    return results


def _r0105_snd_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgHom.snd_prod
    # (snd R B C).comp (prod f g) = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_R_B_C_comp", 1)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: AlgHom_snd_prod"))
        except Exception:
            pass
    return results


def _r0106_prod_fst_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgHom.prod_fst_snd
    # prod (fst R A B) (snd R A B) = AlgHom.id R _
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 2)
    if args is not None:
        try:
            rhs = OOp("AlgHom_id", (OVar("R"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: AlgHom_prod_fst_snd"))
        except Exception:
            pass
    return results


def _r0107_prod_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgHom.prod_comp
    # (g.prod g').comp f = (g.comp f).prod (g'.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_prod_g_prime_comp", 1)
    if args is not None:
        try:
            rhs = OOp("g_comp_f_prod", (OOp("g_prime_comp", (args[0],)),))
            results.append((rhs, "Mathlib: AlgHom_prod_comp"))
        except Exception:
            pass
    return results


def _r0108_prodCongr_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgEquiv.prodCongr_symm_apply
    # (prodCongr l r).symm x = (Equiv.prodCongr l r).symm x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prodCongr_l_r_symm", 1)
    if args is not None:
        try:
            rhs = OOp("Equiv_prodCongr_l_r_symm", (args[0],))
            results.append((rhs, "Mathlib: AlgEquiv_prodCongr_symm_apply"))
        except Exception:
            pass
    return results


def _r0109_resolvent_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: spectrum.resolvent_eq
    # resolvent a r = ↑h.unit⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "resolvent", 2)
    if args is not None:
        try:
            rhs = OVar("h_unitinv")
            results.append((rhs, "Mathlib: spectrum_resolvent_eq"))
        except Exception:
            pass
    return results


def _r0110_isQuasiregular_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: isQuasiregular_iff
    # IsQuasiregular x ↔ ∃ y, y + x + x * y = 0 ∧ x + y + y * x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("and", (OLit(0), OOp("+", (OVar("x"), OOp("+", (OVar("y"), OOp("*", (OVar("y"), OVar("x"))))))))), OLit(0)))
            results.append((rhs, "Mathlib: isQuasiregular_iff"))
        except Exception:
            pass
    return results


def _r0111_coe_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.coe_toSubmodule
    # (toSubmodule S : Set A) = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toSubmodule", 4)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Subalgebra_coe_toSubmodule"))
        except Exception:
            pass
    return results


def _r0112_coe_algebraMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_algebraMap
    # ↑(algebraMap R' S r) = algebraMap R' A r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("algebraMap_R_prime_S_r")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("algebraMap", (OVar("R_prime"), OVar("A"), OVar("r"),))
            results.append((rhs, "Mathlib: coe_algebraMap"))
    except Exception:
        pass
    return results


def _r0113_coe_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: coe_pow
    # (↑(x ^ n) : A) = (x : A) ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_pow_n", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("x", (args[0], args[1],)), OVar("n")))
            results.append((rhs, "Mathlib: coe_pow"))
        except Exception:
            pass
    return results


def _r0114_val_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: val_apply
    # S.val x = (x : A)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_val", 1)
    if args is not None:
        try:
            rhs = OOp("x", (OVar("colon"), OVar("A"),))
            results.append((rhs, "Mathlib: val_apply"))
        except Exception:
            pass
    return results


def _r0115_toSubring_subtype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toSubring_subtype
    # S.toSubring.subtype = (S.val : S →+* A)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_toSubring_subtype")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("S_val", (OVar("colon"), OVar("S"), OVar("to_plus_star"), OVar("A"),))
            results.append((rhs, "Mathlib: toSubring_subtype"))
    except Exception:
        pass
    return results


def _r0116_map_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_map
    # (S.map f).map g = S.map (g.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_map_f_map", 1)
    if args is not None:
        try:
            rhs = OOp("S_map", (OOp("g_comp", (OVar("f"),)),))
            results.append((rhs, "Mathlib: map_map"))
        except Exception:
            pass
    return results


def _r0117_map_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: map_toSubmodule
    # (toSubmodule <| S.map f) = S.toSubmodule.map f.toLinearMap
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toSubmodule", 3)
    if args is not None:
        try:
            rhs = OOp("S_toSubmodule_map", (OVar("f_toLinearMap"),))
            results.append((rhs, "Mathlib: map_toSubmodule"))
        except Exception:
            pass
    return results


def _r0118_mem_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgHom.mem_range
    # y ∈ φ.range ↔ ∃ x, φ x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: AlgHom_mem_range"))
        except Exception:
            pass
    return results


def _r0119_inclusion_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.inclusion_mk
    # inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inclusion", 2)
    if args is not None:
        try:
            rhs = OVar("x_h_hx")
            results.append((rhs, "Mathlib: Subalgebra_inclusion_mk"))
        except Exception:
            pass
    return results


def _r0120_inclusion_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.inclusion_right
    # inclusion h ⟨x, m⟩ = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inclusion", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Subalgebra_inclusion_right"))
        except Exception:
            pass
    return results


def _r0121_equivOfEq_rfl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.equivOfEq_rfl
    # equivOfEq S S rfl = AlgEquiv.refl
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "==", 3)
    if args is not None:
        try:
            rhs = OVar("AlgEquiv_refl")
            results.append((rhs, "Mathlib: Subalgebra_equivOfEq_rfl"))
        except Exception:
            pass
    return results


def _r0122_equivOfEq_trans(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.equivOfEq_trans
    # (equivOfEq S T hST).trans (equivOfEq T U hTU) = equivOfEq S U (hST.trans hTU)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "equivOfEq_S_T_hST_trans", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OVar("S"), OVar("U"), OOp("hST_trans", (OVar("hTU"),)),))
            results.append((rhs, "Mathlib: Subalgebra_equivOfEq_trans"))
        except Exception:
            pass
    return results


def _r0123_center_toSubring(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: center_toSubring
    # (center R A).toSubring = Subring.center A
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("center_R_A_toSubring")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Subring_center", (OVar("A"),))
            results.append((rhs, "Mathlib: center_toSubring"))
    except Exception:
        pass
    return results


def _r0124_mem_centralizer_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: mem_centralizer_iff
    # z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("z"), OVar("g")))
            results.append((rhs, "Mathlib: mem_centralizer_iff"))
        except Exception:
            pass
    return results


def _r0125_equalizer_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgHom.equalizer_toSubmodule
    # Subalgebra.toSubmodule (equalizer φ ψ) = LinearMap.eqLocus φ ψ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subalgebra_toSubmodule", 1)
    if args is not None:
        try:
            rhs = OOp("LinearMap_eqLocus", (OVar("phi"), OVar("psi"),))
            results.append((rhs, "Mathlib: AlgHom_equalizer_toSubmodule"))
        except Exception:
            pass
    return results


def _r0126_top_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.top_toSubmodule
    # Subalgebra.toSubmodule (⊤ : Subalgebra R A) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subalgebra_toSubmodule", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Algebra_top_toSubmodule"))
        except Exception:
            pass
    return results


def _r0127_top_toSubsemiring(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.top_toSubsemiring
    # (⊤ : Subalgebra R A).toSubsemiring = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_Subalgebra_R_A_toSubsemiring")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Algebra_top_toSubsemiring"))
    except Exception:
        pass
    return results


def _r0128_top_toSubring(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.top_toSubring
    # (⊤ : Subalgebra R A).toSubring = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_Subalgebra_R_A_toSubring")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Algebra_top_toSubring"))
    except Exception:
        pass
    return results


def _r0129_toSubmodule_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.toSubmodule_eq_top
    # Subalgebra.toSubmodule S = ⊤ ↔ S = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subalgebra_toSubmodule", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("top"), args[0])), OVar("top")))
            results.append((rhs, "Mathlib: Algebra_toSubmodule_eq_top"))
        except Exception:
            pass
    return results


def _r0130_toSubsemiring_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.toSubsemiring_eq_top
    # S.toSubsemiring = ⊤ ↔ S = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_toSubsemiring")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("S"))), OVar("top")))
            results.append((rhs, "Mathlib: Algebra_toSubsemiring_eq_top"))
    except Exception:
        pass
    return results


def _r0131_toSubring_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.toSubring_eq_top
    # S.toSubring = ⊤ ↔ S = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_toSubring")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("S"))), OVar("top")))
            results.append((rhs, "Mathlib: Algebra_toSubring_eq_top"))
    except Exception:
        pass
    return results


def _r0132_inf_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.inf_toSubmodule
    # toSubmodule (S ⊓ T) = toSubmodule S ⊓ toSubmodule T
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toSubmodule", 1)
    if args is not None:
        try:
            rhs = OOp("toSubmodule", (OVar("S"), OVar("_unknown"), OVar("toSubmodule"), OVar("T"),))
            results.append((rhs, "Mathlib: Algebra_inf_toSubmodule"))
        except Exception:
            pass
    return results


def _r0133_inf_toSubsemiring(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.inf_toSubsemiring
    # (S ⊓ T).toSubsemiring = S.toSubsemiring ⊓ T.toSubsemiring
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_T_toSubsemiring")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("S_toSubsemiring", (OVar("_unknown"), OVar("T_toSubsemiring"),))
            results.append((rhs, "Mathlib: Algebra_inf_toSubsemiring"))
    except Exception:
        pass
    return results


def _r0134_sInf_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.sInf_toSubmodule
    # Subalgebra.toSubmodule (sInf S) = sInf (Subalgebra.toSubmodule '' S)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subalgebra_toSubmodule", 1)
    if args is not None:
        try:
            rhs = OOp("sInf", (OOp("Subalgebra_toSubmodule", (OVar("prime_prime"), OVar("S"),)),))
            results.append((rhs, "Mathlib: Algebra_sInf_toSubmodule"))
        except Exception:
            pass
    return results


def _r0135_map_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.map_iInf
    # (iInf s).map f = ⨅ (i : ι), (s i).map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iInf_s_map", 1)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i_colon_i"), OVar("s_i_map"), args[0],))
            results.append((rhs, "Mathlib: Algebra_map_iInf"))
        except Exception:
            pass
    return results


def _r0136_toSubring_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.toSubring_bot
    # (⊥ : Subalgebra R A).toSubring = R
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Subalgebra_R_A_toSubring")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("R")
            results.append((rhs, "Mathlib: Algebra_toSubring_bot"))
    except Exception:
        pass
    return results


def _r0137_range_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.range_id
    # (AlgHom.id R A).range = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("AlgHom_id_R_A_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Algebra_range_id"))
    except Exception:
        pass
    return results


def _r0138_map_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.map_top
    # (⊤ : Subalgebra R A).map f = f.range
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Subalgebra_R_A_map", 1)
    if args is not None:
        try:
            rhs = OVar("f_range")
            results.append((rhs, "Mathlib: Algebra_map_top"))
        except Exception:
            pass
    return results


def _r0139_map_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.map_bot
    # (⊥ : Subalgebra R A).map f = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_Subalgebra_R_A_map", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Algebra_map_bot"))
        except Exception:
            pass
    return results


def _r0140_equalizer_same(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgHom.equalizer_same
    # equalizer φ φ = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "equalizer", 2)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: AlgHom_equalizer_same"))
        except Exception:
            pass
    return results


def _r0141_adjoin_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.adjoin_univ
    # adjoin R (Set.univ : Set A) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adjoin", 2)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Algebra_adjoin_univ"))
        except Exception:
            pass
    return results


def _r0142_adjoin_singleton_algebraMap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.adjoin_singleton_algebraMap
    # R[algebraMap R A x] = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_algebraMap_R_A_x")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Algebra_adjoin_singleton_algebraMap"))
    except Exception:
        pass
    return results


def _r0143_adjoin_singleton_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.adjoin_singleton_natCast
    # R[n : A] = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_n_colon_A")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Algebra_adjoin_singleton_natCast"))
    except Exception:
        pass
    return results


def _r0144_adjoin_singleton_zero(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.adjoin_singleton_zero
    # R[0 : A] = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_0_colon_A")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Algebra_adjoin_singleton_zero"))
    except Exception:
        pass
    return results


def _r0145_adjoin_singleton_one(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.adjoin_singleton_one
    # R[1 : A]= ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("R_1_colon_A")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Algebra_adjoin_singleton_one"))
    except Exception:
        pass
    return results


def _r0146_adjoin_eq_span(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.adjoin_eq_span
    # Subalgebra.toSubmodule (adjoin R s) = span R (Submonoid.closure s)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Subalgebra_toSubmodule", 1)
    if args is not None:
        try:
            rhs = OOp("span", (OVar("R"), OOp("Submonoid_closure", (OVar("s"),)),))
            results.append((rhs, "Mathlib: Algebra_adjoin_eq_span"))
        except Exception:
            pass
    return results


def _r0147_adjoin_image(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.adjoin_image
    # adjoin R (f '' s) = (adjoin R s).map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adjoin", 2)
    if args is not None:
        try:
            rhs = OOp("adjoin_R_s_map", (OVar("f"),))
            results.append((rhs, "Mathlib: Algebra_adjoin_image"))
        except Exception:
            pass
    return results


def _r0148_adjoin_insert_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: adjoin_insert_intCast
    # adjoin R (insert (n : A) s) = adjoin R s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "adjoin", 2)
    if args is not None:
        try:
            rhs = OOp("adjoin", (args[0], OVar("s"),))
            results.append((rhs, "Mathlib: adjoin_insert_intCast"))
        except Exception:
            pass
    return results


def _r0149_adjoin_eq_ring_closure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: adjoin_eq_ring_closure
    # (adjoin R s).toSubring = Subring.closure (Set.range (algebraMap R A) ∪ s)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("adjoin_R_s_toSubring")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Subring_closure", (OOp("union", (OOp("Set_range", (OOp("algebraMap", (OVar("R"), OVar("A"),)),)), OVar("s"))),))
            results.append((rhs, "Mathlib: adjoin_eq_ring_closure"))
    except Exception:
        pass
    return results


def _r0150_unop_op(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.unop_op
    # S.op.unop = S
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_op_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("S")
            results.append((rhs, "Mathlib: Subalgebra_unop_op"))
    except Exception:
        pass
    return results


def _r0151_op_unop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.op_unop
    # S.unop.op = S
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_unop_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("S")
            results.append((rhs, "Mathlib: Subalgebra_op_unop"))
    except Exception:
        pass
    return results


def _r0152_unop_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.unop_bot
    # (⊥ : Subalgebra R Aᵐᵒᵖ).unop = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Subalgebra_R_A_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Subalgebra_unop_bot"))
    except Exception:
        pass
    return results


def _r0153_op_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.op_top
    # (⊤ : Subalgebra R A).op = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_Subalgebra_R_A_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Subalgebra_op_top"))
    except Exception:
        pass
    return results


def _r0154_unop_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.unop_top
    # (⊤ : Subalgebra R Aᵐᵒᵖ).unop = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_Subalgebra_R_A_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Subalgebra_unop_top"))
    except Exception:
        pass
    return results


def _r0155_op_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.op_sup
    # (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_1_S_2_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("S_1_op", (OVar("_unknown"), OVar("S_2_op"),))
            results.append((rhs, "Mathlib: Subalgebra_op_sup"))
    except Exception:
        pass
    return results


def _r0156_unop_toSubring(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: unop_toSubring
    # S.unop.toSubring = S.toSubring.unop
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_unop_toSubring")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("S_toSubring_unop")
            results.append((rhs, "Mathlib: unop_toSubring"))
    except Exception:
        pass
    return results


def _r0157_pi_toSubmodule(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.pi_toSubmodule
    # toSubmodule (pi s t) = .pi s fun i ↦ (t i).toSubmodule
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toSubmodule", 1)
    if args is not None:
        try:
            rhs = OOp("pi", (OVar("s"), OVar("fun"), OVar("i"), OVar("_unknown"), OVar("t_i_toSubmodule"),))
            results.append((rhs, "Mathlib: Subalgebra_pi_toSubmodule"))
        except Exception:
            pass
    return results


def _r0158_pi_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.pi_top
    # pi s (fun i ↦ (⊤ : Subalgebra R (S i))) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pi", 2)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Subalgebra_pi_top"))
        except Exception:
            pass
    return results


def _r0159_pointwise_smul_toSubsemiring(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.pointwise_smul_toSubsemiring
    # (m • S).toSubsemiring = m • S.toSubsemiring
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("m_S_toSubsemiring")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("m", (OVar("_unknown"), OVar("S_toSubsemiring"),))
            results.append((rhs, "Mathlib: Subalgebra_pointwise_smul_toSubsemiring"))
    except Exception:
        pass
    return results


def _r0160_prod_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.prod_top
    # (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prod", 6)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Subalgebra_prod_top"))
        except Exception:
            pass
    return results


def _r0161_restrictScalars_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subalgebra.restrictScalars_top
    # restrictScalars R (⊤ : Subalgebra S A) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "restrictScalars", 2)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Subalgebra_restrictScalars_top"))
        except Exception:
            pass
    return results


def _r0162_unitization_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalSubsemiring.unitization_range
    # (unitization s).range = subalgebraOfSubsemiring (.closure s)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("unitization_s_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("subalgebraOfSubsemiring", (OOp("closure", (OVar("s"),)),))
            results.append((rhs, "Mathlib: NonUnitalSubsemiring_unitization_range"))
    except Exception:
        pass
    return results


def _r0163_unitization_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalSubring.unitization_range
    # (unitization s).range = subalgebraOfSubring (.closure s)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("unitization_s_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("subalgebraOfSubring", (OOp("closure", (OVar("s"),)),))
            results.append((rhs, "Mathlib: NonUnitalSubring_unitization_range"))
    except Exception:
        pass
    return results


def _r0164_unitization_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: NonUnitalStarSubalgebra.unitization_range
    # (unitization s).range = StarAlgebra.adjoin R s
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("unitization_s_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("StarAlgebra_adjoin", (OVar("R"), OVar("s"),))
            results.append((rhs, "Mathlib: NonUnitalStarSubalgebra_unitization_range"))
    except Exception:
        pass
    return results


def _r0165_restrictScalars_extendScalarsOfSurjectiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AlgEquiv.restrictScalars_extendScalarsOfSurjective
    # (f.extendScalarsOfSurjective h).restrictScalars R = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_extendScalarsOfSurjective_h_restrictScalars", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: AlgEquiv_restrictScalars_extendScalarsOfSurjective"))
        except Exception:
            pass
    return results


def _r0166_snd_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Unitization.snd_inl
    # (inl r : Unitization R A).snd = 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inl_r_colon_Unitization_R_A_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Unitization_snd_inl"))
    except Exception:
        pass
    return results


def _r0167_snd_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: snd_inr
    # (a : Unitization R A).snd = a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_colon_Unitization_R_A_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a")
            results.append((rhs, "Mathlib: snd_inr"))
    except Exception:
        pass
    return results


def _r0168_inl_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inl_inj
    # (inl x : Unitization R A) = inl y ↔ x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 5)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("inl", (OVar("y"),)), args[0])), OVar("y")))
            results.append((rhs, "Mathlib: inl_inj"))
        except Exception:
            pass
    return results


def _r0169_toProd_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toProd_add
    # (x₁ + x₂).toProd = x₁.toProd + x₂.toProd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_1_plus_x_2_toProd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("x_1_toProd"), OVar("x_2_toProd")))
            results.append((rhs, "Mathlib: toProd_add"))
    except Exception:
        pass
    return results


def _r0170_toProd_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: toProd_smul
    # (s • x).toProd = s • x.toProd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_x_toProd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s", (OVar("_unknown"), OVar("x_toProd"),))
            results.append((rhs, "Mathlib: toProd_smul"))
    except Exception:
        pass
    return results


def _r0171_fst_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fst_add
    # (x₁ + x₂).fst = x₁.fst + x₂.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_1_plus_x_2_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("x_1_fst"), OVar("x_2_fst")))
            results.append((rhs, "Mathlib: fst_add"))
    except Exception:
        pass
    return results


def _r0172_snd_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: snd_add
    # (x₁ + x₂).snd = x₁.snd + x₂.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_1_plus_x_2_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("x_1_snd"), OVar("x_2_snd")))
            results.append((rhs, "Mathlib: snd_add"))
    except Exception:
        pass
    return results


def _r0173_fst_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fst_neg
    # (-x).fst = -x.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_x_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_x_fst")
            results.append((rhs, "Mathlib: fst_neg"))
    except Exception:
        pass
    return results


def _r0174_snd_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: snd_neg
    # (-x).snd = -x.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_x_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_x_snd")
            results.append((rhs, "Mathlib: snd_neg"))
    except Exception:
        pass
    return results


def _r0175_fst_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fst_smul
    # (s • x).fst = s • x.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_x_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s", (OVar("_unknown"), OVar("x_fst"),))
            results.append((rhs, "Mathlib: fst_smul"))
    except Exception:
        pass
    return results


def _r0176_snd_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: snd_smul
    # (s • x).snd = s • x.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_x_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("s", (OVar("_unknown"), OVar("x_snd"),))
            results.append((rhs, "Mathlib: snd_smul"))
    except Exception:
        pass
    return results


def _r0177_inl_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inl_add
    # (inl (r₁ + r₂) : Unitization R A) = inl r₁ + inl r₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 5)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("inl", (OVar("r_1"),)), OOp("inl", (OVar("r_2"),))))
            results.append((rhs, "Mathlib: inl_add"))
        except Exception:
            pass
    return results


def _r0178_inl_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inl_sub
    # (inl (r₁ - r₂) : Unitization R A) = inl r₁ - inl r₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 5)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("inl", (OVar("r_1"),)), OOp("inl", (OVar("r_2"),))))
            results.append((rhs, "Mathlib: inl_sub"))
        except Exception:
            pass
    return results


def _r0179_inr_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inr_add
    # (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_1_plus_m_2", 4)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("m_1"), OVar("m_2")))
            results.append((rhs, "Mathlib: inr_add"))
        except Exception:
            pass
    return results


def _r0180_inr_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inr_neg
    # (↑(-m) : Unitization R A) = -m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_m", 4)
    if args is not None:
        try:
            rhs = OVar("minus_m")
            results.append((rhs, "Mathlib: inr_neg"))
        except Exception:
            pass
    return results


def _r0181_inr_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inr_sub
    # (↑(m₁ - m₂) : Unitization R A) = m₁ - m₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_1_minus_m_2", 4)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("m_1"), OVar("m_2")))
            results.append((rhs, "Mathlib: inr_sub"))
        except Exception:
            pass
    return results


def _r0182_inr_smul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inr_smul
    # (↑(r • m) : Unitization R A) = r • (m : Unitization R A)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "r_m", 4)
    if args is not None:
        try:
            rhs = OOp("r", (OVar("_unknown"), OOp("m", (args[0], args[1], args[2], args[3],)),))
            results.append((rhs, "Mathlib: inr_smul"))
        except Exception:
            pass
    return results


def _r0183_fst_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: fst_mul
    # (x₁ * x₂).fst = x₁.fst * x₂.fst
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_1_star_x_2_fst")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("x_1_fst"), OVar("x_2_fst")))
            results.append((rhs, "Mathlib: fst_mul"))
    except Exception:
        pass
    return results


def _r0184_inl_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inl_mul
    # (inl (r₁ * r₂) : Unitization R A) = inl r₁ * inl r₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 5)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("inl", (OVar("r_1"),)), OOp("inl", (OVar("r_2"),))))
            results.append((rhs, "Mathlib: inl_mul"))
        except Exception:
            pass
    return results


def _r0185_snd_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: snd_star
    # (star x).snd = star x.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("star_x_snd")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("star", (OVar("x_snd"),))
            results.append((rhs, "Mathlib: snd_star"))
    except Exception:
        pass
    return results


def _r0186_inl_star(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: inl_star
    # inl (star r) = star (inl r : Unitization R A)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 1)
    if args is not None:
        try:
            rhs = OOp("star", (OOp("inl", (OVar("r"), OVar("colon"), OVar("Unitization"), OVar("R"), OVar("A"),)),))
            results.append((rhs, "Mathlib: inl_star"))
        except Exception:
            pass
    return results


def _r0187_starMap_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: starMap_inr
    # starMap φ (inr a) = inr (φ a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "starMap", 2)
    if args is not None:
        try:
            rhs = OOp("inr", (OOp("phi", (OVar("a"),)),))
            results.append((rhs, "Mathlib: starMap_inr"))
        except Exception:
            pass
    return results


def _r0188_unop_finsuppProd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddOpposite.unop_finsuppProd
    # unop (f.prod g) = f.prod fun i n ↦ unop (g i n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OOp("f_prod", (OVar("fun"), OVar("i"), OVar("n"), OVar("_unknown"), OVar("unop"), OOp("g", (OVar("i"), OVar("n"),)),))
            results.append((rhs, "Mathlib: AddOpposite_unop_finsuppProd"))
        except Exception:
            pass
    return results


def _r0189_finset_prod_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.finset_prod_apply
    # (∏ x ∈ s, f x) b = ∏ x ∈ s, f x b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_in_s_f_x", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (OVar("f"), OVar("x"), args[0],))))
            results.append((rhs, "Mathlib: MonoidHom_finset_prod_apply"))
        except Exception:
            pass
    return results


def _r0190_mul_prod_eraseIdx(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommMonoid.mul_prod_eraseIdx
    # l[i] * (l.eraseIdx i).prod = l.prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("l_prod")
            results.append((rhs, "Mathlib: CommMonoid_mul_prod_eraseIdx"))
        except Exception:
            pass
    return results


def _r0191_kernelIsoKer_inv_comp_i(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddCommGrpCat.kernelIsoKer_inv_comp_ι
    # (kernelIsoKer f).inv ≫ kernel.ι f = ofHom (AddSubgroup.subtype f.hom.ker)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "kernelIsoKer_f_inv", 3)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OOp("AddSubgroup_subtype", (OVar("f_hom_ker"),)),))
            results.append((rhs, "Mathlib: AddCommGrpCat_kernelIsoKer_inv_comp_i"))
        except Exception:
            pass
    return results


def _r0192_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ModuleCat.id_apply
    # (𝟙 M : M ⟶ M) x = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_M_colon_M_M", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: ModuleCat_id_apply"))
        except Exception:
            pass
    return results


def _r0193_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ModuleCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ModuleCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0194_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ModuleCat.ofHom_id
    # ofHom LinearMap.id = 𝟙 (of R M)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("R"), OVar("M"),)),))
            results.append((rhs, "Mathlib: ModuleCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0195_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ModuleCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: ModuleCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0196_hom_2_ofHom_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ModuleCat.Hom.hom₂_ofHom₂
    # (ofHom₂ f).hom₂ = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofHom_2_f_hom_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ModuleCat_Hom_hom_2_ofHom_2"))
    except Exception:
        pass
    return results


def _r0197_ofHom_2_hom_2(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ModuleCat.ofHom₂_hom₂
    # ofHom₂ f.hom₂ = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom_2", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: ModuleCat_ofHom_2_hom_2"))
        except Exception:
            pass
    return results


def _r0198_id_moduleCat_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: LinearMap.id_moduleCat_comp
    # LinearMap.comp (𝟙 H : H ⟶ H).hom f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "LinearMap_comp", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: LinearMap_id_moduleCat_comp"))
        except Exception:
            pass
    return results


def _r0199_d_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ModuleCat.Derivation.d_mul
    # D.d (b * b') = b • D.d b' + b' • D.d b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D_d", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("b", (OVar("_unknown"), OVar("D_d"), OVar("b_prime"),)), OOp("b_prime", (OVar("_unknown"), OVar("D_d"), OVar("b"),))))
            results.append((rhs, "Mathlib: ModuleCat_Derivation_d_mul"))
        except Exception:
            pass
    return results


def _r0200_d_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ModuleCat.Derivation.d_map
    # D.d (f a) = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "D_d", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: ModuleCat_Derivation_d_map"))
        except Exception:
            pass
    return results


def _r0201_id_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingCat.id_apply
    # (𝟙 R : R ⟶ R) r = r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_1_R_colon_R_R", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: RingCat_id_apply"))
        except Exception:
            pass
    return results


def _r0202_ofHom_hom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingCat.ofHom_hom
    # ofHom (Hom.hom f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: RingCat_ofHom_hom"))
        except Exception:
            pass
    return results


def _r0203_ofHom_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingCat.ofHom_id
    # ofHom (RingHom.id R) = 𝟙 (of R)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("_1", (OOp("of", (OVar("R"),)),))
            results.append((rhs, "Mathlib: RingCat_ofHom_id"))
        except Exception:
            pass
    return results


def _r0204_ofHom_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingCat.ofHom_comp
    # ofHom (g.comp f) = ofHom f ≫ ofHom g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofHom", 1)
    if args is not None:
        try:
            rhs = OOp("ofHom", (OVar("f"), OVar("_unknown"), OVar("ofHom"), OVar("g"),))
            results.append((rhs, "Mathlib: RingCat_ofHom_comp"))
        except Exception:
            pass
    return results


def _r0205_forgetToRingCat_obj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: CommRingCat.forgetToRingCat_obj
    # (((forget₂ CommRingCat RingCat).obj R) : Type u) = R
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "forget_2_CommRingCat_RingCat_obj_R", 3)
    if args is not None:
        try:
            rhs = OVar("R")
            results.append((rhs, "Mathlib: CommRingCat_forgetToRingCat_obj"))
        except Exception:
            pass
    return results


def _r0206_quot_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingCat.Colimits.quot_neg
    # Quot.mk Setoid.r (neg x) = -(show ColimitType F from Quot.mk Setoid.r x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Quot_mk", 2)
    if args is not None:
        try:
            rhs = OVar("minus_show_ColimitType_F_from_Quot_mk_Setoid_r_x")
            results.append((rhs, "Mathlib: RingCat_Colimits_quot_neg"))
        except Exception:
            pass
    return results


def _r0207_mem_center_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Algebra.IsCentral.mem_center_iff
    # x ∈ Subalgebra.center K D ↔ ∃ (a : K), x = algebraMap K D a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("algebraMap", (OVar("K"), OVar("D"), OVar("a"),))
            results.append((rhs, "Mathlib: Algebra_IsCentral_mem_center_iff"))
        except Exception:
            pass
    return results


def _r0208_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DirectLimit.Module.hom_ext
    # g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_2")
            results.append((rhs, "Mathlib: DirectLimit_Module_hom_ext"))
    except Exception:
        pass
    return results


def _r0209_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: DirectLimit.Ring.hom_ext
    # g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_2")
            results.append((rhs, "Mathlib: DirectLimit_Ring_hom_ext"))
    except Exception:
        pass
    return results


def _r0210_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Module.DirectLimit.hom_ext
    # g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_2")
            results.append((rhs, "Mathlib: Module_DirectLimit_hom_ext"))
    except Exception:
        pass
    return results


def _r0211_exists_of(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ring.DirectLimit.exists_of
    # ∃ i x, of G f i x = z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exists", 7)
    if args is not None:
        try:
            rhs = OVar("z")
            results.append((rhs, "Mathlib: Ring_DirectLimit_exists_of"))
        except Exception:
            pass
    return results


def _r0212_hom_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Ring.DirectLimit.hom_ext
    # g₁ = g₂
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g_2")
            results.append((rhs, "Mathlib: Ring_DirectLimit_hom_ext"))
    except Exception:
        pass
    return results


def _r0213_gcd_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Field.gcd_eq
    # EuclideanDomain.gcd a b = if a = 0 then b else a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "EuclideanDomain_gcd", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0],)), OOp("_0", (OVar("then"), args[1], OVar("else"), args[0],))))
            results.append((rhs, "Mathlib: Field_gcd_eq"))
        except Exception:
            pass
    return results


def _r0214_unop_nnratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOpposite.unop_nnratCast
    # unop (q : αᵐᵒᵖ) = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: MulOpposite_unop_nnratCast"))
        except Exception:
            pass
    return results


def _r0215_op_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOpposite.op_ratCast
    # op (q : α) = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "op", 1)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: MulOpposite_op_ratCast"))
        except Exception:
            pass
    return results


def _r0216_unop_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOpposite.unop_ratCast
    # unop (q : αᵐᵒᵖ) = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "unop", 1)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: MulOpposite_unop_ratCast"))
        except Exception:
            pass
    return results


def _r0217_mem_fieldRange(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingHom.mem_fieldRange
    # y ∈ f.fieldRange ↔ ∃ x, f x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: RingHom_mem_fieldRange"))
        except Exception:
            pass
    return results


def _r0218_fieldRange_eq_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingHom.fieldRange_eq_map
    # f.fieldRange = Subfield.map f ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_fieldRange")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Subfield_map", (OVar("f"), OVar("top"),))
            results.append((rhs, "Mathlib: RingHom_fieldRange_eq_map"))
    except Exception:
        pass
    return results


def _r0219_coe_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.coe_iInf
    # (↑(⨅ i, S i) : Set K) = ⋂ i, S i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_S_i", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("S"), OVar("i"),))
            results.append((rhs, "Mathlib: Subfield_coe_iInf"))
        except Exception:
            pass
    return results


def _r0220_sInf_toSubring(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.sInf_toSubring
    # (sInf s).toSubring = ⨅ t ∈ s, Subfield.toSubring t
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sInf_s_toSubring")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("in", (OOp("_unknown", (OVar("t"),)), OOp("s", (OVar("Subfield_toSubring"), OVar("t"),))))
            results.append((rhs, "Mathlib: Subfield_sInf_toSubring"))
    except Exception:
        pass
    return results


def _r0221_closure_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.closure_empty
    # closure (∅ : Set K) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Subfield_closure_empty"))
        except Exception:
            pass
    return results


def _r0222_closure_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.closure_univ
    # closure (Set.univ : Set K) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Subfield_closure_univ"))
        except Exception:
            pass
    return results


def _r0223_closure_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.closure_union
    # closure (s ∪ t) = closure s ⊔ closure t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("closure", (OVar("s"), OVar("_unknown"), OVar("closure"), OVar("t"),))
            results.append((rhs, "Mathlib: Subfield_closure_union"))
        except Exception:
            pass
    return results


def _r0224_comap_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.comap_top
    # (⊤ : Subfield L).comap f = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Subfield_L_comap", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Subfield_comap_top"))
        except Exception:
            pass
    return results


def _r0225_rangeRestrictFieldEquiv_apply_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: RingHom.rangeRestrictFieldEquiv_apply_symm_apply
    # f (f.rangeRestrictFieldEquiv.symm x) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: RingHom_rangeRestrictFieldEquiv_apply_symm_apply"))
        except Exception:
            pass
    return results


def _r0226_coe_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SubfieldClass.coe_ratCast
    # ((x : s) : K) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_colon_s", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: SubfieldClass_coe_ratCast"))
        except Exception:
            pass
    return results


def _r0227_coe_qsmul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SubfieldClass.coe_qsmul
    # ↑(q • x) = q • (x : K)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("q", (OVar("_unknown"), OOp("x", (OVar("colon"), OVar("K"),)),))
            results.append((rhs, "Mathlib: SubfieldClass_coe_qsmul"))
    except Exception:
        pass
    return results


def _r0228_coe_set_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.coe_set_mk
    # ((⟨S, h⟩ : Subfield K) : Set K) = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_h_colon_Subfield_K", 3)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: Subfield_coe_set_mk"))
        except Exception:
            pass
    return results


def _r0229_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.copy_eq
    # S.copy s hs = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_copy", 2)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: Subfield_copy_eq"))
        except Exception:
            pass
    return results


def _r0230_coe_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.coe_sub
    # (↑(x - y) : K) = ↑x - ↑y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_minus_y", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Subfield_coe_sub"))
        except Exception:
            pass
    return results


def _r0231_coe_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.coe_neg
    # (↑(-x) : K) = -↑x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_x", 2)
    if args is not None:
        try:
            rhs = OVar("minus_x")
            results.append((rhs, "Mathlib: Subfield_coe_neg"))
        except Exception:
            pass
    return results


def _r0232_coe_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.coe_mul
    # (↑(x * y) : K) = ↑x * ↑y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_star_y", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Subfield_coe_mul"))
        except Exception:
            pass
    return results


def _r0233_coe_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.coe_div
    # (↑(x / y) : K) = ↑x / ↑y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_slash_y", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Subfield_coe_div"))
        except Exception:
            pass
    return results


def _r0234_coe_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subfield.coe_inv
    # (↑x⁻¹ : K) = (↑x)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "xinv", 2)
    if args is not None:
        try:
            rhs = OVar("x_inv")
            results.append((rhs, "Mathlib: Subfield_coe_inv"))
        except Exception:
            pass
    return results


def _r0235_algebraMap_eq_one_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FreeAlgebra.algebraMap_eq_one_iff
    # algebraMap R (FreeAlgebra R X) x = 1 ↔ x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "algebraMap", 3)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OLit(1), args[2])), OLit(1)))
            results.append((rhs, "Mathlib: FreeAlgebra_algebraMap_eq_one_iff"))
        except Exception:
            pass
    return results


def _r0236_coe_toPermHom(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAction.coe_toPermHom
    # ⇑(AddAction.toPermHom G α) = AddAction.toPerm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("AddAction_toPermHom_G_a")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("AddAction_toPerm")
            results.append((rhs, "Mathlib: AddAction_coe_toPermHom"))
    except Exception:
        pass
    return results


def _r0237_map_add_eq_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.map_add_eq_mul
    # ψ (x + y) = ψ x * ψ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("psi", (OVar("x"),)), OOp("psi", (OVar("y"),))))
            results.append((rhs, "Mathlib: AddChar_map_add_eq_mul"))
        except Exception:
            pass
    return results


def _r0238_coe_toMonoidHomEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.coe_toMonoidHomEquiv_symm
    # ⇑(toMonoidHomEquiv.symm ψ) = ψ ∘ Multiplicative.ofAdd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toMonoidHomEquiv_symm_psi")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("psi"), OVar("Multiplicative_ofAdd")))
            results.append((rhs, "Mathlib: AddChar_coe_toMonoidHomEquiv_symm"))
    except Exception:
        pass
    return results


def _r0239_toMonoidHomEquiv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.toMonoidHomEquiv_apply
    # toMonoidHomEquiv ψ a = ψ a.toAdd
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toMonoidHomEquiv", 2)
    if args is not None:
        try:
            rhs = OOp("psi", (OVar("a_toAdd"),))
            results.append((rhs, "Mathlib: AddChar_toMonoidHomEquiv_apply"))
        except Exception:
            pass
    return results


def _r0240_toMonoidHomEquiv_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.toMonoidHomEquiv_symm_apply
    # toMonoidHomEquiv.symm ψ a = ψ (Multiplicative.ofAdd a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toMonoidHomEquiv_symm", 2)
    if args is not None:
        try:
            rhs = OOp("psi", (OOp("Multiplicative_ofAdd", (args[1],)),))
            results.append((rhs, "Mathlib: AddChar_toMonoidHomEquiv_symm_apply"))
        except Exception:
            pass
    return results


def _r0241_toAddMonoidHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.toAddMonoidHom_apply
    # ψ.toAddMonoidHom a = Additive.ofMul (ψ a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi_toAddMonoidHom", 1)
    if args is not None:
        try:
            rhs = OOp("Additive_ofMul", (OOp("psi", (args[0],)),))
            results.append((rhs, "Mathlib: AddChar_toAddMonoidHom_apply"))
        except Exception:
            pass
    return results


def _r0242_coe_toAddMonoidHomEquiv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.coe_toAddMonoidHomEquiv_symm
    # ⇑(toAddMonoidHomEquiv.symm ψ) = Additive.toMul ∘ ψ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("toAddMonoidHomEquiv_symm_psi")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("Additive_toMul"), OVar("psi")))
            results.append((rhs, "Mathlib: AddChar_coe_toAddMonoidHomEquiv_symm"))
    except Exception:
        pass
    return results


def _r0243_toAddMonoidHomEquiv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.toAddMonoidHomEquiv_apply
    # toAddMonoidHomEquiv ψ a = Additive.ofMul (ψ a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAddMonoidHomEquiv", 2)
    if args is not None:
        try:
            rhs = OOp("Additive_ofMul", (OOp("psi", (args[1],)),))
            results.append((rhs, "Mathlib: AddChar_toAddMonoidHomEquiv_apply"))
        except Exception:
            pass
    return results


def _r0244_toAddMonoidHomEquiv_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.toAddMonoidHomEquiv_symm_apply
    # toAddMonoidHomEquiv.symm ψ a = (ψ a).toMul
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toAddMonoidHomEquiv_symm", 2)
    if args is not None:
        try:
            rhs = OVar("psi_a_toMul")
            results.append((rhs, "Mathlib: AddChar_toAddMonoidHomEquiv_symm_apply"))
        except Exception:
            pass
    return results


def _r0245_compAddMonoidHom_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddChar.compAddMonoidHom_apply
    # ψ.compAddMonoidHom f a = ψ (f a)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "psi_compAddMonoidHom", 2)
    if args is not None:
        try:
            rhs = OOp("psi", (OOp("f", (args[1],)),))
            results.append((rhs, "Mathlib: AddChar_compAddMonoidHom_apply"))
        except Exception:
            pass
    return results


def _r0246_coe_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.coe_inv
    # ⇑e⁻¹ = e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("einv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm")
            results.append((rhs, "Mathlib: MulAut_coe_inv"))
    except Exception:
        pass
    return results


def _r0247_mul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.mul_def
    # e₁ * e₂ = e₂.trans e₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("e_2_trans", (args[0],))
            results.append((rhs, "Mathlib: MulAut_mul_def"))
        except Exception:
            pass
    return results


def _r0248_symm_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.symm_inv
    # (e.symm)⁻¹ = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symm_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: MulAut_symm_inv"))
    except Exception:
        pass
    return results


def _r0249_inv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.inv_apply
    # e⁻¹ m = e.symm m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "einv", 1)
    if args is not None:
        try:
            rhs = OOp("e_symm", (args[0],))
            results.append((rhs, "Mathlib: MulAut_inv_apply"))
        except Exception:
            pass
    return results


def _r0250_mul_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.mul_apply
    # (e₁ * e₂) m = e₁ (e₂ m)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_1_star_e_2", 1)
    if args is not None:
        try:
            rhs = OOp("e_1", (OOp("e_2", (args[0],)),))
            results.append((rhs, "Mathlib: MulAut_mul_apply"))
        except Exception:
            pass
    return results


def _r0251_apply_inv_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.apply_inv_self
    # e (e⁻¹ m) = m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e", 1)
    if args is not None:
        try:
            rhs = OVar("m")
            results.append((rhs, "Mathlib: MulAut_apply_inv_self"))
        except Exception:
            pass
    return results


def _r0252_conj_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.conj_symm_apply
    # (conj g).symm h = g⁻¹ * h * g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "conj_g_symm", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("ginv"), OOp("*", (args[0], OVar("g")))))
            results.append((rhs, "Mathlib: MulAut_conj_symm_apply"))
        except Exception:
            pass
    return results


def _r0253_conj_inv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulAut.conj_inv_apply
    # (conj g)⁻¹ h = g⁻¹ * h * g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "conj_g_inv", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("ginv"), OOp("*", (args[0], OVar("g")))))
            results.append((rhs, "Mathlib: MulAut_conj_inv_apply"))
        except Exception:
            pass
    return results


def _r0254_coe_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.coe_inv
    # ⇑e⁻¹ = e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("einv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e_symm")
            results.append((rhs, "Mathlib: AddAut_coe_inv"))
    except Exception:
        pass
    return results


def _r0255_mul_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.mul_def
    # e₁ * e₂ = e₂.trans e₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("e_2_trans", (args[0],))
            results.append((rhs, "Mathlib: AddAut_mul_def"))
        except Exception:
            pass
    return results


def _r0256_inv_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.inv_symm
    # e⁻¹.symm = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("einv_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: AddAut_inv_symm"))
    except Exception:
        pass
    return results


def _r0257_symm_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.symm_inv
    # e.symm⁻¹ = e
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("e_symminv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("e")
            results.append((rhs, "Mathlib: AddAut_symm_inv"))
    except Exception:
        pass
    return results


def _r0258_inv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.inv_apply
    # e⁻¹ a = e.symm a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "einv", 1)
    if args is not None:
        try:
            rhs = OOp("e_symm", (args[0],))
            results.append((rhs, "Mathlib: AddAut_inv_apply"))
        except Exception:
            pass
    return results


def _r0259_inv_apply_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.inv_apply_self
    # e⁻¹ (e a) = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "einv", 1)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: AddAut_inv_apply_self"))
        except Exception:
            pass
    return results


def _r0260_conj_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.conj_symm_apply
    # (conj g).toMul.symm h = -g + h + g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "conj_g_toMul_symm", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("minus_g"), OOp("+", (args[0], OVar("g")))))
            results.append((rhs, "Mathlib: AddAut_conj_symm_apply"))
        except Exception:
            pass
    return results


def _r0261_conj_inv_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddAut.conj_inv_apply
    # (conj g).toMul⁻¹ h = -g + h + g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "conj_g_toMulinv", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OVar("minus_g"), OOp("+", (args[0], OVar("g")))))
            results.append((rhs, "Mathlib: AddAut_conj_inv_apply"))
        except Exception:
            pass
    return results


def _r0262_mk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulEquiv.mk_coe
    # (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : M ≃* N) = e
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_e_prime_h_1_h_2_h_3", 4)
    if args is not None:
        try:
            rhs = OVar("e")
            results.append((rhs, "Mathlib: MulEquiv_mk_coe"))
        except Exception:
            pass
    return results


def _r0263_toEquiv_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulEquiv.toEquiv_eq_coe
    # f.toEquiv = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toEquiv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MulEquiv_toEquiv_eq_coe"))
    except Exception:
        pass
    return results


def _r0264_toFun_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulEquiv.toFun_eq_coe
    # f.toFun = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MulEquiv_toFun_eq_coe"))
    except Exception:
        pass
    return results


def _r0265_coe_symm_opMulEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulOpposite.coe_symm_opMulEquiv
    # ⇑opMulEquiv.symm = unop (α := M)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("opMulEquiv_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("unop", (OOp("a", (OVar("colon_eq"), OVar("M"),)),))
            results.append((rhs, "Mathlib: MulOpposite_coe_symm_opMulEquiv"))
    except Exception:
        pass
    return results


def _r0266_smul_cons(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Matrix.smul_cons
    # x • vecCons y v = vecCons (x • y) (x • v)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x", 4)
    if args is not None:
        try:
            rhs = OOp("vecCons", (OOp("x", (args[0], args[2],)), OOp("x", (args[0], args[3],)),))
            results.append((rhs, "Mathlib: Matrix_smul_cons"))
        except Exception:
            pass
    return results


def _r0267_mgraph_eq_mrange_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.mgraph_eq_mrange_prod
    # f.mgraph = mrange ((id _).prod f)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_mgraph")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("mrange", (OOp("id_prod", (OVar("f"),)),))
            results.append((rhs, "Mathlib: MonoidHom_mgraph_eq_mrange_prod"))
    except Exception:
        pass
    return results


def _r0268_mul_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.mul_comp
    # (g₁ * g₂).comp f = g₁.comp f * g₂.comp f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "g_1_star_g_2_comp", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("g_1_comp", (args[0],)), OOp("g_2_comp", (args[0],))))
            results.append((rhs, "Mathlib: MulHom_mul_comp"))
        except Exception:
            pass
    return results


def _r0269_toFun_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.toFun_eq_coe
    # f.toFun = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MulHom_toFun_eq_coe"))
    except Exception:
        pass
    return results


def _r0270_toMulHom_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.toMulHom_coe
    # f.toMulHom.toFun = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toMulHom_toFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MonoidHom_toMulHom_coe"))
    except Exception:
        pass
    return results


def _r0271_toFun_eq_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.toFun_eq_coe
    # f.toFun = f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_toFun")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MonoidHom_toFun_eq_coe"))
    except Exception:
        pass
    return results


def _r0272_mk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.mk_coe
    # MulHom.mk f hmul = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MulHom_mk", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MulHom_mk_coe"))
        except Exception:
            pass
    return results


def _r0273_mk_coe(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.mk_coe
    # MonoidHom.mk f hmul = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MonoidHom_mk", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MonoidHom_mk_coe"))
        except Exception:
            pass
    return results


def _r0274_coe_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.coe_comp
    # ↑(g.comp f) = g ∘ f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_comp_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("g"), OVar("f")))
            results.append((rhs, "Mathlib: MulHom_coe_comp"))
    except Exception:
        pass
    return results


def _r0275_coe_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.coe_comp
    # ↑(g.comp f) = g ∘ f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("g_comp_f")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comp", (OVar("g"), OVar("f")))
            results.append((rhs, "Mathlib: MonoidHom_coe_comp"))
    except Exception:
        pass
    return results


def _r0276_comp_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.comp_id
    # f.comp (MulHom.id M) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MulHom_comp_id"))
        except Exception:
            pass
    return results


def _r0277_comp_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.comp_id
    # f.comp (MonoidHom.id M) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MonoidHom_comp_id"))
        except Exception:
            pass
    return results


def _r0278_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.id_comp
    # (MulHom.id N).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MulHom_id_N_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MulHom_id_comp"))
        except Exception:
            pass
    return results


def _r0279_id_comp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.id_comp
    # (MonoidHom.id N).comp f = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MonoidHom_id_N_comp", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MonoidHom_id_comp"))
        except Exception:
            pass
    return results


def _r0280_map_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.map_pow
    # f (a ^ n) = f a ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("f", (OVar("a"),)), OVar("n")))
            results.append((rhs, "Mathlib: MonoidHom_map_pow"))
        except Exception:
            pass
    return results


def _r0281_ofNat_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddMonoid.End.ofNat_apply
    # (ofNat(n) : AddMonoid.End M) m = n • m
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ofNat_n_colon_AddMonoid_End_M", 1)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), args[0],))
            results.append((rhs, "Mathlib: AddMonoid_End_ofNat_apply"))
        except Exception:
            pass
    return results


def _r0282_apply_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddMonoidHom.apply_nat
    # f n = n • f 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("n", (OVar("_unknown"), OVar("f"), OLit(1),))
            results.append((rhs, "Mathlib: AddMonoidHom_apply_nat"))
        except Exception:
            pass
    return results


def _r0283_apply_mnat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.apply_mnat
    # f n = f (Multiplicative.ofAdd 1) ^ n.toAdd
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("f", (OOp("Multiplicative_ofAdd", (OLit(1),)),)), OVar("n_toAdd")))
            results.append((rhs, "Mathlib: MonoidHom_apply_mnat"))
        except Exception:
            pass
    return results


def _r0284_coe_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.coe_snd
    # ⇑(snd M N) = Prod.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("snd_M_N")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Prod_snd")
            results.append((rhs, "Mathlib: MulHom_coe_snd"))
    except Exception:
        pass
    return results


def _r0285_fst_comp_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.fst_comp_prod
    # (fst N P).comp (f.prod g) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_N_P_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MulHom_fst_comp_prod"))
        except Exception:
            pass
    return results


def _r0286_snd_comp_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.snd_comp_prod
    # (snd N P).comp (f.prod g) = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_N_P_comp", 1)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: MulHom_snd_comp_prod"))
        except Exception:
            pass
    return results


def _r0287_prod_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulHom.prod_unique
    # ((fst N P).comp f).prod ((snd N P).comp f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_N_P_comp_f_prod", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MulHom_prod_unique"))
        except Exception:
            pass
    return results


def _r0288_coe_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.coe_snd
    # ⇑(snd M N) = Prod.snd
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("snd_M_N")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Prod_snd")
            results.append((rhs, "Mathlib: MonoidHom_coe_snd"))
    except Exception:
        pass
    return results


def _r0289_inl_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.inl_apply
    # inl M N x = (x, 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inl", 3)
    if args is not None:
        try:
            rhs = OOp("x", (OLit(1),))
            results.append((rhs, "Mathlib: MonoidHom_inl_apply"))
        except Exception:
            pass
    return results


def _r0290_inr_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.inr_apply
    # inr M N y = (1, y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "inr", 3)
    if args is not None:
        try:
            rhs = OOp("_1", (args[2],))
            results.append((rhs, "Mathlib: MonoidHom_inr_apply"))
        except Exception:
            pass
    return results


def _r0291_fst_comp_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.fst_comp_inl
    # (fst M N).comp (inl M N) = id M
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_M_N_comp", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("M"),))
            results.append((rhs, "Mathlib: MonoidHom_fst_comp_inl"))
        except Exception:
            pass
    return results


def _r0292_snd_comp_inl(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.snd_comp_inl
    # (snd M N).comp (inl M N) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_M_N_comp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MonoidHom_snd_comp_inl"))
        except Exception:
            pass
    return results


def _r0293_fst_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.fst_comp_inr
    # (fst M N).comp (inr M N) = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_M_N_comp", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MonoidHom_fst_comp_inr"))
        except Exception:
            pass
    return results


def _r0294_snd_comp_inr(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.snd_comp_inr
    # (snd M N).comp (inr M N) = id N
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_M_N_comp", 1)
    if args is not None:
        try:
            rhs = OOp("id", (OVar("N"),))
            results.append((rhs, "Mathlib: MonoidHom_snd_comp_inr"))
        except Exception:
            pass
    return results


def _r0295_fst_comp_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.fst_comp_prod
    # (fst N P).comp (f.prod g) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_N_P_comp", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MonoidHom_fst_comp_prod"))
        except Exception:
            pass
    return results


def _r0296_snd_comp_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.snd_comp_prod
    # (snd N P).comp (f.prod g) = g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "snd_N_P_comp", 1)
    if args is not None:
        try:
            rhs = OVar("g")
            results.append((rhs, "Mathlib: MonoidHom_snd_comp_prod"))
        except Exception:
            pass
    return results


def _r0297_prod_unique(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.prod_unique
    # ((fst N P).comp f).prod ((snd N P).comp f) = f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fst_N_P_comp_f_prod", 1)
    if args is not None:
        try:
            rhs = OVar("f")
            results.append((rhs, "Mathlib: MonoidHom_prod_unique"))
        except Exception:
            pass
    return results


def _r0298_coe_prodComm_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulEquiv.coe_prodComm_symm
    # ⇑(prodComm : M × N ≃* N × M).symm = Prod.swap
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("prodComm_colon_M_times_N_star_N_times_M_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Prod_swap")
            results.append((rhs, "Mathlib: MulEquiv_coe_prodComm_symm"))
    except Exception:
        pass
    return results


def _r0299_coe_prodAssoc_symm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulEquiv.coe_prodAssoc_symm
    # ⇑(prodAssoc : (M × N) × P ≃* M × (N × P)).symm = (Equiv.prodAssoc M N P).symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("prodAssoc_colon_M_times_N_times_P_star_M_times_N_times_P_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("Equiv_prodAssoc_M_N_P_symm")
            results.append((rhs, "Mathlib: MulEquiv_coe_prodAssoc_symm"))
    except Exception:
        pass
    return results


def _r0300_bot_prod_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.bot_prod_bot
    # (⊥ : Subgroup G).prod (⊥ : Subgroup N) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_Subgroup_G_prod", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Subgroup_bot_prod_bot"))
        except Exception:
            pass
    return results


def _r0301_normalClosure_idempotent(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.normalClosure_idempotent
    # normalClosure ↑(normalClosure s) = normalClosure s
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalClosure", 1)
    if args is not None:
        try:
            rhs = OOp("normalClosure", (OVar("s"),))
            results.append((rhs, "Mathlib: Subgroup_normalClosure_idempotent"))
        except Exception:
            pass
    return results


def _r0302_normalCore_idempotent(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.normalCore_idempotent
    # H.normalCore.normalCore = H.normalCore
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_normalCore_normalCore")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("H_normalCore")
            results.append((rhs, "Mathlib: Subgroup_normalCore_idempotent"))
    except Exception:
        pass
    return results


def _r0303_ker_snd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.ker_snd
    # ker (snd G G') = .prod ⊤ ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ker", 1)
    if args is not None:
        try:
            rhs = OOp("prod", (OVar("top"), OVar("bot"),))
            results.append((rhs, "Mathlib: MonoidHom_ker_snd"))
        except Exception:
            pass
    return results


def _r0304_subgroupOf_inertia(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddSubgroup.subgroupOf_inertia
    # (I.inertia G).subgroupOf H = I.inertia H
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "I_inertia_G_subgroupOf", 1)
    if args is not None:
        try:
            rhs = OOp("I_inertia", (args[0],))
            results.append((rhs, "Mathlib: AddSubgroup_subgroupOf_inertia"))
        except Exception:
            pass
    return results


def _r0305_coe_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_inv
    # ↑(x⁻¹ : H) = (x⁻¹ : G)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("xinv_colon_H")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("xinv", (OVar("colon"), OVar("G"),))
            results.append((rhs, "Mathlib: Subgroup_coe_inv"))
    except Exception:
        pass
    return results


def _r0306_coe_div(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_div
    # (↑(x / y) : G) = ↑x / ↑y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_slash_y", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("x"), OVar("y")))
            results.append((rhs, "Mathlib: Subgroup_coe_div"))
        except Exception:
            pass
    return results


def _r0307_coe_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_mk
    # ((⟨x, hx⟩ : H) : G) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "x_hx_colon_H", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Subgroup_coe_mk"))
        except Exception:
            pass
    return results


def _r0308_coe_square(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subsemigroup.coe_square
    # square S = {s : S | IsSquare s}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "square", 1)
    if args is not None:
        try:
            rhs = OVar("s_colon_S_pipe_IsSquare_s")
            results.append((rhs, "Mathlib: Subsemigroup_coe_square"))
        except Exception:
            pass
    return results


def _r0309_coe_square(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.coe_square
    # square M = {s : M | IsSquare s}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "square", 1)
    if args is not None:
        try:
            rhs = OVar("s_colon_M_pipe_IsSquare_s")
            results.append((rhs, "Mathlib: Submonoid_coe_square"))
        except Exception:
            pass
    return results


def _r0310_coe_square(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_square
    # square G = {s : G | IsSquare s}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "square", 1)
    if args is not None:
        try:
            rhs = OVar("s_colon_G_pipe_IsSquare_s")
            results.append((rhs, "Mathlib: Subgroup_coe_square"))
        except Exception:
            pass
    return results


def _r0311_val_multiset_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.val_multiset_prod
    # (m.prod : G) = (m.map Subtype.val).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_prod", 2)
    if args is not None:
        try:
            rhs = OVar("m_map_Subtype_val_prod")
            results.append((rhs, "Mathlib: Subgroup_val_multiset_prod"))
        except Exception:
            pass
    return results


def _r0312_eq_bot_of_card_le(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.eq_bot_of_card_le
    # H = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Subgroup_eq_bot_of_card_le"))
    except Exception:
        pass
    return results


def _r0313_mem_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.mem_range
    # y ∈ f.range ↔ ∃ x, f x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: MonoidHom_mem_range"))
        except Exception:
            pass
    return results


def _r0314_range_eq_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.range_eq_map
    # f.range = (⊤ : Subgroup G).map f
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("top_colon_Subgroup_G_map", (OVar("f"),))
            results.append((rhs, "Mathlib: MonoidHom_range_eq_map"))
    except Exception:
        pass
    return results


def _r0315_map_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.map_range
    # f.range.map g = (g.comp f).range
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_range_map", 1)
    if args is not None:
        try:
            rhs = OVar("g_comp_f_range")
            results.append((rhs, "Mathlib: MonoidHom_map_range"))
        except Exception:
            pass
    return results


def _r0316_range_eq_top_of_surjective(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.range_eq_top_of_surjective
    # f.range = (⊤ : Subgroup N)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("top", (OVar("colon"), OVar("Subgroup"), OVar("N"),))
            results.append((rhs, "Mathlib: MonoidHom_range_eq_top_of_surjective"))
    except Exception:
        pass
    return results


def _r0317_range_subtype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.range_subtype
    # H.subtype.range = H
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_subtype_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("H")
            results.append((rhs, "Mathlib: Subgroup_range_subtype"))
    except Exception:
        pass
    return results


def _r0318_coe_toMultiplicative_range(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.coe_toMultiplicative_range
    # (AddMonoidHom.toMultiplicative f).range = AddSubgroup.toSubgroup f.range
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("AddMonoidHom_toMultiplicative_f_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("AddSubgroup_toSubgroup", (OVar("f_range"),))
            results.append((rhs, "Mathlib: MonoidHom_coe_toMultiplicative_range"))
    except Exception:
        pass
    return results


def _r0319_mem_ker(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.mem_ker
    # x ∈ f.ker ↔ f x = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: MonoidHom_mem_ker"))
        except Exception:
            pass
    return results


def _r0320_div_mem_ker_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.div_mem_ker_iff
    # x / y ∈ ker f ↔ f x = f y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("y"),))
            results.append((rhs, "Mathlib: MonoidHom_div_mem_ker_iff"))
        except Exception:
            pass
    return results


def _r0321_ker_restrict(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.ker_restrict
    # (f.restrict K).ker = f.ker.subgroupOf K
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_restrict_K_ker")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_ker_subgroupOf", (OVar("K"),))
            results.append((rhs, "Mathlib: MonoidHom_ker_restrict"))
    except Exception:
        pass
    return results


def _r0322_ker_codRestrict(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.ker_codRestrict
    # (f.codRestrict s h).ker = f.ker
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_codRestrict_s_h_ker")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("f_ker")
            results.append((rhs, "Mathlib: MonoidHom_ker_codRestrict"))
    except Exception:
        pass
    return results


def _r0323_ker_id(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.ker_id
    # (MonoidHom.id G).ker = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("MonoidHom_id_G_ker")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: MonoidHom_ker_id"))
    except Exception:
        pass
    return results


def _r0324_ker_eq_top_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.ker_eq_top_iff
    # f.ker = ⊤ ↔ f = 1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_ker")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("f"))), OLit(1)))
            results.append((rhs, "Mathlib: MonoidHom_ker_eq_top_iff"))
    except Exception:
        pass
    return results


def _r0325_ker_inclusion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.ker_inclusion
    # (inclusion h).ker = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("inclusion_h_ker")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Subgroup_ker_inclusion"))
    except Exception:
        pass
    return results


def _r0326_ker_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.ker_prod
    # (f.prod g).ker = f.ker ⊓ g.ker
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_prod_g_ker")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("f_ker", (OVar("_unknown"), OVar("g_ker"),))
            results.append((rhs, "Mathlib: MonoidHom_ker_prod"))
    except Exception:
        pass
    return results


def _r0327_coe_toMultiplicative_ker(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.coe_toMultiplicative_ker
    # (AddMonoidHom.toMultiplicative f).ker = AddSubgroup.toSubgroup f.ker
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("AddMonoidHom_toMultiplicative_f_ker")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("AddSubgroup_toSubgroup", (OVar("f_ker"),))
            results.append((rhs, "Mathlib: MonoidHom_coe_toMultiplicative_ker"))
    except Exception:
        pass
    return results


def _r0328_coe_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_top
    # ((⊤ : Subgroup G) : Set G) = Set.univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Subgroup_G", 3)
    if args is not None:
        try:
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: Subgroup_coe_top"))
        except Exception:
            pass
    return results


def _r0329_coe_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_bot
    # ((⊥ : Subgroup G) : Set G) = {1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_Subgroup_G", 3)
    if args is not None:
        try:
            rhs = OVar("_1")
            results.append((rhs, "Mathlib: Subgroup_coe_bot"))
        except Exception:
            pass
    return results


def _r0330_bot_toSubmonoid(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.bot_toSubmonoid
    # (⊥ : Subgroup G).toSubmonoid = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Subgroup_G_toSubmonoid")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Subgroup_bot_toSubmonoid"))
    except Exception:
        pass
    return results


def _r0331_eq_bot_iff_forall(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.eq_bot_iff_forall
    # H = ⊥ ↔ ∀ x ∈ H, x = (1 : G)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("bot"), OOp("in", (OOp("forall", (OVar("x"),)), OOp("H", (OVar("x"),)))))), OOp("_1", (OVar("colon"), OVar("G"),))))
            results.append((rhs, "Mathlib: Subgroup_eq_bot_iff_forall"))
    except Exception:
        pass
    return results


def _r0332_coe_eq_singleton(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_eq_singleton
    # (∃ g : G, (H : Set G) = {g}) ↔ H = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Subgroup_coe_eq_singleton"))
        except Exception:
            pass
    return results


def _r0333_coe_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.coe_iInf
    # (↑(⨅ i, S i) : Set G) = ⋂ i, S i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_S_i", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("S"), OVar("i"),))
            results.append((rhs, "Mathlib: Subgroup_coe_iInf"))
        except Exception:
            pass
    return results


def _r0334_closure_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.closure_empty
    # closure (∅ : Set G) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Subgroup_closure_empty"))
        except Exception:
            pass
    return results


def _r0335_closure_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.closure_univ
    # closure (univ : Set G) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Subgroup_closure_univ"))
        except Exception:
            pass
    return results


def _r0336_closure_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.closure_union
    # closure (s ∪ t) = closure s ⊔ closure t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("closure", (OVar("s"), OVar("_unknown"), OVar("closure"), OVar("t"),))
            results.append((rhs, "Mathlib: Subgroup_closure_union"))
        except Exception:
            pass
    return results


def _r0337_iSup_eq_closure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.iSup_eq_closure
    # ⨆ i, p i = closure (⋃ i, (p i : Set G))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("closure", (OOp("_unknown", (args[2], OOp("p", (args[2], OVar("colon"), OVar("Set"), OVar("G"),)),)),))
            results.append((rhs, "Mathlib: Subgroup_iSup_eq_closure"))
        except Exception:
            pass
    return results


def _r0338_toAddSubgroup_closure(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.toAddSubgroup_closure
    # (Subgroup.closure S).toAddSubgroup = AddSubgroup.closure (Additive.toMul ⁻¹' S)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Subgroup_closure_S_toAddSubgroup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("AddSubgroup_closure", (OOp("Additive_toMul", (OVar("inv_prime"), OVar("S"),)),))
            results.append((rhs, "Mathlib: Subgroup_toAddSubgroup_closure"))
    except Exception:
        pass
    return results


def _r0339_toSubgroup_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: AddSubgroup.toSubgroup_comap
    # s.toSubgroup.comap (AddMonoidHom.toMultiplicative f) = AddSubgroup.toSubgroup (s.comap f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_toSubgroup_comap", 1)
    if args is not None:
        try:
            rhs = OOp("AddSubgroup_toSubgroup", (OOp("s_comap", (OVar("f"),)),))
            results.append((rhs, "Mathlib: AddSubgroup_toSubgroup_comap"))
        except Exception:
            pass
    return results


def _r0340_map_toSubmonoid(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.map_toSubmonoid
    # (Subgroup.map f K).toSubmonoid = Submonoid.map f K.toSubmonoid
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("Subgroup_map_f_K_toSubmonoid")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("Submonoid_map", (OVar("f"), OVar("K_toSubmonoid"),))
            results.append((rhs, "Mathlib: Subgroup_map_toSubmonoid"))
    except Exception:
        pass
    return results


def _r0341_mem_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.mem_map
    # y ∈ K.map f ↔ ∃ x ∈ K, f x = y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("y")
            results.append((rhs, "Mathlib: Subgroup_mem_map"))
        except Exception:
            pass
    return results


def _r0342_map_map(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.map_map
    # (K.map f).map g = K.map (g.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "K_map_f_map", 1)
    if args is not None:
        try:
            rhs = OOp("K_map", (OOp("g_comp", (OVar("f"),)),))
            results.append((rhs, "Mathlib: Subgroup_map_map"))
        except Exception:
            pass
    return results


def _r0343_comap_inclusion_subgroupOf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.comap_inclusion_subgroupOf
    # (H.subgroupOf K₂).comap (inclusion h) = H.subgroupOf K₁
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_subgroupOf_K_2_comap", 1)
    if args is not None:
        try:
            rhs = OOp("H_subgroupOf", (OVar("K_1"),))
            results.append((rhs, "Mathlib: Subgroup_comap_inclusion_subgroupOf"))
        except Exception:
            pass
    return results


def _r0344_top_subgroupOf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.top_subgroupOf
    # (⊤ : Subgroup G).subgroupOf H = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Subgroup_G_subgroupOf", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Subgroup_top_subgroupOf"))
        except Exception:
            pass
    return results


def _r0345_subgroupOf_bot_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.subgroupOf_bot_eq_bot
    # H.subgroupOf ⊥ = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_subgroupOf", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Subgroup_subgroupOf_bot_eq_bot"))
        except Exception:
            pass
    return results


def _r0346_subgroupOf_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.subgroupOf_inj
    # H₁.subgroupOf K = H₂.subgroupOf K ↔ H₁ ⊓ K = H₂ ⊓ K
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_1_subgroupOf", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("H_2_subgroupOf", (args[0],)), OOp("H_1", (OVar("_unknown"), args[0],)))), OOp("H_2", (OVar("_unknown"), args[0],))))
            results.append((rhs, "Mathlib: Subgroup_subgroupOf_inj"))
        except Exception:
            pass
    return results


def _r0347_inf_subgroupOf_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.inf_subgroupOf_left
    # (K ⊓ H).subgroupOf K = H.subgroupOf K
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "K_H_subgroupOf", 1)
    if args is not None:
        try:
            rhs = OOp("H_subgroupOf", (args[0],))
            results.append((rhs, "Mathlib: Subgroup_inf_subgroupOf_left"))
        except Exception:
            pass
    return results


def _r0348_subgroupOf_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.subgroupOf_eq_bot
    # H.subgroupOf K = ⊥ ↔ Disjoint H K
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_subgroupOf", 1)
    if args is not None:
        try:
            rhs = OOp("iff", (OVar("bot"), OOp("Disjoint", (OVar("H"), args[0],))))
            results.append((rhs, "Mathlib: Subgroup_subgroupOf_eq_bot"))
        except Exception:
            pass
    return results


def _r0349_subgroupOf_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.subgroupOf_eq_top
    # H.subgroupOf K = ⊤ ↔ K ≤ H
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "H_subgroupOf", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OVar("top"), args[0])), OVar("H")))
            results.append((rhs, "Mathlib: Subgroup_subgroupOf_eq_top"))
        except Exception:
            pass
    return results


def _r0350_symm_comapSubgroup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulEquiv.symm_comapSubgroup
    # (comapSubgroup e).symm = comapSubgroup e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("comapSubgroup_e_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("comapSubgroup", (OVar("e_symm"),))
            results.append((rhs, "Mathlib: MulEquiv_symm_comapSubgroup"))
    except Exception:
        pass
    return results


def _r0351_symm_mapSubgroup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulEquiv.symm_mapSubgroup
    # (mapSubgroup e).symm = mapSubgroup e.symm
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("mapSubgroup_e_symm")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("mapSubgroup", (OVar("e_symm"),))
            results.append((rhs, "Mathlib: MulEquiv_symm_mapSubgroup"))
    except Exception:
        pass
    return results


def _r0352_subgroupCongr_symm_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MulEquiv.subgroupCongr_symm_apply
    # ((MulEquiv.subgroupCongr h).symm x : G) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MulEquiv_subgroupCongr_h_symm", 3)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: MulEquiv_subgroupCongr_symm_apply"))
        except Exception:
            pass
    return results


def _r0353_op_toSubmonoid(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.op_toSubmonoid
    # H.op.toSubmonoid = H.toSubmonoid.op
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_op_toSubmonoid")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("H_toSubmonoid_op")
            results.append((rhs, "Mathlib: Subgroup_op_toSubmonoid"))
    except Exception:
        pass
    return results


def _r0354_op_toSubsemigroup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.op_toSubsemigroup
    # H.op.toSubsemigroup = H.toSubsemigroup.op
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_op_toSubsemigroup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("H_toSubsemigroup_op")
            results.append((rhs, "Mathlib: Subgroup_op_toSubsemigroup"))
    except Exception:
        pass
    return results


def _r0355_unop_toSubmonoid(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.unop_toSubmonoid
    # H.unop.toSubmonoid = H.toSubmonoid.unop
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_unop_toSubmonoid")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("H_toSubmonoid_unop")
            results.append((rhs, "Mathlib: Subgroup_unop_toSubmonoid"))
    except Exception:
        pass
    return results


def _r0356_unop_toSubsemigroup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.unop_toSubsemigroup
    # H.unop.toSubsemigroup = H.toSubsemigroup.unop
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_unop_toSubsemigroup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("H_toSubsemigroup_unop")
            results.append((rhs, "Mathlib: Subgroup_unop_toSubsemigroup"))
    except Exception:
        pass
    return results


def _r0357_op_unop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.op_unop
    # S.unop.op = S
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_unop_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("S")
            results.append((rhs, "Mathlib: Subgroup_op_unop"))
    except Exception:
        pass
    return results


def _r0358_unop_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.unop_inj
    # S.unop = T.unop ↔ S = T
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("T_unop"), OVar("S"))), OVar("T")))
            results.append((rhs, "Mathlib: Subgroup_unop_inj"))
    except Exception:
        pass
    return results


def _r0359_op_normalizer(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.op_normalizer
    # (normalizer H : Subgroup G).op = normalizer H.op
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("normalizer_H_colon_Subgroup_G_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("normalizer", (OVar("H_op"),))
            results.append((rhs, "Mathlib: Subgroup_op_normalizer"))
    except Exception:
        pass
    return results


def _r0360_op_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.op_eq_bot
    # S.op = ⊥ ↔ S = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("bot"), OVar("S"))), OVar("bot")))
            results.append((rhs, "Mathlib: Subgroup_op_eq_bot"))
    except Exception:
        pass
    return results


def _r0361_unop_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.unop_bot
    # (⊥ : Subgroup Gᵐᵒᵖ).unop = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Subgroup_G_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Subgroup_unop_bot"))
    except Exception:
        pass
    return results


def _r0362_unop_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.unop_eq_bot
    # S.unop = ⊥ ↔ S = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("bot"), OVar("S"))), OVar("bot")))
            results.append((rhs, "Mathlib: Subgroup_unop_eq_bot"))
    except Exception:
        pass
    return results


def _r0363_op_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.op_top
    # (⊤ : Subgroup G).op = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_Subgroup_G_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Subgroup_op_top"))
    except Exception:
        pass
    return results


def _r0364_op_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.op_eq_top
    # S.op = ⊤ ↔ S = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("S"))), OVar("top")))
            results.append((rhs, "Mathlib: Subgroup_op_eq_top"))
    except Exception:
        pass
    return results


def _r0365_unop_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.unop_top
    # (⊤ : Subgroup Gᵐᵒᵖ).unop = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_Subgroup_G_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Subgroup_unop_top"))
    except Exception:
        pass
    return results


def _r0366_unop_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.unop_eq_top
    # S.unop = ⊤ ↔ S = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("S"))), OVar("top")))
            results.append((rhs, "Mathlib: Subgroup_unop_eq_top"))
    except Exception:
        pass
    return results


def _r0367_op_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.op_sup
    # (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_1_S_2_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("S_1_op", (OVar("_unknown"), OVar("S_2_op"),))
            results.append((rhs, "Mathlib: Subgroup_op_sup"))
    except Exception:
        pass
    return results


def _r0368_closure_singleton_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.closure_singleton_inv
    # closure {x⁻¹} = closure {x}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("closure", (OVar("x"),))
            results.append((rhs, "Mathlib: Subgroup_closure_singleton_inv"))
        except Exception:
            pass
    return results


def _r0369_pointwise_smul_toSubmonoid(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.pointwise_smul_toSubmonoid
    # (a • S).toSubmonoid = a • S.toSubmonoid
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_S_toSubmonoid")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("a", (OVar("_unknown"), OVar("S_toSubmonoid"),))
            results.append((rhs, "Mathlib: Subgroup_pointwise_smul_toSubmonoid"))
    except Exception:
        pass
    return results


def _r0370_smul_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.smul_sup
    # a • (S ⊔ T) = a • S ⊔ a • T
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "a", 2)
    if args is not None:
        try:
            rhs = OOp("a", (args[0], OVar("S"), args[0], OVar("a"), args[0], OVar("T"),))
            results.append((rhs, "Mathlib: Subgroup_smul_sup"))
        except Exception:
            pass
    return results


def _r0371_zpowers_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Subgroup.zpowers_inv
    # zpowers g⁻¹ = zpowers g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "zpowers", 1)
    if args is not None:
        try:
            rhs = OOp("zpowers", (OVar("g"),))
            results.append((rhs, "Mathlib: Subgroup_zpowers_inv"))
        except Exception:
            pass
    return results


def _r0372_coe_iInf(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.coe_iInf
    # (↑(⨅ i, S i) : Set M) = ⋂ i, S i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "i_S_i", 3)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("S"), OVar("i"),))
            results.append((rhs, "Mathlib: Submonoid_coe_iInf"))
        except Exception:
            pass
    return results


def _r0373_closure_empty(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.closure_empty
    # closure (∅ : Set M) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Submonoid_closure_empty"))
        except Exception:
            pass
    return results


def _r0374_closure_univ(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.closure_univ
    # closure (univ : Set M) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Submonoid_closure_univ"))
        except Exception:
            pass
    return results


def _r0375_closure_union(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.closure_union
    # closure (s ∪ t) = closure s ⊔ closure t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "closure", 1)
    if args is not None:
        try:
            rhs = OOp("closure", (OVar("s"), OVar("_unknown"), OVar("closure"), OVar("t"),))
            results.append((rhs, "Mathlib: Submonoid_closure_union"))
        except Exception:
            pass
    return results


def _r0376_coe_multiset_prod(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: SubmonoidClass.coe_multiset_prod
    # (m.prod : M) = (m.map (↑)).prod
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m_prod", 2)
    if args is not None:
        try:
            rhs = OVar("m_map_prod")
            results.append((rhs, "Mathlib: SubmonoidClass_coe_multiset_prod"))
        except Exception:
            pass
    return results


def _r0377_copy_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.copy_eq
    # S.copy s hs = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_copy", 2)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: Submonoid_copy_eq"))
        except Exception:
            pass
    return results


def _r0378_coe_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.coe_top
    # ((⊤ : Submonoid M) : Set M) = Set.univ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "top_colon_Submonoid_M", 3)
    if args is not None:
        try:
            rhs = OVar("Set_univ")
            results.append((rhs, "Mathlib: Submonoid_coe_top"))
        except Exception:
            pass
    return results


def _r0379_coe_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.coe_bot
    # ((⊥ : Submonoid M) : Set M) = {1}
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bot_colon_Submonoid_M", 3)
    if args is not None:
        try:
            rhs = OVar("_1")
            results.append((rhs, "Mathlib: Submonoid_coe_bot"))
        except Exception:
            pass
    return results


def _r0380_eqLocusM_same(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.eqLocusM_same
    # f.eqLocusM f = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_eqLocusM", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: MonoidHom_eqLocusM_same"))
        except Exception:
            pass
    return results


def _r0381_eq_of_eqOn_topM(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: MonoidHom.eq_of_eqOn_topM
    # f = g
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("g")
            results.append((rhs, "Mathlib: MonoidHom_eq_of_eqOn_topM"))
    except Exception:
        pass
    return results


def _r0382_mk_mul_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.mk_mul_mk
    # (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, S.mul_mem hx hy⟩
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("x_star_y_S_mul_mem_hx_hy")
            results.append((rhs, "Mathlib: Submonoid_mk_mul_mk"))
        except Exception:
            pass
    return results


def _r0383_op_toSubsemigroup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.op_toSubsemigroup
    # H.op.toSubsemigroup = H.toSubsemigroup.op
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_op_toSubsemigroup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("H_toSubsemigroup_op")
            results.append((rhs, "Mathlib: Submonoid_op_toSubsemigroup"))
    except Exception:
        pass
    return results


def _r0384_unop_toSubsemigroup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.unop_toSubsemigroup
    # H.unop.toSubsemigroup = H.toSubsemigroup.unop
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("H_unop_toSubsemigroup")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("H_toSubsemigroup_unop")
            results.append((rhs, "Mathlib: Submonoid_unop_toSubsemigroup"))
    except Exception:
        pass
    return results


def _r0385_unop_op(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.unop_op
    # S.op.unop = S
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_op_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("S")
            results.append((rhs, "Mathlib: Submonoid_unop_op"))
    except Exception:
        pass
    return results


def _r0386_op_unop(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.op_unop
    # S.unop.op = S
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_unop_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("S")
            results.append((rhs, "Mathlib: Submonoid_op_unop"))
    except Exception:
        pass
    return results


def _r0387_unop_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.unop_inj
    # S.unop = T.unop ↔ S = T
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("T_unop"), OVar("S"))), OVar("T")))
            results.append((rhs, "Mathlib: Submonoid_unop_inj"))
    except Exception:
        pass
    return results


def _r0388_op_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.op_bot
    # (⊥ : Submonoid M).op = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Submonoid_M_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Submonoid_op_bot"))
    except Exception:
        pass
    return results


def _r0389_op_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.op_eq_bot
    # S.op = ⊥ ↔ S = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("bot"), OVar("S"))), OVar("bot")))
            results.append((rhs, "Mathlib: Submonoid_op_eq_bot"))
    except Exception:
        pass
    return results


def _r0390_unop_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.unop_bot
    # (⊥ : Submonoid Mᵐᵒᵖ).unop = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Submonoid_M_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Submonoid_unop_bot"))
    except Exception:
        pass
    return results


def _r0391_unop_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.unop_eq_bot
    # S.unop = ⊥ ↔ S = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("bot"), OVar("S"))), OVar("bot")))
            results.append((rhs, "Mathlib: Submonoid_unop_eq_bot"))
    except Exception:
        pass
    return results


def _r0392_op_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.op_top
    # (⊤ : Submonoid M).op = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_Submonoid_M_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Submonoid_op_top"))
    except Exception:
        pass
    return results


def _r0393_op_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.op_eq_top
    # S.op = ⊤ ↔ S = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("S"))), OVar("top")))
            results.append((rhs, "Mathlib: Submonoid_op_eq_top"))
    except Exception:
        pass
    return results


def _r0394_unop_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.unop_top
    # (⊤ : Submonoid Mᵐᵒᵖ).unop = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("top_colon_Submonoid_M_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("top")
            results.append((rhs, "Mathlib: Submonoid_unop_top"))
    except Exception:
        pass
    return results


def _r0395_unop_eq_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.unop_eq_top
    # S.unop = ⊤ ↔ S = ⊤
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_unop")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("top"), OVar("S"))), OVar("top")))
            results.append((rhs, "Mathlib: Submonoid_unop_eq_top"))
    except Exception:
        pass
    return results


def _r0396_op_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.op_sup
    # (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_1_S_2_op")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("S_1_op", (OVar("_unknown"), OVar("S_2_op"),))
            results.append((rhs, "Mathlib: Submonoid_op_sup"))
    except Exception:
        pass
    return results


def _r0397_comap_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.comap_comap
    # (S.comap g).comap f = S.comap (g.comp f)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_comap_g_comap", 1)
    if args is not None:
        try:
            rhs = OOp("S_comap", (OOp("g_comp", (args[0],)),))
            results.append((rhs, "Mathlib: Submonoid_comap_comap"))
        except Exception:
            pass
    return results


def _r0398_map_coe_toMulEquiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.map_coe_toMulEquiv
    # S.map (f : M ≃* N) = S.map f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_map", 1)
    if args is not None:
        try:
            rhs = OOp("S_map", (OVar("f"),))
            results.append((rhs, "Mathlib: Submonoid_map_coe_toMulEquiv"))
        except Exception:
            pass
    return results


def _r0399_comap_map_comap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Submonoid.comap_map_comap
    # ((S.comap f).map f).comap f = S.comap f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_comap_f_map_f_comap", 1)
    if args is not None:
        try:
            rhs = OOp("S_comap", (args[0],))
            results.append((rhs, "Mathlib: Submonoid_comap_map_comap"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_algebra_group rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("*", "**", "+", "-", "//", "==", "AddHom_mk", "AddMonoidHom_toMultiplicative", "AlgHomClass_toAlgHom", "AlgHom_id_R_B_comp", "Algebra_algebraMapSubmonoid", "D_d", "EuclideanDomain_gcd", "FreeAlgebra", "H", "H_1_subgroupOf", "H_subgroupOf", "H_subgroupOf_K_2_comap", "Hom_hom", "I", "I_inertia_G_subgroupOf", "IsQuasiregular", "K", "K_H_subgroupOf", "K_map", "K_map_f_map", "LinearMap_comp", "LinearMap_ker", "LinearMap_mk", "MonoidHom_id", "MonoidHom_id_N_comp", "MonoidHom_mk", "MulEquiv_subgroupCongr_h_symm", "MulHom_id", "MulHom_id_N_comp", "MulHom_mk", "MulSemiringAction_toRingEquiv", "N", "Quot_mk", "RingHom_id", "S", "S_comap_f_map_f_comap", "S_comap_g_comap", "S_copy", "S_h_colon_Subfield_K", "S_map", "S_map_f_map", "S_prod", "S_val", "Subalgebra_center",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_algebra_group axioms."""
    if recognizes(term):
        return 0.7
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_algebra_group rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_map_add_one(term, ctx))
    results.extend(_r0001_mk_coe(term, ctx))
    results.extend(_r0002_toFun_eq_coe(term, ctx))
    results.extend(_r0003_id_comp(term, ctx))
    results.extend(_r0004_coe_pow(term, ctx))
    results.extend(_r0005_pow_apply(term, ctx))
    results.extend(_r0006_coe_toEquiv(term, ctx))
    results.extend(_r0007_refl_trans(term, ctx))
    results.extend(_r0008_self_trans_symm(term, ctx))
    results.extend(_r0009_symm_trans_self(term, ctx))
    results.extend(_r0010_coe_symm_toEquiv(term, ctx))
    results.extend(_r0011_toEquiv_symm(term, ctx))
    results.extend(_r0012_toEquiv_trans(term, ctx))
    results.extend(_r0013_closure_irreducible(term, ctx))
    results.extend(_r0014_algebraMapSubmonoid_powers(term, ctx))
    results.extend(_r0015_ker_algebraMap_end(term, ctx))
    results.extend(_r0016_algebraMap_eq_one_iff(term, ctx))
    results.extend(_r0017_coe_eq_zero_iff(term, ctx))
    results.extend(_r0018_extendScalarsOfSurjective_apply(term, ctx))
    results.extend(_r0019_extendScalarsOfSurjective_symm(term, ctx))
    results.extend(_r0020_smul_algebraMap(term, ctx))
    results.extend(_r0021_coe_linearMap(term, ctx))
    results.extend(_r0022_algebraMap_self(term, ctx))
    results.extend(_r0023_algebraMap_self_apply(term, ctx))
    results.extend(_r0024_coe_coe(term, ctx))
    results.extend(_r0025_toRingEquiv_eq_coe(term, ctx))
    results.extend(_r0026_toAlgHom_apply(term, ctx))
    results.extend(_r0027_refl_toRingHom(term, ctx))
    results.extend(_r0028_coe_refl(term, ctx))
    results.extend(_r0029_symm_symm(term, ctx))
    results.extend(_r0030_toRingEquiv_symm(term, ctx))
    results.extend(_r0031_symm_toAddEquiv(term, ctx))
    results.extend(_r0032_symm_toMulEquiv(term, ctx))
    results.extend(_r0033_apply_symm_apply(term, ctx))
    results.extend(_r0034_symm_apply_apply(term, ctx))
    results.extend(_r0035_symm_apply_eq(term, ctx))
    results.extend(_r0036_trans_apply(term, ctx))
    results.extend(_r0037_symm_trans_apply(term, ctx))
    results.extend(_r0038_symm_trans_self(term, ctx))
    results.extend(_r0039_arrowCongr_trans(term, ctx))
    results.extend(_r0040_equivCongr_symm(term, ctx))
    results.extend(_r0041_toLinearEquiv_symm(term, ctx))
    results.extend(_r0042_coe_toLinearEquiv(term, ctx))
    results.extend(_r0043_coe_symm_toLinearEquiv(term, ctx))
    results.extend(_r0044_toLinearEquiv_trans(term, ctx))
    results.extend(_r0045_toLinearMap_ofAlgHom(term, ctx))
    results.extend(_r0046_toLinearMap_apply(term, ctx))
    results.extend(_r0047_linearEquivConj_mulRight(term, ctx))
    results.extend(_r0048_linearEquivConj_mulLeftRight(term, ctx))
    results.extend(_r0049_ofBijective_apply(term, ctx))
    results.extend(_r0050_toAlgHom_ofBijective(term, ctx))
    results.extend(_r0051_ofBijective_apply_symm_apply(term, ctx))
    results.extend(_r0052_mul_apply(term, ctx))
    results.extend(_r0053_aut_inv(term, ctx))
    results.extend(_r0054_coe_pow(term, ctx))
    results.extend(_r0055_autCongr_symm(term, ctx))
    results.extend(_r0056_autCongr_trans(term, ctx))
    results.extend(_r0057_toRingEquiv_algEquiv(term, ctx))
    results.extend(_r0058_algebraMap_eq_apply(term, ctx))
    results.extend(_r0059_addHomMk_coe(term, ctx))
    results.extend(_r0060_commutes(term, ctx))
    results.extend(_r0061_comp_apply(term, ctx))
    results.extend(_r0062_id_comp(term, ctx))
    results.extend(_r0063_comp_assoc(term, ctx))
    results.extend(_r0064_coe_toLinearMap(term, ctx))
    results.extend(_r0065_linearMapMk_toAddHom(term, ctx))
    results.extend(_r0066_mul_apply(term, ctx))
    results.extend(_r0067_coe_pow(term, ctx))
    results.extend(_r0068_algebraMap_eq_apply(term, ctx))
    results.extend(_r0069_toNatAlgHom_apply(term, ctx))
    results.extend(_r0070_toIntAlgHom_apply(term, ctx))
    results.extend(_r0071_toRingHom_ofId(term, ctx))
    results.extend(_r0072_ofId_apply(term, ctx))
    results.extend(_r0073_addHomMk_coe(term, ctx))
    results.extend(_r0074_toMulHom_eq_coe(term, ctx))
    results.extend(_r0075_map_add(term, ctx))
    results.extend(_r0076_comp_apply(term, ctx))
    results.extend(_r0077_snd_prod(term, ctx))
    results.extend(_r0078_prod_fst_snd(term, ctx))
    results.extend(_r0079_inl_apply(term, ctx))
    results.extend(_r0080_inr_apply(term, ctx))
    results.extend(_r0081_map_map(term, ctx))
    results.extend(_r0082_map_toSubmodule(term, ctx))
    results.extend(_r0083_coe_comap(term, ctx))
    results.extend(_r0084_adjoin_univ(term, ctx))
    results.extend(_r0085_top_toSubmodule(term, ctx))
    results.extend(_r0086_top_toNonUnitalSubsemiring(term, ctx))
    results.extend(_r0087_toNonUnitalSubring_top(term, ctx))
    results.extend(_r0088_toSubmodule_eq_top(term, ctx))
    results.extend(_r0089_inf_toSubmodule(term, ctx))
    results.extend(_r0090_sInf_toSubmodule(term, ctx))
    results.extend(_r0091_map_iInf(term, ctx))
    results.extend(_r0092_eq_top_iff(term, ctx))
    results.extend(_r0093_map_top(term, ctx))
    results.extend(_r0094_map_bot(term, ctx))
    results.extend(_r0095_prod_toSubmodule(term, ctx))
    results.extend(_r0096_prod_inf_prod(term, ctx))
    results.extend(_r0097_mem_centralizer_iff(term, ctx))
    results.extend(_r0098_bot_smul(term, ctx))
    results.extend(_r0099_smul_sup(term, ctx))
    results.extend(_r0100_bot_mul(term, ctx))
    results.extend(_r0101_algHom_comp(term, ctx))
    results.extend(_r0102_constAlgHom_eq_algebra_ofId(term, ctx))
    results.extend(_r0103_funUnique_symm_apply(term, ctx))
    results.extend(_r0104_snd_apply(term, ctx))
    results.extend(_r0105_snd_prod(term, ctx))
    results.extend(_r0106_prod_fst_snd(term, ctx))
    results.extend(_r0107_prod_comp(term, ctx))
    results.extend(_r0108_prodCongr_symm_apply(term, ctx))
    results.extend(_r0109_resolvent_eq(term, ctx))
    results.extend(_r0110_isQuasiregular_iff(term, ctx))
    results.extend(_r0111_coe_toSubmodule(term, ctx))
    results.extend(_r0112_coe_algebraMap(term, ctx))
    results.extend(_r0113_coe_pow(term, ctx))
    results.extend(_r0114_val_apply(term, ctx))
    results.extend(_r0115_toSubring_subtype(term, ctx))
    results.extend(_r0116_map_map(term, ctx))
    results.extend(_r0117_map_toSubmodule(term, ctx))
    results.extend(_r0118_mem_range(term, ctx))
    results.extend(_r0119_inclusion_mk(term, ctx))
    results.extend(_r0120_inclusion_right(term, ctx))
    results.extend(_r0121_equivOfEq_rfl(term, ctx))
    results.extend(_r0122_equivOfEq_trans(term, ctx))
    results.extend(_r0123_center_toSubring(term, ctx))
    results.extend(_r0124_mem_centralizer_iff(term, ctx))
    results.extend(_r0125_equalizer_toSubmodule(term, ctx))
    results.extend(_r0126_top_toSubmodule(term, ctx))
    results.extend(_r0127_top_toSubsemiring(term, ctx))
    results.extend(_r0128_top_toSubring(term, ctx))
    results.extend(_r0129_toSubmodule_eq_top(term, ctx))
    results.extend(_r0130_toSubsemiring_eq_top(term, ctx))
    results.extend(_r0131_toSubring_eq_top(term, ctx))
    results.extend(_r0132_inf_toSubmodule(term, ctx))
    results.extend(_r0133_inf_toSubsemiring(term, ctx))
    results.extend(_r0134_sInf_toSubmodule(term, ctx))
    results.extend(_r0135_map_iInf(term, ctx))
    results.extend(_r0136_toSubring_bot(term, ctx))
    results.extend(_r0137_range_id(term, ctx))
    results.extend(_r0138_map_top(term, ctx))
    results.extend(_r0139_map_bot(term, ctx))
    results.extend(_r0140_equalizer_same(term, ctx))
    results.extend(_r0141_adjoin_univ(term, ctx))
    results.extend(_r0142_adjoin_singleton_algebraMap(term, ctx))
    results.extend(_r0143_adjoin_singleton_natCast(term, ctx))
    results.extend(_r0144_adjoin_singleton_zero(term, ctx))
    results.extend(_r0145_adjoin_singleton_one(term, ctx))
    results.extend(_r0146_adjoin_eq_span(term, ctx))
    results.extend(_r0147_adjoin_image(term, ctx))
    results.extend(_r0148_adjoin_insert_intCast(term, ctx))
    results.extend(_r0149_adjoin_eq_ring_closure(term, ctx))
    results.extend(_r0150_unop_op(term, ctx))
    results.extend(_r0151_op_unop(term, ctx))
    results.extend(_r0152_unop_bot(term, ctx))
    results.extend(_r0153_op_top(term, ctx))
    results.extend(_r0154_unop_top(term, ctx))
    results.extend(_r0155_op_sup(term, ctx))
    results.extend(_r0156_unop_toSubring(term, ctx))
    results.extend(_r0157_pi_toSubmodule(term, ctx))
    results.extend(_r0158_pi_top(term, ctx))
    results.extend(_r0159_pointwise_smul_toSubsemiring(term, ctx))
    results.extend(_r0160_prod_top(term, ctx))
    results.extend(_r0161_restrictScalars_top(term, ctx))
    results.extend(_r0162_unitization_range(term, ctx))
    results.extend(_r0163_unitization_range(term, ctx))
    results.extend(_r0164_unitization_range(term, ctx))
    results.extend(_r0165_restrictScalars_extendScalarsOfSurjectiv(term, ctx))
    results.extend(_r0166_snd_inl(term, ctx))
    results.extend(_r0167_snd_inr(term, ctx))
    results.extend(_r0168_inl_inj(term, ctx))
    results.extend(_r0169_toProd_add(term, ctx))
    results.extend(_r0170_toProd_smul(term, ctx))
    results.extend(_r0171_fst_add(term, ctx))
    results.extend(_r0172_snd_add(term, ctx))
    results.extend(_r0173_fst_neg(term, ctx))
    results.extend(_r0174_snd_neg(term, ctx))
    results.extend(_r0175_fst_smul(term, ctx))
    results.extend(_r0176_snd_smul(term, ctx))
    results.extend(_r0177_inl_add(term, ctx))
    results.extend(_r0178_inl_sub(term, ctx))
    results.extend(_r0179_inr_add(term, ctx))
    results.extend(_r0180_inr_neg(term, ctx))
    results.extend(_r0181_inr_sub(term, ctx))
    results.extend(_r0182_inr_smul(term, ctx))
    results.extend(_r0183_fst_mul(term, ctx))
    results.extend(_r0184_inl_mul(term, ctx))
    results.extend(_r0185_snd_star(term, ctx))
    results.extend(_r0186_inl_star(term, ctx))
    results.extend(_r0187_starMap_inr(term, ctx))
    results.extend(_r0188_unop_finsuppProd(term, ctx))
    results.extend(_r0189_finset_prod_apply(term, ctx))
    results.extend(_r0190_mul_prod_eraseIdx(term, ctx))
    results.extend(_r0191_kernelIsoKer_inv_comp_i(term, ctx))
    results.extend(_r0192_id_apply(term, ctx))
    results.extend(_r0193_ofHom_hom(term, ctx))
    results.extend(_r0194_ofHom_id(term, ctx))
    results.extend(_r0195_ofHom_comp(term, ctx))
    results.extend(_r0196_hom_2_ofHom_2(term, ctx))
    results.extend(_r0197_ofHom_2_hom_2(term, ctx))
    results.extend(_r0198_id_moduleCat_comp(term, ctx))
    results.extend(_r0199_d_mul(term, ctx))
    results.extend(_r0200_d_map(term, ctx))
    results.extend(_r0201_id_apply(term, ctx))
    results.extend(_r0202_ofHom_hom(term, ctx))
    results.extend(_r0203_ofHom_id(term, ctx))
    results.extend(_r0204_ofHom_comp(term, ctx))
    results.extend(_r0205_forgetToRingCat_obj(term, ctx))
    results.extend(_r0206_quot_neg(term, ctx))
    results.extend(_r0207_mem_center_iff(term, ctx))
    results.extend(_r0208_hom_ext(term, ctx))
    results.extend(_r0209_hom_ext(term, ctx))
    results.extend(_r0210_hom_ext(term, ctx))
    results.extend(_r0211_exists_of(term, ctx))
    results.extend(_r0212_hom_ext(term, ctx))
    results.extend(_r0213_gcd_eq(term, ctx))
    results.extend(_r0214_unop_nnratCast(term, ctx))
    results.extend(_r0215_op_ratCast(term, ctx))
    results.extend(_r0216_unop_ratCast(term, ctx))
    results.extend(_r0217_mem_fieldRange(term, ctx))
    results.extend(_r0218_fieldRange_eq_map(term, ctx))
    results.extend(_r0219_coe_iInf(term, ctx))
    results.extend(_r0220_sInf_toSubring(term, ctx))
    results.extend(_r0221_closure_empty(term, ctx))
    results.extend(_r0222_closure_univ(term, ctx))
    results.extend(_r0223_closure_union(term, ctx))
    results.extend(_r0224_comap_top(term, ctx))
    results.extend(_r0225_rangeRestrictFieldEquiv_apply_symm_apply(term, ctx))
    results.extend(_r0226_coe_ratCast(term, ctx))
    results.extend(_r0227_coe_qsmul(term, ctx))
    results.extend(_r0228_coe_set_mk(term, ctx))
    results.extend(_r0229_copy_eq(term, ctx))
    results.extend(_r0230_coe_sub(term, ctx))
    results.extend(_r0231_coe_neg(term, ctx))
    results.extend(_r0232_coe_mul(term, ctx))
    results.extend(_r0233_coe_div(term, ctx))
    results.extend(_r0234_coe_inv(term, ctx))
    results.extend(_r0235_algebraMap_eq_one_iff(term, ctx))
    results.extend(_r0236_coe_toPermHom(term, ctx))
    results.extend(_r0237_map_add_eq_mul(term, ctx))
    results.extend(_r0238_coe_toMonoidHomEquiv_symm(term, ctx))
    results.extend(_r0239_toMonoidHomEquiv_apply(term, ctx))
    results.extend(_r0240_toMonoidHomEquiv_symm_apply(term, ctx))
    results.extend(_r0241_toAddMonoidHom_apply(term, ctx))
    results.extend(_r0242_coe_toAddMonoidHomEquiv_symm(term, ctx))
    results.extend(_r0243_toAddMonoidHomEquiv_apply(term, ctx))
    results.extend(_r0244_toAddMonoidHomEquiv_symm_apply(term, ctx))
    results.extend(_r0245_compAddMonoidHom_apply(term, ctx))
    results.extend(_r0246_coe_inv(term, ctx))
    results.extend(_r0247_mul_def(term, ctx))
    results.extend(_r0248_symm_inv(term, ctx))
    results.extend(_r0249_inv_apply(term, ctx))
    results.extend(_r0250_mul_apply(term, ctx))
    results.extend(_r0251_apply_inv_self(term, ctx))
    results.extend(_r0252_conj_symm_apply(term, ctx))
    results.extend(_r0253_conj_inv_apply(term, ctx))
    results.extend(_r0254_coe_inv(term, ctx))
    results.extend(_r0255_mul_def(term, ctx))
    results.extend(_r0256_inv_symm(term, ctx))
    results.extend(_r0257_symm_inv(term, ctx))
    results.extend(_r0258_inv_apply(term, ctx))
    results.extend(_r0259_inv_apply_self(term, ctx))
    results.extend(_r0260_conj_symm_apply(term, ctx))
    results.extend(_r0261_conj_inv_apply(term, ctx))
    results.extend(_r0262_mk_coe(term, ctx))
    results.extend(_r0263_toEquiv_eq_coe(term, ctx))
    results.extend(_r0264_toFun_eq_coe(term, ctx))
    results.extend(_r0265_coe_symm_opMulEquiv(term, ctx))
    results.extend(_r0266_smul_cons(term, ctx))
    results.extend(_r0267_mgraph_eq_mrange_prod(term, ctx))
    results.extend(_r0268_mul_comp(term, ctx))
    results.extend(_r0269_toFun_eq_coe(term, ctx))
    results.extend(_r0270_toMulHom_coe(term, ctx))
    results.extend(_r0271_toFun_eq_coe(term, ctx))
    results.extend(_r0272_mk_coe(term, ctx))
    results.extend(_r0273_mk_coe(term, ctx))
    results.extend(_r0274_coe_comp(term, ctx))
    results.extend(_r0275_coe_comp(term, ctx))
    results.extend(_r0276_comp_id(term, ctx))
    results.extend(_r0277_comp_id(term, ctx))
    results.extend(_r0278_id_comp(term, ctx))
    results.extend(_r0279_id_comp(term, ctx))
    results.extend(_r0280_map_pow(term, ctx))
    results.extend(_r0281_ofNat_apply(term, ctx))
    results.extend(_r0282_apply_nat(term, ctx))
    results.extend(_r0283_apply_mnat(term, ctx))
    results.extend(_r0284_coe_snd(term, ctx))
    results.extend(_r0285_fst_comp_prod(term, ctx))
    results.extend(_r0286_snd_comp_prod(term, ctx))
    results.extend(_r0287_prod_unique(term, ctx))
    results.extend(_r0288_coe_snd(term, ctx))
    results.extend(_r0289_inl_apply(term, ctx))
    results.extend(_r0290_inr_apply(term, ctx))
    results.extend(_r0291_fst_comp_inl(term, ctx))
    results.extend(_r0292_snd_comp_inl(term, ctx))
    results.extend(_r0293_fst_comp_inr(term, ctx))
    results.extend(_r0294_snd_comp_inr(term, ctx))
    results.extend(_r0295_fst_comp_prod(term, ctx))
    results.extend(_r0296_snd_comp_prod(term, ctx))
    results.extend(_r0297_prod_unique(term, ctx))
    results.extend(_r0298_coe_prodComm_symm(term, ctx))
    results.extend(_r0299_coe_prodAssoc_symm(term, ctx))
    results.extend(_r0300_bot_prod_bot(term, ctx))
    results.extend(_r0301_normalClosure_idempotent(term, ctx))
    results.extend(_r0302_normalCore_idempotent(term, ctx))
    results.extend(_r0303_ker_snd(term, ctx))
    results.extend(_r0304_subgroupOf_inertia(term, ctx))
    results.extend(_r0305_coe_inv(term, ctx))
    results.extend(_r0306_coe_div(term, ctx))
    results.extend(_r0307_coe_mk(term, ctx))
    results.extend(_r0308_coe_square(term, ctx))
    results.extend(_r0309_coe_square(term, ctx))
    results.extend(_r0310_coe_square(term, ctx))
    results.extend(_r0311_val_multiset_prod(term, ctx))
    results.extend(_r0312_eq_bot_of_card_le(term, ctx))
    results.extend(_r0313_mem_range(term, ctx))
    results.extend(_r0314_range_eq_map(term, ctx))
    results.extend(_r0315_map_range(term, ctx))
    results.extend(_r0316_range_eq_top_of_surjective(term, ctx))
    results.extend(_r0317_range_subtype(term, ctx))
    results.extend(_r0318_coe_toMultiplicative_range(term, ctx))
    results.extend(_r0319_mem_ker(term, ctx))
    results.extend(_r0320_div_mem_ker_iff(term, ctx))
    results.extend(_r0321_ker_restrict(term, ctx))
    results.extend(_r0322_ker_codRestrict(term, ctx))
    results.extend(_r0323_ker_id(term, ctx))
    results.extend(_r0324_ker_eq_top_iff(term, ctx))
    results.extend(_r0325_ker_inclusion(term, ctx))
    results.extend(_r0326_ker_prod(term, ctx))
    results.extend(_r0327_coe_toMultiplicative_ker(term, ctx))
    results.extend(_r0328_coe_top(term, ctx))
    results.extend(_r0329_coe_bot(term, ctx))
    results.extend(_r0330_bot_toSubmonoid(term, ctx))
    results.extend(_r0331_eq_bot_iff_forall(term, ctx))
    results.extend(_r0332_coe_eq_singleton(term, ctx))
    results.extend(_r0333_coe_iInf(term, ctx))
    results.extend(_r0334_closure_empty(term, ctx))
    results.extend(_r0335_closure_univ(term, ctx))
    results.extend(_r0336_closure_union(term, ctx))
    results.extend(_r0337_iSup_eq_closure(term, ctx))
    results.extend(_r0338_toAddSubgroup_closure(term, ctx))
    results.extend(_r0339_toSubgroup_comap(term, ctx))
    results.extend(_r0340_map_toSubmonoid(term, ctx))
    results.extend(_r0341_mem_map(term, ctx))
    results.extend(_r0342_map_map(term, ctx))
    results.extend(_r0343_comap_inclusion_subgroupOf(term, ctx))
    results.extend(_r0344_top_subgroupOf(term, ctx))
    results.extend(_r0345_subgroupOf_bot_eq_bot(term, ctx))
    results.extend(_r0346_subgroupOf_inj(term, ctx))
    results.extend(_r0347_inf_subgroupOf_left(term, ctx))
    results.extend(_r0348_subgroupOf_eq_bot(term, ctx))
    results.extend(_r0349_subgroupOf_eq_top(term, ctx))
    results.extend(_r0350_symm_comapSubgroup(term, ctx))
    results.extend(_r0351_symm_mapSubgroup(term, ctx))
    results.extend(_r0352_subgroupCongr_symm_apply(term, ctx))
    results.extend(_r0353_op_toSubmonoid(term, ctx))
    results.extend(_r0354_op_toSubsemigroup(term, ctx))
    results.extend(_r0355_unop_toSubmonoid(term, ctx))
    results.extend(_r0356_unop_toSubsemigroup(term, ctx))
    results.extend(_r0357_op_unop(term, ctx))
    results.extend(_r0358_unop_inj(term, ctx))
    results.extend(_r0359_op_normalizer(term, ctx))
    results.extend(_r0360_op_eq_bot(term, ctx))
    results.extend(_r0361_unop_bot(term, ctx))
    results.extend(_r0362_unop_eq_bot(term, ctx))
    results.extend(_r0363_op_top(term, ctx))
    results.extend(_r0364_op_eq_top(term, ctx))
    results.extend(_r0365_unop_top(term, ctx))
    results.extend(_r0366_unop_eq_top(term, ctx))
    results.extend(_r0367_op_sup(term, ctx))
    results.extend(_r0368_closure_singleton_inv(term, ctx))
    results.extend(_r0369_pointwise_smul_toSubmonoid(term, ctx))
    results.extend(_r0370_smul_sup(term, ctx))
    results.extend(_r0371_zpowers_inv(term, ctx))
    results.extend(_r0372_coe_iInf(term, ctx))
    results.extend(_r0373_closure_empty(term, ctx))
    results.extend(_r0374_closure_univ(term, ctx))
    results.extend(_r0375_closure_union(term, ctx))
    results.extend(_r0376_coe_multiset_prod(term, ctx))
    results.extend(_r0377_copy_eq(term, ctx))
    results.extend(_r0378_coe_top(term, ctx))
    results.extend(_r0379_coe_bot(term, ctx))
    results.extend(_r0380_eqLocusM_same(term, ctx))
    results.extend(_r0381_eq_of_eqOn_topM(term, ctx))
    results.extend(_r0382_mk_mul_mk(term, ctx))
    results.extend(_r0383_op_toSubsemigroup(term, ctx))
    results.extend(_r0384_unop_toSubsemigroup(term, ctx))
    results.extend(_r0385_unop_op(term, ctx))
    results.extend(_r0386_op_unop(term, ctx))
    results.extend(_r0387_unop_inj(term, ctx))
    results.extend(_r0388_op_bot(term, ctx))
    results.extend(_r0389_op_eq_bot(term, ctx))
    results.extend(_r0390_unop_bot(term, ctx))
    results.extend(_r0391_unop_eq_bot(term, ctx))
    results.extend(_r0392_op_top(term, ctx))
    results.extend(_r0393_op_eq_top(term, ctx))
    results.extend(_r0394_unop_top(term, ctx))
    results.extend(_r0395_unop_eq_top(term, ctx))
    results.extend(_r0396_op_sup(term, ctx))
    results.extend(_r0397_comap_comap(term, ctx))
    results.extend(_r0398_map_coe_toMulEquiv(term, ctx))
    results.extend(_r0399_comap_map_comap(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_algebra_group rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("AddConstMapClass_semiconj", "Semiconj_f_plus_a_plus_b", "Not an equality or iff proposition"),
    ("AddConstMapClass_map_add_nat", "_unknown", "Empty proposition"),
    ("AddConstMapClass_map_add_ofNat", "_unknown", "Empty proposition"),
    ("AddConstMapClass_map_nat", "_unknown", "Empty proposition"),
    ("AddConstMapClass_map_ofNat", "_unknown", "Empty proposition"),
    ("AddConstMapClass_map_nat_add", "_unknown", "Empty proposition"),
    ("AddConstMapClass_map_ofNat_add", "_unknown", "Empty proposition"),
    ("AddConstMapClass_map_sub_nat", "_unknown", "Empty proposition"),
    ("AddConstMapClass_map_sub_ofNat", "_unknown", "Empty proposition"),
    ("AddConstMapClass_map_add_int", "_unknown", "Empty proposition"),
    ("AddConstMapClass_map_sub_int", "_unknown", "Empty proposition"),
    ("AddConstMapClass_map_int_add", "_unknown", "Empty proposition"),
    ("AddConstMapClass_rel_map_of_Icc", "lt_R_f_f", "Not an equality or iff proposition"),
    ("AddConstMap_coe_mk", "mk_f_hf_colon_G_to_plus_c_a_b_H_eq_f", "Not an equality or iff proposition"),
    ("AddConstMap_one_def", "_1_colon_G_to_plus_c_a_a_G_eq_id", "Not an equality or iff proposition"),
    ("AddConstMap_coe_one", "_1_colon_G_to_plus_c_a_a_G_eq_id", "Not an equality or iff proposition"),
    ("AddConstEquiv_toEquiv_injective", "Injective_toEquiv_colon_G_plus_c_a_b_H_to_G_H_pipe_rfl_eq_gt_rfl_in", "Not an equality or iff proposition"),
    ("Submonoid_FG_finite_irreducible_mem_submonoidClosure", "p_in_S_pipe_Irreducible_p_Finite", "Not an equality or iff proposition"),
    ("algebraMap_ofSubsemiring", "algebraMap_S_R_colon_S_to_plus_star_R_eq_S_subtype", "Not an equality or iff proposition"),
    ("coe_algebraMap_ofSubsemiring", "algebraMap_S_R_colon_S_to_R_eq_Subtype_val", "Not an equality or iff proposition"),
    ("algebraMap_ofSubring", "algebraMap_S_R_colon_S_to_plus_star_R_eq_S_subtype", "Not an equality or iff proposition"),
    ("coe_algebraMap_ofSubring", "algebraMap_S_R_colon_S_to_R_eq_Subtype_val", "Not an equality or iff proposition"),
    ("mem_algebraMapSubmonoid_of_mem", "algebraMap_R_S_x_in_algebraMapSubmonoid_S_M", "Not an equality or iff proposition"),
    ("Module_End_algebraMap_isUnit_inv_apply_eq_iff", "_unknown", "Empty proposition"),
    ("FaithfulSMul_algebraMap_injective", "Injective_algebraMap_R_A", "Not an equality or iff proposition"),
    ("IsDomain_of_faithfulSMul", "IsDomain_R", "Not an equality or iff proposition"),
    ("Module_IsTorsionFree_of_faithfulSMul", "IsTorsionFree_S_R", "Not an equality or iff proposition"),
    ("Module_IsTorsionFree_trans_faithfulSMul", "IsTorsionFree_R_M", "Not an equality or iff proposition"),
    ("IsUnit_algebraMap_of_algebraMap", "IsUnit_algebraMap_R_B_r", "Not an equality or iff proposition"),
    ("injective_algebraMap_of_linearMap", "Injective_algebraMap_F_E", "Not an equality or iff proposition"),
    ("surjective_algebraMap_of_linearMap", "Surjective_algebraMap_F_E", "Not an equality or iff proposition"),
    ("bijective_algebraMap_of_linearMap", "Bijective_algebraMap_F_E", "Not an equality or iff proposition"),
    ("bijective_algebraMap_of_linearEquiv", "Bijective_algebraMap_F_E", "Not an equality or iff proposition"),
    ("LinearMap_mul_apply", "_unknown", "Empty proposition"),
    ("LinearMap_mul", "_unknown", "Empty proposition"),
    ("Algebra_lmul_injective", "Function_Injective_Algebra_lmul_R_A", "Not an equality or iff proposition"),
    ("mul", "_unknown", "Empty proposition"),
    ("mul", "_unknown", "Empty proposition"),
    ("NonUnitalAlgHom_comp_mul", "_unknown", "Empty proposition"),
    ("AlgHom_comp_mul", "_unknown", "Empty proposition"),
    ("Algebra_subsingleton", "Subsingleton_A", "Not an equality or iff proposition"),
    ("RingHom_smul_toAlgebra", "_unknown", "Empty proposition"),
    ("RingHom_algebraMap_toAlgebra", "_unknown", "Empty proposition"),
    ("RingHom_smul_toAlgebra", "let", "Not an equality or iff proposition"),
    ("Algebra_algebraMap_eq_smul_one", "_unknown", "Empty proposition"),
    ("Algebra_compHom_smul_def", "letI", "Not an equality or iff proposition"),
    ("Algebra_compHom_algebraMap_eq", "letI", "Not an equality or iff proposition"),
    ("Algebra_compHom_algebraMap_apply", "letI", "Not an equality or iff proposition"),
    ("algebraMap_coe_smul", "_unknown", "Empty proposition"),
    ("algebraMap_smul", "_unknown", "Empty proposition"),
    ("Algebra_isEpi_of_surjective_algebraMap", "Algebra_IsEpi_R_A", "Not an equality or iff proposition"),
    ("injective_lift_lsmul", "Injective_lift_lt_pipe_LinearMap_restrictScalars_1_2_R_R_LinearMap_lsmul_A_M", "Not an equality or iff proposition"),
    ("TensorProduct_lid", "_unknown", "Empty proposition"),
    ("TensorProduct_lid", "_unknown", "Empty proposition"),
    ("AlgEquiv_coe_fun_injective", "at_Function_Injective_A_1_R_A_2_A_1_to_A_2_fun_e_eq_gt_e_colon_A_1_to_A_2", "Not an equality or iff proposition"),
    ("AlgEquiv_coe_toEquiv", "e_colon_A_1_A_2_colon_A_1_to_A_2_eq_e", "Not an equality or iff proposition"),
    ("AlgEquiv_toRingEquiv_toRingHom", "e_colon_A_1_plus_star_A_2_colon_A_1_to_plus_star_A_2_eq_e", "Not an equality or iff proposition"),
    ("AlgEquiv_coe_ringEquiv", "e_colon_A_1_plus_star_A_2_colon_A_1_to_A_2_eq_e", "Not an equality or iff proposition"),
    ("AlgEquiv_coe_ringEquiv", "_unknown", "Empty proposition"),
    ("AlgEquiv_coe_ringEquiv_injective", "Function_Injective_colon_A_1_R_A_2_to_A_1_plus_star_A_2", "Not an equality or iff proposition"),
    ("AlgEquiv_coe_algHom_injective", "Function_Injective_colon_A_1_R_A_2_to_A_1_to_R_A_2", "Not an equality or iff proposition"),
    ("AlgEquiv_toAlgHom_toRingHom", "e_colon_A_1_to_R_A_2_colon_A_1_to_plus_star_A_2_eq_e", "Not an equality or iff proposition"),
    ("bijective", "Function_Bijective_e", "Not an equality or iff proposition"),
    ("injective", "Function_Injective_e", "Not an equality or iff proposition"),
    ("surjective", "Function_Surjective_e", "Not an equality or iff proposition"),
    ("symm_bijective", "Function_Bijective_symm_colon_A_1_R_A_2_to_A_2_R_A_1", "Not an equality or iff proposition"),
    ("mk_coe", "_unknown", "Empty proposition"),
    ("comp_symm", "AlgHom_comp_e_colon_A_1_to_R_A_2_e_symm_eq_AlgHom_id_R_A_2", "Not an equality or iff proposition"),
    ("symm_comp", "AlgHom_comp_e_symm_e_colon_A_1_to_R_A_2_eq_AlgHom_id_R_A_1", "Not an equality or iff proposition"),
    ("leftInverse_symm", "Function_LeftInverse_e_symm_e", "Not an equality or iff proposition"),
    ("rightInverse_symm", "Function_RightInverse_e_symm_e", "Not an equality or iff proposition"),
    ("toRingHom_trans", "e_1_trans_e_2_colon_A_1_to_plus_star_A_3_eq_comp_e_2_e_1_colon_A_1_to_plus_star_A_2", "Not an equality or iff proposition"),
    ("toLinearEquiv_injective", "Function_Injective_toLinearEquiv_colon_to_A_1_R_A_2", "Not an equality or iff proposition"),
    ("toAlgHom_toLinearMap", "e_colon_A_1_to_R_A_2_toLinearMap_eq_e_toLinearMap", "Not an equality or iff proposition"),
    ("toLinearMap_injective", "Function_Injective_toLinearMap_colon_to_A_1_to_R_A_2", "Not an equality or iff proposition"),
    ("coe_ofBijective", "ofBijective_f_hf_colon_A_1_to_A_2_eq_f", "Not an equality or iff proposition"),
    ("MulSemiringAction_toAlgEquiv_injective", "Function_Injective_MulSemiringAction_toAlgEquiv_R_A_colon_G_to_A_R_A", "Not an equality or iff proposition"),
    ("AlgHomClass_toLinearMap_toAlgHom", "AlgHomClass_toAlgHom_f_colon_A_to_R_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_coe_coe", "f_colon_A_to_R_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_coe_mk", "f_h_colon_A_to_R_B_colon_A_to_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_coe_mks", "f_h_1_h_2_h_3_h_4_h_5_colon_A_to_R_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_coe_ringHom_mk", "f_h_colon_A_to_R_B_colon_A_to_plus_star_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_coe_toRingHom", "f_colon_A_to_plus_star_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_coe_toMonoidHom", "f_colon_A_to_star_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_coe_toAddMonoidHom", "f_colon_A_to_plus_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_toRingHom_toMonoidHom", "f_colon_A_to_plus_star_B_colon_A_to_star_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_toRingHom_toAddMonoidHom", "f_colon_A_to_plus_star_B_colon_A_to_plus_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_coe_fn_injective", "at_Function_Injective_A_to_R_B_A_to_B", "Not an equality or iff proposition"),
    ("AlgHom_coe_ringHom_injective", "Function_Injective_colon_A_to_R_B_to_A_to_plus_star_B", "Not an equality or iff proposition"),
    ("AlgHom_coe_monoidHom_injective", "Function_Injective_colon_A_to_R_B_to_A_to_star_B", "Not an equality or iff proposition"),
    ("AlgHom_coe_addMonoidHom_injective", "Function_Injective_colon_A_to_R_B_to_A_to_plus_B", "Not an equality or iff proposition"),
    ("AlgHom_mk_coe", "f_h_1_h_2_h_3_h_4_h_5_colon_A_to_R_B_eq_f", "Not an equality or iff proposition"),
    ("AlgHom_comp_algebraMap", "phi_colon_A_to_plus_star_B_comp_algebraMap_R_A_eq_algebraMap_R_B", "Not an equality or iff proposition"),
    ("AlgHom_coe_mk", "_unknown", "Empty proposition"),
    ("AlgHom_id_toRingHom", "AlgHom_id_R_A_colon_A_to_plus_star_A_eq_RingHom_id", "Not an equality or iff proposition"),
    ("comp_toRingHom", "phi_1_comp_phi_2_colon_A_to_plus_star_C_eq_phi_1_colon_B_to_plus_star_C_comp_phi_2", "Not an equality or iff proposition"),
    ("toLinearMap_injective", "Function_Injective_toLinearMap_colon_to_A_to_R_B", "Not an equality or iff proposition"),
    ("RingHom_toIntAlgHom_injective", "Function_Injective_RingHom_toIntAlgHom_colon_R_to_plus_star_S_to", "Not an equality or iff proposition"),
    ("algebraMapSubmonoid_le_comap", "algebraMapSubmonoid_A_M_le_algebraMapSubmonoid_B_M_comap_f_toRingHom", "Not an equality or iff proposition"),
    ("MulSemiringAction_toAlgHom_injective", "Function_Injective_MulSemiringAction_toAlgHom_R_A_colon_M_to_A_to_R_A", "Not an equality or iff proposition"),
    ("AlgHom_default_apply", "default_colon_S_to_R_T_x_eq_0", "Not an equality or iff proposition"),
    ("AlgHom_toRingHom_toRatAlgHom", "f_colon_R_to_plus_star_S_toRatAlgHom_eq_f", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_coe", "f_colon_A_to_phi_B_eq_f", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_injective", "at_Function_Injective_A_to_phi_B_A_to_B", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_mk", "f_h_1_h_2_h_3_h_4_colon_A_to_phi_B_eq_f", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_mk_coe", "f_h_1_h_2_h_3_h_4_colon_A_to_phi_B_eq_f", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_to_mulHom", "f_colon_A_to_star_B_eq_f", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_mulHom_mk", "f_h_1_h_2_h_3_h_4_colon_A_to_phi_B_colon_A_to_star_B_eq_f_h_4", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_inverse", "inverse_f_g_h_1_h_2_colon_B_1_to_A_eq_g", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_inverse", "_unknown", "Empty proposition"),
    ("NonUnitalAlgHom_coe_inl", "inl_R_A_B_colon_A_to_A_times_B_eq_fun_x_eq_gt_x_0", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_inr", "inr_R_A_B_colon_B_to_A_times_B_eq_Prod_mk_0", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_restrictScalars", "f_restrictScalars_R_colon_A_to_plus_star_B_eq_f", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_coe_restrictScalars", "_unknown", "Empty proposition"),
    ("NonUnitalAlgHom_restrictScalars_injective", "Function_Injective_restrictScalars_R_colon_A_to_S_B_to_A_to_R_B", "Not an equality or iff proposition"),
    ("NonUnitalSubalgebraClass_subtype_injective", "Function_Injective_subtype_s", "Not an equality or iff proposition"),
    ("NonUnitalSubalgebraClass_coe_subtype", "subtype_s_colon_s_to_A_eq_colon_s_to_A", "Not an equality or iff proposition"),
    ("NonUnitalSubalgebra_toNonUnitalSubsemiring_injective", "toNonUnitalSubsemiring_colon_NonUnitalSubalgebra_R_A_to_NonUnitalSubsemiring_A_Inje", "Not an equality or iff proposition"),
    ("NonUnitalSubalgebra_toSubmodule_injective", "toSubmodule_colon_NonUnitalSubalgebra_R_A_to_Submodule_R_A_Injective", "Not an equality or iff proposition"),
    ("toNonUnitalSubring_injective", "Function_Injective_toNonUnitalSubring_colon_NonUnitalSubalgebra_R_A_to_NonUnitalSubr", "Not an equality or iff proposition"),
    ("map_mono", "S_1_le_S_2_to_map_f_S_1_colon_NonUnitalSubalgebra_R_B_le_map_f_S_2", "Not an equality or iff proposition"),
    ("map_injective", "Function_Injective_map_f_colon_NonUnitalSubalgebra_R_A_to_NonUnitalSubalgebra_R_B", "Not an equality or iff proposition"),
    ("gc_map_comap", "GaloisConnection_map_f_colon_NonUnitalSubalgebra_R_A_to_NonUnitalSubalgebra_R_B_co", "Not an equality or iff proposition"),
    ("Submodule_toNonUnitalSubalgebra_mk", "_unknown", "Empty proposition"),
    ("NonUnitalAlgHom_mem_range_self", "phi_x_in_NonUnitalAlgHom_range_phi_colon_NonUnitalSubalgebra_R_B", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_range_comp_le_range", "NonUnitalAlgHom_range_g_comp_f_le_NonUnitalAlgHom_range_g", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_subset_adjoin", "s_sub_adjoin_R_s", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_mem_adjoin_of_mem", "x_in_adjoin_R_s", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_self_mem_adjoin_singleton", "x_in_adjoin_R_x_colon_Set_A", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_gc", "GaloisConnection_adjoin_R_colon_Set_A_to_NonUnitalSubalgebra_R_A", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_adjoin_le", "adjoin_R_s_le_S", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_adjoin_mono", "adjoin_R_s_le_adjoin_R_t", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_adjoin_induction", "p_x_hx", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_adjoin_induction_2", "p_x_y_hx_hy", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_mem_top", "x_in_top_colon_NonUnitalSubalgebra_R_A", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_mem_sup_left", "forall_x_colon_A_x_in_S_to_x_in_S_T", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_mem_sup_right", "forall_x_colon_A_x_in_T_to_x_in_S_T", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_mul_mem_sup", "x_star_y_in_S_T", "Not an equality or iff proposition"),
    ("NonUnitalSubalgebra_prod_mono", "S_le_T_to_S_1_le_T_1_to_prod_S_S_1_le_prod_T_T_1", "Not an equality or iff proposition"),
    ("inclusion_injective", "Function_Injective_inclusion_h", "Not an equality or iff proposition"),
    ("centralizer_le", "centralizer_R_t_le_centralizer_R_s", "Not an equality or iff proposition"),
    ("NonUnitalAlgebra_adjoin_le_centralizer_centralizer", "adjoin_R_s_le_centralizer_R_centralizer_R_s", "Not an equality or iff proposition"),
    ("SubMulAction_algebraMap_mem", "algebraMap_R_A_r_in_1_colon_SubMulAction_R_A", "Not an equality or iff proposition"),
    ("Submodule_smul_mem_smul", "r_n_in_I_N", "Not an equality or iff proposition"),
    ("Submodule_smul_induction_on", "p_x", "Not an equality or iff proposition"),
    ("Submodule_smul_induction_on", "_unknown", "Empty proposition"),
    ("Submodule_smul_mono", "I_N_le_J_P", "Not an equality or iff proposition"),
    ("Submodule_smul_mono_left", "I_N_le_J_N", "Not an equality or iff proposition"),
    ("Submodule_smul_subset_smul", "I_colon_Set_A_N_colon_Set_M_sub_I_N_colon_Set_M", "Not an equality or iff proposition"),
    ("mul_mem_mul", "m_star_n_in_M_star_N", "Not an equality or iff proposition"),
    ("mul_induction_on", "C_r", "Not an equality or iff proposition"),
    ("mul_induction_on", "_unknown", "Empty proposition"),
    ("mul_subset_mul", "M_colon_Set_A_star_N_colon_Set_A_sub_M_star_N_colon_Set_A", "Not an equality or iff proposition"),
    ("pow_succ", "_unknown", "Empty proposition"),
    ("le_pow_toAddSubmonoid", "M_toAddSubmonoid_pow_n_le_M_pow_n_toAddSubmonoid", "Not an equality or iff proposition"),
    ("pow_subset_pow", "M_colon_Set_A_pow_n_sub_M_pow_n_colon_Submodule_R_A", "Not an equality or iff proposition"),
    ("pow_mem_pow", "x_pow_n_in_M_pow_n", "Not an equality or iff proposition"),
    ("algebraMap_mem", "algebraMap_R_A_r_in_1_colon_Submodule_R_A", "Not an equality or iff proposition"),
    ("map_op_one", "map_opLinearEquiv_R_colon_A_R_A_colon_A_to_R_A_1_colon_Submodule_R_A_eq_1", "Not an equality or iff proposition"),
    ("comap_op_one", "comap_opLinearEquiv_R_colon_A_R_A_colon_A_to_R_A_1_colon_Submodule_R_A", "Not an equality or iff proposition"),
    ("map_unop_one", "map_opLinearEquiv_R_colon_A_R_A_symm_colon_A_to_R_A_1_colon_Submodule_R_A", "Not an equality or iff proposition"),
    ("comap_unop_one", "comap_opLinearEquiv_R_colon_A_R_A_symm_colon_A_to_R_A_1_colon_Submodule_R_A", "Not an equality or iff proposition"),
    ("map_op_mul", "map_opLinearEquiv_R_colon_A_R_A_colon_A_to_R_A_M_star_N_eq_map_op", "Not an equality or iff proposition"),
    ("comap_unop_mul", "comap_opLinearEquiv_R_colon_A_R_A_symm_colon_A_to_R_A_M_star_N_eq_co", "Not an equality or iff proposition"),
    ("map_unop_mul", "map_opLinearEquiv_R_colon_A_R_A_symm_colon_A_to_R_A_M_star_N_eq_map", "Not an equality or iff proposition"),
    ("comap_op_mul", "comap_opLinearEquiv_R_colon_A_R_A_colon_A_to_R_A_M_star_N_eq_comap", "Not an equality or iff proposition"),
    ("mem_span_mul_finite_of_mem_span_mul", "exists_T_T_prime_colon_Finset_A_T_sub_S_and_T_prime_sub_S_prime_and_x_in_span_R_T_star_T_prime_colon_Set_A", "Not an equality or iff proposition"),
    ("mem_span_mul_finite_of_mem_mul", "exists_T_T_prime_colon_Finset_A_T_colon_Set_A_sub_P_and_T_prime_colon_Set_A_sub_Q_and_x_in_span_R_T_star_T_prime_colon_Set", "Not an equality or iff proposition"),
    ("pow_induction_on_left", "_unknown", "Empty proposition"),
    ("pow_induction_on_left", "C_x", "Not an equality or iff proposition"),
    ("comap_unop_pow", "comap_opLinearEquiv_R_colon_A_R_A_symm_colon_A_to_R_A_M_pow_n_eq_co", "Not an equality or iff proposition"),
    ("comap_op_pow", "comap_opLinearEquiv_R_colon_A_R_A_colon_A_to_R_A_M_pow_n_eq_comap", "Not an equality or iff proposition"),
    ("map_op_pow", "map_opLinearEquiv_R_colon_A_R_A_colon_A_to_R_A_M_pow_n_eq_map_op", "Not an equality or iff proposition"),
    ("map_unop_pow", "map_opLinearEquiv_R_colon_A_R_A_symm_colon_A_to_R_A_M_pow_n_eq_map", "Not an equality or iff proposition"),
    ("mul_mem_mul_rev", "n_star_m_in_M_star_N", "Not an equality or iff proposition"),
    ("smul_le_smul", "s_M_le_t_N", "Not an equality or iff proposition"),
    ("AlgHom_toRingHom_fromOpposite", "f_fromOpposite_hf_colon_A_to_plus_star_B_eq_f_colon_A_to_plus_star_B_fromOpposite_hf", "Not an equality or iff proposition"),
    ("AlgHom_toRingHom_toOpposite", "f_toOpposite_hf_colon_A_to_plus_star_B_eq_f_colon_A_to_plus_star_B_toOpposite_hf", "Not an equality or iff proposition"),
    ("AlgEquiv_piCongrLeft", "_unknown", "Empty proposition"),
    ("AlgEquiv_piCongrLeft", "_unknown", "Empty proposition"),
    ("IsScalarTower_restrictScalars", "letI", "Not an equality or iff proposition"),
    ("spectrum_subset_singleton_zero_compl", "spectrum_R_a_sub_0", "Not an equality or iff proposition"),
    ("spectrum_mem_resolventSet_of_left_right_inverse", "r_in_resolventSet_R_a", "Not an equality or iff proposition"),
    ("spectrum_inv_mem_resolventSet", "rinv_colon_R_in_resolventSet_R_ainv_colon_A", "Not an equality or iff proposition"),
    ("subset_subalgebra", "spectrum_R_a_colon_A_sub_spectrum_R_a", "Not an equality or iff proposition"),
    ("AlgHom_mem_resolventSet_apply", "r_in_resolventSet_R_phi_colon_A_to_B_a", "Not an equality or iff proposition"),
    ("AlgHom_spectrum_apply_subset", "sig_phi_colon_A_to_B_a_sub_sig_a", "Not an equality or iff proposition"),
    ("apply_mem_spectrum", "phi_a_in_sig_a", "Not an equality or iff proposition"),
    ("spectrum_units_conjugate", "_unknown", "Empty proposition"),
    ("isQuasiregular_iff", "_unknown", "Empty proposition"),
    ("IsQuasiregular_map", "IsQuasiregular_f_x", "Not an equality or iff proposition"),
    ("isQuasiregular_iff_isUnit", "_unknown", "Empty proposition"),
    ("quasispectrum_not_isUnit_mem", "r_in_quasispectrum_R_a", "Not an equality or iff proposition"),
    ("quasispectrum_nonempty", "quasispectrum_R_a_Nonempty", "Not an equality or iff proposition"),
    ("NonUnitalAlgHom_quasispectrum_apply_subset", "_unknown", "Empty proposition"),
    ("NonUnitalAlgHom_quasispectrum_apply_subset", "quasispectrum_R_phi_a_sub_quasispectrum_R_a", "Not an equality or iff proposition"),
    ("quasispectrum_mem_of_not_quasiregular", "r_colon_R_in_quasispectrum_R_a", "Not an equality or iff proposition"),
    ("spectrum_subset_quasispectrum", "spectrum_R_a_sub_quasispectrum_R_a", "Not an equality or iff proposition"),
    ("Unitization_mem_spectrum_inr_of_not_isUnit", "r_in_spectrum_R_a_colon_Unitization_R_A", "Not an equality or iff proposition"),
    ("Unitization_quasispectrum_eq_spectrum_inr", "_unknown", "Empty proposition"),
]
