"""Mathlib: Int Basic — auto-generated from Mathlib4.

Contains 400 rewrite rules derived from Mathlib theorems.
Plus 442 untranslatable theorems stored for reference.
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

AXIOM_NAME = "mathlib_ml_int_basic"
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

def _r0000_balance_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.balance_sub
    # balance (f - g) = balance f - balance g
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "balance", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("balance", (OVar("f"),)), OOp("balance", (OVar("g"),))))
            results.append((rhs, "Mathlib: Fintype_balance_sub"))
        except Exception:
            pass
    return results


def _r0001_balance_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.balance_neg
    # balance (-f) = -balance f
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "balance", 1)
    if args is not None:
        try:
            rhs = OOp("minus_balance", (OVar("f"),))
            results.append((rhs, "Mathlib: Fintype_balance_neg"))
        except Exception:
            pass
    return results


def _r0002_prod_of_support_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.prod_of_support_subset
    # f.prod g = ∏ x ∈ s, g x (f x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_prod", 1)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (args[0], OVar("x"), OOp("f", (OVar("x"),)),))))
            results.append((rhs, "Mathlib: Finsupp_prod_of_support_subset"))
        except Exception:
            pass
    return results


def _r0003_floor_sub_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_sub_natCast
    # ⌊a - n⌋ = ⌊a⌋ - n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: Int_floor_sub_natCast"))
        except Exception:
            pass
    return results


def _r0004_floor_sub_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_sub_ofNat
    # ⌊a - ofNat(n)⌋ = ⌊a⌋ - ofNat(n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: Int_floor_sub_ofNat"))
        except Exception:
            pass
    return results


def _r0005_sub_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.sub_bot
    # s - ⊥ = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = args[1]
            results.append((rhs, "Mathlib: Interval_sub_bot"))
        except Exception:
            pass
    return results


def _r0006_toAddSubgroup_closedBall(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FiniteArchimedeanClass.toAddSubgroup_closedBall
    # (closedBall K c).toAddSubgroup = closedBallAddSubgroup c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("closedBall_K_c_toAddSubgroup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("closedBallAddSubgroup", (OVar("c"),))
            results.append((rhs, "Mathlib: FiniteArchimedeanClass_toAddSubgroup_closedBall"))
    except Exception:
        pass
    return results


def _r0007_cast_nonneg_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.cast_nonneg_iff
    # ∀ {n : ℤ}, (0 : R) ≤ n ↔ 0 ≤ n   | (n : ℕ) =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: Int_cast_nonneg_iff"))
        except Exception:
            pass
    return results


def _r0008_val_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.val_sub
    # (x - y).1 = x.1 - y.1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_minus_y_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("x_1"), OVar("y_1")))
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_val_sub"))
    except Exception:
        pass
    return results


def _r0009_mk_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.mk_natCast
    # FiniteElement.mk (n : K) (mk_natCast_nonneg n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FiniteElement_mk", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_mk_natCast"))
        except Exception:
            pass
    return results


def _r0010_mk_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.mk_intCast
    # FiniteElement.mk (n : K) (mk_intCast_nonneg n) = n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FiniteElement_mk", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_mk_intCast"))
        except Exception:
            pass
    return results


def _r0011_neg_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.neg_mk
    # -FiniteElement.mk x h = FiniteElement.mk (-x) (by rwa [mk_neg])
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_FiniteElement_mk", 2)
    if args is not None:
        try:
            rhs = OOp("FiniteElement_mk", (OVar("minus_x"), OOp("by", (OVar("rwa"), OSeq((OVar("mk_neg"),)),)),))
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_neg_mk"))
        except Exception:
            pass
    return results


def _r0012_den_abs_eq_den(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.den_abs_eq_den
    # |q|.den = q.den
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_qpipe_den")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q_den")
            results.append((rhs, "Mathlib: Rat_den_abs_eq_den"))
    except Exception:
        pass
    return results


def _r0013_negOnePow_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.negOnePow_sub
    # (n₁ - n₂).negOnePow = n₁.negOnePow * n₂.negOnePow
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_1_minus_n_2_negOnePow")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("n_1_negOnePow"), OVar("n_2_negOnePow")))
            results.append((rhs, "Mathlib: Int_negOnePow_sub"))
    except Exception:
        pass
    return results


def _r0014_exp_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_neg
    # exp (-x) = (exp x)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OVar("exp_x_inv")
            results.append((rhs, "Mathlib: Complex_exp_neg"))
        except Exception:
            pass
    return results


def _r0015_norm_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_of_nonneg
    # ‖(r : ℂ)‖ = r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("r")
            results.append((rhs, "Mathlib: Complex_norm_of_nonneg"))
    except Exception:
        pass
    return results


def _r0016_norm_int_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_int_of_nonneg
    # ‖(n : ℂ)‖ = n
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Complex_norm_int_of_nonneg"))
    except Exception:
        pass
    return results


def _r0017_sq_norm_sub_sq_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sq_norm_sub_sq_im
    # ‖z‖ ^ 2 - z.im ^ 2 = z.re ^ 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("z_re"), OLit(2)))
            results.append((rhs, "Mathlib: Complex_sq_norm_sub_sq_im"))
        except Exception:
            pass
    return results


def _r0018_sinh_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sinh_neg
    # sinh (-x) = -sinh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sinh", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sinh", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sinh_neg"))
        except Exception:
            pass
    return results


def _r0019_cosh_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cosh_neg
    # cosh (-x) = cosh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cosh", 1)
    if args is not None:
        try:
            rhs = OOp("cosh", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_cosh_neg"))
        except Exception:
            pass
    return results


def _r0020_tanh_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tanh_neg
    # tanh (-x) = -tanh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tanh", 1)
    if args is not None:
        try:
            rhs = OOp("minus_tanh", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_tanh_neg"))
        except Exception:
            pass
    return results


def _r0021_exp_sub_cosh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_sub_cosh
    # exp x - cosh x = sinh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("sinh", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_exp_sub_cosh"))
        except Exception:
            pass
    return results


def _r0022_exp_sub_sinh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_sub_sinh
    # exp x - sinh x = cosh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("cosh", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_exp_sub_sinh"))
        except Exception:
            pass
    return results


def _r0023_cosh_sub_sinh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cosh_sub_sinh
    # cosh x - sinh x = exp (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (OVar("minus_x"),))
            results.append((rhs, "Mathlib: Complex_cosh_sub_sinh"))
        except Exception:
            pass
    return results


def _r0024_sinh_sub_cosh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sinh_sub_cosh
    # sinh x - cosh x = -exp (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("minus_exp", (OVar("minus_x"),))
            results.append((rhs, "Mathlib: Complex_sinh_sub_cosh"))
        except Exception:
            pass
    return results


def _r0025_cosh_sq_sub_sinh_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cosh_sq_sub_sinh_sq
    # cosh x ^ 2 - sinh x ^ 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Complex_cosh_sq_sub_sinh_sq"))
        except Exception:
            pass
    return results


def _r0026_sin_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_neg
    # sin (-x) = -sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sin_neg"))
        except Exception:
            pass
    return results


def _r0027_cos_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_neg
    # cos (-x) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_cos_neg"))
        except Exception:
            pass
    return results


def _r0028_cot_inv_eq_tan(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cot_inv_eq_tan
    # (cot x)⁻¹ = tan x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cot_x_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("tan", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_cot_inv_eq_tan"))
    except Exception:
        pass
    return results


def _r0029_tan_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tan_neg
    # tan (-x) = -tan x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OOp("minus_tan", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_tan_neg"))
        except Exception:
            pass
    return results


def _r0030_sin_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_neg
    # sin (-x) = -sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_neg"))
        except Exception:
            pass
    return results


def _r0031_cos_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_neg
    # cos (-x) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_neg"))
        except Exception:
            pass
    return results


def _r0032_cos_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_abs
    # cos |x| = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_abs"))
        except Exception:
            pass
    return results


def _r0033_cot_inv_eq_tan(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cot_inv_eq_tan
    # (cot x)⁻¹ = tan x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("cot_x_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("tan", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cot_inv_eq_tan"))
    except Exception:
        pass
    return results


def _r0034_tan_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tan_neg
    # tan (-x) = -tan x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OOp("minus_tan", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_tan_neg"))
        except Exception:
            pass
    return results


def _r0035_sinh_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sinh_neg
    # sinh (-x) = -sinh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sinh", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sinh", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sinh_neg"))
        except Exception:
            pass
    return results


def _r0036_cosh_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cosh_neg
    # cosh (-x) = cosh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cosh", 1)
    if args is not None:
        try:
            rhs = OOp("cosh", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cosh_neg"))
        except Exception:
            pass
    return results


def _r0037_cosh_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cosh_abs
    # cosh |x| = cosh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cosh", 1)
    if args is not None:
        try:
            rhs = OOp("cosh", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cosh_abs"))
        except Exception:
            pass
    return results


def _r0038_tanh_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tanh_neg
    # tanh (-x) = -tanh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tanh", 1)
    if args is not None:
        try:
            rhs = OOp("minus_tanh", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_tanh_neg"))
        except Exception:
            pass
    return results


def _r0039_exp_sub_cosh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.exp_sub_cosh
    # exp x - cosh x = sinh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("sinh", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_exp_sub_cosh"))
        except Exception:
            pass
    return results


def _r0040_exp_sub_sinh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.exp_sub_sinh
    # exp x - sinh x = cosh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("cosh", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_exp_sub_sinh"))
        except Exception:
            pass
    return results


def _r0041_cosh_sub_sinh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cosh_sub_sinh
    # cosh x - sinh x = exp (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (OVar("minus_x"),))
            results.append((rhs, "Mathlib: Real_cosh_sub_sinh"))
        except Exception:
            pass
    return results


def _r0042_cosh_sq_sub_sinh_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cosh_sq_sub_sinh_sq
    # cosh x ^ 2 - sinh x ^ 2 = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_cosh_sq_sub_sinh_sq"))
        except Exception:
            pass
    return results


def _r0043_coe_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.coe_neg
    # ↑(-z) = (-z : ℂ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_z")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("minus_z", (OVar("colon"), OVar("_unknown"),))
            results.append((rhs, "Mathlib: Complex_UnitDisc_coe_neg"))
    except Exception:
        pass
    return results


def _r0044_re_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.re_neg
    # (-z).re = -z.re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_z_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_z_re")
            results.append((rhs, "Mathlib: Complex_UnitDisc_re_neg"))
    except Exception:
        pass
    return results


def _r0045_im_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.im_neg
    # (-z).im = -z.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_z_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_z_im")
            results.append((rhs, "Mathlib: Complex_UnitDisc_im_neg"))
    except Exception:
        pass
    return results


def _r0046_toNat_add_toNat_neg_eq_nnnorm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.toNat_add_toNat_neg_eq_nnnorm
    # ↑n.toNat + ↑(-n).toNat = ‖n‖₊
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Int_toNat_add_toNat_neg_eq_nnnorm"))
        except Exception:
            pass
    return results


def _r0047_toNat_add_toNat_neg_eq_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.toNat_add_toNat_neg_eq_norm
    # ↑n.toNat + ↑(-n).toNat = ‖n‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OVar("n")
            results.append((rhs, "Mathlib: Int_toNat_add_toNat_neg_eq_norm"))
        except Exception:
            pass
    return results


def _r0048_sqrt_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sqrt_of_nonneg
    # a.sqrt = √a.re
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a_sqrt")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("a_re")
            results.append((rhs, "Mathlib: Complex_sqrt_of_nonneg"))
    except Exception:
        pass
    return results


def _r0049_add_sqrt_self_sq_sub_one_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.add_sqrt_self_sq_sub_one_inv
    # (x + √(x ^ 2 - 1))⁻¹ = x - √(x ^ 2 - 1)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_plus_x_pow_2_minus_1_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("x"), OVar("x_pow_2_minus_1")))
            results.append((rhs, "Mathlib: Real_add_sqrt_self_sq_sub_one_inv"))
    except Exception:
        pass
    return results


def _r0050_arsinh_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arsinh_neg
    # arsinh (-x) = -arsinh x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arsinh", 1)
    if args is not None:
        try:
            rhs = OOp("minus_arsinh", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_arsinh_neg"))
        except Exception:
            pass
    return results


def _r0051_binEntropy_two_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.binEntropy_two_inv
    # binEntropy 2⁻¹ = log 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "binEntropy", 1)
    if args is not None:
        try:
            rhs = OOp("log", (OLit(2),))
            results.append((rhs, "Mathlib: Real_binEntropy_two_inv"))
        except Exception:
            pass
    return results


def _r0052_binEntropy_eq_negMulLog_add_negMulLog_on(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub
    # binEntropy p = negMulLog p + negMulLog (1 - p)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "binEntropy", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("negMulLog", (args[0],)), OOp("negMulLog", (OOp("-", (OLit(1), args[0])),))))
            results.append((rhs, "Mathlib: Real_binEntropy_eq_negMulLog_add_negMulLog_one_sub"))
        except Exception:
            pass
    return results


def _r0053_binEntropy_two_inv_add(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.binEntropy_two_inv_add
    # binEntropy (2⁻¹ + p) = binEntropy (2⁻¹ - p)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "binEntropy", 1)
    if args is not None:
        try:
            rhs = OOp("binEntropy", (OOp("-", (OVar("_2inv"), OVar("p"))),))
            results.append((rhs, "Mathlib: Real_binEntropy_two_inv_add"))
        except Exception:
            pass
    return results


def _r0054_arg_neg_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_neg_I
    # arg (-I) = -(π / 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OVar("minus_pi_slash_2")
            results.append((rhs, "Mathlib: Complex_arg_neg_I"))
        except Exception:
            pass
    return results


def _r0055_arg_inv_coe_angle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_inv_coe_angle
    # (arg x⁻¹ : Real.Angle) = -arg x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 3)
    if args is not None:
        try:
            rhs = OOp("minus_arg", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_arg_inv_coe_angle"))
        except Exception:
            pass
    return results


def _r0056_arg_neg_eq_arg_sub_pi_of_im_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_neg_eq_arg_sub_pi_of_im_pos
    # arg (-x) = arg x - π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("arg", (OVar("x"),)), OVar("pi")))
            results.append((rhs, "Mathlib: Complex_arg_neg_eq_arg_sub_pi_of_im_pos"))
        except Exception:
            pass
    return results


def _r0057_toCircle_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toCircle_neg
    # toCircle (-θ) = (toCircle θ)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "toCircle", 1)
    if args is not None:
        try:
            rhs = OVar("toCircle_th_inv")
            results.append((rhs, "Mathlib: Real_Angle_toCircle_neg"))
        except Exception:
            pass
    return results


def _r0058_logb_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_abs
    # logb b |x| = logb b x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OOp("logb", (args[0], OVar("x"),))
            results.append((rhs, "Mathlib: Real_logb_abs"))
        except Exception:
            pass
    return results


def _r0059_logb_neg_base_eq_logb(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_neg_base_eq_logb
    # logb (-b) = logb b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 1)
    if args is not None:
        try:
            rhs = OOp("logb", (OVar("b"),))
            results.append((rhs, "Mathlib: Real_logb_neg_base_eq_logb"))
        except Exception:
            pass
    return results


def _r0060_logb_neg_eq_logb(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_neg_eq_logb
    # logb b (-x) = logb b x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OOp("logb", (args[0], OVar("x"),))
            results.append((rhs, "Mathlib: Real_logb_neg_eq_logb"))
        except Exception:
            pass
    return results


def _r0061_logb_inv_base(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_inv_base
    # logb b⁻¹ x = -logb b x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OOp("minus_logb", (OVar("b"), args[1],))
            results.append((rhs, "Mathlib: Real_logb_inv_base"))
        except Exception:
            pass
    return results


def _r0062_inv_logb(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.inv_logb
    # (logb a b)⁻¹ = logb b a
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("logb_a_b_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("logb", (OVar("b"), OVar("a"),))
            results.append((rhs, "Mathlib: Real_inv_logb"))
    except Exception:
        pass
    return results


def _r0063_log_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.log_abs
    # log |x| = log x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("log", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_log_abs"))
        except Exception:
            pass
    return results


def _r0064_posLog_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.posLog_abs
    # log⁺ |x| = log⁺ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logpos", 1)
    if args is not None:
        try:
            rhs = OOp("logpos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_posLog_abs"))
        except Exception:
            pass
    return results


def _r0065_cpow_nat_inv_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_nat_inv_pow
    # (x ^ (n⁻¹ : ℂ)) ^ n = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Complex_cpow_nat_inv_pow"))
        except Exception:
            pass
    return results


def _r0066_mul_cpow_ofReal_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.mul_cpow_ofReal_nonneg
    # ((a : ℂ) * (b : ℂ)) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OOp("a", (OVar("colon"), OVar("_unknown"),)), args[1])), OOp("**", (OOp("b", (OVar("colon"), OVar("_unknown"),)), args[1]))))
            results.append((rhs, "Mathlib: Complex_mul_cpow_ofReal_nonneg"))
        except Exception:
            pass
    return results


def _r0067_rpow_neg_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_neg_natCast
    # x ^ (-n : ℝ) = x ^ (-n : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OOp("minus_n", (OVar("colon"), OVar("_unknown"),))))
            results.append((rhs, "Mathlib: Real_rpow_neg_natCast"))
        except Exception:
            pass
    return results


def _r0068_norm_cpow_inv_nat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_cpow_inv_nat
    # ‖x ^ (n⁻¹ : ℂ)‖ = ‖x‖ ^ (n⁻¹ : ℝ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OOp("ninv", (OVar("colon"), OVar("_unknown"),))))
            results.append((rhs, "Mathlib: Complex_norm_cpow_inv_nat"))
        except Exception:
            pass
    return results


def _r0069_rpow_inv_rpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_inv_rpow
    # (x ^ y⁻¹) ^ y = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Real_rpow_inv_rpow"))
        except Exception:
            pass
    return results


def _r0070_pow_rpow_inv_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.pow_rpow_inv_natCast
    # (x ^ n) ^ (n⁻¹ : ℝ) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Real_pow_rpow_inv_natCast"))
        except Exception:
            pass
    return results


def _r0071_sigmoid_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sigmoid_neg
    # sigmoid (-x) = 1 - sigmoid x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sigmoid", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OLit(1), OOp("sigmoid", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_sigmoid_neg"))
        except Exception:
            pass
    return results


def _r0072_coe_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.coe_neg
    # ↑(-x : ℝ) = -(↑x : Angle)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_x_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_x_colon_Angle")
            results.append((rhs, "Mathlib: Real_Angle_coe_neg"))
    except Exception:
        pass
    return results


def _r0073_coe_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.coe_sub
    # ↑(x - y : ℝ) = (↑x - ↑y : Angle)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_minus_y_colon")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("x"), OOp("y", (OVar("colon"), OVar("Angle"),))))
            results.append((rhs, "Mathlib: Real_Angle_coe_sub"))
    except Exception:
        pass
    return results


def _r0074_neg_coe_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.neg_coe_pi
    # -(π : Angle) = π
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_pi_colon_Angle")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("pi")
            results.append((rhs, "Mathlib: Real_Angle_neg_coe_pi"))
    except Exception:
        pass
    return results


def _r0075_two_nsmul_neg_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.two_nsmul_neg_pi_div_two
    # (2 : ℕ) • (↑(-π / 2) : Angle) = π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_2_colon", 2)
    if args is not None:
        try:
            rhs = OVar("pi")
            results.append((rhs, "Mathlib: Real_Angle_two_nsmul_neg_pi_div_two"))
        except Exception:
            pass
    return results


def _r0076_sin_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sin_sub_pi
    # sin (θ - π) = -sin θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_sin_sub_pi"))
        except Exception:
            pass
    return results


def _r0077_cos_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_sub_pi
    # cos (θ - π) = -cos θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("minus_cos", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_cos_sub_pi"))
        except Exception:
            pass
    return results


def _r0078_toReal_neg_eq_neg_toReal_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_neg_eq_neg_toReal_iff
    # (-θ).toReal = -(θ.toReal) ↔ θ ≠ π
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_th_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("!=", (OOp("iff", (OVar("minus_th_toReal"), OVar("th"))), OVar("pi")))
            results.append((rhs, "Mathlib: Real_Angle_toReal_neg_eq_neg_toReal_iff"))
    except Exception:
        pass
    return results


def _r0079_toReal_neg_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_neg_pi_div_two
    # ((-π / 2 : ℝ) : Angle).toReal = -π / 2
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_pi_slash_2_colon_colon_Angle_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("//", (OVar("minus_pi"), OLit(2)))
            results.append((rhs, "Mathlib: Real_Angle_toReal_neg_pi_div_two"))
    except Exception:
        pass
    return results


def _r0080_toReal_eq_neg_pi_div_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_eq_neg_pi_div_two_iff
    # θ.toReal = -π / 2 ↔ θ = (-π / 2 : ℝ)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("th_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("//", (OVar("minus_pi"), OLit(2))), OVar("th"))), OOp("//", (OVar("minus_pi"), OOp("_2", (OVar("colon"), OVar("_unknown"),))))))
            results.append((rhs, "Mathlib: Real_Angle_toReal_eq_neg_pi_div_two_iff"))
    except Exception:
        pass
    return results


def _r0081_tan_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.tan_sub_pi
    # tan (θ - π) = tan θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OOp("tan", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_tan_sub_pi"))
        except Exception:
            pass
    return results


def _r0082_sign_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sign_neg
    # (-θ).sign = -θ.sign
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_th_sign")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_th_sign")
            results.append((rhs, "Mathlib: Real_Angle_sign_neg"))
    except Exception:
        pass
    return results


def _r0083_sign_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sign_sub_pi
    # (θ - π).sign = -θ.sign
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("th_minus_pi_sign")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_th_sign")
            results.append((rhs, "Mathlib: Real_Angle_sign_sub_pi"))
    except Exception:
        pass
    return results


def _r0084_sign_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sign_pi_sub
    # ((π : Angle) - θ).sign = θ.sign
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pi_colon_Angle_minus_th_sign")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("th_sign")
            results.append((rhs, "Mathlib: Real_Angle_sign_pi_sub"))
    except Exception:
        pass
    return results


def _r0085_sign_coe_neg_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sign_coe_neg_pi_div_two
    # (↑(-π / 2) : Angle).sign = -1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_pi_slash_2_colon_Angle_sign")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Real_Angle_sign_coe_neg_pi_div_two"))
    except Exception:
        pass
    return results


def _r0086_arctan_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_neg
    # arctan (-x) = -arctan x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arctan", 1)
    if args is not None:
        try:
            rhs = OOp("minus_arctan", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_arctan_neg"))
        except Exception:
            pass
    return results


def _r0087_arctan_eq_neg_pi_div_four(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_eq_neg_pi_div_four
    # arctan x = -(π / 4) ↔ x = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arctan", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("minus_pi_slash_4"), args[0])), OVar("minus_1")))
            results.append((rhs, "Mathlib: Real_arctan_eq_neg_pi_div_four"))
        except Exception:
            pass
    return results


def _r0088_sin_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_sub_pi
    # sin (x - π) = -sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_sub_pi"))
        except Exception:
            pass
    return results


def _r0089_sin_sub_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_sub_two_pi
    # sin (x - 2 * π) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_sub_two_pi"))
        except Exception:
            pass
    return results


def _r0090_sin_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_pi_sub
    # sin (π - x) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_pi_sub"))
        except Exception:
            pass
    return results


def _r0091_sin_two_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_two_pi_sub
    # sin (2 * π - x) = -sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_two_pi_sub"))
        except Exception:
            pass
    return results


def _r0092_sin_sub_nat_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_sub_nat_mul_two_pi
    # sin (x - n * (2 * π)) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_sub_nat_mul_two_pi"))
        except Exception:
            pass
    return results


def _r0093_sin_sub_int_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_sub_int_mul_two_pi
    # sin (x - n * (2 * π)) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_sub_int_mul_two_pi"))
        except Exception:
            pass
    return results


def _r0094_sin_nat_mul_two_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_nat_mul_two_pi_sub
    # sin (n * (2 * π) - x) = -sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_nat_mul_two_pi_sub"))
        except Exception:
            pass
    return results


def _r0095_sin_int_mul_two_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_int_mul_two_pi_sub
    # sin (n * (2 * π) - x) = -sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_int_mul_two_pi_sub"))
        except Exception:
            pass
    return results


def _r0096_cos_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_sub_pi
    # cos (x - π) = -cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("minus_cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_sub_pi"))
        except Exception:
            pass
    return results


def _r0097_cos_sub_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_sub_two_pi
    # cos (x - 2 * π) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_sub_two_pi"))
        except Exception:
            pass
    return results


def _r0098_cos_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi_sub
    # cos (π - x) = -cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("minus_cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_pi_sub"))
        except Exception:
            pass
    return results


def _r0099_cos_two_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_two_pi_sub
    # cos (2 * π - x) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_two_pi_sub"))
        except Exception:
            pass
    return results


def _r0100_cos_sub_nat_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_sub_nat_mul_two_pi
    # cos (x - n * (2 * π)) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_sub_nat_mul_two_pi"))
        except Exception:
            pass
    return results


def _r0101_cos_sub_int_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_sub_int_mul_two_pi
    # cos (x - n * (2 * π)) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_sub_int_mul_two_pi"))
        except Exception:
            pass
    return results


def _r0102_cos_nat_mul_two_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_nat_mul_two_pi_sub
    # cos (n * (2 * π) - x) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_nat_mul_two_pi_sub"))
        except Exception:
            pass
    return results


def _r0103_cos_int_mul_two_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_int_mul_two_pi_sub
    # cos (n * (2 * π) - x) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_int_mul_two_pi_sub"))
        except Exception:
            pass
    return results


def _r0104_exp_neg_pi_div_two_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_neg_pi_div_two_mul_I
    # exp (-π / 2 * I) = -I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OVar("minus_I")
            results.append((rhs, "Mathlib: Complex_exp_neg_pi_div_two_mul_I"))
        except Exception:
            pass
    return results


def _r0105_exp_sub_pi_mul_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_sub_pi_mul_I
    # exp (z - π * I) = -exp z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OOp("minus_exp", (OVar("z"),))
            results.append((rhs, "Mathlib: Complex_exp_sub_pi_mul_I"))
        except Exception:
            pass
    return results


def _r0106_abs_sinh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.abs_sinh
    # |sinh x| = sinh |x|
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pipe_sinh", 1)
    if args is not None:
        try:
            rhs = OOp("sinh", (OVar("pipe_xpipe"),))
            results.append((rhs, "Mathlib: Real_abs_sinh"))
        except Exception:
            pass
    return results


def _r0107_sinh_sub_id_strictMono(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sinh_sub_id_strictMono
    # StrictMono fun x => sinh x - x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "StrictMono", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("gt", (OVar("sinh"), args[1],)), args[1]))
            results.append((rhs, "Mathlib: Real_sinh_sub_id_strictMono"))
        except Exception:
            pass
    return results


def _r0108_arcsin_eq_neg_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arcsin_eq_neg_pi_div_two
    # arcsin x = -(π / 2) ↔ x ≤ -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arcsin", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (OVar("minus_pi_slash_2"), args[0])), OVar("minus_1")))
            results.append((rhs, "Mathlib: Real_arcsin_eq_neg_pi_div_two"))
        except Exception:
            pass
    return results


def _r0109_neg_pi_div_two_eq_arcsin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.neg_pi_div_two_eq_arcsin
    # -(π / 2) = arcsin x ↔ x ≤ -1
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_pi_slash_2")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("iff", (OOp("arcsin", (OVar("x"),)), OVar("x"))), OVar("minus_1")))
            results.append((rhs, "Mathlib: Real_neg_pi_div_two_eq_arcsin"))
    except Exception:
        pass
    return results


def _r0110_memberSubfamily_image_erase(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.memberSubfamily_image_erase
    # (𝒜.image (erase · a)).memberSubfamily a = ∅
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "image_erase_a_memberSubfamily", 1)
    if args is not None:
        try:
            rhs = OVar("empty")
            results.append((rhs, "Mathlib: Finset_memberSubfamily_image_erase"))
        except Exception:
            pass
    return results


def _r0111_subset_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Shatters.subset_iff
    # t ⊆ s ↔ ∃ u ∈ 𝒜, s ∩ u = t
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "iff", 2)
    if args is not None:
        try:
            rhs = OVar("t")
            results.append((rhs, "Mathlib: Finset_Shatters_subset_iff"))
        except Exception:
            pass
    return results


def _r0112_neg_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.neg_im
    # (-z).im = -z.im
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_z_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_z_im")
            results.append((rhs, "Mathlib: Complex_neg_im"))
    except Exception:
        pass
    return results


def _r0113_ofReal_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.ofReal_neg
    # ((-r : ℝ) : ℂ) = -r
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_r_colon", 2)
    if args is not None:
        try:
            rhs = OVar("minus_r")
            results.append((rhs, "Mathlib: Complex_ofReal_neg"))
        except Exception:
            pass
    return results


def _r0114_equivSubtype_symm_trans_valEmbedding(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.equivSubtype_symm_trans_valEmbedding
    # equivSubtype.symm.toEmbedding.trans valEmbedding = Embedding.subtype (· < n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "equivSubtype_symm_toEmbedding_trans", 1)
    if args is not None:
        try:
            rhs = OOp("Embedding_subtype", (OOp("<", (OVar("_unknown"), OVar("n"))),))
            results.append((rhs, "Mathlib: Fin_equivSubtype_symm_trans_valEmbedding"))
        except Exception:
            pass
    return results


def _r0115_antisymm_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Subset.antisymm_iff
    # s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s_1")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("and", (OOp("iff", (OVar("s_2"), OOp("subset", (OVar("s_1"), OVar("s_2"))))), OOp("subset", (OVar("s_2"), OVar("s_1")))))
            results.append((rhs, "Mathlib: Finset_Subset_antisymm_iff"))
    except Exception:
        pass
    return results


def _r0116_toDFinsupp_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.toDFinsupp_sub
    # (f - g).toDFinsupp = f.toDFinsupp - g.toDFinsupp
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("f_minus_g_toDFinsupp")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("f_toDFinsupp"), OVar("g_toDFinsupp")))
            results.append((rhs, "Mathlib: Finsupp_toDFinsupp_sub"))
    except Exception:
        pass
    return results


def _r0117_prod_eq_mul_prod_subtype_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.prod_eq_mul_prod_subtype_ne
    # ∏ i, f i = f a * ∏ i : {i // i ≠ a}, f i.1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_unknown", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("f", (OVar("a"),)), OOp("_unknown", (args[2], OVar("colon"), OVar("i_slash_slash_i_ne_a"), args[1], OVar("i_1"),))))
            results.append((rhs, "Mathlib: Fintype_prod_eq_mul_prod_subtype_ne"))
        except Exception:
            pass
    return results


def _r0118_bodd_subNatNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.bodd_subNatNat
    # bodd (subNatNat m n) = xor m.bodd n.bodd
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "bodd", 1)
    if args is not None:
        try:
            rhs = OOp("xor", (OVar("m_bodd"), OVar("n_bodd"),))
            results.append((rhs, "Mathlib: Int_bodd_subNatNat"))
        except Exception:
            pass
    return results


def _r0119_shiftRight_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.shiftRight_neg
    # m >>> (-n) = m <<< n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "m", 2)
    if args is not None:
        try:
            rhs = OOp("m", (OVar("lt_lt_lt"), OVar("n"),))
            results.append((rhs, "Mathlib: Int_shiftRight_neg"))
        except Exception:
            pass
    return results


def _r0120_shiftLeft_negSucc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.shiftLeft_negSucc
    # -[m+1] <<< (n : ℤ) = -[Nat.shiftLeft' true m n+1]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_mplus_1", 2)
    if args is not None:
        try:
            rhs = OVar("minus_Nat_shiftLeft_prime_true_m_nplus_1")
            results.append((rhs, "Mathlib: Int_shiftLeft_negSucc"))
        except Exception:
            pass
    return results


def _r0121_shiftRight_negSucc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.shiftRight_negSucc
    # -[m+1] >>> (n : ℤ) = -[m >>> n+1]
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_mplus_1", 2)
    if args is not None:
        try:
            rhs = OVar("minus_m_gt_gt_gt_nplus_1")
            results.append((rhs, "Mathlib: Int_shiftRight_negSucc"))
        except Exception:
            pass
    return results


def _r0122_cast_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.cast_neg
    # ∀ n, ((-n : ℤ) : R) = -n   | (0 : ℕ) =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_n_colon", 2)
    if args is not None:
        try:
            rhs = OOp("minus_n", (OVar("pipe"), OOp("_0", (args[0], OVar("_unknown"),)), OVar("eq_gt"),))
            results.append((rhs, "Mathlib: Int_cast_neg"))
        except Exception:
            pass
    return results


def _r0123_fib_neg_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.fib_neg_two
    # fib (-2) = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fib", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Int_fib_neg_two"))
        except Exception:
            pass
    return results


def _r0124_fib_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.fib_of_nonneg
    # fib n = n.toNat.fib
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fib", 1)
    if args is not None:
        try:
            rhs = OVar("n_toNat_fib")
            results.append((rhs, "Mathlib: Int_fib_of_nonneg"))
        except Exception:
            pass
    return results


def _r0125_fib_of_odd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.fib_of_odd
    # fib n = (natAbs n).fib
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fib", 1)
    if args is not None:
        try:
            rhs = OVar("natAbs_n_fib")
            results.append((rhs, "Mathlib: Int_fib_of_odd"))
        except Exception:
            pass
    return results


def _r0126_units_inv_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.units_inv_eq_self
    # u⁻¹ = u
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("uinv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("u")
            results.append((rhs, "Mathlib: Int_units_inv_eq_self"))
    except Exception:
        pass
    return results


def _r0127_nnabs_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.nnabs_of_nonneg
    # nnabs x = toNNReal x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "nnabs", 1)
    if args is not None:
        try:
            rhs = OOp("toNNReal", (args[0],))
            results.append((rhs, "Mathlib: Real_nnabs_of_nonneg"))
        except Exception:
            pass
    return results


def _r0128_cast_natAbs_eq_nnabs_cast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cast_natAbs_eq_nnabs_cast
    # (n.natAbs : ℝ≥0) = nnabs n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "n_natAbs", 2)
    if args is not None:
        try:
            rhs = OOp("nnabs", (OVar("n"),))
            results.append((rhs, "Mathlib: Real_cast_natAbs_eq_nnabs_cast"))
        except Exception:
            pass
    return results


def _r0129_cast_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.cast_sub
    # ↑(p - q) = (p - q : α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p_minus_q")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("p"), OOp("q", (OVar("colon"), OVar("a"),))))
            results.append((rhs, "Mathlib: Rat_cast_sub"))
    except Exception:
        pass
    return results


def _r0130_cast_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.cast_inv
    # ↑(p⁻¹) = (p⁻¹ : α)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pinv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("pinv", (OVar("colon"), OVar("a"),))
            results.append((rhs, "Mathlib: Rat_cast_inv"))
    except Exception:
        pass
    return results


def _r0131_num_neg_eq_neg_num(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.num_neg_eq_neg_num
    # (-q).num = -q.num
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_q_num")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_q_num")
            results.append((rhs, "Mathlib: Rat_num_neg_eq_neg_num"))
    except Exception:
        pass
    return results


def _r0132_sub_intCast_den(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.sub_intCast_den
    # (q - n).den = q.den
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_minus_n_den")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q_den")
            results.append((rhs, "Mathlib: Rat_sub_intCast_den"))
    except Exception:
        pass
    return results


def _r0133_intCast_sub_den(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.intCast_sub_den
    # (n - q).den = q.den
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_minus_q_den")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q_den")
            results.append((rhs, "Mathlib: Rat_intCast_sub_den"))
    except Exception:
        pass
    return results


def _r0134_sub_natCast_den(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.sub_natCast_den
    # (q - n).den = q.den
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_minus_n_den")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q_den")
            results.append((rhs, "Mathlib: Rat_sub_natCast_den"))
    except Exception:
        pass
    return results


def _r0135_natCast_sub_den(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.natCast_sub_den
    # (n - q).den = q.den
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("n_minus_q_den")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q_den")
            results.append((rhs, "Mathlib: Rat_natCast_sub_den"))
    except Exception:
        pass
    return results


def _r0136_sub_ofNat_den(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.sub_ofNat_den
    # (q - ofNat(n)).den = q.den
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("q_minus_ofNat_n_den")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q_den")
            results.append((rhs, "Mathlib: Rat_sub_ofNat_den"))
    except Exception:
        pass
    return results


def _r0137_ofNat_sub_den(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.ofNat_sub_den
    # (ofNat(n) - q).den = q.den
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ofNat_n_minus_q_den")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q_den")
            results.append((rhs, "Mathlib: Rat_ofNat_sub_den"))
    except Exception:
        pass
    return results


def _r0138_den_mul_den_eq_den_mul_gcd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.den_mul_den_eq_den_mul_gcd
    # q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("q_1_star_q_2_den"), OOp("q_1_num_star_q_2_num_natAbs_gcd", (OOp("*", (args[0], args[1])),))))
            results.append((rhs, "Mathlib: Rat_den_mul_den_eq_den_mul_gcd"))
        except Exception:
            pass
    return results


def _r0139_sqrt_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sqrt_inv
    # √x⁻¹ = (√x)⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("xinv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_inv")
            results.append((rhs, "Mathlib: Real_sqrt_inv"))
    except Exception:
        pass
    return results


def _r0140_fixingSubgroup_top(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.fixingSubgroup_top
    # fixingSubgroup (⊤ : IntermediateField F E) = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fixingSubgroup", 1)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: IntermediateField_fixingSubgroup_top"))
        except Exception:
            pass
    return results


def _r0141_fixingSubgroup_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.fixingSubgroup_bot
    # fixingSubgroup (⊥ : IntermediateField F E) = ⊤
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fixingSubgroup", 1)
    if args is not None:
        try:
            rhs = OVar("top")
            results.append((rhs, "Mathlib: IntermediateField_fixingSubgroup_bot"))
        except Exception:
            pass
    return results


def _r0142_fixingSubgroup_sup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.fixingSubgroup_sup
    # (K ⊔ L).fixingSubgroup = K.fixingSubgroup ⊓ L.fixingSubgroup
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("K_L_fixingSubgroup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("K_fixingSubgroup", (OVar("_unknown"), OVar("L_fixingSubgroup"),))
            results.append((rhs, "Mathlib: IntermediateField_fixingSubgroup_sup"))
    except Exception:
        pass
    return results


def _r0143_finrank_eq_finrank_subalgebra(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.finrank_eq_finrank_subalgebra
    # finrank K F.toSubalgebra = finrank K F
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finrank", 2)
    if args is not None:
        try:
            rhs = OOp("finrank", (args[0], OVar("F"),))
            results.append((rhs, "Mathlib: IntermediateField_finrank_eq_finrank_subalgebra"))
        except Exception:
            pass
    return results


def _r0144_coe_toSubfield(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.coe_toSubfield
    # (S.toSubfield : Set L) = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_toSubfield", 3)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: IntermediateField_coe_toSubfield"))
        except Exception:
            pass
    return results


def _r0145_coe_type_toSubalgebra(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.coe_type_toSubalgebra
    # (S.toSubalgebra : Type _) = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_toSubalgebra", 3)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: IntermediateField_coe_type_toSubalgebra"))
        except Exception:
            pass
    return results


def _r0146_coe_type_toSubfield(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.coe_type_toSubfield
    # (S.toSubfield : Type _) = S
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "S_toSubfield", 3)
    if args is not None:
        try:
            rhs = OVar("S")
            results.append((rhs, "Mathlib: IntermediateField_coe_type_toSubfield"))
        except Exception:
            pass
    return results


def _r0147_coe_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.coe_neg
    # (↑(-x) : L) = -↑x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus_x", 2)
    if args is not None:
        try:
            rhs = OVar("minus_x")
            results.append((rhs, "Mathlib: IntermediateField_coe_neg"))
        except Exception:
            pass
    return results


def _r0148_coe_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.coe_inv
    # (↑x⁻¹ : L) = (↑x)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "xinv", 2)
    if args is not None:
        try:
            rhs = OVar("x_inv")
            results.append((rhs, "Mathlib: IntermediateField_coe_inv"))
        except Exception:
            pass
    return results


def _r0149_range_val(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.range_val
    # S.val.range = S.toSubalgebra
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("S_val_range")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("S_toSubalgebra")
            results.append((rhs, "Mathlib: IntermediateField_range_val"))
    except Exception:
        pass
    return results


def _r0150_toSubfield_inj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.toSubfield_inj
    # F.toSubfield = E.toSubfield ↔ F = E
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("F_toSubfield")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("E_toSubfield"), OVar("F"))), OVar("E")))
            results.append((rhs, "Mathlib: IntermediateField_toSubfield_inj"))
    except Exception:
        pass
    return results


def _r0151_extendScalars_toSubfield(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: IntermediateField.extendScalars_toSubfield
    # (extendScalars h).toSubfield = E.toSubfield
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("extendScalars_h_toSubfield")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("E_toSubfield")
            results.append((rhs, "Mathlib: IntermediateField_extendScalars_toSubfield"))
    except Exception:
        pass
    return results


def _r0152_weightedVSub_vadd(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.weightedVSub_vadd
    # s.weightedVSub (v +ᵥ p) w = s.weightedVSub p w
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "s_weightedVSub", 2)
    if args is not None:
        try:
            rhs = OOp("s_weightedVSub", (OVar("p"), args[1],))
            results.append((rhs, "Mathlib: Finset_weightedVSub_vadd"))
        except Exception:
            pass
    return results


def _r0153_weightedVSubVSubWeights_apply_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.weightedVSubVSubWeights_apply_left
    # weightedVSubVSubWeights k i j i = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "weightedVSubVSubWeights", 4)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Finset_weightedVSubVSubWeights_apply_left"))
        except Exception:
            pass
    return results


def _r0154_weightedVSubVSubWeights_apply_right(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.weightedVSubVSubWeights_apply_right
    # weightedVSubVSubWeights k i j j = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "weightedVSubVSubWeights", 4)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Finset_weightedVSubVSubWeights_apply_right"))
        except Exception:
            pass
    return results


def _r0155_weightedVSubVSubWeights_apply_of_ne(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.weightedVSubVSubWeights_apply_of_ne
    # weightedVSubVSubWeights k i j t = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "weightedVSubVSubWeights", 4)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Finset_weightedVSubVSubWeights_apply_of_ne"))
        except Exception:
            pass
    return results


def _r0156_sum_weightedVSubVSubWeights(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.sum_weightedVSubVSubWeights
    # ∑ t ∈ s, weightedVSubVSubWeights k i j t = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Finset_sum_weightedVSubVSubWeights"))
        except Exception:
            pass
    return results


def _r0157_eq_properDivisors_of_subset_of_sum_eq_su(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Nat.eq_properDivisors_of_subset_of_sum_eq_sum
    # ((∑ x ∈ s, x) = ∑ x ∈ n.properDivisors, x) → s = n.properDivisors
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("s")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("n_properDivisors")
            results.append((rhs, "Mathlib: Nat_eq_properDivisors_of_subset_of_sum_eq_sum"))
    except Exception:
        pass
    return results


def _r0158_goldenRatio_pow_sub_goldenRatio_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.goldenRatio_pow_sub_goldenRatio_pow
    # φ ^ (n + 2) - φ ^ (n + 1) = φ ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("phi"), OVar("n")))
            results.append((rhs, "Mathlib: Real_goldenRatio_pow_sub_goldenRatio_pow"))
        except Exception:
            pass
    return results


def _r0159_prod_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.prod_inv
    # (f.prod fun a b => (h a b)⁻¹) = (f.prod h)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f_prod", 5)
    if args is not None:
        try:
            rhs = OVar("f_prod_h_inv")
            results.append((rhs, "Mathlib: Finsupp_prod_inv"))
        except Exception:
            pass
    return results


def _r0160_sum_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finsupp.sum_sub
    # (f.sum fun a b => h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("f_sum", (OVar("h_1"),)), OOp("f_sum", (OVar("h_2"),))))
            results.append((rhs, "Mathlib: Finsupp_sum_sub"))
        except Exception:
            pass
    return results


def _r0161_prod_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_subset
    # ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s_2", (OVar("f"), OVar("x"),))))
            results.append((rhs, "Mathlib: Finset_prod_subset"))
        except Exception:
            pass
    return results


def _r0162_prod_subtype_mul_prod_subtype(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.prod_subtype_mul_prod_subtype
    # (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("f"), OVar("i"),))
            results.append((rhs, "Mathlib: Fintype_prod_subtype_mul_prod_subtype"))
        except Exception:
            pass
    return results


def _r0163_prod_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.prod_subset
    # ∏ i ∈ s, f i = ∏ i, f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("_unknown", (OVar("i"), OVar("f"), OVar("i"),))
            results.append((rhs, "Mathlib: Fintype_prod_subset"))
        except Exception:
            pass
    return results


def _r0164_prod_mulIndicator_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_mulIndicator_subset
    # ∏ i ∈ t, mulIndicator (↑s) f i = ∏ i ∈ s, f i
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("i"),)), OOp("s", (OVar("f"), OVar("i"),))))
            results.append((rhs, "Mathlib: Finset_prod_mulIndicator_subset"))
        except Exception:
            pass
    return results


def _r0165_prod_Ico_add_right_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_Ico_add_right_sub_eq
    # ∏ x ∈ Ico (a + c) (b + c), f (x - c) = ∏ x ∈ Ico a b, f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("Ico", (OVar("a"), OVar("b"), OVar("f"), OVar("x"),))))
            results.append((rhs, "Mathlib: Finset_prod_Ico_add_right_sub_eq"))
        except Exception:
            pass
    return results


def _r0166_prod_antidiagonal_subst(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.Nat.prod_antidiagonal_subst
    # ∏ p ∈ antidiagonal n, f p n = ∏ p ∈ antidiagonal n, f p (p.1 + p.2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("p"),)), OOp("antidiagonal", (OVar("n"), OVar("f"), OVar("p"), OOp("+", (OVar("p_1"), OVar("p_2"))),))))
            results.append((rhs, "Mathlib: Finset_Nat_prod_antidiagonal_subst"))
        except Exception:
            pass
    return results


def _r0167_prod_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.prod_neg
    # ∏ x ∈ s, -f x = (-1) ^ #s * ∏ x ∈ s, f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("hash_s"))), OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("s", (OVar("f"), OVar("x"),))))))
            results.append((rhs, "Mathlib: Finset_prod_neg"))
        except Exception:
            pass
    return results


def _r0168_gcd_eq_of_dvd_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.gcd_eq_of_dvd_sub
    # GCDMonoid.gcd a (s.gcd f) = GCDMonoid.gcd a (s.gcd g)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "GCDMonoid_gcd", 2)
    if args is not None:
        try:
            rhs = OOp("GCDMonoid_gcd", (args[0], OOp("s_gcd", (OVar("g"),)),))
            results.append((rhs, "Mathlib: Finset_gcd_eq_of_dvd_sub"))
        except Exception:
            pass
    return results


def _r0169_normalize_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.normalize_of_nonneg
    # normalize z = z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Int_normalize_of_nonneg"))
        except Exception:
            pass
    return results


def _r0170_nonneg_iff_normalize_eq_self(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.nonneg_iff_normalize_eq_self
    # normalize z = z ↔ 0 ≤ z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "normalize", 1)
    if args is not None:
        try:
            rhs = OOp("<=", (OOp("iff", (args[0], OLit(0))), args[0]))
            results.append((rhs, "Mathlib: Int_nonneg_iff_normalize_eq_self"))
        except Exception:
            pass
    return results


def _r0171_rev_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fin.rev_sub
    # rev (a - b) = rev a + b
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "rev", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("rev", (OVar("a"),)), OVar("b")))
            results.append((rhs, "Mathlib: Fin_rev_sub"))
        except Exception:
            pass
    return results


def _r0172_units_natAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.units_natAbs
    # natAbs u = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "abs", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Int_units_natAbs"))
        except Exception:
            pass
    return results


def _r0173_natAbs_of_isUnit(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.natAbs_of_isUnit
    # natAbs u = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "abs", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Int_natAbs_of_isUnit"))
        except Exception:
            pass
    return results


def _r0174_isUnit_ne_iff_eq_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.isUnit_ne_iff_eq_neg
    # u ≠ v ↔ u = -v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OVar("minus_v")
            results.append((rhs, "Mathlib: Int_isUnit_ne_iff_eq_neg"))
        except Exception:
            pass
    return results


def _r0175_isUnit_eq_or_eq_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.isUnit_eq_or_eq_neg
    # u = v ∨ u = -v
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("u")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("or", (OVar("v"), OVar("u"))), OVar("minus_v")))
            results.append((rhs, "Mathlib: Int_isUnit_eq_or_eq_neg"))
    except Exception:
        pass
    return results


def _r0176_piFinset_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Fintype.piFinset_inv
    # piFinset (fun i ↦ (s i)⁻¹) = (piFinset s)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "piFinset", 1)
    if args is not None:
        try:
            rhs = OVar("piFinset_s_inv")
            results.append((rhs, "Mathlib: Fintype_piFinset_inv"))
        except Exception:
            pass
    return results


def _r0177_dens_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.dens_inv
    # s⁻¹.dens = s.dens
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("sinv_dens")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("s_dens")
            results.append((rhs, "Mathlib: Finset_dens_inv"))
    except Exception:
        pass
    return results


def _r0178_toFinset_vsub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finite.toFinset_vsub
    # hf.toFinset = hs.toFinset -ᵥ ht.toFinset
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("hf_toFinset")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("hs_toFinset", (OVar("minus"), OVar("ht_toFinset"),))
            results.append((rhs, "Mathlib: Finite_toFinset_vsub"))
    except Exception:
        pass
    return results


def _r0179_f_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ComplexShape.Embedding.liftExtend.f_eq
    # f φ i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 2)
    if args is not None:
        try:
            rhs = OOp("K_restrictionXIso_e_hi_inv", (OVar("_unknown"), OVar("phi_f"), OVar("i"), OVar("_unknown"), OVar("L_extendXIso_e_hi_inv"),))
            results.append((rhs, "Mathlib: ComplexShape_Embedding_liftExtend_f_eq"))
        except Exception:
            pass
    return results


def _r0180_liftExtend_f(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ComplexShape.Embedding.liftExtend_f
    # (e.liftExtend φ hφ).f i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫       (L.extendXIso e hi).inv
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "e_liftExtend_phi_hphi_f", 1)
    if args is not None:
        try:
            rhs = OOp("K_restrictionXIso_e_hi_inv", (OVar("_unknown"), OVar("phi_f"), OVar("i"), OVar("_unknown"), OVar("L_extendXIso_e_hi_inv"),))
            results.append((rhs, "Mathlib: ComplexShape_Embedding_liftExtend_f"))
        except Exception:
            pass
    return results


def _r0181_finsuppAntidiag_insert(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.finsuppAntidiag_insert
    # finsuppAntidiag (insert a s) n = (antidiagonal n).biUnion       (fun p : μ × μ =>         (finsuppAntidiag s p.snd).atta
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "finsuppAntidiag", 2)
    if args is not None:
        try:
            rhs = OOp("antidiagonal_n_biUnion", (OOp("product", (OOp("fun", (OVar("p"), OVar("colon"), OVar("mu"),)), OOp("mu", (OVar("eq_gt"), OVar("finsuppAntidiag_s_p_snd_attach_map"), OVar("fun_f_eq_gt_Finsupp_update_f_val_a_p_fst_fun_f_hf_g_hg_hfg_eq_gt_Subtype_ext_lt_pipe_by_simp_only_mem_finsuppAntidiag_at_hf_hg_simp_only_DFunLike_ext_iff_at_hfg_intro_x_obtain_rfl_pipe_hx_colon_eq_eq_or_ne_x_a_replace_hf_colon_eq_mt_hf_2_h_replace_hg_colon_eq_mt_hg_2_h_rw_notMem_support_iff_mp_hf_notMem_support_iff_mp_hg_simpa_only_coe_update_Function_update_dif_neg_hx_using_hfg_x"),)))),))
            results.append((rhs, "Mathlib: Finset_finsuppAntidiag_insert"))
        except Exception:
            pass
    return results


def _r0182_antidiagonal_subtype_ext(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.antidiagonal_subtype_ext
    # p = q
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("p")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("q")
            results.append((rhs, "Mathlib: Finset_antidiagonal_subtype_ext"))
    except Exception:
        pass
    return results


def _r0183_mk_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FiniteMulArchimedeanClass.mk_inv
    # mk a⁻¹ (by simp [ha]) = mk a ha
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OOp("pair", (OVar("a"), OVar("ha"),))
            results.append((rhs, "Mathlib: FiniteMulArchimedeanClass_mk_inv"))
        except Exception:
            pass
    return results


def _r0184_subsemigroup_eq_subgroup(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FiniteMulArchimedeanClass.subsemigroup_eq_subgroup
    # MulArchimedeanClass.subsemigroup (toUpperSetMulArchimedeanClass s) = (subgroup s : Set M)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "MulArchimedeanClass_subsemigroup", 1)
    if args is not None:
        try:
            rhs = OOp("subgroup", (OVar("s"), OVar("colon"), OVar("Set"), OVar("M"),))
            results.append((rhs, "Mathlib: FiniteMulArchimedeanClass_subsemigroup_eq_subgroup"))
        except Exception:
            pass
    return results


def _r0185_subgroup_eq_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FiniteMulArchimedeanClass.subgroup_eq_bot
    # subgroup (M := M) ⊤ = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "subgroup", 2)
    if args is not None:
        try:
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: FiniteMulArchimedeanClass_subgroup_eq_bot"))
        except Exception:
            pass
    return results


def _r0186_floor_sub_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.floor_sub_intCast
    # ⌊a - z⌋ = ⌊a⌋ - z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: Int_floor_sub_intCast"))
        except Exception:
            pass
    return results


def _r0187_abs_eq_natAbs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.abs_eq_natAbs
    # ∀ a : ℤ, |a| = natAbs a   | (n : ℕ) => abs_of_nonneg <| natCast_nonneg _   | -[_+1] => abs_of_nonpos <| le_of_lt <| negS
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_apipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("abs", (OVar("a"), OVar("pipe"), OOp("n", (OVar("colon"), OVar("_unknown"),)), OVar("eq_gt"), OVar("abs_of_nonneg"), OVar("lt_pipe"), OVar("natCast_nonneg"), OVar("_unknown"), OVar("pipe"), OVar("minus_plus_1"), OVar("eq_gt"), OVar("abs_of_nonpos"), OVar("lt_pipe"), OVar("le_of_lt"), OVar("lt_pipe"), OVar("negSucc_lt_zero"), OVar("at_norm_cast"), OVar("lemma"), OVar("natCast_natAbs"), OOp("n", (OVar("colon"), OVar("_unknown"),)), OVar("colon"), OOp("n_natAbs", (OVar("colon"), OVar("_unknown"),)),)), OVar("pipe_npipe")))
            results.append((rhs, "Mathlib: Int_abs_eq_natAbs"))
    except Exception:
        pass
    return results


def _r0188_natAbs_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.natAbs_abs
    # natAbs |a| = natAbs a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "abs", 1)
    if args is not None:
        try:
            rhs = OOp("abs", (OVar("a"),))
            results.append((rhs, "Mathlib: Int_natAbs_abs"))
        except Exception:
            pass
    return results


def _r0189_sign_mul_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.sign_mul_abs
    # sign a * |a| = a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("a")
            results.append((rhs, "Mathlib: Int_sign_mul_abs"))
        except Exception:
            pass
    return results


def _r0190_sign_mul_self_eq_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.sign_mul_self_eq_abs
    # sign a * a = |a|
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OVar("pipe_apipe")
            results.append((rhs, "Mathlib: Int_sign_mul_self_eq_abs"))
        except Exception:
            pass
    return results


def _r0191_bot_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.bot_sub
    # ⊥ - t = ⊥
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Interval_bot_sub"))
        except Exception:
            pass
    return results


def _r0192_inv_bot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Interval.inv_bot
    # (⊥ : Interval α)⁻¹ = ⊥
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("bot_colon_Interval_a_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("bot")
            results.append((rhs, "Mathlib: Interval_inv_bot"))
    except Exception:
        pass
    return results


def _r0193_toAddSubgroup_ball(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: FiniteArchimedeanClass.toAddSubgroup_ball
    # (ball K c).toAddSubgroup = ballAddSubgroup c
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("ball_K_c_toAddSubgroup")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ballAddSubgroup", (OVar("c"),))
            results.append((rhs, "Mathlib: FiniteArchimedeanClass_toAddSubgroup_ball"))
    except Exception:
        pass
    return results


def _r0194_cast_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.cast_nonneg
    # ∀ {n : ℤ}, 0 ≤ n → (0 : R) ≤ n | (n : ℕ), _ =>
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("gt")
            results.append((rhs, "Mathlib: Int_cast_nonneg"))
        except Exception:
            pass
    return results


def _r0195_mk_sub_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.mk_sub_mk
    # .mk x hx - .mk y hy = FiniteElement.mk (x - y) ((le_min hx hy).trans <| min_le_mk_sub ..)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("FiniteElement_mk", (OOp("-", (OVar("x"), OVar("y"))), OOp("le_min_hx_hy_trans", (OVar("lt_pipe"), OVar("min_le_mk_sub"), OVar("_unknown"),)),))
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_mk_sub_mk"))
        except Exception:
            pass
    return results


def _r0196_mk_mul_mk(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.mk_mul_mk
    # .mk x hx * .mk y hy = FiniteElement.mk (x * y) (add_nonneg hx hy)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("FiniteElement_mk", (OOp("*", (OVar("x"), OVar("y"))), OOp("add_nonneg", (OVar("hx"), OVar("hy"),)),))
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_mk_mul_mk"))
        except Exception:
            pass
    return results


def _r0197_mk_ratCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: ArchimedeanClass.FiniteElement.mk_ratCast
    # FiniteElement.mk (q : K) (mk_ratCast_nonneg q) = q
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "FiniteElement_mk", 2)
    if args is not None:
        try:
            rhs = OVar("q")
            results.append((rhs, "Mathlib: ArchimedeanClass_FiniteElement_mk_ratCast"))
        except Exception:
            pass
    return results


def _r0198_abs_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.abs_def
    # |q| = q.num.natAbs /. q.den
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_qpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("q_num_natAbs", (OVar("slash"), OVar("q_den"),))
            results.append((rhs, "Mathlib: Rat_abs_def"))
    except Exception:
        pass
    return results


def _r0199_num_abs_eq_abs_num(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Rat.num_abs_eq_abs_num
    # |q|.num = |q.num|
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_qpipe_num")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("pipe_q_numpipe")
            results.append((rhs, "Mathlib: Rat_num_abs_eq_abs_num"))
    except Exception:
        pass
    return results


def _r0200_units_ne_iff_eq_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Int.units_ne_iff_eq_neg
    # u ≠ v ↔ u = -v
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "!=", 2)
    if args is not None:
        try:
            rhs = OVar("minus_v")
            results.append((rhs, "Mathlib: Int_units_ne_iff_eq_neg"))
        except Exception:
            pass
    return results


def _r0201_norm_eq_norm_of_isMaxOn_of_ball_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_eq_norm_of_isMaxOn_of_ball_subset
    # ‖f w‖ = ‖f z‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("z"),))
            results.append((rhs, "Mathlib: Complex_norm_eq_norm_of_isMaxOn_of_ball_subset"))
        except Exception:
            pass
    return results


def _r0202_eq_of_isMaxOn_of_ball_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.eq_of_isMaxOn_of_ball_subset
    # f w = f z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "f", 1)
    if args is not None:
        try:
            rhs = OOp("f", (OVar("z"),))
            results.append((rhs, "Mathlib: Complex_eq_of_isMaxOn_of_ball_subset"))
        except Exception:
            pass
    return results


def _r0203_norm_sub_eq_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_sub_eq_iff
    # ‖x - y‖ = |‖x‖ - ‖y‖| ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("-", (OVar("pipe_x"), OVar("y_pipe"))), args[0])), OOp("==", (OOp("or", (OLit(0), args[1])), OOp("==", (OOp("or", (OLit(0), OVar("x_arg"))), OVar("y_arg")))))))
            results.append((rhs, "Mathlib: Complex_norm_sub_eq_iff"))
        except Exception:
            pass
    return results


def _r0204_norm_sub_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_sub_eq
    # ‖x - y‖ = ‖‖x‖ - ‖y‖‖
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (args[0], args[1]))
            results.append((rhs, "Mathlib: Complex_norm_sub_eq"))
        except Exception:
            pass
    return results


def _r0205_isBigO_re_sub_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.isBigO_re_sub_re
    # (fun (w : ℂ) ↦ w.re - z.re) =O[𝓝 z] fun w ↦ w - z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("O_z", (OVar("fun"), OVar("w"), OVar("_unknown"), OVar("w"),)), OVar("z")))
            results.append((rhs, "Mathlib: Complex_isBigO_re_sub_re"))
        except Exception:
            pass
    return results


def _r0206_isBigO_im_sub_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.isBigO_im_sub_im
    # (fun (w : ℂ) ↦ w.im - z.im) =O[𝓝 z] fun w ↦ w - z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("O_z", (OVar("fun"), OVar("w"), OVar("_unknown"), OVar("w"),)), OVar("z")))
            results.append((rhs, "Mathlib: Complex_isBigO_im_sub_im"))
        except Exception:
            pass
    return results


def _r0207_inv_eq_conj(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.inv_eq_conj
    # z⁻¹ = conj z
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("zinv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("conj", (OVar("z"),))
            results.append((rhs, "Mathlib: Complex_inv_eq_conj"))
    except Exception:
        pass
    return results


def _r0208_eq_coe_norm_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.eq_coe_norm_of_nonneg
    # z = ↑‖z‖
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("z")
            results.append((rhs, "Mathlib: Complex_eq_coe_norm_of_nonneg"))
    except Exception:
        pass
    return results


def _r0209_exp_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.exp_sub
    # exp (x - y) = exp x / exp y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("exp", (OVar("x"),)), OOp("exp", (OVar("y"),))))
            results.append((rhs, "Mathlib: Complex_exp_sub"))
        except Exception:
            pass
    return results


def _r0210_exp_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.exp_sub
    # exp (x - y) = exp x / exp y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("exp", (OVar("x"),)), OOp("exp", (OVar("y"),))))
            results.append((rhs, "Mathlib: Real_exp_sub"))
        except Exception:
            pass
    return results


def _r0211_abs_exp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.abs_exp
    # |exp x| = exp x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pipe_exp", 1)
    if args is not None:
        try:
            rhs = OOp("exp", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_abs_exp"))
        except Exception:
            pass
    return results


def _r0212_expNear_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.expNear_sub
    # expNear n x r₁ -     expNear n x r₂ = x ^ n / n.factorial * (r₁ - r₂)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("//", (OOp("**", (OVar("x"), OVar("n"))), OVar("n_factorial"))), OOp("-", (OVar("r_1"), OVar("r_2")))))
            results.append((rhs, "Mathlib: Real_expNear_sub"))
        except Exception:
            pass
    return results


def _r0213_norm_invInterpStrip(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.HadamardThreeLines.norm_invInterpStrip
    # ‖invInterpStrip f z ε‖ =     (ε + sSupNormIm f 0) ^ (z.re - 1) * (ε + sSupNormIm f 1) ^ (-z.re)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "invInterpStrip", 3)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OOp("+", (args[2], OOp("sSupNormIm", (args[0], OLit(0),)))), OOp("-", (OVar("z_re"), OLit(1))))), OOp("**", (OOp("+", (args[2], OOp("sSupNormIm", (args[0], OLit(1),)))), OVar("minus_z_re")))))
            results.append((rhs, "Mathlib: Complex_HadamardThreeLines_norm_invInterpStrip"))
        except Exception:
            pass
    return results


def _r0214_cderiv_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cderiv_sub
    # cderiv r (f - g) z = cderiv r f z - cderiv r g z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cderiv", 3)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("cderiv", (args[0], OVar("f"), args[2],)), OOp("cderiv", (args[0], OVar("g"), args[2],))))
            results.append((rhs, "Mathlib: Complex_cderiv_sub"))
        except Exception:
            pass
    return results


def _r0215_sq_norm_sub_sq_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sq_norm_sub_sq_re
    # ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("z_im"), OLit(2)))
            results.append((rhs, "Mathlib: Complex_sq_norm_sub_sq_re"))
        except Exception:
            pass
    return results


def _r0216_nonneg_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.nonneg_iff
    # 0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OVar("z_im")
            results.append((rhs, "Mathlib: Complex_nonneg_iff"))
        except Exception:
            pass
    return results


def _r0217_neg_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.neg_iff
    # z < 0 ↔ z.re < 0 ∧ z.im = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_neg_iff"))
        except Exception:
            pass
    return results


def _r0218_sq_nonneg_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sq_nonneg_iff
    # 0 ≤ z ^ 2 ↔ z.im = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_sq_nonneg_iff"))
        except Exception:
            pass
    return results


def _r0219_neg_re_eq_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.neg_re_eq_norm
    # -z.re = ‖z‖ ↔ z ≤ 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_z_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("iff", (OVar("z"), OVar("z"))), OLit(0)))
            results.append((rhs, "Mathlib: Complex_neg_re_eq_norm"))
    except Exception:
        pass
    return results


def _r0220_re_eq_neg_norm(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.re_eq_neg_norm
    # z.re = -‖z‖ ↔ z ≤ 0
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("z_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("iff", (OVar("minus_z"), OVar("z"))), OLit(0)))
            results.append((rhs, "Mathlib: Complex_re_eq_neg_norm"))
    except Exception:
        pass
    return results


def _r0221_two_pi_I_inv_smul_circleIntegral_sub_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
    # ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), ((z - w₀) ^ 2)⁻¹ • f z) = deriv f w₀
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_2_star_pi_star_I_colon_inv", 9)
    if args is not None:
        try:
            rhs = OOp("deriv", (args[7], OVar("w_0"),))
            results.append((rhs, "Mathlib: Complex_two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable"))
        except Exception:
            pass
    return results


def _r0222_sinh_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sinh_sub
    # sinh (x - y) = sinh x * cosh y - cosh x * sinh y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sinh", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("sinh", (OVar("x"),)), OOp("*", (OOp("-", (OOp("cosh", (OVar("y"),)), OOp("cosh", (OVar("x"),)))), OOp("sinh", (OVar("y"),))))))
            results.append((rhs, "Mathlib: Complex_sinh_sub"))
        except Exception:
            pass
    return results


def _r0223_cosh_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cosh_sub
    # cosh (x - y) = cosh x * cosh y - sinh x * sinh y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cosh", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("cosh", (OVar("x"),)), OOp("*", (OOp("-", (OOp("cosh", (OVar("y"),)), OOp("sinh", (OVar("x"),)))), OOp("sinh", (OVar("y"),))))))
            results.append((rhs, "Mathlib: Complex_cosh_sub"))
        except Exception:
            pass
    return results


def _r0224_sin_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_sub
    # sin (x - y) = sin x * cos y - cos x * sin y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("sin", (OVar("x"),)), OOp("*", (OOp("-", (OOp("cos", (OVar("y"),)), OOp("cos", (OVar("x"),)))), OOp("sin", (OVar("y"),))))))
            results.append((rhs, "Mathlib: Complex_sin_sub"))
        except Exception:
            pass
    return results


def _r0225_cos_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_sub
    # cos (x - y) = cos x * cos y + sin x * sin y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (OOp("cos", (OVar("x"),)), OOp("cos", (OVar("y"),)))), OOp("*", (OOp("sin", (OVar("x"),)), OOp("sin", (OVar("y"),))))))
            results.append((rhs, "Mathlib: Complex_cos_sub"))
        except Exception:
            pass
    return results


def _r0226_sin_sub_sin(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_sub_sin
    # sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OLit(2), OOp("*", (OOp("sin", (OOp("//", (OOp("-", (OVar("x"), OVar("y"))), OLit(2))),)), OOp("cos", (OOp("//", (OOp("+", (OVar("x"), OVar("y"))), OLit(2))),))))))
            results.append((rhs, "Mathlib: Complex_sin_sub_sin"))
        except Exception:
            pass
    return results


def _r0227_cos_sub_cos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_sub_cos
    # cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("minus_2"), OOp("*", (OOp("sin", (OOp("//", (OOp("+", (OVar("x"), OVar("y"))), OLit(2))),)), OOp("sin", (OOp("//", (OOp("-", (OVar("x"), OVar("y"))), OLit(2))),))))))
            results.append((rhs, "Mathlib: Complex_cos_sub_cos"))
        except Exception:
            pass
    return results


def _r0228_tan_inv_eq_cot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tan_inv_eq_cot
    # (tan x)⁻¹ = cot x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("tan_x_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("cot", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_tan_inv_eq_cot"))
    except Exception:
        pass
    return results


def _r0229_cos_sub_sin_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cos_sub_sin_I
    # cos x - sin x * I = exp (-x * I)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (OOp("*", (OVar("minus_x"), args[1])),))
            results.append((rhs, "Mathlib: Complex_cos_sub_sin_I"))
        except Exception:
            pass
    return results


def _r0230_sin_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_sub
    # sin (x - y) = sin x * cos y - cos x * sin y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("sin", (OVar("x"),)), OOp("*", (OOp("-", (OOp("cos", (OVar("y"),)), OOp("cos", (OVar("x"),)))), OOp("sin", (OVar("y"),))))))
            results.append((rhs, "Mathlib: Real_sin_sub"))
        except Exception:
            pass
    return results


def _r0231_cos_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_sub
    # cos (x - y) = cos x * cos y + sin x * sin y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (OOp("cos", (OVar("x"),)), OOp("cos", (OVar("y"),)))), OOp("*", (OOp("sin", (OVar("x"),)), OOp("sin", (OVar("y"),))))))
            results.append((rhs, "Mathlib: Real_cos_sub"))
        except Exception:
            pass
    return results


def _r0232_tan_inv_eq_cot(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tan_inv_eq_cot
    # (tan x)⁻¹ = cot x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("tan_x_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("cot", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_tan_inv_eq_cot"))
    except Exception:
        pass
    return results


def _r0233_sin_sq_eq_half_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_sq_eq_half_sub
    # sin x ^ 2 = 1 / 2 - cos (2 * x) / 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("//", (OLit(1), OLit(2))), OOp("//", (OOp("cos", (OOp("*", (OLit(2), OVar("x"))),)), OLit(2)))))
            results.append((rhs, "Mathlib: Real_sin_sq_eq_half_sub"))
        except Exception:
            pass
    return results


def _r0234_sinh_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sinh_sub
    # sinh (x - y) = sinh x * cosh y - cosh x * sinh y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sinh", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("sinh", (OVar("x"),)), OOp("*", (OOp("-", (OOp("cosh", (OVar("y"),)), OOp("cosh", (OVar("x"),)))), OOp("sinh", (OVar("y"),))))))
            results.append((rhs, "Mathlib: Real_sinh_sub"))
        except Exception:
            pass
    return results


def _r0235_cosh_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cosh_sub
    # cosh (x - y) = cosh x * cosh y - sinh x * sinh y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cosh", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("cosh", (OVar("x"),)), OOp("*", (OOp("-", (OOp("cosh", (OVar("y"),)), OOp("sinh", (OVar("x"),)))), OOp("sinh", (OVar("y"),))))))
            results.append((rhs, "Mathlib: Real_cosh_sub"))
        except Exception:
            pass
    return results


def _r0236_sinh_sub_cosh(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sinh_sub_cosh
    # sinh x - cosh x = -exp (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("minus_exp", (OVar("minus_x"),))
            results.append((rhs, "Mathlib: Real_sinh_sub_cosh"))
        except Exception:
            pass
    return results


def _r0237_mk_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.mk_neg
    # mk (-z) hz = -mk z (norm_neg z ▸ hz)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pair", 2)
    if args is not None:
        try:
            rhs = OOp("minus_mk", (OVar("z"), OOp("subst", (OOp("norm_neg", (OVar("z"),)), args[1])),))
            results.append((rhs, "Mathlib: Complex_UnitDisc_mk_neg"))
        except Exception:
            pass
    return results


def _r0238_star_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.UnitDisc.star_neg
    # star (-z) = -(star z)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "star", 1)
    if args is not None:
        try:
            rhs = OVar("minus_star_z")
            results.append((rhs, "Mathlib: Complex_UnitDisc_star_neg"))
        except Exception:
            pass
    return results


def _r0239_centerMass_neg_left(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.centerMass_neg_left
    # t.centerMass (-w) z = t.centerMass w z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "t_centerMass", 2)
    if args is not None:
        try:
            rhs = OOp("t_centerMass", (OVar("w"), args[1],))
            results.append((rhs, "Mathlib: Finset_centerMass_neg_left"))
        except Exception:
            pass
    return results


def _r0240_centerMass_subset(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Finset.centerMass_subset
    # t.centerMass w z = t'.centerMass w z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "t_centerMass", 2)
    if args is not None:
        try:
            rhs = OOp("t_prime_centerMass", (args[0], args[1],))
            results.append((rhs, "Mathlib: Finset_centerMass_subset"))
        except Exception:
            pass
    return results


def _r0241_fderiv_fourierChar_neg_bilinear_right_ap(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.fderiv_fourierChar_neg_bilinear_right_apply
    # fderiv ℝ (fun w ↦ (𝐞 (-L v w) : ℂ)) w y = -2 * π * I * L v y * 𝐞 (-L v w)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderiv", 4)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("minus_2"), OOp("*", (OVar("pi"), OOp("*", (OVar("I"), OOp("*", (OOp("L", (OVar("v"), args[3],)), OOp("_unknown", (OOp("minus_L", (OVar("v"), args[2],)),))))))))))
            results.append((rhs, "Mathlib: Real_fderiv_fourierChar_neg_bilinear_right_apply"))
        except Exception:
            pass
    return results


def _r0242_fderiv_fourierChar_neg_bilinear_left_app(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.fderiv_fourierChar_neg_bilinear_left_apply
    # fderiv ℝ (fun v ↦ (𝐞 (-L v w) : ℂ)) v y = -2 * π * I * L y w * 𝐞 (-L v w)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "fderiv", 4)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("minus_2"), OOp("*", (OVar("pi"), OOp("*", (OVar("I"), OOp("*", (OOp("L", (args[3], OVar("w"),)), OOp("_unknown", (OOp("minus_L", (args[2], OVar("w"),)),))))))))))
            results.append((rhs, "Mathlib: Real_fderiv_fourierChar_neg_bilinear_left_apply"))
        except Exception:
            pass
    return results


def _r0243_norm_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.norm_of_nonneg
    # ‖r‖ = r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("r")
            results.append((rhs, "Mathlib: Real_norm_of_nonneg"))
    except Exception:
        pass
    return results


def _r0244_nnnorm_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.nnnorm_of_nonneg
    # ‖r‖₊ = .mk r hr
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("mk", (OVar("r"), OVar("hr"),))
            results.append((rhs, "Mathlib: Real_nnnorm_of_nonneg"))
    except Exception:
        pass
    return results


def _r0245_enorm_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.enorm_of_nonneg
    # ‖r‖ₑ = .ofReal r
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("ofReal", (OVar("r"),))
            results.append((rhs, "Mathlib: Real_enorm_of_nonneg"))
    except Exception:
        pass
    return results


def _r0246_enorm_ofReal_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.enorm_ofReal_of_nonneg
    # ‖ENNReal.ofReal a‖ₑ = ‖a‖ₑ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "ENNReal_ofReal", 1)
    if args is not None:
        try:
            rhs = args[0]
            results.append((rhs, "Mathlib: Real_enorm_ofReal_of_nonneg"))
        except Exception:
            pass
    return results


def _r0247_toNNReal_eq_nnnorm_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.toNNReal_eq_nnnorm_of_nonneg
    # r.toNNReal = ‖r‖₊
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("r_toNNReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("r")
            results.append((rhs, "Mathlib: Real_toNNReal_eq_nnnorm_of_nonneg"))
    except Exception:
        pass
    return results


def _r0248_iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg
    # ⨆ a : ι × ι', v (x a.1 * y a.2) = (⨆ i, v (x i)) * ⨆ j, v (y j)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "product", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("_unknown", (OVar("i"), OVar("v"), OOp("x", (OVar("i"),)),)), OOp("_unknown", (OVar("j"), OVar("v"), OOp("y", (OVar("j"),)),))))
            results.append((rhs, "Mathlib: Real_iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg"))
        except Exception:
            pass
    return results


def _r0249_sqrt_neg_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sqrt_neg_of_nonneg
    # (-a).sqrt = I * a.sqrt
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_a_sqrt")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OVar("I"), OVar("a_sqrt")))
            results.append((rhs, "Mathlib: Complex_sqrt_neg_of_nonneg"))
    except Exception:
        pass
    return results


def _r0250_sqrt_neg_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sqrt_neg_I
    # sqrt (-I : ℂ) = √2⁻¹ * (1 - I)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sqrt", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("_2inv"), OOp("-", (OLit(1), OVar("I")))))
            results.append((rhs, "Mathlib: Complex_sqrt_neg_I"))
        except Exception:
            pass
    return results


def _r0251_arg_ofReal_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_ofReal_of_nonneg
    # arg x = 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OLit(0)
            results.append((rhs, "Mathlib: Complex_arg_ofReal_of_nonneg"))
        except Exception:
            pass
    return results


def _r0252_arg_ofReal_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_ofReal_of_neg
    # arg x = π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OVar("pi")
            results.append((rhs, "Mathlib: Complex_arg_ofReal_of_neg"))
        except Exception:
            pass
    return results


def _r0253_arg_eq_neg_pi_div_two_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_eq_neg_pi_div_two_iff
    # arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("minus_pi_slash_2"), OVar("z_re"))), OOp("<", (OOp("and", (OLit(0), OVar("z_im"))), OLit(0)))))
            results.append((rhs, "Mathlib: Complex_arg_eq_neg_pi_div_two_iff"))
        except Exception:
            pass
    return results


def _r0254_arg_of_re_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_of_re_nonneg
    # arg x = Real.arcsin (x.im / ‖x‖)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("Real_arcsin", (OOp("//", (OVar("x_im"), args[0])),))
            results.append((rhs, "Mathlib: Complex_arg_of_re_nonneg"))
        except Exception:
            pass
    return results


def _r0255_arg_of_re_neg_of_im_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_of_re_neg_of_im_nonneg
    # arg x = Real.arcsin ((-x).im / ‖x‖) + π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("Real_arcsin", (OOp("//", (OVar("minus_x_im"), args[0])),)), OVar("pi")))
            results.append((rhs, "Mathlib: Complex_arg_of_re_neg_of_im_nonneg"))
        except Exception:
            pass
    return results


def _r0256_arg_of_re_neg_of_im_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_of_re_neg_of_im_neg
    # arg x = Real.arcsin ((-x).im / ‖x‖) - π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("Real_arcsin", (OOp("//", (OVar("minus_x_im"), args[0])),)), OVar("pi")))
            results.append((rhs, "Mathlib: Complex_arg_of_re_neg_of_im_neg"))
        except Exception:
            pass
    return results


def _r0257_arg_of_im_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_of_im_neg
    # arg z = -Real.arccos (z.re / ‖z‖)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("minus_Real_arccos", (OOp("//", (OVar("z_re"), args[0])),))
            results.append((rhs, "Mathlib: Complex_arg_of_im_neg"))
        except Exception:
            pass
    return results


def _r0258_arg_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_inv
    # arg x⁻¹ = if arg x = π then π else -arg x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (OVar("arg"), OVar("x"),)), OOp("pi", (OVar("then"), OVar("pi"), OVar("else"), OVar("minus_arg"), OVar("x"),))))
            results.append((rhs, "Mathlib: Complex_arg_inv"))
        except Exception:
            pass
    return results


def _r0259_abs_arg_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.abs_arg_inv
    # |x⁻¹.arg| = |x.arg|
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_xinv_argpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("pipe_x_argpipe")
            results.append((rhs, "Mathlib: Complex_abs_arg_inv"))
    except Exception:
        pass
    return results


def _r0260_arg_neg_eq_arg_add_pi_of_im_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_neg_eq_arg_add_pi_of_im_neg
    # arg (-x) = arg x + π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("arg", (OVar("x"),)), OVar("pi")))
            results.append((rhs, "Mathlib: Complex_arg_neg_eq_arg_add_pi_of_im_neg"))
        except Exception:
            pass
    return results


def _r0261_arg_neg_eq_arg_sub_pi_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_neg_eq_arg_sub_pi_iff
    # arg (-x) = arg x - π ↔ 0 < x.im ∨ x.im = 0 ∧ x.re < 0
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("<", (OOp("iff", (OOp("-", (OOp("arg", (OVar("x"),)), OVar("pi"))), OLit(0))), OOp("or", (OVar("x_im"), OVar("x_im"))))), OOp("<", (OOp("and", (OLit(0), OVar("x_re"))), OLit(0)))))
            results.append((rhs, "Mathlib: Complex_arg_neg_eq_arg_sub_pi_iff"))
        except Exception:
            pass
    return results


def _r0262_arg_neg_eq_arg_add_pi_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_neg_eq_arg_add_pi_iff
    # arg (-x) = arg x + π ↔ x.im < 0 ∨ x.im = 0 ∧ 0 < x.re
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("<", (OOp("iff", (OOp("+", (OOp("arg", (OVar("x"),)), OVar("pi"))), OVar("x_im"))), OOp("or", (OLit(0), OVar("x_im"))))), OOp("<", (OOp("and", (OLit(0), OLit(0))), OVar("x_re")))))
            results.append((rhs, "Mathlib: Complex_arg_neg_eq_arg_add_pi_iff"))
        except Exception:
            pass
    return results


def _r0263_arg_neg_coe_angle(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_neg_coe_angle
    # (arg (-x) : Real.Angle) = arg x + π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arg", 3)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("arg", (OVar("x"),)), OVar("pi")))
            results.append((rhs, "Mathlib: Complex_arg_neg_coe_angle"))
        except Exception:
            pass
    return results


def _r0264_arg_mul_cos_add_sin_mul_I_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_mul_cos_add_sin_mul_I_sub
    # arg (r * (cos θ + sin θ * I)) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OLit(2), OOp("*", (OVar("pi"), OOp("//", (OVar("pi_minus_th"), OVar("_2_star_pi")))))))
            results.append((rhs, "Mathlib: Complex_arg_mul_cos_add_sin_mul_I_sub"))
        except Exception:
            pass
    return results


def _r0265_arg_cos_add_sin_mul_I_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.arg_cos_add_sin_mul_I_sub
    # arg (cos θ + sin θ * I) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OLit(2), OOp("*", (OVar("pi"), OOp("//", (OVar("pi_minus_th"), OVar("_2_star_pi")))))))
            results.append((rhs, "Mathlib: Complex_arg_cos_add_sin_mul_I_sub"))
        except Exception:
            pass
    return results


def _r0266_log_exp_eq_sub_toIocDiv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_exp_eq_sub_toIocDiv
    # log (exp x) = x - (toIocDiv Real.two_pi_pos (-π) x.im) * (2 * π * I)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("-", (OVar("x"), OOp("toIocDiv", (OVar("Real_two_pi_pos"), OVar("minus_pi"), OVar("x_im"),)))), OOp("*", (OLit(2), OOp("*", (OVar("pi"), OVar("I")))))))
            results.append((rhs, "Mathlib: Complex_log_exp_eq_sub_toIocDiv"))
        except Exception:
            pass
    return results


def _r0267_log_neg_I(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_neg_I
    # log (-I) = -(π / 2) * I
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("minus_pi_slash_2"), OVar("I")))
            results.append((rhs, "Mathlib: Complex_log_neg_I"))
        except Exception:
            pass
    return results


def _r0268_log_inv_eq_ite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_inv_eq_ite
    # log x⁻¹ = if x.arg = π then -conj (log x) else -log x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (OVar("x_arg"),)), OOp("pi", (OVar("then"), OVar("minus_conj"), OOp("log", (OVar("x"),)), OVar("else"), OVar("minus_log"), OVar("x"),))))
            results.append((rhs, "Mathlib: Complex_log_inv_eq_ite"))
        except Exception:
            pass
    return results


def _r0269_log_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_inv
    # log x⁻¹ = -log x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("minus_log", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_log_inv"))
        except Exception:
            pass
    return results


def _r0270_log_inv_eq_integral(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_inv_eq_integral
    # log (1 - z)⁻¹ = z * ∫ (t : ℝ) in (0 : ℝ)..1, (1 - t • z)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OVar("z"), OOp("_unknown", (OOp("t", (OVar("colon"), OVar("_unknown"),)), OVar("in"), OVar("_0_colon_1"), OVar("_1_minus_t_z_inv"),))))
            results.append((rhs, "Mathlib: Complex_log_inv_eq_integral"))
        except Exception:
            pass
    return results


def _r0271_log_sub_logTaylor_isBigO(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_sub_logTaylor_isBigO
    # (fun z ↦ log (1 + z) - logTaylor (n + 1) z) =O[𝓝 0] fun z ↦ z ^ (n + 1)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("O_0", (OVar("fun"), OVar("z"), OVar("_unknown"), OVar("z"),)), OOp("+", (OVar("n"), OLit(1)))))
            results.append((rhs, "Mathlib: Complex_log_sub_logTaylor_isBigO"))
        except Exception:
            pass
    return results


def _r0272_log_sub_self_isBigO(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.log_sub_self_isBigO
    # (fun z ↦ log (1 + z) - z) =O[𝓝 0] fun z ↦ z ^ 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("O_0", (OVar("fun"), args[1], OVar("_unknown"), args[1],)), OLit(2)))
            results.append((rhs, "Mathlib: Complex_log_sub_self_isBigO"))
        except Exception:
            pass
    return results


def _r0273_exp_sub_sum_range_isBigO_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.exp_sub_sum_range_isBigO_pow
    # (fun x ↦ exp x - ∑ i ∈ Finset.range n, x ^ i / i !) =O[𝓝 0] (· ^ n)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("O_0", (OOp("**", (OVar("_unknown"), OVar("n"))),))
            results.append((rhs, "Mathlib: Real_exp_sub_sum_range_isBigO_pow"))
        except Exception:
            pass
    return results


def _r0274_integral_rpow_mul_exp_neg_mul_Ioi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.integral_rpow_mul_exp_neg_mul_Ioi
    # ∫ t : ℝ in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OOp("//", (OLit(1), OVar("r"))), OVar("a"))), OOp("Gamma", (OVar("a"),))))
            results.append((rhs, "Mathlib: Real_integral_rpow_mul_exp_neg_mul_Ioi"))
        except Exception:
            pass
    return results


def _r0275_tsum_exp_neg_quadratic(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tsum_exp_neg_quadratic
    # (∑' n : ℤ, cexp (-π * a * n ^ 2 + 2 * π * b * n)) =       1 / a ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (-π / a * (n + I * b) ^ 2
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime", 5)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("//", (OLit(1), OOp("**", (OVar("a"), OOp("//", (OLit(1), OOp("_2", (args[1], args[2],)))))))), OOp("prime", (args[0], args[1], args[2], args[3], OOp("*", (OOp("//", (OVar("minus_pi"), OVar("a"))), OOp("**", (OOp("+", (args[0], OOp("*", (OVar("I"), OVar("b"))))), OLit(2))))),))))
            results.append((rhs, "Mathlib: Complex_tsum_exp_neg_quadratic"))
        except Exception:
            pass
    return results


def _r0276_tsum_exp_neg_mul_int_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.tsum_exp_neg_mul_int_sq
    # (∑' n : ℤ, cexp (-π * a * (n : ℂ) ^ 2)) =       1 / a ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (-π / a * (n : ℂ) ^ 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime", 5)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("//", (OLit(1), OOp("**", (OVar("a"), OOp("//", (OLit(1), OOp("_2", (args[1], args[2],)))))))), OOp("prime", (args[0], args[1], args[2], args[3], OOp("*", (OOp("//", (OVar("minus_pi"), OVar("a"))), OOp("**", (OOp("n", (args[1], args[2],)), OLit(2))))),))))
            results.append((rhs, "Mathlib: Complex_tsum_exp_neg_mul_int_sq"))
        except Exception:
            pass
    return results


def _r0277_tsum_exp_neg_mul_int_sq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tsum_exp_neg_mul_int_sq
    # (∑' n : ℤ, exp (-π * a * (n : ℝ) ^ 2)) =       (1 : ℝ) / a ^ (1 / 2 : ℝ) * (∑' n : ℤ, exp (-π / a * (n : ℝ) ^ 2))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "prime", 5)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("//", (OOp("_1", (args[1], args[2],)), OOp("**", (OVar("a"), OOp("//", (OLit(1), OOp("_2", (args[1], args[2],)))))))), OOp("prime", (args[0], args[1], args[2], args[3], OOp("*", (OOp("//", (OVar("minus_pi"), OVar("a"))), OOp("**", (OOp("n", (args[1], args[2],)), OLit(2))))),))))
            results.append((rhs, "Mathlib: Real_tsum_exp_neg_mul_int_sq"))
        except Exception:
            pass
    return results


def _r0278_logb_abs_base(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_abs_base
    # logb |b| x = logb b x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OOp("logb", (OVar("b"), args[1],))
            results.append((rhs, "Mathlib: Real_logb_abs_base"))
        except Exception:
            pass
    return results


def _r0279_logb_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.logb_inv
    # logb b x⁻¹ = -logb b x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logb", 2)
    if args is not None:
        try:
            rhs = OOp("minus_logb", (args[0], OVar("x"),))
            results.append((rhs, "Mathlib: Real_logb_inv"))
        except Exception:
            pass
    return results


def _r0280_inv_logb_mul_base(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.inv_logb_mul_base
    # (logb (a * b) c)⁻¹ = (logb a c)⁻¹ + (logb b c)⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("logb_a_star_b_c_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("logb_a_c_inv"), OVar("logb_b_c_inv")))
            results.append((rhs, "Mathlib: Real_inv_logb_mul_base"))
    except Exception:
        pass
    return results


def _r0281_inv_logb_div_base(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.inv_logb_div_base
    # (logb (a / b) c)⁻¹ = (logb a c)⁻¹ - (logb b c)⁻¹
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("logb_a_slash_b_c_inv")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OVar("logb_a_c_inv"), OVar("logb_b_c_inv")))
            results.append((rhs, "Mathlib: Real_inv_logb_div_base"))
    except Exception:
        pass
    return results


def _r0282_rpow_logb_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_logb_of_neg
    # b ^ logb b x = -x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("minus_x")
            results.append((rhs, "Mathlib: Real_rpow_logb_of_neg"))
        except Exception:
            pass
    return results


def _r0283_exp_log_eq_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.exp_log_eq_abs
    # exp (log x) = |x|
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OVar("pipe_xpipe")
            results.append((rhs, "Mathlib: Real_exp_log_eq_abs"))
        except Exception:
            pass
    return results


def _r0284_exp_log_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.exp_log_of_neg
    # exp (log x) = -x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "exp", 1)
    if args is not None:
        try:
            rhs = OVar("minus_x")
            results.append((rhs, "Mathlib: Real_exp_log_of_neg"))
        except Exception:
            pass
    return results


def _r0285_log_neg_eq_log(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.log_neg_eq_log
    # log (-x) = log x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("log", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_log_neg_eq_log"))
        except Exception:
            pass
    return results


def _r0286_log_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.log_inv
    # log x⁻¹ = -log x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "log", 1)
    if args is not None:
        try:
            rhs = OOp("minus_log", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_log_inv"))
        except Exception:
            pass
    return results


def _r0287_deriv_inv_log(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.deriv_inv_log
    # deriv (fun x ↦ (log x)⁻¹) x = -x⁻¹ / (log x ^ 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "deriv", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("minus_xinv"), OOp("**", (OOp("log", (args[1],)), OLit(2)))))
            results.append((rhs, "Mathlib: Real_deriv_inv_log"))
        except Exception:
            pass
    return results


def _r0288_negMulLog_def(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.negMulLog_def
    # negMulLog = fun x ↦ - x * log x
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("negMulLog")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OOp("-", (OOp("fun", (OVar("x"), OVar("_unknown"),)), OVar("x"))), OOp("log", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_negMulLog_def"))
    except Exception:
        pass
    return results


def _r0289_negMulLog_eq_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.negMulLog_eq_neg
    # negMulLog = fun x ↦ -(x * log x)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("negMulLog")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("-", (OOp("fun", (OVar("x"), OVar("_unknown"),)), OOp("*", (OVar("x"), OOp("log", (OVar("x"),))))))
            results.append((rhs, "Mathlib: Real_negMulLog_eq_neg"))
    except Exception:
        pass
    return results


def _r0290_negMulLog_mul(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.negMulLog_mul
    # negMulLog (x * y) = y * negMulLog x + x * negMulLog y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "negMulLog", 1)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("*", (OVar("y"), OOp("negMulLog", (OVar("x"),)))), OOp("*", (OVar("x"), OOp("negMulLog", (OVar("y"),))))))
            results.append((rhs, "Mathlib: Real_negMulLog_mul"))
        except Exception:
            pass
    return results


def _r0291_deriv_negMulLog(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.deriv_negMulLog
    # deriv negMulLog x = - log x - 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "deriv", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("minus", (OVar("log"), args[1],)), OLit(1)))
            results.append((rhs, "Mathlib: Real_deriv_negMulLog"))
        except Exception:
            pass
    return results


def _r0292_deriv2_negMulLog(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.deriv2_negMulLog
    # deriv^[2] negMulLog x = -x⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "derivpow_2", 2)
    if args is not None:
        try:
            rhs = OVar("minus_xinv")
            results.append((rhs, "Mathlib: Real_deriv2_negMulLog"))
        except Exception:
            pass
    return results


def _r0293_posLog_sub_posLog_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.posLog_sub_posLog_inv
    # log⁺ x - log⁺ x⁻¹ = log x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("log", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_posLog_sub_posLog_inv"))
        except Exception:
            pass
    return results


def _r0294_half_mul_log_add_log_abs(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.half_mul_log_add_log_abs
    # 2⁻¹ * (log x + |log x|) = log⁺ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("logpos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_half_mul_log_add_log_abs"))
        except Exception:
            pass
    return results


def _r0295_posLog_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.posLog_neg
    # log⁺ (-x) = log⁺ x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "logpos", 1)
    if args is not None:
        try:
            rhs = OOp("logpos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_posLog_neg"))
        except Exception:
            pass
    return results


def _r0296_mulExpNegSq_apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.mulExpNegSq_apply
    # mulExpNegMulSq ε x = x * exp (-(ε * x * x))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "mulExpNegMulSq", 2)
    if args is not None:
        try:
            rhs = OOp("*", (args[1], OOp("exp", (OVar("minus_e_star_x_star_x"),))))
            results.append((rhs, "Mathlib: Real_mulExpNegSq_apply"))
        except Exception:
            pass
    return results


def _r0297_neg_mulExpNegMulSq_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.neg_mulExpNegMulSq_neg
    # - mulExpNegMulSq ε (-x) = mulExpNegMulSq ε x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "minus", 3)
    if args is not None:
        try:
            rhs = OOp("mulExpNegMulSq", (args[1], OVar("x"),))
            results.append((rhs, "Mathlib: Real_neg_mulExpNegMulSq_neg"))
        except Exception:
            pass
    return results


def _r0298_deriv_mulExpNegMulSq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.deriv_mulExpNegMulSq
    # deriv (mulExpNegMulSq ε) y =     exp (-(ε * y * y)) + y * (exp (-(ε * y * y)) * (-2 * ε * y))
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "deriv", 2)
    if args is not None:
        try:
            rhs = OOp("+", (OOp("exp", (OVar("minus_e_star_y_star_y"),)), OOp("*", (args[1], OOp("*", (OOp("exp", (OVar("minus_e_star_y_star_y"),)), OOp("*", (OVar("minus_2"), OOp("*", (OVar("e"), args[1]))))))))))
            results.append((rhs, "Mathlib: Real_deriv_mulExpNegMulSq"))
        except Exception:
            pass
    return results


def _r0299_cpow_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_neg
    # x ^ (-y) = (x ^ y)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x_pow_y_inv")
            results.append((rhs, "Mathlib: Complex_cpow_neg"))
        except Exception:
            pass
    return results


def _r0300_cpow_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_sub
    # x ^ (y - z) = x ^ y / x ^ z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("**", (args[0], OVar("y"))), OOp("**", (args[0], OVar("z")))))
            results.append((rhs, "Mathlib: Complex_cpow_sub"))
        except Exception:
            pass
    return results


def _r0301_cpow_ofNat_inv_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_ofNat_inv_pow
    # (x ^ ((ofNat(n) : ℂ)⁻¹)) ^ (ofNat(n) : ℕ) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Complex_cpow_ofNat_inv_pow"))
        except Exception:
            pass
    return results


def _r0302_pow_cpow_nat_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.pow_cpow_nat_inv
    # (x ^ n) ^ (n⁻¹ : ℂ) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Complex_pow_cpow_nat_inv"))
        except Exception:
            pass
    return results


def _r0303_pow_cpow_ofNat_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.pow_cpow_ofNat_inv
    # (x ^ ofNat(n)) ^ ((OfNat.ofNat n : ℂ)⁻¹) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Complex_pow_cpow_ofNat_inv"))
        except Exception:
            pass
    return results


def _r0304_sq_cpow_two_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sq_cpow_two_inv
    # (x ^ (2 : ℕ)) ^ (2⁻¹ : ℂ) = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Complex_sq_cpow_two_inv"))
        except Exception:
            pass
    return results


def _r0305_inv_cpow_eq_ite(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.inv_cpow_eq_ite
    # x⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (OVar("x_arg"),)), OOp("pi", (OVar("then"), OVar("conj"), OVar("x_pow_conj_n_inv"), OVar("else"), OVar("x_pow_n_inv"),))))
            results.append((rhs, "Mathlib: Complex_inv_cpow_eq_ite"))
        except Exception:
            pass
    return results


def _r0306_inv_cpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.inv_cpow
    # x⁻¹ ^ n = (x ^ n)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x_pow_n_inv")
            results.append((rhs, "Mathlib: Complex_inv_cpow"))
        except Exception:
            pass
    return results


def _r0307_rpow_eq_nhds_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_eq_nhds_of_neg
    # (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "product", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("p", (OVar("fun"), OVar("x"), OVar("eq_gt"), OVar("exp"), OOp("*", (OOp("log", (OVar("x_1"),)), OVar("x_2"))),)), OOp("cos", (OOp("*", (OVar("x_2"), OVar("pi"))),))))
            results.append((rhs, "Mathlib: Real_rpow_eq_nhds_of_neg"))
        except Exception:
            pass
    return results


def _r0308_toNNReal_rpow_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.toNNReal_rpow_of_nonneg
    # Real.toNNReal (x ^ y) = Real.toNNReal x ^ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "Real_toNNReal", 1)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("Real_toNNReal", (OVar("x"),)), OVar("y")))
            results.append((rhs, "Mathlib: Real_toNNReal_rpow_of_nonneg"))
        except Exception:
            pass
    return results


def _r0309_nnnorm_rpow_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.nnnorm_rpow_of_nonneg
    # ‖x ^ y‖₊ = ‖x‖₊ ^ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], args[1]))
            results.append((rhs, "Mathlib: Real_nnnorm_rpow_of_nonneg"))
        except Exception:
            pass
    return results


def _r0310_rpow_def_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_def_of_nonneg
    # x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("if", (args[0],)), OOp("==", (OOp("_0", (OVar("then"), OVar("if"), args[1],)), OOp("_0", (OVar("then"), OLit(1), OVar("else"), OLit(0), OVar("else"), OVar("exp"), OOp("*", (OOp("log", (args[0],)), args[1])),))))))
            results.append((rhs, "Mathlib: Real_rpow_def_of_nonneg"))
        except Exception:
            pass
    return results


def _r0311_rpow_neg_ofNat(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_neg_ofNat
    # x ^ (-ofNat(n) : ℝ) = x ^ (-ofNat(n) : ℤ)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], OOp("minus_ofNat_n", (OVar("colon"), OVar("_unknown"),))))
            results.append((rhs, "Mathlib: Real_rpow_neg_ofNat"))
        except Exception:
            pass
    return results


def _r0312_rpow_def_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_def_of_neg
    # x ^ y = exp (log x * y) * cos (y * π)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("exp", (OOp("*", (OOp("log", (args[0],)), args[1])),)), OOp("cos", (OOp("*", (args[1], OVar("pi"))),))))
            results.append((rhs, "Mathlib: Real_rpow_def_of_neg"))
        except Exception:
            pass
    return results


def _r0313_abs_rpow_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.abs_rpow_of_nonneg
    # |x ^ y| = |x| ^ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("pipe_xpipe"), OVar("y")))
            results.append((rhs, "Mathlib: Real_abs_rpow_of_nonneg"))
        except Exception:
            pass
    return results


def _r0314_rpow_inv_log(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_inv_log
    # x ^ (log x)⁻¹ = exp 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("exp", (OLit(1),))
            results.append((rhs, "Mathlib: Real_rpow_inv_log"))
        except Exception:
            pass
    return results


def _r0315_norm_rpow_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.norm_rpow_of_nonneg
    # ‖x ^ y‖ = ‖x‖ ^ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (args[0], args[1]))
            results.append((rhs, "Mathlib: Real_norm_rpow_of_nonneg"))
        except Exception:
            pass
    return results


def _r0316_rpow_add_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_add_of_nonneg
    # x ^ (y + z) = x ^ y * x ^ z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (args[0], OVar("y"))), OOp("**", (args[0], OVar("z")))))
            results.append((rhs, "Mathlib: Real_rpow_add_of_nonneg"))
        except Exception:
            pass
    return results


def _r0317_rpow_sum_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_sum_of_nonneg
    # (a ^ ∑ x ∈ s, f x) = ∏ x ∈ s, a ^ f x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "in", 2)
    if args is not None:
        try:
            rhs = OOp("in", (OOp("_unknown", (OVar("x"),)), OOp("**", (OOp("s", (OVar("a"),)), OOp("f", (OVar("x"),))))))
            results.append((rhs, "Mathlib: Real_rpow_sum_of_nonneg"))
        except Exception:
            pass
    return results


def _r0318_rpow_neg_eq_inv_rpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_neg_eq_inv_rpow
    # x ^ (-y) = x⁻¹ ^ y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("xinv"), OVar("y")))
            results.append((rhs, "Mathlib: Real_rpow_neg_eq_inv_rpow"))
        except Exception:
            pass
    return results


def _r0319_rpow_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_neg
    # x ^ (-y) = (x ^ y)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x_pow_y_inv")
            results.append((rhs, "Mathlib: Real_rpow_neg"))
        except Exception:
            pass
    return results


def _r0320_rpow_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_sub
    # x ^ (y - z) = x ^ y / x ^ z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("**", (args[0], OVar("y"))), OOp("**", (args[0], OVar("z")))))
            results.append((rhs, "Mathlib: Real_rpow_sub"))
        except Exception:
            pass
    return results


def _r0321_norm_cpow_eq_rpow_re_of_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.norm_cpow_eq_rpow_re_of_nonneg
    # ‖(x : ℂ) ^ y‖ = x ^ re y
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OVar("x"), OOp("re", (args[1],))))
            results.append((rhs, "Mathlib: Complex_norm_cpow_eq_rpow_re_of_nonneg"))
        except Exception:
            pass
    return results


def _r0322_cpow_mul_ofReal_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_mul_ofReal_nonneg
    # (x : ℂ) ^ (↑y * z) = (↑(x ^ y) : ℂ) ^ z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("**", (OOp("x_pow_y", (OVar("colon"), OVar("_unknown"),)), OVar("z")))
            results.append((rhs, "Mathlib: Complex_cpow_mul_ofReal_nonneg"))
        except Exception:
            pass
    return results


def _r0323_rpow_sub_intCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_sub_intCast
    # x ^ (y - n) = x ^ y / x ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("**", (args[0], OVar("y"))), OOp("**", (args[0], OVar("n")))))
            results.append((rhs, "Mathlib: Real_rpow_sub_intCast"))
        except Exception:
            pass
    return results


def _r0324_rpow_sub_natCast(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_sub_natCast
    # x ^ (y - n) = x ^ y / x ^ n
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("**", (args[0], OVar("y"))), OOp("**", (args[0], OVar("n")))))
            results.append((rhs, "Mathlib: Real_rpow_sub_natCast"))
        except Exception:
            pass
    return results


def _r0325_inv_rpow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.inv_rpow
    # x⁻¹ ^ y = (x ^ y)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x_pow_y_inv")
            results.append((rhs, "Mathlib: Real_inv_rpow"))
        except Exception:
            pass
    return results


def _r0326_rpow_rpow_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_rpow_inv
    # (x ^ y) ^ y⁻¹ = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Real_rpow_rpow_inv"))
        except Exception:
            pass
    return results


def _r0327_rpow_inv_natCast_pow(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_inv_natCast_pow
    # (x ^ (n⁻¹ : ℝ)) ^ n = x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OVar("x")
            results.append((rhs, "Mathlib: Real_rpow_inv_natCast_pow"))
        except Exception:
            pass
    return results


def _r0328_rpow_inv_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.rpow_inv_eq
    # x ^ z⁻¹ = y ↔ x = y ^ z
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "**", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("y"), args[0])), OOp("**", (OVar("y"), OVar("z")))))
            results.append((rhs, "Mathlib: Real_rpow_inv_eq"))
        except Exception:
            pass
    return results


def _r0329_eq_rpow_inv(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.eq_rpow_inv
    # x = y ^ z⁻¹ ↔ x ^ z = y
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OOp("**", (OVar("y"), OVar("zinv"))), OOp("**", (OVar("x"), OVar("z"))))), OVar("y")))
            results.append((rhs, "Mathlib: Real_eq_rpow_inv"))
    except Exception:
        pass
    return results


def _r0330_cpow_inv_two_re(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_inv_two_re
    # (x ^ (2⁻¹ : ℂ)).re = √((‖x‖ + x.re) / 2)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pow_2inv_colon_re")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_plus_x_re_slash_2")
            results.append((rhs, "Mathlib: Complex_cpow_inv_two_re"))
    except Exception:
        pass
    return results


def _r0331_cpow_inv_two_im_eq_sqrt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_inv_two_im_eq_sqrt
    # (x ^ (2⁻¹ : ℂ)).im = √((‖x‖ - x.re) / 2)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pow_2inv_colon_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_minus_x_re_slash_2")
            results.append((rhs, "Mathlib: Complex_cpow_inv_two_im_eq_sqrt"))
    except Exception:
        pass
    return results


def _r0332_cpow_inv_two_im_eq_neg_sqrt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.cpow_inv_two_im_eq_neg_sqrt
    # (x ^ (2⁻¹ : ℂ)).im = -√((‖x‖ - x.re) / 2)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("x_pow_2inv_colon_im")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("minus_x_minus_x_re_slash_2")
            results.append((rhs, "Mathlib: Complex_cpow_inv_two_im_eq_neg_sqrt"))
    except Exception:
        pass
    return results


def _r0333_abs_cpow_inv_two_im(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.abs_cpow_inv_two_im
    # |(x ^ (2⁻¹ : ℂ)).im| = √((‖x‖ - x.re) / 2)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_x_pow_2inv_colon_impipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("x_minus_x_re_slash_2")
            results.append((rhs, "Mathlib: Complex_abs_cpow_inv_two_im"))
    except Exception:
        pass
    return results


def _r0334_sigmoid_mul_rexp_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sigmoid_mul_rexp_neg
    # sigmoid x * exp (-x) = sigmoid (-x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("sigmoid", (OVar("minus_x"),))
            results.append((rhs, "Mathlib: Real_sigmoid_mul_rexp_neg"))
        except Exception:
            pass
    return results


def _r0335_angle_eq_iff_two_pi_dvd_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.angle_eq_iff_two_pi_dvd_sub
    # (θ : Angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "th", 2)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OVar("psi"), OOp("-", (OOp("exists", (OVar("k"), args[0], OVar("_unknown"), OVar("th"),)), OVar("psi"))))), OOp("*", (OLit(2), OOp("*", (OVar("pi"), OVar("k")))))))
            results.append((rhs, "Mathlib: Real_Angle_angle_eq_iff_two_pi_dvd_sub"))
        except Exception:
            pass
    return results


def _r0336_two_zsmul_neg_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.two_zsmul_neg_pi_div_two
    # (2 : ℤ) • (↑(-π / 2) : Angle) = π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "_2_colon", 2)
    if args is not None:
        try:
            rhs = OVar("pi")
            results.append((rhs, "Mathlib: Real_Angle_two_zsmul_neg_pi_div_two"))
        except Exception:
            pass
    return results


def _r0337_sub_coe_pi_eq_add_coe_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sub_coe_pi_eq_add_coe_pi
    # θ - π = θ + π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "-", 2)
    if args is not None:
        try:
            rhs = OOp("+", (args[0], args[1]))
            results.append((rhs, "Mathlib: Real_Angle_sub_coe_pi_eq_add_coe_pi"))
        except Exception:
            pass
    return results


def _r0338_eq_neg_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.eq_neg_self_iff
    # θ = -θ ↔ θ = 0 ∨ θ = π
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("th")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("minus_th"), OVar("th"))), OOp("==", (OOp("or", (OLit(0), OVar("th"))), OVar("pi")))))
            results.append((rhs, "Mathlib: Real_Angle_eq_neg_self_iff"))
    except Exception:
        pass
    return results


def _r0339_neg_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.neg_eq_self_iff
    # -θ = θ ↔ θ = 0 ∨ θ = π
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_th")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("th"), OVar("th"))), OOp("==", (OOp("or", (OLit(0), OVar("th"))), OVar("pi")))))
            results.append((rhs, "Mathlib: Real_Angle_neg_eq_self_iff"))
    except Exception:
        pass
    return results


def _r0340_cos_eq_iff_coe_eq_or_eq_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_eq_iff_coe_eq_or_eq_neg
    # cos θ = cos ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) = -ψ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("cos", (OVar("psi"),)), OOp("th", (OVar("colon"), OVar("Angle"),)))), OOp("==", (OOp("or", (OVar("psi"), OOp("th", (OVar("colon"), OVar("Angle"),)))), OVar("minus_psi")))))
            results.append((rhs, "Mathlib: Real_Angle_cos_eq_iff_coe_eq_or_eq_neg"))
        except Exception:
            pass
    return results


def _r0341_cos_eq_real_cos_iff_eq_or_eq_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg
    # cos θ = Real.cos ψ ↔ θ = ψ ∨ θ = -ψ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("Real_cos", (OVar("psi"),)), args[0])), OOp("==", (OOp("or", (OVar("psi"), args[0])), OVar("minus_psi")))))
            results.append((rhs, "Mathlib: Real_Angle_cos_eq_real_cos_iff_eq_or_eq_neg"))
        except Exception:
            pass
    return results


def _r0342_cos_eq_iff_eq_or_eq_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_eq_iff_eq_or_eq_neg
    # cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("==", (OOp("iff", (OOp("cos", (OVar("psi"),)), args[0])), OOp("==", (OOp("or", (OVar("psi"), args[0])), OVar("minus_psi")))))
            results.append((rhs, "Mathlib: Real_Angle_cos_eq_iff_eq_or_eq_neg"))
        except Exception:
            pass
    return results


def _r0343_sin_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sin_neg
    # sin (-θ) = -sin θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_sin_neg"))
        except Exception:
            pass
    return results


def _r0344_cos_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_neg
    # cos (-θ) = cos θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_cos_neg"))
        except Exception:
            pass
    return results


def _r0345_sin_sub_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sin_sub_pi_div_two
    # sin (θ - ↑(π / 2)) = -cos θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_cos", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_sin_sub_pi_div_two"))
        except Exception:
            pass
    return results


def _r0346_sin_pi_div_two_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sin_pi_div_two_sub
    # sin (↑(π / 2) - θ) = cos θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_sin_pi_div_two_sub"))
        except Exception:
            pass
    return results


def _r0347_cos_sub_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_sub_pi_div_two
    # cos (θ - ↑(π / 2)) = sin θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_cos_sub_pi_div_two"))
        except Exception:
            pass
    return results


def _r0348_cos_pi_div_two_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.cos_pi_div_two_sub
    # cos (↑(π / 2) - θ) = sin θ
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("th"),))
            results.append((rhs, "Mathlib: Real_Angle_cos_pi_div_two_sub"))
        except Exception:
            pass
    return results


def _r0349_abs_toReal_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.abs_toReal_neg
    # |(-θ).toReal| = |θ.toReal|
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_minus_th_toRealpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("pipe_th_toRealpipe")
            results.append((rhs, "Mathlib: Real_Angle_abs_toReal_neg"))
    except Exception:
        pass
    return results


def _r0350_abs_toReal_neg_coe_eq_self_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.abs_toReal_neg_coe_eq_self_iff
    # |(-θ : Angle).toReal| = θ ↔ 0 ≤ θ ∧ θ ≤ π
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_minus_th_colon_Angle_toRealpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<=", (OOp("iff", (OVar("th"), OLit(0))), OOp("<=", (OOp("and", (OVar("th"), OVar("th"))), OVar("pi")))))
            results.append((rhs, "Mathlib: Real_Angle_abs_toReal_neg_coe_eq_self_iff"))
    except Exception:
        pass
    return results


def _r0351_toReal_coe_eq_self_sub_two_mul_int_mul_p(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff
    # (θ : Angle).toReal = θ - 2 * k * π ↔ θ ∈ Set.Ioc ((2 * k - 1 : ℝ) * π) ((2 * k + 1) * π)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("th_colon_Angle_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("*", (OOp("-", (OVar("th"), OLit(2))), OOp("*", (OVar("k"), OVar("pi"))))), OOp("in", (OVar("th"), OOp("Set_Ioc", (OOp("*", (OOp("*", (OLit(2), OOp("-", (OVar("k"), OOp("_1", (OVar("colon"), OVar("_unknown"),)))))), OVar("pi"))), OOp("*", (OOp("+", (OOp("*", (OLit(2), OVar("k"))), OLit(1))), OVar("pi"))),))))))
            results.append((rhs, "Mathlib: Real_Angle_toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff"))
    except Exception:
        pass
    return results


def _r0352_toReal_coe_eq_self_sub_two_pi_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_coe_eq_self_sub_two_pi_iff
    # (θ : Angle).toReal = θ - 2 * π ↔ θ ∈ Set.Ioc π (3 * π)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("th_colon_Angle_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("iff", (OOp("*", (OOp("-", (OVar("th"), OLit(2))), OVar("pi"))), OOp("in", (OVar("th"), OOp("Set_Ioc", (OVar("pi"), OOp("*", (OLit(3), OVar("pi"))),))))))
            results.append((rhs, "Mathlib: Real_Angle_toReal_coe_eq_self_sub_two_pi_iff"))
    except Exception:
        pass
    return results


def _r0353_two_nsmul_toReal_eq_two_mul_sub_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.two_nsmul_toReal_eq_two_mul_sub_two_pi
    # ((2 : ℕ) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_2_colon_th_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<", (OOp("iff", (OOp("*", (OLit(2), OOp("*", (OOp("-", (OVar("th_toReal"), OLit(2))), OVar("pi"))))), OOp("//", (OVar("pi"), OLit(2))))), OVar("th_toReal")))
            results.append((rhs, "Mathlib: Real_Angle_two_nsmul_toReal_eq_two_mul_sub_two_pi"))
    except Exception:
        pass
    return results


def _r0354_two_zsmul_toReal_eq_two_mul_sub_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.two_zsmul_toReal_eq_two_mul_sub_two_pi
    # ((2 : ℤ) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_2_colon_th_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("<", (OOp("iff", (OOp("*", (OLit(2), OOp("*", (OOp("-", (OVar("th_toReal"), OLit(2))), OVar("pi"))))), OOp("//", (OVar("pi"), OLit(2))))), OVar("th_toReal")))
            results.append((rhs, "Mathlib: Real_Angle_two_zsmul_toReal_eq_two_mul_sub_two_pi"))
    except Exception:
        pass
    return results


def _r0355_tan_eq_inv_of_two_nsmul_add_two_nsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi
    # tan ψ = (tan θ)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OVar("tan_th_inv")
            results.append((rhs, "Mathlib: Real_Angle_tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi"))
        except Exception:
            pass
    return results


def _r0356_tan_eq_inv_of_two_zsmul_add_two_zsmul_eq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi
    # tan ψ = (tan θ)⁻¹
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OVar("tan_th_inv")
            results.append((rhs, "Mathlib: Real_Angle_tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi"))
        except Exception:
            pass
    return results


def _r0357_toReal_neg_iff_sign_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_neg_iff_sign_neg
    # θ.toReal < 0 ↔ θ.sign = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<", 2)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Real_Angle_toReal_neg_iff_sign_neg"))
        except Exception:
            pass
    return results


def _r0358_coe_abs_toReal_of_sign_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.coe_abs_toReal_of_sign_nonneg
    # ↑|θ.toReal| = θ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_th_toRealpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("th")
            results.append((rhs, "Mathlib: Real_Angle_coe_abs_toReal_of_sign_nonneg"))
    except Exception:
        pass
    return results


def _r0359_neg_coe_abs_toReal_of_sign_nonpos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.neg_coe_abs_toReal_of_sign_nonpos
    # -↑|θ.toReal| = θ
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("minus_pipe_th_toRealpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OVar("th")
            results.append((rhs, "Mathlib: Real_Angle_neg_coe_abs_toReal_of_sign_nonpos"))
    except Exception:
        pass
    return results


def _r0360_sign_two_nsmul_eq_neg_sign_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sign_two_nsmul_eq_neg_sign_iff
    # ((2 : ℕ) • θ).sign = -θ.sign ↔ θ = 0 ∨ π / 2 < |θ.toReal|
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_2_colon_th_sign")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("minus_th_sign"), OVar("th"))), OOp("<", (OOp("or", (OLit(0), OOp("//", (OVar("pi"), OLit(2))))), OVar("pipe_th_toRealpipe")))))
            results.append((rhs, "Mathlib: Real_Angle_sign_two_nsmul_eq_neg_sign_iff"))
    except Exception:
        pass
    return results


def _r0361_sign_two_zsmul_eq_neg_sign_iff(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.sign_two_zsmul_eq_neg_sign_iff
    # ((2 : ℤ) • θ).sign = -θ.sign ↔ θ = 0 ∨ π / 2 < |θ.toReal|
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("_2_colon_th_sign")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("==", (OOp("iff", (OVar("minus_th_sign"), OVar("th"))), OOp("<", (OOp("or", (OLit(0), OOp("//", (OVar("pi"), OLit(2))))), OVar("pipe_th_toRealpipe")))))
            results.append((rhs, "Mathlib: Real_Angle_sign_two_zsmul_eq_neg_sign_iff"))
    except Exception:
        pass
    return results


def _r0362_eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg
    # a = b + π
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("a")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("b"), OVar("pi")))
            results.append((rhs, "Mathlib: Real_Angle_eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg"))
    except Exception:
        pass
    return results


def _r0363_toReal_add_of_sign_pos_sign_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_add_of_sign_pos_sign_neg
    # (θ + ψ).toReal = θ.toReal + ψ.toReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("th_plus_psi_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("th_toReal"), OVar("psi_toReal")))
            results.append((rhs, "Mathlib: Real_Angle_toReal_add_of_sign_pos_sign_neg"))
    except Exception:
        pass
    return results


def _r0364_toReal_add_of_sign_eq_neg_sign(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.toReal_add_of_sign_eq_neg_sign
    # (θ + ψ).toReal = θ.toReal + ψ.toReal
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("th_plus_psi_toReal")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("+", (OVar("th_toReal"), OVar("psi_toReal")))
            results.append((rhs, "Mathlib: Real_Angle_toReal_add_of_sign_eq_neg_sign"))
    except Exception:
        pass
    return results


def _r0365_abs_toReal_add_eq_two_pi_sub_abs_toReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux
    # |(θ + ψ).toReal| = 2 * π - (|θ.toReal| + |ψ.toReal|)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_th_plus_psi_toRealpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OLit(2), OOp("-", (OVar("pi"), OOp("+", (OVar("pipe_th_toRealpipe"), OVar("pipe_psi_toRealpipe")))))))
            results.append((rhs, "Mathlib: Real_Angle_abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal_aux"))
    except Exception:
        pass
    return results


def _r0366_abs_toReal_add_eq_two_pi_sub_abs_toReal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.Angle.abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal
    # |(θ + ψ).toReal| = 2 * π - (|θ.toReal| + |ψ.toReal|)
    results: List[Tuple[OTerm, str]] = []
    try:
        lhs_pattern = OVar("pipe_th_plus_psi_toRealpipe")
        if term.canon() == lhs_pattern.canon():
            rhs = OOp("*", (OLit(2), OOp("-", (OVar("pi"), OOp("+", (OVar("pipe_th_toRealpipe"), OVar("pipe_psi_toRealpipe")))))))
            results.append((rhs, "Mathlib: Real_Angle_abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal"))
    except Exception:
        pass
    return results


def _r0367_tan_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.tan_sub
    # tan (x - y) = (tan x - tan y) / (1 + tan x * tan y)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "tan", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OOp("-", (OOp("tan", (OVar("x"),)), OOp("tan", (OVar("y"),)))), OOp("+", (OLit(1), OOp("*", (OOp("tan", (OVar("x"),)), OOp("tan", (OVar("y"),))))))))
            results.append((rhs, "Mathlib: Real_tan_sub"))
        except Exception:
            pass
    return results


def _r0368_arctan_inv_sqrt_three(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_inv_sqrt_three
    # arctan (√3)⁻¹ = π / 6
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arctan", 1)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pi"), OLit(6)))
            results.append((rhs, "Mathlib: Real_arctan_inv_sqrt_three"))
        except Exception:
            pass
    return results


def _r0369_arctan_inv_of_pos(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_inv_of_pos
    # arctan x⁻¹ = π / 2 - arctan x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arctan", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("//", (OVar("pi"), OLit(2))), OOp("arctan", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_arctan_inv_of_pos"))
        except Exception:
            pass
    return results


def _r0370_arctan_inv_of_neg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_inv_of_neg
    # arctan x⁻¹ = -(π / 2) - arctan x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "arctan", 1)
    if args is not None:
        try:
            rhs = OOp("-", (OVar("minus_pi_slash_2"), OOp("arctan", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_arctan_inv_of_neg"))
        except Exception:
            pass
    return results


def _r0371_arctan_add_eq_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_add_eq_sub_pi
    # arctan x + arctan y = arctan ((x + y) / (1 - x * y)) - π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("arctan", (OOp("//", (OOp("+", (OVar("x"), OVar("y"))), OOp("*", (OOp("-", (OLit(1), OVar("x"))), OVar("y"))))),)), OVar("pi")))
            results.append((rhs, "Mathlib: Real_arctan_add_eq_sub_pi"))
        except Exception:
            pass
    return results


def _r0372_two_mul_arctan_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.two_mul_arctan_sub_pi
    # 2 * arctan x = arctan (2 * x / (1 - x ^ 2)) - π
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("-", (OOp("arctan", (OOp("*", (OLit(2), OOp("//", (OVar("x"), OOp("-", (OLit(1), OOp("**", (OVar("x"), OLit(2))))))))),)), OVar("pi")))
            results.append((rhs, "Mathlib: Real_two_mul_arctan_sub_pi"))
        except Exception:
            pass
    return results


def _r0373_arctan_inv_2_add_arctan_inv_3(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.arctan_inv_2_add_arctan_inv_3
    # arctan 2⁻¹ + arctan 3⁻¹ = π / 4
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pi"), OLit(4)))
            results.append((rhs, "Mathlib: Real_arctan_inv_2_add_arctan_inv_3"))
        except Exception:
            pass
    return results


def _r0374_two_mul_arctan_inv_2_sub_arctan_inv_7(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.two_mul_arctan_inv_2_sub_arctan_inv_7
    # 2 * arctan 2⁻¹ - arctan 7⁻¹ = π / 4
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pi"), OLit(4)))
            results.append((rhs, "Mathlib: Real_two_mul_arctan_inv_2_sub_arctan_inv_7"))
        except Exception:
            pass
    return results


def _r0375_two_mul_arctan_inv_3_add_arctan_inv_7(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.two_mul_arctan_inv_3_add_arctan_inv_7
    # 2 * arctan 3⁻¹ + arctan 7⁻¹ = π / 4
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "+", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pi"), OLit(4)))
            results.append((rhs, "Mathlib: Real_two_mul_arctan_inv_3_add_arctan_inv_7"))
        except Exception:
            pass
    return results


def _r0376_four_mul_arctan_inv_5_sub_arctan_inv_239(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    # 4 * arctan 5⁻¹ - arctan 239⁻¹ = π / 4
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "*", 2)
    if args is not None:
        try:
            rhs = OOp("//", (OVar("pi"), OLit(4)))
            results.append((rhs, "Mathlib: Real_four_mul_arctan_inv_5_sub_arctan_inv_239"))
        except Exception:
            pass
    return results


def _r0377_sin_sub_int_mul_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_sub_int_mul_pi
    # sin (x - n * π) = (-1) ^ n * sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("sin", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_sin_sub_int_mul_pi"))
        except Exception:
            pass
    return results


def _r0378_sin_sub_nat_mul_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_sub_nat_mul_pi
    # sin (x - n * π) = (-1) ^ n * sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("sin", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_sin_sub_nat_mul_pi"))
        except Exception:
            pass
    return results


def _r0379_sin_int_mul_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_int_mul_pi_sub
    # sin (n * π - x) = -((-1) ^ n * sin x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OVar("minus_minus_1_pow_n_star_sin_x")
            results.append((rhs, "Mathlib: Real_sin_int_mul_pi_sub"))
        except Exception:
            pass
    return results


def _r0380_sin_nat_mul_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_nat_mul_pi_sub
    # sin (n * π - x) = -((-1) ^ n * sin x)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OVar("minus_minus_1_pow_n_star_sin_x")
            results.append((rhs, "Mathlib: Real_sin_nat_mul_pi_sub"))
        except Exception:
            pass
    return results


def _r0381_abs_cos_int_mul_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.abs_cos_int_mul_pi
    # |cos (k * π)| = 1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pipe_cos", 1)
    if args is not None:
        try:
            rhs = OLit(1)
            results.append((rhs, "Mathlib: Real_abs_cos_int_mul_pi"))
        except Exception:
            pass
    return results


def _r0382_cos_sub_int_mul_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_sub_int_mul_pi
    # cos (x - n * π) = (-1) ^ n * cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("cos", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_cos_sub_int_mul_pi"))
        except Exception:
            pass
    return results


def _r0383_cos_sub_nat_mul_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_sub_nat_mul_pi
    # cos (x - n * π) = (-1) ^ n * cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("cos", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_cos_sub_nat_mul_pi"))
        except Exception:
            pass
    return results


def _r0384_cos_int_mul_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_int_mul_pi_sub
    # cos (n * π - x) = (-1) ^ n * cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("cos", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_cos_int_mul_pi_sub"))
        except Exception:
            pass
    return results


def _r0385_cos_nat_mul_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_nat_mul_pi_sub
    # cos (n * π - x) = (-1) ^ n * cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("*", (OOp("**", (OVar("minus_1"), OVar("n"))), OOp("cos", (OVar("x"),))))
            results.append((rhs, "Mathlib: Real_cos_nat_mul_pi_sub"))
        except Exception:
            pass
    return results


def _r0386_cos_nat_mul_two_pi_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_nat_mul_two_pi_sub_pi
    # cos (n * (2 * π) - π) = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Real_cos_nat_mul_two_pi_sub_pi"))
        except Exception:
            pass
    return results


def _r0387_cos_int_mul_two_pi_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_int_mul_two_pi_sub_pi
    # cos (n * (2 * π) - π) = -1
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1")
            results.append((rhs, "Mathlib: Real_cos_int_mul_two_pi_sub_pi"))
        except Exception:
            pass
    return results


def _r0388_sin_sub_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_sub_pi_div_two
    # sin (x - π / 2) = -cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_sub_pi_div_two"))
        except Exception:
            pass
    return results


def _r0389_sin_pi_div_two_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_pi_div_two_sub
    # sin (π / 2 - x) = cos x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("cos", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_sin_pi_div_two_sub"))
        except Exception:
            pass
    return results


def _r0390_cos_sub_pi_div_two(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_sub_pi_div_two
    # cos (x - π / 2) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_sub_pi_div_two"))
        except Exception:
            pass
    return results


def _r0391_cos_pi_div_two_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.cos_pi_div_two_sub
    # cos (π / 2 - x) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "cos", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Real_cos_pi_div_two_sub"))
        except Exception:
            pass
    return results


def _r0392_abs_sin_half(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.abs_sin_half
    # |sin (x / 2)| = √((1 - cos x) / 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "pipe_sin", 1)
    if args is not None:
        try:
            rhs = OVar("_1_minus_cos_x_slash_2")
            results.append((rhs, "Mathlib: Real_abs_sin_half"))
        except Exception:
            pass
    return results


def _r0393_sin_half_eq_neg_sqrt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sin_half_eq_neg_sqrt
    # sin (x / 2) = -√((1 - cos x) / 2)
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OVar("minus_1_minus_cos_x_slash_2")
            results.append((rhs, "Mathlib: Real_sin_half_eq_neg_sqrt"))
        except Exception:
            pass
    return results


def _r0394_sqrtTwoAddSeries_nonneg(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Real.sqrtTwoAddSeries_nonneg
    # ∀ n : ℕ, 0 ≤ sqrtTwoAddSeries x n   | 0 => h   | _ + 1 => sqrt_nonneg _  theorem sqrtTwoAddSeries_lt_two : ∀ n : ℕ, sqrt
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "<=", 2)
    if args is not None:
        try:
            rhs = OOp("<", (OOp("+", (OOp("gt", (OVar("h"), OVar("pipe"), OVar("_unknown"),)), OOp("_1", (OVar("eq_gt"), OVar("sqrt_nonneg"), OVar("theorem"), OVar("sqrtTwoAddSeries_lt_two"), OVar("colon"), OVar("forall"), OVar("n"), OVar("colon"), OVar("_unknown"), OVar("sqrtTwoAddSeries"), OLit(0), OVar("n"),)))), OOp("_2", (OVar("pipe"), OLit(0), OVar("eq_gt"),))))
            results.append((rhs, "Mathlib: Real_sqrtTwoAddSeries_nonneg"))
        except Exception:
            pass
    return results


def _r0395_sin_sub_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_sub_pi
    # sin (x - π) = -sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sin_sub_pi"))
        except Exception:
            pass
    return results


def _r0396_sin_sub_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_sub_two_pi
    # sin (x - 2 * π) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sin_sub_two_pi"))
        except Exception:
            pass
    return results


def _r0397_sin_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_pi_sub
    # sin (π - x) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sin_pi_sub"))
        except Exception:
            pass
    return results


def _r0398_sin_two_pi_sub(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_two_pi_sub
    # sin (2 * π - x) = -sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("minus_sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sin_two_pi_sub"))
        except Exception:
            pass
    return results


def _r0399_sin_sub_nat_mul_two_pi(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    # Mathlib: Complex.sin_sub_nat_mul_two_pi
    # sin (x - n * (2 * π)) = sin x
    results: List[Tuple[OTerm, str]] = []
    args = _match_op(term, "sin", 1)
    if args is not None:
        try:
            rhs = OOp("sin", (OVar("x"),))
            results.append((rhs, "Mathlib: Complex_sin_sub_nat_mul_two_pi"))
        except Exception:
            pass
    return results


# ════════════════════════════════════════════════════════════
# Public API
# ════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could any ml_int_basic rule apply to term?"""
    if isinstance(term, OOp):
        return term.name in ("!=", "*", "**", "+", "-", "//", "<", "<=", "ENNReal_ofReal", "FiniteElement_mk", "GCDMonoid_gcd", "Ico", "M", "MulArchimedeanClass_subsemigroup", "Real_toNNReal", "S_toSubalgebra", "S_toSubfield", "StrictMono", "_0", "_2", "_2_colon", "_2_star_pi_star_I_colon_inv", "_2inv", "_unknown", "a", "abs", "and", "antidiagonal", "arcsin", "arctan", "arg", "arsinh", "b", "balance", "binEntropy", "bodd", "bot", "by", "cderiv", "cos", "cosh", "deriv", "derivpow_2", "e_liftExtend_phi_hphi_f", "equivSubtype_symm_toEmbedding_trans", "exists", "exp", "expNear", "f", "f_prod",)
    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """Relevance score for ml_int_basic axioms."""
    if recognizes(term):
        return 0.8
    return 0.0


def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all ml_int_basic rewrite rules to term."""
    results: List[Tuple[OTerm, str]] = []
    if not recognizes(term):
        return results
    results.extend(_r0000_balance_sub(term, ctx))
    results.extend(_r0001_balance_neg(term, ctx))
    results.extend(_r0002_prod_of_support_subset(term, ctx))
    results.extend(_r0003_floor_sub_natCast(term, ctx))
    results.extend(_r0004_floor_sub_ofNat(term, ctx))
    results.extend(_r0005_sub_bot(term, ctx))
    results.extend(_r0006_toAddSubgroup_closedBall(term, ctx))
    results.extend(_r0007_cast_nonneg_iff(term, ctx))
    results.extend(_r0008_val_sub(term, ctx))
    results.extend(_r0009_mk_natCast(term, ctx))
    results.extend(_r0010_mk_intCast(term, ctx))
    results.extend(_r0011_neg_mk(term, ctx))
    results.extend(_r0012_den_abs_eq_den(term, ctx))
    results.extend(_r0013_negOnePow_sub(term, ctx))
    results.extend(_r0014_exp_neg(term, ctx))
    results.extend(_r0015_norm_of_nonneg(term, ctx))
    results.extend(_r0016_norm_int_of_nonneg(term, ctx))
    results.extend(_r0017_sq_norm_sub_sq_im(term, ctx))
    results.extend(_r0018_sinh_neg(term, ctx))
    results.extend(_r0019_cosh_neg(term, ctx))
    results.extend(_r0020_tanh_neg(term, ctx))
    results.extend(_r0021_exp_sub_cosh(term, ctx))
    results.extend(_r0022_exp_sub_sinh(term, ctx))
    results.extend(_r0023_cosh_sub_sinh(term, ctx))
    results.extend(_r0024_sinh_sub_cosh(term, ctx))
    results.extend(_r0025_cosh_sq_sub_sinh_sq(term, ctx))
    results.extend(_r0026_sin_neg(term, ctx))
    results.extend(_r0027_cos_neg(term, ctx))
    results.extend(_r0028_cot_inv_eq_tan(term, ctx))
    results.extend(_r0029_tan_neg(term, ctx))
    results.extend(_r0030_sin_neg(term, ctx))
    results.extend(_r0031_cos_neg(term, ctx))
    results.extend(_r0032_cos_abs(term, ctx))
    results.extend(_r0033_cot_inv_eq_tan(term, ctx))
    results.extend(_r0034_tan_neg(term, ctx))
    results.extend(_r0035_sinh_neg(term, ctx))
    results.extend(_r0036_cosh_neg(term, ctx))
    results.extend(_r0037_cosh_abs(term, ctx))
    results.extend(_r0038_tanh_neg(term, ctx))
    results.extend(_r0039_exp_sub_cosh(term, ctx))
    results.extend(_r0040_exp_sub_sinh(term, ctx))
    results.extend(_r0041_cosh_sub_sinh(term, ctx))
    results.extend(_r0042_cosh_sq_sub_sinh_sq(term, ctx))
    results.extend(_r0043_coe_neg(term, ctx))
    results.extend(_r0044_re_neg(term, ctx))
    results.extend(_r0045_im_neg(term, ctx))
    results.extend(_r0046_toNat_add_toNat_neg_eq_nnnorm(term, ctx))
    results.extend(_r0047_toNat_add_toNat_neg_eq_norm(term, ctx))
    results.extend(_r0048_sqrt_of_nonneg(term, ctx))
    results.extend(_r0049_add_sqrt_self_sq_sub_one_inv(term, ctx))
    results.extend(_r0050_arsinh_neg(term, ctx))
    results.extend(_r0051_binEntropy_two_inv(term, ctx))
    results.extend(_r0052_binEntropy_eq_negMulLog_add_negMulLog_on(term, ctx))
    results.extend(_r0053_binEntropy_two_inv_add(term, ctx))
    results.extend(_r0054_arg_neg_I(term, ctx))
    results.extend(_r0055_arg_inv_coe_angle(term, ctx))
    results.extend(_r0056_arg_neg_eq_arg_sub_pi_of_im_pos(term, ctx))
    results.extend(_r0057_toCircle_neg(term, ctx))
    results.extend(_r0058_logb_abs(term, ctx))
    results.extend(_r0059_logb_neg_base_eq_logb(term, ctx))
    results.extend(_r0060_logb_neg_eq_logb(term, ctx))
    results.extend(_r0061_logb_inv_base(term, ctx))
    results.extend(_r0062_inv_logb(term, ctx))
    results.extend(_r0063_log_abs(term, ctx))
    results.extend(_r0064_posLog_abs(term, ctx))
    results.extend(_r0065_cpow_nat_inv_pow(term, ctx))
    results.extend(_r0066_mul_cpow_ofReal_nonneg(term, ctx))
    results.extend(_r0067_rpow_neg_natCast(term, ctx))
    results.extend(_r0068_norm_cpow_inv_nat(term, ctx))
    results.extend(_r0069_rpow_inv_rpow(term, ctx))
    results.extend(_r0070_pow_rpow_inv_natCast(term, ctx))
    results.extend(_r0071_sigmoid_neg(term, ctx))
    results.extend(_r0072_coe_neg(term, ctx))
    results.extend(_r0073_coe_sub(term, ctx))
    results.extend(_r0074_neg_coe_pi(term, ctx))
    results.extend(_r0075_two_nsmul_neg_pi_div_two(term, ctx))
    results.extend(_r0076_sin_sub_pi(term, ctx))
    results.extend(_r0077_cos_sub_pi(term, ctx))
    results.extend(_r0078_toReal_neg_eq_neg_toReal_iff(term, ctx))
    results.extend(_r0079_toReal_neg_pi_div_two(term, ctx))
    results.extend(_r0080_toReal_eq_neg_pi_div_two_iff(term, ctx))
    results.extend(_r0081_tan_sub_pi(term, ctx))
    results.extend(_r0082_sign_neg(term, ctx))
    results.extend(_r0083_sign_sub_pi(term, ctx))
    results.extend(_r0084_sign_pi_sub(term, ctx))
    results.extend(_r0085_sign_coe_neg_pi_div_two(term, ctx))
    results.extend(_r0086_arctan_neg(term, ctx))
    results.extend(_r0087_arctan_eq_neg_pi_div_four(term, ctx))
    results.extend(_r0088_sin_sub_pi(term, ctx))
    results.extend(_r0089_sin_sub_two_pi(term, ctx))
    results.extend(_r0090_sin_pi_sub(term, ctx))
    results.extend(_r0091_sin_two_pi_sub(term, ctx))
    results.extend(_r0092_sin_sub_nat_mul_two_pi(term, ctx))
    results.extend(_r0093_sin_sub_int_mul_two_pi(term, ctx))
    results.extend(_r0094_sin_nat_mul_two_pi_sub(term, ctx))
    results.extend(_r0095_sin_int_mul_two_pi_sub(term, ctx))
    results.extend(_r0096_cos_sub_pi(term, ctx))
    results.extend(_r0097_cos_sub_two_pi(term, ctx))
    results.extend(_r0098_cos_pi_sub(term, ctx))
    results.extend(_r0099_cos_two_pi_sub(term, ctx))
    results.extend(_r0100_cos_sub_nat_mul_two_pi(term, ctx))
    results.extend(_r0101_cos_sub_int_mul_two_pi(term, ctx))
    results.extend(_r0102_cos_nat_mul_two_pi_sub(term, ctx))
    results.extend(_r0103_cos_int_mul_two_pi_sub(term, ctx))
    results.extend(_r0104_exp_neg_pi_div_two_mul_I(term, ctx))
    results.extend(_r0105_exp_sub_pi_mul_I(term, ctx))
    results.extend(_r0106_abs_sinh(term, ctx))
    results.extend(_r0107_sinh_sub_id_strictMono(term, ctx))
    results.extend(_r0108_arcsin_eq_neg_pi_div_two(term, ctx))
    results.extend(_r0109_neg_pi_div_two_eq_arcsin(term, ctx))
    results.extend(_r0110_memberSubfamily_image_erase(term, ctx))
    results.extend(_r0111_subset_iff(term, ctx))
    results.extend(_r0112_neg_im(term, ctx))
    results.extend(_r0113_ofReal_neg(term, ctx))
    results.extend(_r0114_equivSubtype_symm_trans_valEmbedding(term, ctx))
    results.extend(_r0115_antisymm_iff(term, ctx))
    results.extend(_r0116_toDFinsupp_sub(term, ctx))
    results.extend(_r0117_prod_eq_mul_prod_subtype_ne(term, ctx))
    results.extend(_r0118_bodd_subNatNat(term, ctx))
    results.extend(_r0119_shiftRight_neg(term, ctx))
    results.extend(_r0120_shiftLeft_negSucc(term, ctx))
    results.extend(_r0121_shiftRight_negSucc(term, ctx))
    results.extend(_r0122_cast_neg(term, ctx))
    results.extend(_r0123_fib_neg_two(term, ctx))
    results.extend(_r0124_fib_of_nonneg(term, ctx))
    results.extend(_r0125_fib_of_odd(term, ctx))
    results.extend(_r0126_units_inv_eq_self(term, ctx))
    results.extend(_r0127_nnabs_of_nonneg(term, ctx))
    results.extend(_r0128_cast_natAbs_eq_nnabs_cast(term, ctx))
    results.extend(_r0129_cast_sub(term, ctx))
    results.extend(_r0130_cast_inv(term, ctx))
    results.extend(_r0131_num_neg_eq_neg_num(term, ctx))
    results.extend(_r0132_sub_intCast_den(term, ctx))
    results.extend(_r0133_intCast_sub_den(term, ctx))
    results.extend(_r0134_sub_natCast_den(term, ctx))
    results.extend(_r0135_natCast_sub_den(term, ctx))
    results.extend(_r0136_sub_ofNat_den(term, ctx))
    results.extend(_r0137_ofNat_sub_den(term, ctx))
    results.extend(_r0138_den_mul_den_eq_den_mul_gcd(term, ctx))
    results.extend(_r0139_sqrt_inv(term, ctx))
    results.extend(_r0140_fixingSubgroup_top(term, ctx))
    results.extend(_r0141_fixingSubgroup_bot(term, ctx))
    results.extend(_r0142_fixingSubgroup_sup(term, ctx))
    results.extend(_r0143_finrank_eq_finrank_subalgebra(term, ctx))
    results.extend(_r0144_coe_toSubfield(term, ctx))
    results.extend(_r0145_coe_type_toSubalgebra(term, ctx))
    results.extend(_r0146_coe_type_toSubfield(term, ctx))
    results.extend(_r0147_coe_neg(term, ctx))
    results.extend(_r0148_coe_inv(term, ctx))
    results.extend(_r0149_range_val(term, ctx))
    results.extend(_r0150_toSubfield_inj(term, ctx))
    results.extend(_r0151_extendScalars_toSubfield(term, ctx))
    results.extend(_r0152_weightedVSub_vadd(term, ctx))
    results.extend(_r0153_weightedVSubVSubWeights_apply_left(term, ctx))
    results.extend(_r0154_weightedVSubVSubWeights_apply_right(term, ctx))
    results.extend(_r0155_weightedVSubVSubWeights_apply_of_ne(term, ctx))
    results.extend(_r0156_sum_weightedVSubVSubWeights(term, ctx))
    results.extend(_r0157_eq_properDivisors_of_subset_of_sum_eq_su(term, ctx))
    results.extend(_r0158_goldenRatio_pow_sub_goldenRatio_pow(term, ctx))
    results.extend(_r0159_prod_inv(term, ctx))
    results.extend(_r0160_sum_sub(term, ctx))
    results.extend(_r0161_prod_subset(term, ctx))
    results.extend(_r0162_prod_subtype_mul_prod_subtype(term, ctx))
    results.extend(_r0163_prod_subset(term, ctx))
    results.extend(_r0164_prod_mulIndicator_subset(term, ctx))
    results.extend(_r0165_prod_Ico_add_right_sub_eq(term, ctx))
    results.extend(_r0166_prod_antidiagonal_subst(term, ctx))
    results.extend(_r0167_prod_neg(term, ctx))
    results.extend(_r0168_gcd_eq_of_dvd_sub(term, ctx))
    results.extend(_r0169_normalize_of_nonneg(term, ctx))
    results.extend(_r0170_nonneg_iff_normalize_eq_self(term, ctx))
    results.extend(_r0171_rev_sub(term, ctx))
    results.extend(_r0172_units_natAbs(term, ctx))
    results.extend(_r0173_natAbs_of_isUnit(term, ctx))
    results.extend(_r0174_isUnit_ne_iff_eq_neg(term, ctx))
    results.extend(_r0175_isUnit_eq_or_eq_neg(term, ctx))
    results.extend(_r0176_piFinset_inv(term, ctx))
    results.extend(_r0177_dens_inv(term, ctx))
    results.extend(_r0178_toFinset_vsub(term, ctx))
    results.extend(_r0179_f_eq(term, ctx))
    results.extend(_r0180_liftExtend_f(term, ctx))
    results.extend(_r0181_finsuppAntidiag_insert(term, ctx))
    results.extend(_r0182_antidiagonal_subtype_ext(term, ctx))
    results.extend(_r0183_mk_inv(term, ctx))
    results.extend(_r0184_subsemigroup_eq_subgroup(term, ctx))
    results.extend(_r0185_subgroup_eq_bot(term, ctx))
    results.extend(_r0186_floor_sub_intCast(term, ctx))
    results.extend(_r0187_abs_eq_natAbs(term, ctx))
    results.extend(_r0188_natAbs_abs(term, ctx))
    results.extend(_r0189_sign_mul_abs(term, ctx))
    results.extend(_r0190_sign_mul_self_eq_abs(term, ctx))
    results.extend(_r0191_bot_sub(term, ctx))
    results.extend(_r0192_inv_bot(term, ctx))
    results.extend(_r0193_toAddSubgroup_ball(term, ctx))
    results.extend(_r0194_cast_nonneg(term, ctx))
    results.extend(_r0195_mk_sub_mk(term, ctx))
    results.extend(_r0196_mk_mul_mk(term, ctx))
    results.extend(_r0197_mk_ratCast(term, ctx))
    results.extend(_r0198_abs_def(term, ctx))
    results.extend(_r0199_num_abs_eq_abs_num(term, ctx))
    results.extend(_r0200_units_ne_iff_eq_neg(term, ctx))
    results.extend(_r0201_norm_eq_norm_of_isMaxOn_of_ball_subset(term, ctx))
    results.extend(_r0202_eq_of_isMaxOn_of_ball_subset(term, ctx))
    results.extend(_r0203_norm_sub_eq_iff(term, ctx))
    results.extend(_r0204_norm_sub_eq(term, ctx))
    results.extend(_r0205_isBigO_re_sub_re(term, ctx))
    results.extend(_r0206_isBigO_im_sub_im(term, ctx))
    results.extend(_r0207_inv_eq_conj(term, ctx))
    results.extend(_r0208_eq_coe_norm_of_nonneg(term, ctx))
    results.extend(_r0209_exp_sub(term, ctx))
    results.extend(_r0210_exp_sub(term, ctx))
    results.extend(_r0211_abs_exp(term, ctx))
    results.extend(_r0212_expNear_sub(term, ctx))
    results.extend(_r0213_norm_invInterpStrip(term, ctx))
    results.extend(_r0214_cderiv_sub(term, ctx))
    results.extend(_r0215_sq_norm_sub_sq_re(term, ctx))
    results.extend(_r0216_nonneg_iff(term, ctx))
    results.extend(_r0217_neg_iff(term, ctx))
    results.extend(_r0218_sq_nonneg_iff(term, ctx))
    results.extend(_r0219_neg_re_eq_norm(term, ctx))
    results.extend(_r0220_re_eq_neg_norm(term, ctx))
    results.extend(_r0221_two_pi_I_inv_smul_circleIntegral_sub_sq(term, ctx))
    results.extend(_r0222_sinh_sub(term, ctx))
    results.extend(_r0223_cosh_sub(term, ctx))
    results.extend(_r0224_sin_sub(term, ctx))
    results.extend(_r0225_cos_sub(term, ctx))
    results.extend(_r0226_sin_sub_sin(term, ctx))
    results.extend(_r0227_cos_sub_cos(term, ctx))
    results.extend(_r0228_tan_inv_eq_cot(term, ctx))
    results.extend(_r0229_cos_sub_sin_I(term, ctx))
    results.extend(_r0230_sin_sub(term, ctx))
    results.extend(_r0231_cos_sub(term, ctx))
    results.extend(_r0232_tan_inv_eq_cot(term, ctx))
    results.extend(_r0233_sin_sq_eq_half_sub(term, ctx))
    results.extend(_r0234_sinh_sub(term, ctx))
    results.extend(_r0235_cosh_sub(term, ctx))
    results.extend(_r0236_sinh_sub_cosh(term, ctx))
    results.extend(_r0237_mk_neg(term, ctx))
    results.extend(_r0238_star_neg(term, ctx))
    results.extend(_r0239_centerMass_neg_left(term, ctx))
    results.extend(_r0240_centerMass_subset(term, ctx))
    results.extend(_r0241_fderiv_fourierChar_neg_bilinear_right_ap(term, ctx))
    results.extend(_r0242_fderiv_fourierChar_neg_bilinear_left_app(term, ctx))
    results.extend(_r0243_norm_of_nonneg(term, ctx))
    results.extend(_r0244_nnnorm_of_nonneg(term, ctx))
    results.extend(_r0245_enorm_of_nonneg(term, ctx))
    results.extend(_r0246_enorm_ofReal_of_nonneg(term, ctx))
    results.extend(_r0247_toNNReal_eq_nnnorm_of_nonneg(term, ctx))
    results.extend(_r0248_iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg(term, ctx))
    results.extend(_r0249_sqrt_neg_of_nonneg(term, ctx))
    results.extend(_r0250_sqrt_neg_I(term, ctx))
    results.extend(_r0251_arg_ofReal_of_nonneg(term, ctx))
    results.extend(_r0252_arg_ofReal_of_neg(term, ctx))
    results.extend(_r0253_arg_eq_neg_pi_div_two_iff(term, ctx))
    results.extend(_r0254_arg_of_re_nonneg(term, ctx))
    results.extend(_r0255_arg_of_re_neg_of_im_nonneg(term, ctx))
    results.extend(_r0256_arg_of_re_neg_of_im_neg(term, ctx))
    results.extend(_r0257_arg_of_im_neg(term, ctx))
    results.extend(_r0258_arg_inv(term, ctx))
    results.extend(_r0259_abs_arg_inv(term, ctx))
    results.extend(_r0260_arg_neg_eq_arg_add_pi_of_im_neg(term, ctx))
    results.extend(_r0261_arg_neg_eq_arg_sub_pi_iff(term, ctx))
    results.extend(_r0262_arg_neg_eq_arg_add_pi_iff(term, ctx))
    results.extend(_r0263_arg_neg_coe_angle(term, ctx))
    results.extend(_r0264_arg_mul_cos_add_sin_mul_I_sub(term, ctx))
    results.extend(_r0265_arg_cos_add_sin_mul_I_sub(term, ctx))
    results.extend(_r0266_log_exp_eq_sub_toIocDiv(term, ctx))
    results.extend(_r0267_log_neg_I(term, ctx))
    results.extend(_r0268_log_inv_eq_ite(term, ctx))
    results.extend(_r0269_log_inv(term, ctx))
    results.extend(_r0270_log_inv_eq_integral(term, ctx))
    results.extend(_r0271_log_sub_logTaylor_isBigO(term, ctx))
    results.extend(_r0272_log_sub_self_isBigO(term, ctx))
    results.extend(_r0273_exp_sub_sum_range_isBigO_pow(term, ctx))
    results.extend(_r0274_integral_rpow_mul_exp_neg_mul_Ioi(term, ctx))
    results.extend(_r0275_tsum_exp_neg_quadratic(term, ctx))
    results.extend(_r0276_tsum_exp_neg_mul_int_sq(term, ctx))
    results.extend(_r0277_tsum_exp_neg_mul_int_sq(term, ctx))
    results.extend(_r0278_logb_abs_base(term, ctx))
    results.extend(_r0279_logb_inv(term, ctx))
    results.extend(_r0280_inv_logb_mul_base(term, ctx))
    results.extend(_r0281_inv_logb_div_base(term, ctx))
    results.extend(_r0282_rpow_logb_of_neg(term, ctx))
    results.extend(_r0283_exp_log_eq_abs(term, ctx))
    results.extend(_r0284_exp_log_of_neg(term, ctx))
    results.extend(_r0285_log_neg_eq_log(term, ctx))
    results.extend(_r0286_log_inv(term, ctx))
    results.extend(_r0287_deriv_inv_log(term, ctx))
    results.extend(_r0288_negMulLog_def(term, ctx))
    results.extend(_r0289_negMulLog_eq_neg(term, ctx))
    results.extend(_r0290_negMulLog_mul(term, ctx))
    results.extend(_r0291_deriv_negMulLog(term, ctx))
    results.extend(_r0292_deriv2_negMulLog(term, ctx))
    results.extend(_r0293_posLog_sub_posLog_inv(term, ctx))
    results.extend(_r0294_half_mul_log_add_log_abs(term, ctx))
    results.extend(_r0295_posLog_neg(term, ctx))
    results.extend(_r0296_mulExpNegSq_apply(term, ctx))
    results.extend(_r0297_neg_mulExpNegMulSq_neg(term, ctx))
    results.extend(_r0298_deriv_mulExpNegMulSq(term, ctx))
    results.extend(_r0299_cpow_neg(term, ctx))
    results.extend(_r0300_cpow_sub(term, ctx))
    results.extend(_r0301_cpow_ofNat_inv_pow(term, ctx))
    results.extend(_r0302_pow_cpow_nat_inv(term, ctx))
    results.extend(_r0303_pow_cpow_ofNat_inv(term, ctx))
    results.extend(_r0304_sq_cpow_two_inv(term, ctx))
    results.extend(_r0305_inv_cpow_eq_ite(term, ctx))
    results.extend(_r0306_inv_cpow(term, ctx))
    results.extend(_r0307_rpow_eq_nhds_of_neg(term, ctx))
    results.extend(_r0308_toNNReal_rpow_of_nonneg(term, ctx))
    results.extend(_r0309_nnnorm_rpow_of_nonneg(term, ctx))
    results.extend(_r0310_rpow_def_of_nonneg(term, ctx))
    results.extend(_r0311_rpow_neg_ofNat(term, ctx))
    results.extend(_r0312_rpow_def_of_neg(term, ctx))
    results.extend(_r0313_abs_rpow_of_nonneg(term, ctx))
    results.extend(_r0314_rpow_inv_log(term, ctx))
    results.extend(_r0315_norm_rpow_of_nonneg(term, ctx))
    results.extend(_r0316_rpow_add_of_nonneg(term, ctx))
    results.extend(_r0317_rpow_sum_of_nonneg(term, ctx))
    results.extend(_r0318_rpow_neg_eq_inv_rpow(term, ctx))
    results.extend(_r0319_rpow_neg(term, ctx))
    results.extend(_r0320_rpow_sub(term, ctx))
    results.extend(_r0321_norm_cpow_eq_rpow_re_of_nonneg(term, ctx))
    results.extend(_r0322_cpow_mul_ofReal_nonneg(term, ctx))
    results.extend(_r0323_rpow_sub_intCast(term, ctx))
    results.extend(_r0324_rpow_sub_natCast(term, ctx))
    results.extend(_r0325_inv_rpow(term, ctx))
    results.extend(_r0326_rpow_rpow_inv(term, ctx))
    results.extend(_r0327_rpow_inv_natCast_pow(term, ctx))
    results.extend(_r0328_rpow_inv_eq(term, ctx))
    results.extend(_r0329_eq_rpow_inv(term, ctx))
    results.extend(_r0330_cpow_inv_two_re(term, ctx))
    results.extend(_r0331_cpow_inv_two_im_eq_sqrt(term, ctx))
    results.extend(_r0332_cpow_inv_two_im_eq_neg_sqrt(term, ctx))
    results.extend(_r0333_abs_cpow_inv_two_im(term, ctx))
    results.extend(_r0334_sigmoid_mul_rexp_neg(term, ctx))
    results.extend(_r0335_angle_eq_iff_two_pi_dvd_sub(term, ctx))
    results.extend(_r0336_two_zsmul_neg_pi_div_two(term, ctx))
    results.extend(_r0337_sub_coe_pi_eq_add_coe_pi(term, ctx))
    results.extend(_r0338_eq_neg_self_iff(term, ctx))
    results.extend(_r0339_neg_eq_self_iff(term, ctx))
    results.extend(_r0340_cos_eq_iff_coe_eq_or_eq_neg(term, ctx))
    results.extend(_r0341_cos_eq_real_cos_iff_eq_or_eq_neg(term, ctx))
    results.extend(_r0342_cos_eq_iff_eq_or_eq_neg(term, ctx))
    results.extend(_r0343_sin_neg(term, ctx))
    results.extend(_r0344_cos_neg(term, ctx))
    results.extend(_r0345_sin_sub_pi_div_two(term, ctx))
    results.extend(_r0346_sin_pi_div_two_sub(term, ctx))
    results.extend(_r0347_cos_sub_pi_div_two(term, ctx))
    results.extend(_r0348_cos_pi_div_two_sub(term, ctx))
    results.extend(_r0349_abs_toReal_neg(term, ctx))
    results.extend(_r0350_abs_toReal_neg_coe_eq_self_iff(term, ctx))
    results.extend(_r0351_toReal_coe_eq_self_sub_two_mul_int_mul_p(term, ctx))
    results.extend(_r0352_toReal_coe_eq_self_sub_two_pi_iff(term, ctx))
    results.extend(_r0353_two_nsmul_toReal_eq_two_mul_sub_two_pi(term, ctx))
    results.extend(_r0354_two_zsmul_toReal_eq_two_mul_sub_two_pi(term, ctx))
    results.extend(_r0355_tan_eq_inv_of_two_nsmul_add_two_nsmul_eq(term, ctx))
    results.extend(_r0356_tan_eq_inv_of_two_zsmul_add_two_zsmul_eq(term, ctx))
    results.extend(_r0357_toReal_neg_iff_sign_neg(term, ctx))
    results.extend(_r0358_coe_abs_toReal_of_sign_nonneg(term, ctx))
    results.extend(_r0359_neg_coe_abs_toReal_of_sign_nonpos(term, ctx))
    results.extend(_r0360_sign_two_nsmul_eq_neg_sign_iff(term, ctx))
    results.extend(_r0361_sign_two_zsmul_eq_neg_sign_iff(term, ctx))
    results.extend(_r0362_eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg(term, ctx))
    results.extend(_r0363_toReal_add_of_sign_pos_sign_neg(term, ctx))
    results.extend(_r0364_toReal_add_of_sign_eq_neg_sign(term, ctx))
    results.extend(_r0365_abs_toReal_add_eq_two_pi_sub_abs_toReal(term, ctx))
    results.extend(_r0366_abs_toReal_add_eq_two_pi_sub_abs_toReal(term, ctx))
    results.extend(_r0367_tan_sub(term, ctx))
    results.extend(_r0368_arctan_inv_sqrt_three(term, ctx))
    results.extend(_r0369_arctan_inv_of_pos(term, ctx))
    results.extend(_r0370_arctan_inv_of_neg(term, ctx))
    results.extend(_r0371_arctan_add_eq_sub_pi(term, ctx))
    results.extend(_r0372_two_mul_arctan_sub_pi(term, ctx))
    results.extend(_r0373_arctan_inv_2_add_arctan_inv_3(term, ctx))
    results.extend(_r0374_two_mul_arctan_inv_2_sub_arctan_inv_7(term, ctx))
    results.extend(_r0375_two_mul_arctan_inv_3_add_arctan_inv_7(term, ctx))
    results.extend(_r0376_four_mul_arctan_inv_5_sub_arctan_inv_239(term, ctx))
    results.extend(_r0377_sin_sub_int_mul_pi(term, ctx))
    results.extend(_r0378_sin_sub_nat_mul_pi(term, ctx))
    results.extend(_r0379_sin_int_mul_pi_sub(term, ctx))
    results.extend(_r0380_sin_nat_mul_pi_sub(term, ctx))
    results.extend(_r0381_abs_cos_int_mul_pi(term, ctx))
    results.extend(_r0382_cos_sub_int_mul_pi(term, ctx))
    results.extend(_r0383_cos_sub_nat_mul_pi(term, ctx))
    results.extend(_r0384_cos_int_mul_pi_sub(term, ctx))
    results.extend(_r0385_cos_nat_mul_pi_sub(term, ctx))
    results.extend(_r0386_cos_nat_mul_two_pi_sub_pi(term, ctx))
    results.extend(_r0387_cos_int_mul_two_pi_sub_pi(term, ctx))
    results.extend(_r0388_sin_sub_pi_div_two(term, ctx))
    results.extend(_r0389_sin_pi_div_two_sub(term, ctx))
    results.extend(_r0390_cos_sub_pi_div_two(term, ctx))
    results.extend(_r0391_cos_pi_div_two_sub(term, ctx))
    results.extend(_r0392_abs_sin_half(term, ctx))
    results.extend(_r0393_sin_half_eq_neg_sqrt(term, ctx))
    results.extend(_r0394_sqrtTwoAddSeries_nonneg(term, ctx))
    results.extend(_r0395_sin_sub_pi(term, ctx))
    results.extend(_r0396_sin_sub_two_pi(term, ctx))
    results.extend(_r0397_sin_pi_sub(term, ctx))
    results.extend(_r0398_sin_two_pi_sub(term, ctx))
    results.extend(_r0399_sin_sub_nat_mul_two_pi(term, ctx))
    return results


def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply inverse of ml_int_basic rewrite rules."""
    return []  # Inverse direction not yet implemented


# ════════════════════════════════════════════════════════════
# Untranslatable theorems (stored for reference)
# ════════════════════════════════════════════════════════════

UNTRANSLATABLE_THEOREMS = [
    ("Finset_mulSupport_of_fiberwise_prod_subset_image", "mulSupport_fun_b_a_in_s_with_g_a_eq_b_f_a_sub_s_image_g", "Not an equality or iff proposition"),
    ("Finsupp_prod_dvd_prod_of_subset_of_dvd", "f1_prod_g1_f2_prod_g2", "Not an equality or iff proposition"),
    ("Finset_support_prod_subset", "support_fun_x_i_in_s_f_i_x_sub_i_in_s_support_f_i", "Not an equality or iff proposition"),
    ("Nat_Prime_dvd_add_pow_sub_pow_of_dvd", "r_x_plus_y_pow_p_minus_y_pow_p", "Not an equality or iff proposition"),
    ("IntFractPair_of_inv_fr_num_lt_num_of_pos", "IntFractPair_of_qinv_fr_num_lt_q_num", "Not an equality or iff proposition"),
    ("Rat_inv_nonneg", "_0_le_ainv", "Not an equality or iff proposition"),
    ("Rat_div_nonneg", "_0_le_a_slash_b", "Not an equality or iff proposition"),
    ("Int_finsetGcd_nonneg", "_0_le_s_gcd_f", "Not an equality or iff proposition"),
    ("Int_nonneg_of_normalize_eq_self", "_0_le_z", "Not an equality or iff proposition"),
    ("Finset_Icc_mul_Icc_subset", "_unknown", "Empty proposition"),
    ("Finset_Iic_mul_Iic_subset", "_unknown", "Empty proposition"),
    ("Finset_Ici_mul_Ici_subset", "_unknown", "Empty proposition"),
    ("Finset_smul_subset_smul", "s_1_sub_s_2_to_t_1_sub_t_2_to_s_1_t_1_sub_s_2_t_2", "Not an equality or iff proposition"),
    ("Finset_smul_subset_smul_left", "t_1_sub_t_2_to_s_t_1_sub_s_t_2", "Not an equality or iff proposition"),
    ("Finset_smul_subset_smul_right", "s_1_sub_s_2_to_s_1_t_sub_s_2_t", "Not an equality or iff proposition"),
    ("Finset_inter_smul_subset", "s_1_inter_s_2_t_sub_s_1_t_inter_s_2_t", "Not an equality or iff proposition"),
    ("Finset_smul_inter_subset", "s_t_1_inter_t_2_sub_s_t_1_inter_s_t_2", "Not an equality or iff proposition"),
    ("Finset_subset_smul", "u_sub_s_t_to_exists_s_prime_colon_Finset_a_t_prime_colon_Finset_b_s_prime_sub_s_and_t_prime_sub_t_and_u_sub_s_prime_t_prime", "Not an equality or iff proposition"),
    ("Finite_vsub", "Set_Finite_s_minus_t", "Not an equality or iff proposition"),
    ("FiniteMulArchimedeanClass_subgroup_strictAnti", "StrictAnti_subgroup_M_colon_eq_M", "Not an equality or iff proposition"),
    ("FiniteMulArchimedeanClass_ballSubgroup_strictAnti", "StrictAnti_ballSubgroup_M_colon_eq_M", "Not an equality or iff proposition"),
    ("Finset_expect_nonneg", "_0_le_i_in_s_f_i", "Not an equality or iff proposition"),
    ("Finset_prod_nonneg", "_0_le_i_in_s_f_i", "Not an equality or iff proposition"),
    ("Finset_sum_sq_le_sq_sum_of_nonneg", "i_in_s_f_i_pow_2_le_i_in_s_f_i_pow_2", "Not an equality or iff proposition"),
    ("Nat_cast_le_pow_sub_div_sub", "n_colon_a_le_a_pow_n_minus_1_slash_a_minus_1", "Not an equality or iff proposition"),
    ("Nat_cast_le_pow_div_sub", "n_colon_a_le_a_pow_n_slash_a_minus_1", "Not an equality or iff proposition"),
    ("Int_ceil_nonneg", "_0_le_a", "Not an equality or iff proposition"),
    ("Finsupp_support_floorDiv_subset", "f_slash_a_support_sub_f_support", "Not an equality or iff proposition"),
    ("Int_abs_sub_lt_of_lt_lt", "pipe_b_colon_minus_apipe_lt_m", "Not an equality or iff proposition"),
    ("Finset_sup_mul_le_mul_sup_of_nonneg", "s_sup_a_star_b_le_s_sup_a_star_s_sup_b", "Not an equality or iff proposition"),
    ("Finset_mul_inf_le_inf_mul_of_nonneg", "s_inf_a_star_s_inf_b_le_s_inf_a_star_b", "Not an equality or iff proposition"),
    ("FiniteArchimedeanClass_submodule_strictAnti", "StrictAnti_submodule_K_M_colon_eq_M", "Not an equality or iff proposition"),
    ("ArchimedeanClass_FiniteResidueField_mul_le_mul_of_nonneg_left", "_unknown", "Empty proposition"),
    ("Rat_mkRat_nonneg", "_0_le_mkRat_a_b", "Not an equality or iff proposition"),
    ("Rat_ofScientific_nonneg", "_0_le_Rat_ofScientific_m_s_e", "Not an equality or iff proposition"),
    ("Rat_mkRat_neg", "mkRat_a_b_lt_0", "Not an equality or iff proposition"),
    ("Rat_abs_def", "_unknown", "Empty proposition"),
    ("Nat_sub_dvd_pow_sub_pow", "x_minus_y_x_pow_n_minus_y_pow_n", "Not an equality or iff proposition"),
    ("Nat_pow_sub_pow_dvd_pow_sub_pow", "x_pow_m_minus_y_pow_m_x_pow_k_minus_y_pow_k", "Not an equality or iff proposition"),
    ("Int_even_sub", "_unknown", "Empty proposition"),
    ("Int_odd_sub", "_unknown", "Empty proposition"),
    ("Int_four_dvd_add_or_sub_of_odd", "_4_a_plus_b_or_4_a_minus_b", "Not an equality or iff proposition"),
    ("Nat_even_sub", "_unknown", "Empty proposition"),
    ("Nat_Odd_sub_odd", "Even_m_minus_n", "Not an equality or iff proposition"),
    ("Nat_Odd_sub_even", "Odd_m_minus_n", "Not an equality or iff proposition"),
    ("Nat_odd_sub", "_unknown", "Empty proposition"),
    ("Nat_Even_sub_odd", "Odd_m_minus_n", "Not an equality or iff proposition"),
    ("Finset_mul_add_subset", "s_star_t_plus_u_sub_s_star_t_plus_s_star_u", "Not an equality or iff proposition"),
    ("Finset_add_mul_subset", "s_plus_t_star_u_sub_s_star_u_plus_t_star_u", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_neg", "Integrable_I_l_minus_f_vol", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_of_neg", "Integrable_I_l_f_vol", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_sub", "Integrable_I_l_f_minus_g_vol", "Not an equality or iff proposition"),
    ("BoxIntegral_Integrable_to_subbox", "Integrable_J_l_f_vol", "Not an equality or iff proposition"),
    ("BoxIntegral_IntegrationParams_MemBaseSet_unionComplToSubordinate", "l_MemBaseSet_I_c_r_1_pi_1_unionComplToSubordinate_pi_2_hU_r_2", "Not an equality or iff proposition"),
    ("Complex_norm_sub_mem_Icc_angle", "x_minus_y_in_Icc_2_slash_pi_star_angle_x_y_angle_x_y", "Not an equality or iff proposition"),
    ("Complex_norm_sub_le_angle", "x_minus_y_le_angle_x_y", "Not an equality or iff proposition"),
    ("Complex_mul_angle_le_norm_sub", "_2_slash_pi_star_angle_x_y_le_x_minus_y", "Not an equality or iff proposition"),
    ("Complex_angle_le_mul_norm_sub", "angle_x_y_le_pi_slash_2_star_x_minus_y", "Not an equality or iff proposition"),
    ("Complex_norm_of_nonneg", "_unknown", "Empty proposition"),
    ("Complex_norm_le_norm_two_mul_sub", "z_le_2_star_M_minus_z", "Not an equality or iff proposition"),
    ("Complex_Convex_rectangle_subset", "Rectangle_z_w_sub_U", "Not an equality or iff proposition"),
    ("Real_quadratic_le_exp_of_nonneg", "_1_plus_x_plus_x_pow_2_slash_2_le_exp_x", "Not an equality or iff proposition"),
    ("Real_exp_nonneg", "_0_le_exp_x", "Not an equality or iff proposition"),
    ("Real_one_sub_lt_exp_neg", "_1_minus_x_lt_exp_minus_x", "Not an equality or iff proposition"),
    ("Real_one_sub_le_exp_neg", "_1_minus_x_le_exp_minus_x", "Not an equality or iff proposition"),
    ("Real_one_sub_div_pow_le_exp_neg", "_1_minus_t_slash_n_pow_n_le_exp_minus_t", "Not an equality or iff proposition"),
    ("Real_le_inv_mul_exp", "x_le_cinv_star_exp_c_star_x", "Not an equality or iff proposition"),
    ("Complex_HadamardThreeLines_sSupNormIm_nonneg", "_0_le_sSupNormIm_f_x", "Not an equality or iff proposition"),
    ("Complex_HadamardThreeLines_diffContOnCl_invInterpStrip", "DiffContOnCl_fun_z_invInterpStrip_f_z_e_verticalStrip_0_1", "Not an equality or iff proposition"),
    ("Complex_norm_nonneg", "_0_le_z", "Not an equality or iff proposition"),
    ("Complex_norm_neg", "_unknown", "Empty proposition"),
    ("Real_cos_two_neg", "cos_2_lt_0", "Not an equality or iff proposition"),
    ("Real_integrable_prod_sub", "Integrable_fun_p_colon_E_times_E_B_star_f_1_p_1_minus_p_2_star_f_2_p_2_volume_prod", "Not an equality or iff proposition"),
    ("Real_hasFDerivAt_fourierChar_neg_bilinear_right", "HasFDerivAt_fun_w_minus_L_v_w_colon_minus_2_star_pi_star_I_star_minus_L_v_w_ofRea", "Not an equality or iff proposition"),
    ("Real_differentiable_fourierChar_neg_bilinear_right", "Differentiable_fun_w_minus_L_v_w_colon", "Not an equality or iff proposition"),
    ("Real_hasFDerivAt_fourierChar_neg_bilinear_left", "HasFDerivAt_fun_v_minus_L_v_w_colon_minus_2_star_pi_star_I_star_minus_L_v_w_ofRea", "Not an equality or iff proposition"),
    ("Real_differentiable_fourierChar_neg_bilinear_left", "Differentiable_fun_v_minus_L_v_w_colon", "Not an equality or iff proposition"),
    ("Real_young_inequality_of_nonneg", "a_star_b_le_a_pow_p_slash_p_plus_b_pow_q_slash_q", "Not an equality or iff proposition"),
    ("Real_inner_le_Lp_mul_Lq_of_nonneg", "i_in_s_f_i_star_g_i_le_i_in_s_f_i_pow_p_pow_1_slash_p_star_i_in_s_g_i_pow_q_pow_1_slash_q", "Not an equality or iff proposition"),
    ("Real_Lr_rpow_le_Lp_mul_Lq_of_nonneg", "i_in_s_f_i_star_g_i_pow_r_le_i_in_s_f_i_pow_p_pow_r_slash_p_star_i_in_s_g_i_pow_q_pow", "Not an equality or iff proposition"),
    ("Real_inner_le_weight_mul_Lp_of_nonneg", "i_in_s_w_i_star_f_i_le_i_in_s_w_i_pow_1_minus_pinv_star_i_in_s_w_i_star_f_i_pow_p_pow_pinv", "Not an equality or iff proposition"),
    ("Real_compact_inner_le_weight_mul_Lp_of_nonneg", "i_in_s_w_i_star_f_i_le_i_in_s_w_i_pow_1_minus_pinv_star_i_in_s_w_i_star_f_i_pow_p_pow_pinv", "Not an equality or iff proposition"),
    ("Real_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg", "prime_i_f_i_star_g_i_pow_r_le_prime_i_f_i_pow_p_pow_r_slash_p_star_prime_i_g_i_pow_q_pow_r_slash_q", "Not an equality or iff proposition"),
    ("Real_Lr_le_Lp_mul_Lq_tsum_of_nonneg", "prime_i_f_i_star_g_i_pow_r_pow_1_slash_r_le_prime_i_f_i_pow_p_pow_1_slash_p_star_prime_i_g_i_pow_q", "Not an equality or iff proposition"),
    ("Real_inner_le_Lp_mul_Lq_tsum_of_nonneg", "prime_i_f_i_star_g_i_le_prime_i_f_i_pow_p_pow_1_slash_p_star_prime_i_g_i_pow_q_pow_1_slash_q", "Not an equality or iff proposition"),
    ("Real_inner_le_Lp_mul_Lq_hasSum_of_nonneg", "exists_C_colon_0_le_C_and_C_le_A_star_B_and_HasSum_fun_i_eq_gt_f_i_star_g_i_C", "Not an equality or iff proposition"),
    ("Real_Lp_add_le_of_nonneg", "i_in_s_f_i_plus_g_i_pow_p_pow_1_slash_p_le_i_in_s_f_i_pow_p_pow_1_slash_p_plus_i", "Not an equality or iff proposition"),
    ("Real_Lp_add_le_tsum_of_nonneg", "_unknown", "Empty proposition"),
    ("Real_Lp_add_le_hasSum_of_nonneg", "exists_C_0_le_C_and_C_le_A_plus_B_and_HasSum_fun_i_eq_gt_f_i_plus_g_i_pow_p_C_pow_p", "Not an equality or iff proposition"),
    ("Real_ofDigitsTerm_nonneg", "_0_le_ofDigitsTerm_digits_n", "Not an equality or iff proposition"),
    ("Real_ofDigits_nonneg", "_0_le_ofDigits_digits", "Not an equality or iff proposition"),
    ("Real_abs_ofDigits_sub_ofDigits_le", "pipe_ofDigits_x_minus_ofDigits_ypipe_le_b_colon_pow_n_inv", "Not an equality or iff proposition"),
    ("Real_arcosh_nonneg", "_0_le_arcosh_x", "Not an equality or iff proposition"),
    ("Real_artanh_neg", "artanh_x_lt_0", "Not an equality or iff proposition"),
    ("Real_artanh_nonneg", "_0_le_artanh_x", "Not an equality or iff proposition"),
    ("Real_binEntropy_eq_negMulLog_add_negMulLog_one_sub", "_unknown", "Empty proposition"),
    ("Real_binEntropy_nonneg", "_0_le_binEntropy_p", "Not an equality or iff proposition"),
    ("Real_binEntropy_neg_of_neg", "binEntropy_p_lt_0", "Not an equality or iff proposition"),
    ("Real_qaryEntropy_nonneg", "_0_le_qaryEntropy_q_p", "Not an equality or iff proposition"),
    ("Real_qaryEntropy_neg_of_neg", "qaryEntropy_q_p_lt_0", "Not an equality or iff proposition"),
    ("Complex_hasDerivAt_log_sub_logTaylor", "HasDerivAt_fun_z_colon_log_1_plus_z_minus_logTaylor_n_plus_1_z_minus_z_pow_n_star_1_plus_z_inv", "Not an equality or iff proposition"),
    ("Complex_norm_log_sub_logTaylor_le", "log_1_plus_z_minus_logTaylor_n_plus_1_z_le_z_pow_n_plus_1_star_1_minus_z_inv_slash_n_plus_1", "Not an equality or iff proposition"),
    ("Complex_norm_log_one_sub_inv_add_logTaylor_neg_le", "log_1_minus_z_inv_plus_logTaylor_n_plus_1_minus_z_le_z_pow_n_plus_1_star_1_minus_z_inv_slash_n_plus_1", "Not an equality or iff proposition"),
    ("Complex_norm_log_one_sub_inv_sub_self_le", "log_1_minus_z_inv_minus_z_le_z_pow_2_star_1_minus_z_inv_slash_2", "Not an equality or iff proposition"),
    ("Complex_hasSum_taylorSeries_neg_log", "HasSum_fun_n_colon_z_pow_n_slash_n_minus_log_1_minus_z", "Not an equality or iff proposition"),
    ("Complex_tendsto_pow_exp_of_isLittleO_sub_add_div", "Tendsto_fun_n_f_n_pow_n_atTop_exp_t", "Not an equality or iff proposition"),
    ("Real_rpowIntegrand_0_1_nonneg", "_0_le_rpowIntegrand_0_1_p_t_x", "Not an equality or iff proposition"),
    ("Real_rpowIntegrand_0_1_le_rpow_sub_two_mul_self", "rpowIntegrand_0_1_p_t_x_le_t_pow_p_minus_2_star_x", "Not an equality or iff proposition"),
    ("Real_Gamma_nonneg_of_nonneg", "_0_le_Gamma_s", "Not an equality or iff proposition"),
    ("Complex_differentiable_Gamma_inv", "Differentiable_fun_s_Gamma_s_inv", "Not an equality or iff proposition"),
    ("Complex_not_continuousAt_Gamma_neg_nat", "not_ContinuousAt_Gamma_minus_n", "Not an equality or iff proposition"),
    ("Complex_not_differentiableAt_Gamma_neg_nat", "not_DifferentiableAt_Gamma_minus_n", "Not an equality or iff proposition"),
    ("Real_tendsto_logb_comp_add_sub_logb", "Tendsto_fun_x_colon_eq_gt_logb_b_x_plus_y_minus_logb_b_x_atTop_0", "Not an equality or iff proposition"),
    ("Real_log_neg", "log_x_lt_0", "Not an equality or iff proposition"),
    ("Real_log_nonneg", "_0_le_log_x", "Not an equality or iff proposition"),
    ("Real_log_natCast_nonneg", "_0_le_log_n", "Not an equality or iff proposition"),
    ("Real_log_neg_natCast_nonneg", "_0_le_log_minus_n", "Not an equality or iff proposition"),
    ("Real_log_intCast_nonneg", "_0_le_log_n", "Not an equality or iff proposition"),
    ("Real_one_sub_inv_le_log_of_pos", "_1_minus_xinv_le_log_x", "Not an equality or iff proposition"),
    ("Real_neg_inv_le_log", "minus_xinv_le_log_x", "Not an equality or iff proposition"),
    ("Real_tendsto_log_comp_add_sub_log", "Tendsto_fun_x_colon_eq_gt_log_x_plus_y_minus_log_x_atTop_0", "Not an equality or iff proposition"),
    ("Real_not_continuousAt_inv_log_neg_one", "not_ContinuousAt_fun_x_log_x_inv_minus_1", "Not an equality or iff proposition"),
    ("Real_mul_log_nonneg", "_0_le_x_star_log_x", "Not an equality or iff proposition"),
    ("Real_negMulLog_nonneg", "_0_le_negMulLog_x", "Not an equality or iff proposition"),
    ("Real_continuous_negMulLog", "Continuous_negMulLog", "Not an equality or iff proposition"),
    ("Real_differentiableOn_negMulLog", "DifferentiableOn_negMulLog_0", "Not an equality or iff proposition"),
    ("Real_hasDerivAt_negMulLog", "HasDerivAt_negMulLog_minus_log_x_minus_1_x", "Not an equality or iff proposition"),
    ("Real_strictConcaveOn_negMulLog", "StrictConcaveOn_Set_Ici_0_colon_negMulLog", "Not an equality or iff proposition"),
    ("Real_concaveOn_negMulLog", "ConcaveOn_Set_Ici_0_colon_negMulLog", "Not an equality or iff proposition"),
    ("Real_posLog_nonneg", "_0_le_logpos_x", "Not an equality or iff proposition"),
    ("Real_norm_inv_mul_rpow_sub_one_sub_log_le", "pinv_star_x_pow_p_minus_1_minus_log_x_le_p_star_log_x_pow_2", "Not an equality or iff proposition"),
    ("Real_neg_one_le_mulExpNegMulSq_one", "minus_1_le_mulExpNegMulSq_1_x", "Not an equality or iff proposition"),
    ("Real_continuous_mulExpNegMulSq", "Continuous_fun_x_eq_gt_mulExpNegMulSq_e_x", "Not an equality or iff proposition"),
    ("Continuous_mulExpNegMulSq", "Continuous_fun_x_eq_gt_mulExpNegMulSq_e_f_x", "Not an equality or iff proposition"),
    ("Real_differentiableAt_mulExpNegMulSq", "DifferentiableAt_mulExpNegMulSq_e_y", "Not an equality or iff proposition"),
    ("Real_differentiable_mulExpNegMulSq", "Differentiable_mulExpNegMulSq_e", "Not an equality or iff proposition"),
    ("Real_hasDerivAt_mulExpNegMulSq", "HasDerivAt_mulExpNegMulSq_e_exp_minus_e_star_y_star_y_plus_y_star_exp_minus_e_star_y_star_y", "Not an equality or iff proposition"),
    ("Real_abs_mulExpNegMulSq_le", "pipe_mulExpNegMulSq_e_xpipe_le_e_inv", "Not an equality or iff proposition"),
    ("Real_dist_mulExpNegMulSq_le_two_mul_sqrt", "dist_mulExpNegMulSq_e_x_mulExpNegMulSq_e_y_le_2_star_e_inv", "Not an equality or iff proposition"),
    ("Real_dist_mulExpNegMulSq_le_dist", "dist_mulExpNegMulSq_e_x_mulExpNegMulSq_e_y_le_dist_x_y", "Not an equality or iff proposition"),
    ("Real_tendsto_mulExpNegMulSq", "Tendsto_fun_e_eq_gt_mulExpNegMulSq_e_x_0_x", "Not an equality or iff proposition"),
    ("Real_abs_mulExpNegMulSq_comp_le_norm", "pipe_mulExpNegMulSq_e_comp_g_xpipe_le_g", "Not an equality or iff proposition"),
    ("Complex_inv_cpow_eq_ite", "_unknown", "Empty proposition"),
    ("Real_rpow_nonneg", "_0_le_x_pow_y", "Not an equality or iff proposition"),
    ("Real_rpow_sub", "_unknown", "Empty proposition"),
    ("Real_rpow_sub_intCast", "_unknown", "Empty proposition"),
    ("Real_rpow_sub_natCast", "_unknown", "Empty proposition"),
    ("Real_rpow_lt_rpow_of_neg", "y_pow_z_lt_x_pow_z", "Not an equality or iff proposition"),
    ("Complex_inv_natCast_cpow_ofReal_pos", "_0_lt_n_colon_pow_x_colon_inv", "Not an equality or iff proposition"),
    ("Real_sigmoid_nonneg", "_0_le_sigmoid_x", "Not an equality or iff proposition"),
    ("Real_smoothTransition_pos_denom", "_0_lt_expNegInvGlue_x_plus_expNegInvGlue_1_minus_x", "Not an equality or iff proposition"),
    ("Real_smoothTransition_nonneg", "_0_le_smoothTransition_x", "Not an equality or iff proposition"),
    ("Real_Angle_sign_coe_nonneg_of_nonneg_of_le_pi", "_0_le_th_colon_Angle_sign", "Not an equality or iff proposition"),
    ("Real_Angle_sign_neg_coe_nonpos_of_nonneg_of_le_pi", "minus_th_colon_Angle_sign_le_0", "Not an equality or iff proposition"),
    ("Real_tan_sub", "_unknown", "Empty proposition"),
    ("Real_neg_pi_div_two_lt_arctan", "minus_pi_slash_2_lt_arctan_x", "Not an equality or iff proposition"),
    ("Real_tendsto_abs_tan_atTop", "Tendsto_fun_x_eq_gt_abs_tan_x_ne_2_star_k_plus_1_star_pi_slash_2_atTop", "Not an equality or iff proposition"),
    ("Real_pi_nonneg", "_0_le_pi", "Not an equality or iff proposition"),
    ("Real_sin_nonneg_of_mem_Icc", "_0_le_sin_x", "Not an equality or iff proposition"),
    ("Real_sin_nonneg_of_nonneg_of_le_pi", "_0_le_sin_x", "Not an equality or iff proposition"),
    ("Real_sin_neg_of_neg_of_neg_pi_lt", "sin_x_lt_0", "Not an equality or iff proposition"),
    ("Real_sin_nonpos_of_nonpos_of_neg_pi_le", "sin_x_le_0", "Not an equality or iff proposition"),
    ("Real_cos_nonneg_of_mem_Icc", "_0_le_cos_x", "Not an equality or iff proposition"),
    ("Real_cos_nonneg_of_neg_pi_div_two_le_of_le", "_0_le_cos_x", "Not an equality or iff proposition"),
    ("Real_cos_neg_of_pi_div_two_lt_of_lt", "cos_x_lt_0", "Not an equality or iff proposition"),
    ("Real_cos_le_cos_of_nonneg_of_le_pi", "cos_y_le_cos_x", "Not an equality or iff proposition"),
    ("Complex_norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le", "exp_a_star_exp_z_plus_exp_minus_z_le_Real_exp_a_star_Real_cos_b_star_Real_exp_pipe_z_repipe", "Not an equality or iff proposition"),
    ("Real_sin_gt_sub_cube", "x_minus_x_pow_3_slash_4_lt_sin_x", "Not an equality or iff proposition"),
    ("Real_abs_sin_sub_sin_le", "pipe_sin_x_minus_sin_ypipe_le_pipe_x_minus_ypipe", "Not an equality or iff proposition"),
    ("Real_abs_cos_sub_cos_le", "pipe_cos_x_minus_cos_ypipe_le_pipe_x_minus_ypipe", "Not an equality or iff proposition"),
    ("Complex_tan_sub", "_unknown", "Empty proposition"),
    ("Real_neg_pi_div_two_le_arcsin", "minus_pi_slash_2_le_arcsin_x", "Not an equality or iff proposition"),
    ("Real_cos_arcsin_nonneg", "_0_le_cos_arcsin_x", "Not an equality or iff proposition"),
    ("Real_arccos_nonneg", "_0_le_arccos_x", "Not an equality or iff proposition"),
    ("Real_sin_div_le_inv_abs", "sin_x_slash_x_le_pipe_xpipe_inv", "Not an equality or iff proposition"),
    ("Real_sinc_le_inv_abs", "sinc_x_le_pipe_xpipe_inv", "Not an equality or iff proposition"),
    ("Finset_subset_mulSpan", "s_sub_mulSpan_s", "Not an equality or iff proposition"),
    ("Finset_mulDysonETransform_subset", "mulDysonETransform_e_x_1_star_mulDysonETransform_e_x_2_sub_x_1_star_x_2", "Not an equality or iff proposition"),
    ("Finset_mulDysonETransform_smul_finset_snd_subset_fst", "e_mulDysonETransform_e_x_2_sub_mulDysonETransform_e_x_1", "Not an equality or iff proposition"),
    ("Finset_ruzsa_triangle_inequality_mulInv_mulInv_mulInv", "hash_A_star_Cinv_star_hash_B_le_hash_A_star_Binv_star_hash_C_star_Binv", "Not an equality or iff proposition"),
    ("Finset_ruzsa_triangle_inequality_invMul_invMul_invMul", "hash_B_star_hash_Ainv_star_C_le_hash_Binv_star_A_star_hash_Binv_star_C", "Not an equality or iff proposition"),
    ("Finset_ruzsa_triangle_inequality_mulInv_mul_mul", "hash_A_star_Cinv_star_hash_B_le_hash_A_star_B_star_hash_C_star_B", "Not an equality or iff proposition"),
    ("Finset_ruzsa_triangle_inequality_invMul_mul_mul", "hash_B_star_hash_Ainv_star_C_le_hash_B_star_A_star_hash_B_star_C", "Not an equality or iff proposition"),
    ("Finset_ruzsa_triangle_inequality_mul_mulInv_mul", "hash_B_star_hash_A_star_C_le_hash_B_star_Ainv_star_hash_B_star_C", "Not an equality or iff proposition"),
    ("Finset_ruzsa_triangle_inequality_mul_mul_invMul", "hash_A_star_C_star_hash_B_le_hash_A_star_B_star_hash_Cinv_star_B", "Not an equality or iff proposition"),
    ("Finset_small_neg_pos_pos_mul", "hash_Ainv_star_A_star_A_le_K_pow_2_star_hash_A", "Not an equality or iff proposition"),
    ("Finset_small_neg_neg_pos_mul", "hash_Ainv_star_Ainv_star_A_le_K_pow_2_star_hash_A", "Not an equality or iff proposition"),
    ("Finset_small_pos_neg_neg_mul", "hash_A_star_Ainv_star_Ainv_le_K_pow_2_star_hash_A", "Not an equality or iff proposition"),
    ("Finset_small_pos_pos_neg_mul", "hash_A_star_A_star_Ainv_le_K_pow_2_star_hash_A", "Not an equality or iff proposition"),
    ("Finset_small_pos_neg_pos_mul", "hash_A_star_Ainv_star_A_le_K_pow_3_star_hash_A", "Not an equality or iff proposition"),
    ("Finset_small_neg_pos_neg_mul", "hash_Ainv_star_A_star_Ainv_le_K_pow_3_star_hash_A", "Not an equality or iff proposition"),
    ("Finset_subset_subsetSum", "A_sub_A_subsetSum", "Not an equality or iff proposition"),
    ("Finset_subsetSum_mono", "A_subsetSum_sub_B_subsetSum", "Not an equality or iff proposition"),
    ("Finset_vadd_finset_subsetSum_subset_subsetSum_insert", "a_plus_A_subsetSum_sub_insert_a_A_subsetSum", "Not an equality or iff proposition"),
    ("Finset_nonneg_of_mem_subsetSum", "forall_x_in_A_subsetSum_0_le_x", "Not an equality or iff proposition"),
    ("Finset_card_choose_two_lt_card_subsetSum_of_nonneg", "hash_A_choose_2_lt_hash_A_subsetSum", "Not an equality or iff proposition"),
    ("Finset_mul_inv_eq_inv_mul_of_doubling_lt_two_aux", "Ainv_star_A_sub_A_star_Ainv", "Not an equality or iff proposition"),
    ("Finset_weak_invMulSubgroup_bound", "hash_Ainv_star_A_lt_2_star_hash_A", "Not an equality or iff proposition"),
    ("Finset_A_subset_aH", "A_sub_a_Ainv_star_A", "Not an equality or iff proposition"),
    ("Finset_subgroup_strong_bound_left", "A_star_A_sub_a_op_a_Ainv_star_A", "Not an equality or iff proposition"),
]
